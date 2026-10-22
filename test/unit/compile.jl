using MatchMaker
using MatchMaker: NodePlan, Matcher
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic, FnType
using Moshi.Match: @match
using Test

@syms x y z f(x) g(x)
f2 = Sym{SymReal}(:f2; type = FnType{Tuple{Number, Number}, Number, Nothing})
hfn = set_operation_traits(
    Sym{SymReal}(:hf; type = FnType{Tuple{Number, Number}, Number, Nothing});
    associative = true
)
gfn = set_operation_traits(
    Sym{SymReal}(:gf; type = FnType{Tuple{Number, Number}, Number, Nothing});
    commutative = true
)

@testset "plan shapes" begin
    m = compile_pattern(slot(x) + 2)
    @test m isa Matcher
    @test m.nvars == 1
    @test m.var_syms[1] === x
    @match m.plans[m.root] begin
        NodePlan.ACCall(op, _, _, _, _, _) => @test op === (+)
        _ => @test false
    end
    @match m.plans[m.ir[slot(x)]] begin
        NodePlan.Slot(vid, opt) => (@test vid == 1 && !opt)
        _ => @test false
    end

    m2 = compile_pattern(f(slot(x)))
    @match m2.plans[m2.root] begin
        NodePlan.Call(op, head, children) =>
            (@test op === f && head != 0 && length(children) == 1)
        _ => @test false
    end

    m3 = compile_pattern(hfn(slot(x), y))         # assoc-only symbolic head
    @match m3.plans[m3.root] begin
        NodePlan.AssocCall(_, head, children) =>
            (@test head != 0 && length(children) == 2)
        _ => @test false
    end

    m4 = compile_pattern(gfn(slot(x), slot(y)))   # comm-only symbolic head
    @match m4.plans[m4.root] begin
        NodePlan.CommCall(_, _, fixed, slots, _, _) =>
            (@test isempty(fixed) && length(slots) == 2)
        _ => @test false
    end

    m5 = compile_pattern(segment(x) * 3)
    @match m5.plans[m5.ir[segment(x)]] begin
        NodePlan.Segment(vid) => @test vid == 1
        _ => @test false
    end

    # head-slot: slot(f)(y) — §4.10
    m6 = compile_pattern(slot(f)(y))
    @match m6.plans[m6.root] begin
        NodePlan.Call(op, head, children) => begin
            @test is_marker_term(op) && head != 0 && length(children) == 1
            @match m6.plans[head] begin
                NodePlan.Slot(_, _) => @test true
                _ => @test false
            end
        end
        _ => @test false
    end
end

@testset "ground flags" begin
    m = compile_pattern(sin(x) + slot(y))
    @test m.is_ground[m.ir[sin(x)]]
    @test m.is_ground[m.ir[x]]
    @test !m.is_ground[m.root]
    @test !m.is_ground[m.ir[slot(y)]]

    # var-free pattern compiles and is fully ground
    mg = compile_pattern(x + 2)
    @test mg.nvars == 0
    @test all(mg.is_ground)
end

@testset "var table" begin
    m = compile_pattern(slot(x) + slot(x) * y)
    @test m.nvars == 1                    # both slot(x) occurrences share a var
    @test m.var_of[x] == 1
    # separate vars get separate ids
    m2 = compile_pattern(slot(x) + slot(y))
    @test m2.nvars == 2
    @test m2.var_of[x] != m2.var_of[y]
end

@testset "vars merge" begin
    m = compile_pattern(slot(x) + segment(y); vars = Dict(x => slotspec(; default = 0)))
    @match m.var_specs[m.var_of[x]] begin
        VarSpec.Slot(_, d) => @test d !== nothing
        _ => @test false
    end
    @match m.var_specs[m.var_of[y]] begin
        VarSpec.Segment(_, _, mn, mx) => (@test mn == 0 && mx == typemax(Int))
        _ => @test false
    end
    # marker-term keys normalize to the inner sym
    m2 = compile_pattern(slot(x); vars = Dict(slot(x) => slotspec(; default = 1)))
    @match m2.var_specs[m2.var_of[x]] begin
        VarSpec.Slot(_, d) => @test d !== nothing
        _ => @test false
    end
end

@testset "validation errors" begin
    # bare occurrence of a marked sym
    @test_throws ArgumentError compile_pattern(sin(slot(x)) + x)
    # marked var as bare head — head needs an FnType sym whose domain
    # accepts its own (FnType-typed) marker arg
    h2 = Sym{SymReal}(:h2; type = FnType{Tuple{Any}, Number, Nothing})
    @test_throws ArgumentError compile_pattern(h2(slot(h2)))
    # marker-kind conflict
    @test_throws ArgumentError compile_pattern(slot(x) + segment(x))
    # vars-map errors
    @test_throws ArgumentError compile_pattern(slot(x); vars = Dict(y => slotspec()))
    @test_throws ArgumentError compile_pattern(slot(x); vars = Dict(x => segmentspec()))
    @test_throws ArgumentError compile_pattern(
        segment(x) + y;
        vars = Dict(x => slotspec())
    )
    # non-sym keys / non-VarSpec values fail the kwarg signature itself
    @test_throws TypeError compile_pattern(slot(x); vars = Dict("a" => slotspec()))
    @test_throws TypeError compile_pattern(slot(x); vars = Dict(x => 5))
    # optional without default
    @test_throws ArgumentError compile_pattern(optional(x) + y)
    # optional outside AC/A node
    @test_throws ArgumentError compile_pattern(f(optional(x)))
    @test_throws ArgumentError compile_pattern(gfn(optional(x), y))  # C-only not enough
    # root-position markers
    @test_throws ArgumentError compile_pattern(optional(x))
    @test_throws ArgumentError compile_pattern(segment(x))
    # head-position markers: slot ok (§4.10), segment/optional rejected
    @test_throws ArgumentError compile_pattern(segment(f)(y))
    @test_throws ArgumentError compile_pattern(optional(f)(y))
    # segment min provably exceeds fixed-arity parent
    @test_throws ArgumentError compile_pattern(
        f2(segment(x), y);
        vars = Dict(x => segmentspec(; min = 3))
    )

    # non-throwing counterparts
    @test compile_pattern(
        optional(x) + y;
        vars = Dict(x => slotspec(; default = 0))
    ) isa Matcher
    @test compile_pattern(
        optional(x) * y;
        vars = Dict(x => slotspec(; default = 1))
    ) isa Matcher
    @test compile_pattern(
        f2(segment(x), y);
        vars = Dict(x => segmentspec(; min = 1))
    ) isa Matcher
    @test compile_pattern(slot(x) + slot(x)) isa Matcher
end
