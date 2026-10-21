using MatchMaker
using MatchMaker: VarSpec, PredT, SeqPredT
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic, symtype, issym, isconst
using Moshi.Match: @match
using Test

@syms x y z f(x)

@testset "marker terms" begin
    sx = slot(x)
    @test sx isa BasicSymbolic{SymReal}
    @test iscall(sx)
    @test operation(sx) === slot
    @test is_marker_term(sx)
    @test is_pattern_var(sx)
    @test is_marker_op(operation(sx))
    @test is_slot_marker(operation(sx))
    @test !is_segment_marker(operation(sx))
    @test unwrap_varspec(sx) === x          # hashconsed Sym — same object
    @test varsym(sx) === x
    @test unwrap_varspec(x) === x
    @test !is_pattern_var(x)
    @test !is_pattern_var(sin(x))
    @test_throws ArgumentError varsym(x)

    # equality & hashconsing: equal marker terms are the same object, and
    # distinct markers/vars are `isequal`-distinguished
    @test sx === slot(x)
    @test isequal(sx, slot(x))
    @test !isequal(sx, segment(x))
    @test !isequal(sx, optional(x))
    @test !isequal(sx, slot(y))
    @test !isequal(sx, x)
    @test is_marker_term(segment(x)) && is_segment_marker(operation(segment(x)))
    @test is_marker_term(optional(x)) && is_slot_marker(operation(optional(x)))
end

@testset "constructor validation" begin
    @test_throws ArgumentError slot(f(1))      # a Term, not a Sym
    @test_throws ArgumentError slot(slot(x))   # marker nesting rejected
    @test_throws ArgumentError slot(1)
    @test_throws ArgumentError slot(x + y)
    @test_throws ArgumentError segment(x + y)
end

@testset "Symbol constructors" begin
    q = slot(:q)
    @test is_pattern_var(q)
    @test nameof(varsym(q)) === :q
    @test symtype(varsym(q)) === Number
    r = slot(:r; type = Real)
    @test symtype(varsym(r)) === Real
    # `Sym` is hashconsed: same name+type → same inner sym → same variable
    @test varsym(slot(:q)) === varsym(q)
    # ...but a different symtype is a different sym — not the same variable
    @test varsym(slot(:r)) !== varsym(r)
    @test varsym(segment(:s)) === varsym(segment(:s))
end

@testset "in expressions" begin
    p = slot(x) + slot(y)
    @test iscall(p)                          # normalized AddMul form
    @test isequal(slot(x) * slot(x), slot(x)^2)  # normalization caveat (§1.2)
    @test isequal(slot(x) + slot(x), 2 * slot(x))
end

@testset "VarSpec" begin
    s = slotspec()
    @match s begin
        VarSpec.Slot(p, d) => (@test p === nothing && d === nothing)
        _ => @test false
    end
    sp = slotspec(predicate = x -> issym(x), default = 0)
    @match sp begin
        VarSpec.Slot(p, d) => begin
            @test p isa PredT
            @test p(x) === true
            @test p(sin(x)) === false
            @test d isa BasicSymbolic{SymReal}
            @test isconst(d)
        end
        _ => @test false
    end
    sg = segmentspec(predicate = x -> issym(x),
                     sequence_predicate = v -> length(v) > 0, min = 1, max = 3)
    @match sg begin
        VarSpec.Segment(p, sq, mn, mx) => begin
            @test p isa PredT && sq isa SeqPredT
            @test mn == 1 && mx == 3
        end
        _ => @test false
    end
    @test_throws ArgumentError segmentspec(min = -1)
    @test_throws ArgumentError segmentspec(min = 3, max = 1)
end

@testset "macros" begin
    t = @slot x
    @test is_pattern_var(t)
    @test unwrap_varspec(t) === x

    @slots a b::Real
    @test is_pattern_var(a) && is_pattern_var(b)
    @test nameof(varsym(a)) === :a
    @test symtype(varsym(a)) === Number
    @test symtype(varsym(b)) === Real

    @segments xs ys::Real
    @test operation(xs) === segment
    @test operation(ys) === segment
    @test nameof(varsym(xs)) === :xs
    @test symtype(varsym(ys)) === Real
end

@testset "Substitution" begin
    d = Substitution(x => y)
    @test d[x] === y
    @test d[slot(x)] === y
    @test d[segment(x)] === y
    @test d[optional(x)] === y
    @test haskey(d, slot(x))
    @test haskey(d, x)
    @test get(d, z, nothing) === nothing

    d2 = Substitution()
    d2[slot(y)] = z
    @test d2[y] === z
    @test haskey(d2, y)
    @test length(d2) == 1
    @test only(collect(keys(d2))) === y
    @test first(d2).first === y
    @test first(d2).second === z

    delete!(d2, segment(y))
    @test isempty(d2)
    @test_throws KeyError d2[y]
end
