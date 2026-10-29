# A-head semantics (§4.5–4.7): nested same-op args flatten for an
# associative head; a non-f-call subject coerces to a singleton argument
# when the head declares an identity; `optional` consumes an arg first,
# then binds the default.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

@syms x y z a b s

let
    f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f = set_operation_traits(f; associative = true, identity = :f0)
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = set_operation_traits(g; associative = true)   # no identity

    @testset "flattening" begin
        # nested same-op subject args inline under an A head
        @test isequal(
            only(matchall(f(segment(s)), f(x, f(y, z)))),
            MarkersMap(s => f(x, y, z))
        )
        @test isequal(
            only(matchall(f(x, segment(s)), f(f(x, y), z))),
            MarkersMap(s => f(y, z))
        )
        # non-f nested calls don't flatten — they capture as one element
        @test isequal(
            only(matchall(f(x, segment(s)), f(x, g(y, z)))),
            MarkersMap(s => f(g(y, z)))
        )
    end

    @testset "identity coercion" begin
        # non-f-call subject becomes its own only argument (§4.6)
        @test isequal(
            only(matchall(f(slot(a), segment(s)), x)),
            MarkersMap(a => x, s => :f0)
        )
        @test isequal(
            only(matchall(f(x, segment(s)), x)),
            MarkersMap(s => :f0)
        )
        @test isequal(only(matchall(f(slot(a)), x)), MarkersMap(a => x))
        # arity still enforced on the singleton
        @test isempty(matchall(f(x, y), x))
        # a different head's call also coerces (it's not an f-call)
        @test isequal(
            only(matchall(f(slot(a)), g(x, y))), MarkersMap(a => g(x, y))
        )
        # no identity declared → no coercion
        @test isempty(matchall(g(slot(a), segment(s)), x))
        @test isempty(matchall(g(slot(a)), x))
    end

    @testset "optionals (§4.7)" begin
        m = compile_pattern(
            f(optional(a), segment(s));
            vars = Dict(a => slotspec(nothing; default = 5))
        )
        # consume-first: the arg binds a, the rest go to the segment
        @test isequal(
            collect(matches(m, f(x, y))),
            MarkersMap[MarkersMap(a => x, s => f(y)), MarkersMap(a => 5, s => f(x, y))]
        )
        # default alternative materializes through extra
        @test isequal(
            collect(matches(m, f(y))),
            MarkersMap[MarkersMap(a => y, s => :f0), MarkersMap(a => 5, s => f(y))]
        )
        @test isequal(
            collect(matches(m, f())), MarkersMap[MarkersMap(a => 5, s => :f0)]
        )
        # non-linear optional: bound value must satisfy both alternatives
        m2 = compile_pattern(
            f(slot(a), optional(a));
            vars = Dict(a => slotspec(nothing; default = x))
        )
        @test isequal(only(collect(matches(m2, f(x)))), MarkersMap(a => x))
        @test isempty(collect(matches(m2, f(y))))
    end
end
