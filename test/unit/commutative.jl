# Comm frame (§5.5d): commutative-not-associative heads. C-only heads
# have no identity coercion — a non-g() subject can't match g(...) at
# all. Segments capture a sub-multiset of the remaining args; all args
# must be consumed.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

@syms x y z a b s

let
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = set_operation_traits(g; commutative = true)
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    @testset "commutativity" begin
        # commuted arguments match in any order
        @test isequal(only(matchall(g(x, y), g(y, x))), MarkersMap())
        # no coercion: non-g() subject can't match g(...)
        @test isempty(matchall(g(x, y), x + y))
        @test isempty(matchall(g(x, y), x))
        # arity must fit exactly without segments
        @test isempty(matchall(g(x, y), g(x)))
        @test isempty(matchall(g(x), g(x, y)))
        # literal heads still checked
        @test isempty(matchall(g(x, y), h(x, y)))
        # slot takes whichever arg is left over
        @test isequal(only(matchall(g(slot(a), x), g(x, y))), MarkersMap(a => y))
        # both assignments enumerate
        @test isequal(
            collect(matchall(g(slot(a), slot(b)), g(y, x))),
            MarkersMap[MarkersMap(a => y, b => x), MarkersMap(a => x, b => y)]
        )
    end
    @testset "non-linear" begin
        # a slot bound elsewhere rechecks against remaining args
        @test isempty(matchall(g(slot(a), slot(a)), g(x, y)))
        # duplicate subject args give distinct assignments with equal binds
        @test length(matchall(g(slot(a), slot(a)), g(x, x))) == 2
    end
    @testset "segments (sub-multisets)" begin
        # a segment consumes whatever the fixed children don't
        @test isequal(
            only(matchall(g(x, segment(s)), g(x, y, z))),
            MarkersMap(s => g(y, z))
        )
        # empty capture materializes through the head
        @test isequal(
            only(matchall(g(x, segment(s)), g(x))), MarkersMap(s => g())
        )
        # a segment consumes whatever the fixed children don't
        @test isequal(
            only(matchall(g(x, segment(s)), g(x, y))),
            MarkersMap(s => g(y))
        )
        # two same-var segments need equal multisets left over
        @test length(matchall(g(segment(s), segment(s)), g(x, y, x, y))) == 2
        @test isempty(matchall(g(segment(s), segment(s)), g(x, y, x, z)))
    end
end
