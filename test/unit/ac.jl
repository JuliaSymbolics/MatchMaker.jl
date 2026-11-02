# AC frame (§5.5f): associative+commutative heads. The arg view is
# `_seq_args` (head check, A-flattening, identity coercion); assignment
# positions (fixed ∪ slots) dispatch most-constrained-first over the
# phase-1 candidate matrix. All subject args must be consumed (§4.1).
# For `+`/`*` subjects, enumeration order is dict-order-dependent (§1.2),
# so results are compared as sets.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

@syms x y z a b c p q r

let
    f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f = set_operation_traits(
        f; associative = true, commutative = true, identity = :f0
    )
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})

    @testset "assignment" begin
        # builtin AC ops: both assignments enumerate
        res = collect(matchall(slot(a) + slot(b), p + q))
        @test length(res) == 2
        @test any(Base.Fix1(isequal, MarkersMap(a => p, b => q)), res)
        @test any(Base.Fix1(isequal, MarkersMap(a => q, b => p)), res)
        res = collect(matchall(slot(a) * slot(b), p * q))
        @test length(res) == 2
        @test any(Base.Fix1(isequal, MarkersMap(a => p, b => q)), res)
        @test any(Base.Fix1(isequal, MarkersMap(a => q, b => p)), res)
        # generic AC head
        res = collect(matchall(f(slot(a), slot(b)), f(p, q)))
        @test isequal(
            res,
            MarkersMap[MarkersMap(a => p, b => q), MarkersMap(a => q, b => p)]
        )
        # three positions enumerate all permutations
        @test length(collect(matchall(slot(a) + slot(b) + slot(c), p + q + r))) ==
            6
    end
    @testset "fixed + ground children" begin
        # a ground child picks out its arg, whichever position it's in
        @test isequal(only(matchall(x + slot(a), x + q)), MarkersMap(a => q))
        @test isequal(only(matchall(x + slot(a), p + x)), MarkersMap(a => p))
        # a fixed position with no candidates fails the whole match
        @test isempty(matchall(x + slot(a), p + q))
        @test isempty(matchall(f(sin(x), slot(a)), f(y, z)))
        # ground subtrees compare by isequal without frames
        @test isequal(
            only(matchall(sin(y) + slot(a), sin(y) + z)), MarkersMap(a => z)
        )
        # non-ground subpatterns get real obligations
        @test isequal(
            only(matchall(sin(slot(x)) + slot(a), sin(y) + z)),
            MarkersMap(x => y, a => z)
        )
    end
    @testset "head + arity" begin
        # a different head can't match
        @test isempty(matchall(f(slot(a), slot(b)), h(p, q)))
        @test isempty(matchall(x * slot(a), p + q))
        # all subject args must be consumed
        @test isempty(matchall(slot(a) + slot(b), p + q + r))
        @test isempty(matchall(slot(a) + slot(b) + slot(c), p + q))
    end
    @testset "non-linear" begin
        # a var bound by one position rechecks the other assignment
        res = collect(matchall(f(slot(a), slot(a)), f(p, p)))
        @test length(res) == 2            # distinct assignments, equal binds
        @test all(isequal(MarkersMap(a => p)), res)
        @test isempty(matchall(f(slot(a), slot(a)), f(p, q)))
        # non-linear across nested AC nodes
        @test isequal(
            only(matchall(x * slot(a) + y * slot(a), x * p + y * p)),
            MarkersMap(a => p)
        )
        @test isempty(matchall(x * slot(a) + y * slot(a), x * p + y * q))
    end
    @testset "bound elsewhere" begin
        # a slot bound by an outer frame is a fixed-by-lookup position
        @test isequal(
            only(matchall(g(slot(a), slot(a) + slot(b)), g(p, p + q))),
            MarkersMap(a => p, b => q)
        )
        @test isempty(matchall(g(slot(a), slot(a) + slot(b)), g(p, r + q)))
    end
    @testset "flattening + coercion" begin
        # nested same-op calls flatten under A
        res = collect(matchall(f(slot(a), slot(b), slot(c)), f(p, f(q, r))))
        @test length(res) == 6
        @test any(Base.Fix1(isequal, MarkersMap(a => p, b => q, c => r)), res)
        # non-call subject coerces to a singleton arg (§4.6)
        @test isequal(only(matchall(f(slot(a)), p)), MarkersMap(a => p))
        @test isequal(only(matchall(f(x), x)), MarkersMap())
        # ...but one arg can't fill two required positions
        @test isempty(matchall(f(slot(a), slot(b)), p))
        @test isempty(matchall(slot(a) + slot(b), p))
    end
end
