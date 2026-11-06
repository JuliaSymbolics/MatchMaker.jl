# Cross-variable constraints (§4.9): `Constraint(fn, vars)` fires `fn`
# with a vector of bound values as soon as every var in `vars` is bound
# — early pruning, not post-hoc filtering.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const

@syms a b c s t x y z p q r w

let
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = set_operation_traits(g; commutative = true)
    f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f = set_operation_traits(
        f; associative = true, commutative = true, identity = :f0
    )

    @testset "early pruning (§4.9)" begin
        # a constraint fires at the bind that completes its var set, not
        # after a full assignment: an always-false constraint on [a]
        # fires once per a-bind — never reaching b/c positions
        count = Ref(0)
        cn = Constraint(v -> (count[] += 1; false), [a])
        res = collect(
            matchall(
                g(slot(a), slot(b), slot(c)), g(x, y, z);
                constraints = [cn]
            )
        )
        @test isempty(res)
        @test count[] == 3
        # the same shape with a passing constraint still fires once per
        # bind of a, not once per produced alternative
        count[] = 0
        cn = Constraint(v -> (count[] += 1; true), [a])
        @test length(matchall(
            g(slot(a), slot(b), slot(c)), g(x, y, z);
            constraints = [cn]
        )) == 6
        @test count[] == 3
        # a two-var constraint fires when the second var binds — once
        # per (a, b) pairing
        count[] = 0
        cn = Constraint(v -> (count[] += 1; true), [a, b])
        @test length(matchall(
            g(slot(a), slot(b), slot(c)), g(x, y, z);
            constraints = [cn]
        )) == 6
        @test count[] == 6
    end
    @testset "equivalent to post-hoc filtering" begin
        # constrained results = unconstrained results filtered by the
        # same predicate on the materialized bindings
        cn = Constraint(v -> isequal(v[1], q), [a])
        got = collect(
            matchall(f(slot(a), segment(s)), f(p, q, r); constraints = [cn])
        )
        want = [
            m for m in matchall(f(slot(a), segment(s)), f(p, q, r)) if
            isequal(m[a], q)
        ]
        @test length(got) == length(want) == 1
        @test isequal(only(got), only(want))
        # non-linear vars constrain each other through the engine
        cn = Constraint(v -> !isequal(v[1], v[2]), [a, b])
        got = collect(
            matchall(g(slot(a), slot(b)), g(x, y); constraints = [cn])
        )
        @test length(got) == 2
        got = collect(
            matchall(g(slot(a), slot(b)), g(x, x); constraints = [cn])
        )
        @test isempty(got)
    end
    @testset "segment + extra values" begin
        # a segment var delivers its materialized f(captured…) value —
        # here: exactly two-arg captures (Const results are not calls)
        cn = Constraint(
            v -> iscall(v[1]) && length(arguments(v[1])) == 2, [s]
        )
        res = collect(
            matchall(f(segment(s), segment(t)), f(p, q, r);
            constraints = [cn])
        )
        @test length(res) == 3
        @test any(
            Base.Fix1(isequal, MarkersMap(s => f(p, q), t => f(r))), res
        )
        # an optional default binds through extra — the constraint sees
        # the Const-wrapped default
        m = compile_pattern(
            f(optional(a), segment(s));
            vars = Dict(a => slotspec(nothing; default = 5))
        )
        cn = Constraint(v -> isequal(v[1], Const{SymReal}(5)), [a])
        @test isequal(
            only(collect(matches(m, f(p); constraints = [cn]))),
            MarkersMap(a => 5, s => f(p))
        )
        # ...and it rejects the consume alternative the same way
        cn = Constraint(v -> isequal(v[1], p), [a])
        @test isequal(
            only(collect(matches(m, f(p); constraints = [cn]))),
            MarkersMap(a => p, s => :f0)
        )
    end
    @testset "api" begin
        # fn must return Bool
        @test_throws MethodError match(
            g(slot(a)), g(x); constraints = [Constraint(v -> v[1], [a])]
        )
        # constraint vars must be pattern vars
        @test_throws ArgumentError match(
            g(slot(a)), g(x); constraints = [Constraint(v -> true, [z])]
        )
        # match returns nothing when constraints fail
        @test match(
            g(slot(a)), g(x);
            constraints = [Constraint(v -> false, [a])]
        ) === nothing
    end
end
