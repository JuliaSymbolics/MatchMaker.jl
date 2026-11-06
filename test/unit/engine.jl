using MatchMaker
using MatchMaker: MatchEngine, next_match!, SubstitutionView, _STRICT_VIEWS
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic, FnType
using Test

@syms x y z f(x) g(x)
h = Sym{SymReal}(:h; type = FnType{Tuple{Number, Number}, Number, Nothing})
@syms a b

# `==` on BasicSymbolic values is symbolic; tests compare via isequal.
mm(kvs...) = m -> isequal(m, MarkersMap(kvs...))

@testset "leaf obligations" begin
    # literals
    @test isequal(match(h(x, y), h(x, y)), MarkersMap())
    @test match(h(x, y), h(x, x)) === nothing
    # slot root
    @test isequal(match(slot(x), y), MarkersMap(x => y))
    @test isequal(match(x, x), MarkersMap())       # literal root match
    @test match(x, y) === nothing
    # symtype constraint from the inner sym
    xi = Sym{SymReal}(:xi; type = Int)
    @test match(slot(xi), Sym{SymReal}(:q; type = Int)) !== nothing
    @test match(slot(xi), x) === nothing    # Number-typed sym doesn't satisfy Int
end

@testset "Seq frames — positional" begin
    @test isequal(match(h(slot(a), slot(b)), h(x, y)), MarkersMap(a => x, b => y))
    @test isequal(match(f(slot(a)), f(x)), MarkersMap(a => x))
    @test match(f(slot(a)), h(x, y)) === nothing    # different heads
end

@testset "nested + non-linear" begin
    @test isequal(match(f(g(slot(a))), f(g(x))), MarkersMap(a => x))
    @test match(h(slot(a), slot(a)), h(x, x)) |> mm(a => x)
    @test match(h(slot(a), slot(a)), h(x, y)) === nothing
    @test match(h(f(slot(a)), f(slot(a))), h(f(x), f(x))) |> mm(a => x)
    @test match(h(f(slot(a)), f(slot(a))), h(f(x), f(y))) === nothing
    # deep chain of alternatives — terminates rather than looping
    @test match(h(f(f(slot(a))), f(f(slot(a)))), h(f(f(x)), f(f(y)))) === nothing
end

@testset "head-slots (§4.10)" begin
    @test match(slot(f)(slot(a)), g(y)) |> mm(f => g, a => y)
    @test match(slot(f)(slot(a)), f(x)) |> mm(f => f, a => x)
    # literal head position
    @test match(f(slot(a)), f(x)) |> mm(a => x)
    @test match(f(slot(a)), g(x)) === nothing
end

@testset "constraints" begin
    c = Constraint(v -> isequal(v[1], v[2]), [a, b])
    @test match(h(slot(a), slot(b)), h(x, x); constraints = [c]) |> mm(a => x, b => x)
    @test match(h(slot(a), slot(b)), h(x, y); constraints = [c]) === nothing
    @test_throws ArgumentError match(
        h(slot(a), slot(b)), h(x, y);
        constraints = [Constraint(v -> true, [z])]
    )
    @test_throws MethodError match(
        h(slot(a), slot(b)), h(x, y); constraints = [3]
    )
end

@testset "iterator + views" begin
    ms = matchall(h(slot(a), slot(b)), h(x, y))
    @test length(ms) == 1 && isequal(ms[1], MarkersMap(a => x, b => y))
    @test isempty(matchall(h(x, y), h(x, x)))

    @test isequal(
        collect(matches(h(slot(a), slot(b)), h(x, y)))[1],
        MarkersMap(a => x, b => y)
    )

    # stale-view debug flag
    eng = MatchEngine(
        compile_pattern(h(slot(a), slot(b))), h(x, y), Constraint[]
    )
    next_match!(eng)
    v = SubstitutionView(eng, eng.steps)
    _STRICT_VIEWS[] = true
    @test v[a] === x
    next_match!(eng)
    @test_throws AssertionError v[a]
    _STRICT_VIEWS[] = false
end

@testset "instantiate" begin
    @test isequal(instantiate(f(slot(a)), match(f(slot(a)), f(x))), f(x))
    @test isequal(
        instantiate(h(slot(a), slot(b)), match(h(slot(a), slot(b)), h(x, y))),
        h(x, y)
    )
    @test isequal(instantiate(h(slot(a), 2), MarkersMap(a => x)), h(x, 2))
end

@testset "maxsteps + eachmatch" begin
    # budget exhausted → truncated results, no error
    @test length(matchall(slot(a) + slot(b), x + y; maxsteps = 1)) == 1
    @test matchall(slot(a) + slot(b), x + y; maxsteps = 0) |> isempty
    @test match(slot(a), x; maxsteps = 0) === nothing
    # a large budget is equivalent to no budget
    @test isequal(
        matchall(slot(a) + slot(b), x + y),
        matchall(slot(a) + slot(b), x + y; maxsteps = typemax(Int))
    )
    # eachmatch visits every match through a live view
    seen = MarkersMap[]
    eachmatch(slot(a) + slot(b), x + y) do v
        push!(seen, materialize(v))
        true
    end
    @test isequal(seen, collect(matchall(slot(a) + slot(b), x + y)))
    # returning false stops the iteration early
    n = Ref(0)
    eachmatch(slot(a) + slot(b), x + y) do v
        n[] += 1
        false
    end
    @test n[] == 1
end
