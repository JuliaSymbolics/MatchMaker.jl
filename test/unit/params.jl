using MatchMaker
using MatchMaker: RuleSet, ParamDict, MatchEngine, next_match!
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic, FnType, BSImpl, ArgsT, symtype
using Moshi.Match: @match
using Test

@syms x y z t f(x) g(x)
h = Sym{SymReal}(:h; type = FnType{Tuple{Number, Number}, Number, Nothing})
@syms a b

@testset "param marker" begin
    pt = param(t)
    @test is_param_term(pt)
    @test is_param_op(operation(pt))
    @test !is_marker_term(pt)
    @test !is_param_term(slot(t))
    @test !is_param_op(slot)
    @test isequal(unwrap_varspec(pt), pt)   # not a var marker
    @test symtype(pt) === symtype(t)
    @test is_param_term(param(:q))
    @test_throws ArgumentError param(x + y)
end

@testset "param compile" begin
    m = compile_pattern(param(t))
    @match m.plans[m.root] begin
        NodePlan.Param(name) => @test name === :t
        _ => @test false
    end
    @test !m.is_ground[m.root]
    @test m.nvars == 0

    m = compile_pattern(sin(param(t)))
    @test !m.is_ground[m.root]
    @match m.plans[m.ir[param(t)]] begin
        NodePlan.Param(name) => @test name === :t
        _ => @test false
    end
    # a param child poisons the ground flag up the spine
    m = compile_pattern(param(t) + slot(a))
    @test !m.is_ground[m.root]

    # malformed param terms (bypassing the ctor) are rejected at compile
    bad = BSImpl.Term{SymReal}(param, ArgsT{SymReal}((x, y)); type = Number)
    @test_throws ArgumentError compile_pattern(bad)
    bad = BSImpl.Term{SymReal}(param, ArgsT{SymReal}((x + y,)); type = Number)
    @test_throws ArgumentError compile_pattern(bad)
end

@testset "param match" begin
    params = ParamDict(:t => x)
    @test isequal(match(param(t), x; params), MarkersMap())
    @test match(param(t), y; params) === nothing
    @test isequal(
        match(param(t), x + y; params = ParamDict(:t => x + y)), MarkersMap()
    )
    @test_throws ArgumentError match(param(t), x)   # unset param errors

    @test isequal(match(sin(param(t)), sin(x); params), MarkersMap())
    @test match(sin(param(t)), sin(y); params) === nothing
    @test match(sin(param(t)), cos(x); params) === nothing

    # param is not a var — binds nothing even inside a bigger pattern
    @test isequal(
        match(h(slot(a), param(t)), h(y, x); params),
        MarkersMap(a => y)
    )
    # same param twice = non-linear literal
    @test isequal(match(h(param(t), param(t)), h(x, x); params), MarkersMap())
    @test match(h(param(t), param(t)), h(x, y); params) === nothing

    # param inside an unordered head
    @test isequal(
        match(slot(a) + param(t), y + x; params), MarkersMap(a => y)
    )

    # kwargs thread through every Matcher-level entry point
    @test length(matchall(sin(param(t)), sin(x); params)) == 1
    @test length(collect(boundmatches_at(h(param(t), slot(a)), h(x, y); params))) == 1
    @test length(collect(matches_at(sin(param(t)), cos(sin(x)); params))) == 1
    hits = Ref(0)
    eachmatch(sin(param(t)), sin(x); params) do _
        hits[] += 1
    end
    @test hits[] == 1

    # plain Dict input is coerced
    @test isequal(match(param(t), x; params = Dict(:t => x)), MarkersMap())

    # direct engine construction
    eng = MatchEngine(
        compile_pattern(param(t)), x, Constraint[]; params = ParamDict(:t => x)
    )
    @test next_match!(eng)
end

@testset "param ruleset" begin
    rules = CompiledRule[mmrule(sin(param(t)) => x), mmrule(cos(param(t)) => y)]
    ws = RuleWorkspace(RuleSet(rules); params = ParamDict(:t => x))
    @test isequal(ws(sin(x)), x)
    @test ws(sin(y)) === nothing
    @test isequal(ws(cos(x)), y)

    # set_params! rebinding — engines and index survive
    eng = ws.engines[1]
    set_params!(ws, ParamDict(:t => y))
    @test ws.engines[1] === eng
    @test isequal(ws(sin(y)), x)
    @test ws(sin(x)) === nothing

    # ctor-kwarg params
    ws = RuleWorkspace(RuleSet(rules); params = Dict(:t => x))
    @test isequal(ws(sin(x)), x)

    # unset params error on first matching site
    ws = RuleWorkspace(RuleSet(rules))
    @test_throws ArgumentError ws(sin(x))

    # call-valued params need a candidate at call sites — param roots spill
    ws = RuleWorkspace(
        RuleSet(CompiledRule[mmrule(param(t) => z)]);
        params = ParamDict(:t => x + y)
    )
    @test isequal(ws(x + y), z)
    @test ws(x) === nothing

    # same coverage under DiscrimNet
    ws = RuleWorkspace(
        RuleSet(rules, DiscrimNet); params = ParamDict(:t => x)
    )
    @test isequal(ws(sin(x)), x)
    @test ws(sin(y)) === nothing
    ws = RuleWorkspace(
        RuleSet(CompiledRule[mmrule(param(t) => z)], DiscrimNet);
        params = ParamDict(:t => x + y)
    )
    @test isequal(ws(x + y), z)
end

@testset "param rhs guard" begin
    # rhs splicing is a later phase — today it errors instead of
    # emitting a literal `param` term into the output
    @test_throws ArgumentError mmrule(slot(a) => param(t))
    @test_throws ArgumentError mmrule(sin(param(t)) => param(t))
end
