using MatchMaker
using MatchMaker: RuleSet, ParamDict, MatchEngine, next_match!
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic, FnType, BSImpl, ArgsT, symtype
using Moshi.Match: @match
using Test

@syms x y z t u f(x) g(x)
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

    # param-headed calls compile to ParamCall — both the positional
    # child list and the classified groups, for runtime frame selection
    pv = Sym{SymReal}(:op; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    m = compile_pattern(term(param(pv), slot(x), segment(t)))
    @test !m.is_ground[m.root]
    @match m.plans[m.root] begin
        NodePlan.ParamCall(; op, head, children, fixed, slots, optionals, segments) => begin
            @test is_param_term(op)
            @test head != 0
            @test length(children) == 2
            @test isempty(fixed) && isempty(optionals)
            @test length(slots) == 1 && length(segments) == 1
        end
        _ => @test false
    end
    # the head node itself is a Param leaf — `_head_obligation!`
    # resolves it against the params table
    @match m.plans[m.plans[m.root].head] begin
        NodePlan.Param(name) => @test name === :op
        _ => @test false
    end
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

@testset "param workspace history" begin
    # `ws.subj` accumulates across passes — passes must not re-evaluate
    # stale nodes against a new params table
    rules = CompiledRule[
        mmrule(sin(param(t)) => z),
        mmrule(cos(param(u)) => x),
    ]
    for idx in (BucketIndex, DiscrimNet)
        ws = RuleWorkspace(RuleSet(rules, idx); params = ParamDict(:t => x))
        @test isequal(rewrite(ws, sin(x)), z)
        set_params!(ws, ParamDict(:u => y))
        @test isequal(rewrite(ws, cos(y)), x)
    end
    for idx in (BucketIndex, DiscrimNet)
        ws = RuleWorkspace(RuleSet(rules, idx); params = ParamDict(:t => x))
        @test isequal(fixpoint_rewrite(ws, sin(x)), z)
        set_params!(ws, ParamDict(:u => y))
        @test isequal(fixpoint_rewrite(ws, cos(y)), x)
    end

    # a ParamDict table is used live
    d = ParamDict(:t => x)
    ws = RuleWorkspace(RuleSet(rules); params = d)
    @test ws.params === d

    # descendants of a rewrite result interned by an earlier pass are
    # still evaluated — `x => sin(y)`, `y => z` must reach `sin(z)`
    rules = CompiledRule[mmrule(x => sin(y)), mmrule(y => z)]
    for idx in (BucketIndex, DiscrimNet)
        ws = RuleWorkspace(RuleSet(rules, idx))
        @test isequal(rewrite(ws, sin(y)), sin(z))
        @test isequal(fixpoint_rewrite(ws, x), sin(z))
    end
end

@testset "param default table" begin
    # no params table — `nothing` shares nothing across engines
    eng = MatchEngine(compile_pattern(param(t)), x, Constraint[])
    @test eng.params === nothing
    @test_throws ArgumentError match(param(t), x)
    ws = RuleWorkspace(RuleSet(CompiledRule[mmrule(x => z)]))
    @test ws.params === nothing
end

@testset "param rhs" begin
    # template splices resolve per pass — set_params! rebinds them
    r = mmrule(slot(a) => param(t) + slot(a))
    ws = RuleWorkspace(RuleSet(CompiledRule[r]); params = ParamDict(:t => y))
    @test isequal(ws(x), x + y)
    set_params!(ws, ParamDict(:t => z))
    @test isequal(ws(x), x + z)

    # bare param rhs and param spliced into a head
    r = mmrule(slot(a) => param(u))
    ws = RuleWorkspace(RuleSet(CompiledRule[r]); params = ParamDict(:u => z))
    @test isequal(ws(x), z)
    r = mmrule(slot(a) => param(f)(slot(a)))
    ws = RuleWorkspace(RuleSet(CompiledRule[r]); params = ParamDict(:f => sin))
    @test isequal(ws(x), sin(x))
    set_params!(ws, ParamDict(:f => cos))
    @test isequal(ws(x), cos(x))

    # a callable rhs reads params off the view
    r = mmrule(slot(a) => (v -> v[param(t)] + v[a]))
    ws = RuleWorkspace(RuleSet(CompiledRule[r]); params = ParamDict(:t => y))
    @test isequal(ws(x), x + y)

    # an unset param errors at apply, not at compile
    ws = RuleWorkspace(RuleSet(CompiledRule[mmrule(slot(a) => param(t))]))
    @test_throws ArgumentError ws(x)

    # a param under a segment-capable head in the rhs
    r = mmrule(f(slot(a)) => h(slot(a), param(t)))
    ws = RuleWorkspace(RuleSet(CompiledRule[r]); params = ParamDict(:t => z))
    @test isequal(ws(f(x)), h(x, z))

    # a param nested inside a *computed op* splices too — the head
    # node's own vid is 0, so the rebuilt head must come from `out`
    RetT = FnType{Tuple{Number}, Number, Nothing}
    gg = Sym{SymReal}(:gg; type = FnType{Tuple{Number}, RetT, Nothing})
    r = mmrule(slot(a) => term(gg(param(t)), slot(a)))
    for idx in (MatchMaker.BucketIndex, MatchMaker.DiscrimNet)
        ws = RuleWorkspace(RuleSet(CompiledRule[r], idx); params = ParamDict(:t => y))
        @test isequal(ws(x), term(gg(y), x))
        set_params!(ws, ParamDict(:t => z))
        @test isequal(ws(x), term(gg(z), x))
    end
end

@testset "param occurrence iterators" begin
    # one live table can drive successive traversals — it is only
    # mutating mid-enumeration that is undefined
    subj = f(g(a) + g(b))
    pat = g(param(t))
    params = ParamDict(:t => a)
    for mk in (matches_at, boundmatches_at)
        got = collect(mk(pat, subj; params))
        @test length(got) == 1 && isequal(got[1][2], g(a))
        params[:t] = b
        got = collect(mk(pat, subj; params))
        @test length(got) == 1 && isequal(got[1][2], g(b))
        params[:t] = a
    end
end

@testset "param view membership" begin
    # indexing and haskey agree: a callable rhs's membership guard sees
    # the same configured parameters getindex resolves
    seen = Ref(false)
    eachmatch(param(t), b; params = ParamDict(:t => b)) do v
        seen[] = true
        @test haskey(v, param(t))
        @test isequal(v[param(t)], b)
        @test !haskey(v, param(u))
        @test isempty(materialize(v))   # param binds no vars
    end
    @test seen[]
end

@testset "param fixpoint shared children" begin
    # the warm-workspace fixpoint case driven by a runtime parameter:
    # `param(u) => d` matches `c` through the table, and `c` was
    # interned by an earlier `rewrite` call on the same workspace
    @syms c d
    rules = CompiledRule[mmrule(a => g(param(u))), mmrule(param(u) => d)]
    for idx in (MatchMaker.BucketIndex, MatchMaker.DiscrimNet)
        ws = RuleWorkspace(RuleSet(rules, idx); params = ParamDict(:u => c))
        rewrite(ws, c)
        @test isequal(fixpoint_rewrite(ws, f(a)), f(g(d)))
    end
end

@testset "param fixpoint discarded intermediates" begin
    # `f(g(sin(b))) => e` fires at the `f(a)` site, so the interned
    # `sin(b)` is part of a discarded intermediate — `sin(param(t))`
    # must never be evaluated, even with no `:t` in the table
    @syms d e
    rules = CompiledRule[
        mmrule(a => g(sin(b))),
        mmrule(f(g(sin(b))) => e),
        mmrule(sin(param(t)) => d),
    ]
    for idx in (MatchMaker.BucketIndex, MatchMaker.DiscrimNet)
        # fresh workspace
        ws = RuleWorkspace(RuleSet(rules, idx); params = ParamDict(:t => b))
        @test isequal(fixpoint_rewrite(ws, f(a)), e)
        # warm: `sin(b)` interned under `:t => b`, then the table
        # swapped out — the param rule must never run
        ws = RuleWorkspace(RuleSet(rules, idx); params = ParamDict(:t => b))
        rewrite(ws, sin(b))
        set_params!(ws, ParamDict())
        @test isequal(fixpoint_rewrite(ws, f(a)), e)
    end
end

@testset "param heads" begin
    # `param(op)(…)` — the resolved op's traits pick the frame at
    # runtime: free → Call, segments/associative → Seq, commutative →
    # Comm, AC → AC. The head obligation resolves against the params
    # table like any param leaf.
    pv = Sym{SymReal}(:op; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    hv = Sym{SymReal}(:hv; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    @syms c

    for idx in (MatchMaker.BucketIndex, MatchMaker.DiscrimNet)
        rules = CompiledRule[mmrule(term(param(pv), slot(x), slot(y)) => x)]
        ws = RuleWorkspace(
            RuleSet(rules, idx); params = ParamDict(:op => hv)
        )

        # free op → Call frame: positional slots, exact arity
        ms = match(rules[1].pat, hv(a, b); params = ws.params)
        @test isequal(ms[x], a) && isequal(ms[y], b)
        @test match(rules[1].pat, hv(a); params = ws.params) === nothing
        @test match(rules[1].pat, a + b; params = ws.params) === nothing

        # AC op → AC frame: unordered slots, wrong-op subject rejected
        set_params!(ws, ParamDict(:op => (+)))
        ms = match(rules[1].pat, a + b; params = ws.params)
        @test (isequal(ms[x], a) && isequal(ms[y], b)) ||
            (isequal(ms[x], b) && isequal(ms[y], a))
        @test match(rules[1].pat, a * b; params = ws.params) === nothing
        @test match(rules[1].pat, a + b + c; params = ws.params) === nothing

        rules2 = CompiledRule[mmrule(term(param(pv), a, segment(u)) => x)]

        # AC op: the segment binds under the subject's op
        set_params!(ws, ParamDict(:op => (+)))
        ms = match(rules2[1].pat, a + b + c; params = ws.params)
        @test isequal(ms[u], b + c)
        @test match(rules2[1].pat, b + c; params = ws.params) === nothing

        # free op → Seq frame: `u` rebuilds under `hv`, the subject's
        # op — not the `param` placeholder
        set_params!(ws, ParamDict(:op => hv))
        ms = match(rules2[1].pat, hv(a, b, c); params = ws.params)
        @test isequal(ms[u], hv(b, c))
        @test match(rules2[1].pat, hv(b, c); params = ws.params) === nothing

        # unset param is a usage error at the head too
        @test_throws ArgumentError match(rules2[1].pat, hv(a, b))
    end
end
