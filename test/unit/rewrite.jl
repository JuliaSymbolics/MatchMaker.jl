using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, BasicSymbolic, issym
import SymbolicUtils.Rewriters
using SymbolicUtils.Rewriters:
    Chain, RestartedChain, IfElse, Postwalk, Prewalk, Fixpoint, Empty

const CS = SymbolicUtils.Const{SymReal}

@testset "rule objects + workspace" begin
    @syms x y z a b s t v p q r w u

    # mmrule: template rhs compiles to RhsPlan, callables to RhsT
    r1 = mmrule(slot(a) + slot(b) => slot(a) * slot(b))
    @test r1.rhs isa RhsPlan
    r2 = mmrule(slot(a) + slot(b) => (v -> v[slot(a)]))
    @test r2.rhs isa RhsT
    # rhs var must be an lhs var
    @test_throws ArgumentError mmrule(slot(a) => slot(b))

    # workspace callable: first match in declaration order
    rs = compile_rules(
        CompiledRule[
            mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
            mmrule(segment(s) + slot(t) => segment(s)),
            mmrule(slot(a) * CS(2) => slot(a) + slot(a)),
        ]
    )
    ws = RuleWorkspace(rs)
    @test isequal(ws(x + y), x * y)
    @test isequal(ws(CS(2) * x), CS(2) * x)      # r3 matched; x+x canonicalizes to 2x
    # r3: t binds one arg, s captures the other three — which arg t takes
    # is process-dependent, so any 3-of-4 subset is a valid result
    rw = ws(x + y + z + w)
    @test any(
        Base.Fix1(isequal, rw),
        (x + y + z, x + y + w, x + z + w, y + z + w),
    )
    @test ws(x * y) === nothing                 # no candidate
    @test ws(CS(5)) === nothing                 # atom, no leaf rules

    # callable rhs: `nothing` falls through to the next rule
    only_equal = mmrule(
        slot(a) + slot(b) =>
            (
            view -> isequal(view[slot(a)], view[slot(b)]) ?
                CS(2) * view[slot(a)] : nothing
        )
    )
    mul = mmrule(slot(a) + slot(b) => slot(a) * slot(b))
    ws2 = RuleWorkspace(compile_rules(CompiledRule[only_equal, mul]))
    @test isequal(ws2(x + y), x * y)   # callable -> nothing -> r2 fires
    e = x + x
    @test ws2(e) === nothing           # x+x is a Mul — no + head

    # same engine is reset and reused across sites — bindings don't leak
    rs3 = compile_rules(
        CompiledRule[
            mmrule(slot(a) + slot(b) => slot(b)),
        ]
    )
    pat_ab = compile_pattern(slot(a) + slot(b))
    ws3 = RuleWorkspace(rs3)
    # canonical Add arg order is process-dependent — compare against the
    # matcher's own first result rather than a literal argument
    @test isequal(ws3(x + y), match(pat_ab, x + y)[b])
    @test isequal(ws3(p + q), match(pat_ab, p + q)[b])

    # reset! clears the prior match's bindings before re-searching
    eng = MatchEngine(pat_ab, x + y, Constraint[])
    @test next_match!(eng)
    @test any(v -> v != 0, eng.binds.node)         # match leaves binds
    reset!(eng, eng.subj, populate_ir!(eng.subj, p + q))
    @test all(v -> v == 0, eng.binds.node)         # cleared by reset
    @test next_match!(eng)                          # fresh search re-binds
    @test isequal(eng.subj[eng.binds.node[pat_ab.var_of[b]]], match(pat_ab, p + q)[b])

    # workspace bounded reuse: buffer plateaus, no per-site engine alloc
    ws3(x + y); ws3(p + q)
    e1 = ws3.engines[1]
    ws3(a + b)
    @test ws3.engines[1] === e1

    # maxsteps: a tiny budget ends the search with no result
    ws4 = RuleWorkspace(rs3; maxsteps = 0)
    @test ws4(x + y) === nothing
    ws4.maxsteps = typemax(Int)
    @test isequal(ws4(x + y), match(pat_ab, x + y)[b])
end

@testset "bucket index" begin
    @syms x y z a b s t f(x)

    r_add = mmrule(slot(a) + slot(b) => slot(a))
    r_mul = mmrule(slot(a) * slot(b) => slot(a))
    r_any = mmrule(slot(a) => a)                 # bare slot — any node
    r_leaf = mmrule(CS(3) => CS(4))              # literal root
    rs = compile_rules(CompiledRule[r_add, r_mul, r_any, r_leaf])
    idx = rs.index

    @test haskey(idx.by_op, +) && haskey(idx.by_op, *)
    @test length(idx.any_head) == 1              # bare slot rule
    @test length(idx.leaf_rules) == 1            # literal rule

    buf = SymbolicUtils.SmallV{Int32}()
    ws = RuleWorkspace(rs)
    sr(t) = populate_ir!(ws.subj, t)
    MatchMaker.lookup!(idx, buf, ws, x + y, sr(x + y))
    @test Set(collect(buf)) == Set(Int32[1, 3])  # + bucket + any_head
    MatchMaker.lookup!(idx, buf, ws, x * y, sr(x * y))
    @test Set(collect(buf)) == Set(Int32[2, 3])  # * bucket + any_head
    MatchMaker.lookup!(idx, buf, ws, CS(3), sr(CS(3)))
    @test Set(collect(buf)) == Set(Int32[3, 4])  # leaf + any_head

    # arity filters candidates: a+b needs exactly 2 args
    MatchMaker.lookup!(idx, buf, ws, x + y + z, sr(x + y + z))
    @test collect(buf) == Int32[3]               # only any_head survives
    MatchMaker.lookup!(idx, buf, ws, x * y * z, sr(x * y * z))
    @test collect(buf) == Int32[3]               # a*b is 2-factor — filtered

    # head-slot pattern lands in any_head
    fh = Sym{SymReal}(:fh; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    r_hd = mmrule(
        slot(f)(slot(a)) => slot(a);
        vars = Dict(a => slotspec())
    )
    idx2 = compile_rules(CompiledRule[r_hd]).index
    @test collect(idx2.any_head) == Int32[1]
end

@testset "rewrite pass" begin
    @syms x y z a b p q h(a, b)

    r_mul = mmrule(slot(a) + slot(b) => slot(a) * slot(b))
    rs = compile_rules(CompiledRule[r_mul])
    ws = RuleWorkspace(rs)

    # bottom-up: adds nested under a non-AC head rewrite before the parent
    subj = h(x + y, p + q)
    @test isequal(rewrite(ws, subj), h(x * y, p * q))

    # unchanged nodes keep interned identity — only ancestors rebuild
    @test rewrite(ws, x * y) === (x * y)
    @test rewrite(ws, x) === x

    # :pre vs :post differ on whether the parent sees original children:
    # h(x+y, x*y) — :pre parent sees unequal args, :post sees x*y==x*y
    ws_pair = RuleWorkspace(
        compile_rules(
            CompiledRule[
                r_mul,
                mmrule(h(slot(a), slot(a)) => slot(a)),   # non-linear h rule
            ]
        )
    )
    @test isequal(rewrite(ws_pair, h(x + y, x * y); order = :pre), h(x * y, x * y))
    @test isequal(rewrite(ws_pair, h(x + y, x * y); order = :post), x * y)
    @test_throws ArgumentError rewrite(ws_pair, x; order = :bogus)

    # callable rhs producing non-symbolic values gets Const-wrapped
    r_num = mmrule(CS(1) + slot(a) => (v -> 42))
    ws_num = RuleWorkspace(compile_rules(CompiledRule[r_num]))
    @test isequal(ws_num(CS(1) + x), CS(42))

    # fixpoint: iterate until stable — a+b -> a*b has no + left
    ws_mul = RuleWorkspace(rs)
    @test isequal(fixpoint_rewrite(ws_mul, x + y), x * y)

    # 2x+2y (canonical (x+y)+(x+y)) -> 2x*2y = 4xy in one pass
    nested = (x + y) + (x + y)
    got = fixpoint_rewrite(ws_mul, nested)
    @test isequal(got, CS(4) * x * y)
end

@testset "incremental fixpoint" begin
    @syms x y z a b s t p q w
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})

    mkrules() = CompiledRule[
        mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
        mmrule(sin(slot(a)) => slot(a)),
        mmrule(h(slot(a), slot(b)) => slot(a)),
    ]
    # multi-iteration convergence — h strips after children rewrite
    @test isequal(
        fixpoint_rewrite(
            RuleWorkspace(compile_rules(mkrules())),
            h(sin(x + y), sin(p + q))
        ),
        x * y
    )
    # result is stable — re-running fixes nothing
    @test isequal(
        fixpoint_rewrite(RuleWorkspace(compile_rules(mkrules())), x * y),
        x * y
    )
    # :pre order still works via the naive loop
    @test isequal(
        fixpoint_rewrite(
            RuleWorkspace(compile_rules(mkrules())),
            h(sin(x + y), sin(p + q)); order = :pre
        ),
        x * y
    )

    # 2-cycle terminates on the first repeated term
    ws_cyc = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(slot(a) * slot(b) => slot(a) + slot(b)),
            ]
        )
    )
    r = fixpoint_rewrite(ws_cyc, x + y)
    @test isequal(r, x * y) || isequal(r, x + y)

    # 3-cycle terminates
    ws_cyc3 = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(slot(a) * slot(b) => h(slot(a), slot(b))),
                mmrule(h(slot(a), slot(b)) => slot(a) + slot(b)),
            ]
        )
    )
    @test fixpoint_rewrite(ws_cyc3, x + y) !== nothing

    # maxiterations bounds the loop
    @test fixpoint_rewrite(ws_cyc, x + y; maxiterations = 2) !== nothing

    # dirty propagation: a convergent deep subject — results equal a
    # naive full-rewrite loop oracle
    ws_deep = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(sin(slot(a)) => slot(a)),
                mmrule(cos(slot(a)) => slot(a)),
                mmrule(h(slot(a), slot(b)) => slot(a)),
                mmrule(g(slot(a), slot(b)) => slot(a) * slot(b)),
            ]
        )
    )
    function naive_fp(ws, x)
        seen = Base.IdSet{BasicSymbolic{SymReal}}()
        for _ in 1:10_000
            x′ = rewrite(ws, x)
            isequal(x′, x) && return x
            x′ in seen && return x′
            push!(seen, x); x = x′
        end
        return x
    end
    ws_naive = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(sin(slot(a)) => slot(a)),
                mmrule(cos(slot(a)) => slot(a)),
                mmrule(h(slot(a), slot(b)) => slot(a)),
                mmrule(g(slot(a), slot(b)) => slot(a) * slot(b)),
            ]
        )
    )
    sub = h(sin(sin(sin(x + y))), cos(g(sin(p + q), sin(a + b)))) +
        sin(sin(w + z)) + g(cos(x + y), sin(p + q))
    @test isequal(fixpoint_rewrite(ws_deep, sub), naive_fp(ws_naive, sub))
end

@testset "SU combinator compatibility" begin
    @syms x y z a b p q

    ws = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(slot(a) * slot(a) => slot(a)^CS(2)),
            ]
        )
    )

    # Postwalk/Prewalk apply the workspace per node
    @test isequal(Postwalk(ws)((x + y) * (p + q)), x * y * (p * q))
    # Chain: sequential pipeline
    @test isequal(Chain([ws])(x + y), x * y)
    # IfElse branches on the condition
    @test isequal(IfElse(v -> iscall(v), ws, v -> CS(0))(x + y), x * y)
    @test isequal(IfElse(v -> iscall(v), ws, v -> CS(0))(x), CS(0))
    # Fixpoint over the workspace: x+y -> x*y is stable after one pass
    @test isequal(Fixpoint(ws)(x + y), x * y)
    # PassThrough applies rw without recursing; If gates on a predicate
    @test Rewriters.PassThrough(ws)(x + y) |> isequal(x * y)
    @test Rewriters.If(v -> iscall(v), ws)(x + y) |> isequal(x * y)
    @test Rewriters.If(v -> iscall(v), ws)(x) === nothing
    # Empty never fires
    @test Empty()(x + y) === nothing
end

@testset "discrim net" begin
    @syms x y z a b s t w p q c
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    fh = Sym{SymReal}(:fh; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})

    rules = CompiledRule[
        mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
        mmrule(segment(s) + slot(t) => segment(s)),
        mmrule(slot(a) * CS(2) => slot(a) + slot(a)),
        mmrule(CS(1) + slot(a) => slot(a)),
        mmrule(h(slot(a), slot(b)) => slot(a)),
        mmrule(h(slot(a), CS(1)) => CS(0)),
        mmrule(sin(slot(a)) => slot(a)),
        mmrule(
            slot(fh)(slot(a), slot(b)) => slot(a);
            vars = Dict(fh => slotspec())
        ),
        mmrule(slot(a) * CS(1) => slot(a)),   # a*1 canonicalizes → bare slot
        mmrule(CS(3) => CS(4)),
    ]
    rs_b = compile_rules(rules)
    rs_n = compile_rules(rules, DiscrimNet)
    @test rs_n.index isa DiscrimNet

    ws_b = RuleWorkspace(rs_b)
    ws_n = RuleWorkspace(rs_n)
    buf = SymbolicUtils.SmallV{Int32}()
    surv(ws, t) = begin
        sr = populate_ir!(ws.subj, t)
        MatchMaker.lookup!(ws.set.index, buf, ws, t, sr)
        collect(buf)
    end

    # net is stricter than the root-only bucket check, never looser —
    # and both agree on what apply produces
    terms = [
        x + y, x + y + z, x * y, 2x * y, h(x, y), h(x, CS(1)),
        sin(x), fh(x, y), CS(3), x, CS(1) + x, CS(3) * y,
    ]
    for t in terms
        sb, sn = surv(ws_b, t), surv(ws_n, t)
        @test issorted(sn)
        @test sn ⊆ sb
        rb, rn = ws_b(t), ws_n(t)
        @test isequal(something(rb, t), something(rn, t))
    end

    # net confirms deterministic structure the bucket can't see:
    # literal children and leaf literals prune candidates
    @test surv(ws_n, h(x, y)) == [5, 8, 9]  # head-slot + bare slot ok,
    @test 6 ∉ surv(ws_n, h(x, y))           # but h(a,1) rejected at child
    @test 10 ∉ surv(ws_n, x)                # literal 3 vs leaf x

    # declaration order preserved across index kinds on a leaf:
    # `a*1` (canonicalized to a bare slot) applies before `3→4`
    @test isequal(ws_n(CS(3)), CS(3)) && isequal(ws_b(CS(3)), CS(3))

    # rewrite + fixpoint parity
    sub = h(sin(x + y), p * q) + cos(w) * (a + b + c) + sin(p + q)
    @test isequal(rewrite(ws_b, sub), rewrite(ws_n, sub))
    ws2b = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(sin(slot(a)) => slot(a)),
            ]
        )
    )
    ws2n = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
                mmrule(sin(slot(a)) => slot(a)),
            ], DiscrimNet
        )
    )
    @test isequal(
        fixpoint_rewrite(ws2b, h(sin(x + y), sin(p + q))),
        fixpoint_rewrite(ws2n, h(sin(x + y), sin(p + q)))
    )

    # net_cache: a DAG-shared subterm evaluates once — h(x+y, x+y)
    # visits the same interned node from two trie states' descents
    ws3 = RuleWorkspace(
        compile_rules(
            CompiledRule[
                mmrule(h(slot(a), slot(a)) => slot(a)),
            ], DiscrimNet
        )
    )
    ws3(h(x + y, x + y))
    @test length(ws3.net_cache) > 0
    nbefore = length(ws3.net_cache)
    ws3(h(x + y, x + y))
    @test length(ws3.net_cache) == nbefore   # all memo hits
end

@testset "discrim net fuzz oracle" begin
    # REWRITING.md §9 milestone-3 oracle: net survivors ⊆ bucket
    # survivors (the net is strictly deeper), and `ws` apply results
    # identical, over randomized rule sets.
    @syms x y z a b s t w p q c u v
    using Random: Xoshiro
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    ATOMS = BasicSymbolic{SymReal}[x, y, z, CS(0), CS(1), CS(2), CS(3)]
    SLOTS = (a, b, c)
    HEADS = (+, *, h, g, sin, cos)
    subj_atoms = BasicSymbolic{SymReal}[x, y, z, CS(0), CS(1), CS(2), CS(3)]

    nargs(rng, op) = op === sin || op === cos ? 1 : rand(rng, 1:3)
    function rand_term(rng, depth)
        (depth <= 0 || rand(rng) < 0.3) && return rand(rng, subj_atoms)
        op = rand(rng, HEADS)
        args = BasicSymbolic{SymReal}[
            rand_term(rng, depth - 1)
                for _ in 1:nargs(rng, op)
        ]
        return op === (+) ? SymbolicUtils.add_worker(SymReal, args) :
            op === (*) ? SymbolicUtils.mul_worker(SymReal, args) : op(args...)
    end
    function rand_pat(rng, depth, vars)
        r = rand(rng)
        if depth <= 0 || r < 0.35
            return rand(rng, ATOMS)
        elseif r < 0.65
            vs = rand(rng, SLOTS)
            vars[vs] = get!(vars, vs, VarSpec.Slot(nothing, nothing))
            return slot(vs)
        else
            op = rand(rng, HEADS)
            args = BasicSymbolic{SymReal}[
                rand_pat(rng, depth - 1, vars)
                    for _ in 1:nargs(rng, op)
            ]
            return op === (+) ? +(args...) :
                op === (*) ? *(args...) : op(args...)
        end
    end

    buf = SymbolicUtils.SmallV{Int32}()
    for seed in 1:25
        rng = Xoshiro(seed)
        rules = CompiledRule[]
        for _ in 1:6
            vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}()
            pat = rand_pat(rng, 3, vars)
            iscall(pat) || issym(pat) || continue
            push!(rules, mmrule(pat => pat; vars))
        end
        isempty(rules) && continue
        rs_b = compile_rules(rules)
        rs_n = compile_rules(rules, DiscrimNet)
        ws_b, ws_n = RuleWorkspace(rs_b), RuleWorkspace(rs_n)
        for _ in 1:8
            t = rand_term(rng, 3)
            sr_b = populate_ir!(ws_b.subj, t)
            MatchMaker.lookup!(rs_b.index, buf, ws_b, t, sr_b)
            sb = collect(buf)
            sr_n = populate_ir!(ws_n.subj, t)
            MatchMaker.lookup!(rs_n.index, buf, ws_n, t, sr_n)
            sn = collect(buf)
            @test issorted(sn)
            @test sn ⊆ sb
            rb, rn = ws_b(t), ws_n(t)
            @test isequal(something(rb, t), something(rn, t))
        end
    end
end
