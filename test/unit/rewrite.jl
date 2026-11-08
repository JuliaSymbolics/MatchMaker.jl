using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType
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
    rs = compile_rules(CompiledRule[
        mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
        mmrule(segment(s) + slot(t) => segment(s)),
        mmrule(slot(a) * CS(2) => slot(a) + slot(a)),
    ])
    ws = RuleWorkspace(rs)
    @test isequal(ws(x + y), x * y)
    @test isequal(ws(CS(2) * x), CS(2) * x)      # r3 matched; x+x canonicalizes to 2x
    @test isequal(ws(x + y + z + w), x + z + w) # r3: t=y, s captures the rest
    @test ws(x * y) === nothing                 # no candidate
    @test ws(CS(5)) === nothing                 # atom, no leaf rules

    # callable rhs: `nothing` falls through to the next rule
    only_equal = mmrule(slot(a) + slot(b) =>
        (view -> isequal(view[slot(a)], view[slot(b)]) ?
            CS(2) * view[slot(a)] : nothing))
    mul = mmrule(slot(a) + slot(b) => slot(a) * slot(b))
    ws2 = RuleWorkspace(compile_rules(CompiledRule[only_equal, mul]))
    @test isequal(ws2(x + y), x * y)   # callable -> nothing -> r2 fires
    e = x + x
    @test ws2(e) === nothing           # x+x is a Mul — no + head

    # same engine is reset and reused across sites — bindings don't leak
    rs3 = compile_rules(CompiledRule[
        mmrule(slot(a) + slot(b) => slot(b)),
    ])
    ws3 = RuleWorkspace(rs3)
    @test isequal(ws3(x + y), y)       # b=y
    @test isequal(ws3(p + q), q)       # reset: b=q, not a stale y

    # reset! clears the prior match's bindings before re-searching
    pat_ab = compile_pattern(slot(a) + slot(b))
    eng = MatchEngine(pat_ab, x + y, Constraint[])
    @test next_match!(eng)
    @test any(v -> v != 0, eng.binds.node)         # match leaves binds
    reset!(eng, eng.subj, populate_ir!(eng.subj, p + q))
    @test all(v -> v == 0, eng.binds.node)         # cleared by reset
    @test next_match!(eng)                          # fresh search re-binds
    @test isequal(eng.subj[eng.binds.node[pat_ab.var_of[b]]], q)

    # workspace bounded reuse: buffer plateaus, no per-site engine alloc
    ws3(x + y); ws3(p + q)
    e1 = ws3.engines[1]
    ws3(a + b)
    @test ws3.engines[1] === e1

    # maxsteps: a tiny budget ends the search with no result
    ws4 = RuleWorkspace(rs3; maxsteps = 0)
    @test ws4(x + y) === nothing
    ws4.maxsteps = typemax(Int)
    @test isequal(ws4(x + y), y)
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
    MatchMaker.lookup!(idx, buf, x + y)
    @test Set(collect(buf)) == Set(Int32[1, 3])  # + bucket + any_head
    MatchMaker.lookup!(idx, buf, x * y)
    @test Set(collect(buf)) == Set(Int32[2, 3])  # * bucket + any_head
    MatchMaker.lookup!(idx, buf, CS(3))
    @test Set(collect(buf)) == Set(Int32[3, 4])  # leaf + any_head

    # arity filters candidates: a+b needs exactly 2 args
    MatchMaker.lookup!(idx, buf, x + y + z)
    @test collect(buf) == Int32[3]               # only any_head survives
    MatchMaker.lookup!(idx, buf, x * y * z)
    @test collect(buf) == Int32[3]               # a*b is 2-factor — filtered

    # head-slot pattern lands in any_head
    fh = Sym{SymReal}(:fh; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    r_hd = mmrule(slot(f)(slot(a)) => slot(a);
        vars = Dict(a => slotspec()))
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
    ws_pair = RuleWorkspace(compile_rules(CompiledRule[
        r_mul,
        mmrule(h(slot(a), slot(a)) => slot(a)),   # non-linear h rule
    ]))
    @test isequal(rewrite(ws_pair, h(x + y, x * y); order = :pre), h(x * y, x * y))
    @test isequal(rewrite(ws_pair, h(x + y, x * y); order = :post), x * y)
    @test_throws ArgumentError rewrite(ws_pair, x; order = :bogus)

    # callable rhs producing non-symbolic values gets Const-wrapped
    r_num = mmrule(CS(1) + slot(a) => (v -> 42))
    ws_num = RuleWorkspace(compile_rules(CompiledRule[r_num]))
    @test isequal(ws_num(CS(1) + x), CS(42))

    # fixpoint: iterate until stable — a+b -> a*b has no + left
    ws_mul = RuleWorkspace(rs)
    @test isequal(fixrewrite(ws_mul, x + y), x * y)

    # 2x+2y (canonical (x+y)+(x+y)) -> 2x*2y = 4xy in one pass
    nested = (x + y) + (x + y)
    got = fixrewrite(ws_mul, nested)
    @test isequal(got, CS(4) * x * y)
end

@testset "SU combinator compatibility" begin
    @syms x y z a b p q

    ws = RuleWorkspace(compile_rules(CompiledRule[
        mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
        mmrule(slot(a) * slot(a) => slot(a)^CS(2)),
    ]))

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
