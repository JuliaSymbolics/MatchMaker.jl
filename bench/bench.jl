# perf/hardening benchmark suite (§9, §12). Run via jld:
#   jld run bench/bench.jl
# Timing uses @elapsed/@allocated (BenchmarkTools is not a dep).

using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

function bench(name::String, f; reps::Int = 5)
    f()  # warmup
    tbest, abest = Inf, typemax(Int)
    for _ in 1:reps
        GC.gc()
        t = @elapsed f()
        a = @allocated f()
        tbest = min(tbest, t)
        abest = min(abest, a)
    end
    println(
        rpad(name, 58),
        lpad(round(tbest * 1e6; digits = 1), 10), " μs  ",
        lpad(abest, 12), " B"
    )
    return nothing
end

@syms x y z a b c d s t p q r w
h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
g = set_operation_traits(g; commutative = true)
f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
f = set_operation_traits(
    f; associative = true, commutative = true, identity = :f0
)

include(joinpath(@__DIR__, "..", "test", "oracle.jl"))

println("── engine ─────────────────────────────────────────────────")
pat_free = compile_pattern(h(slot(a), slot(b)))
bench("match  h(slot,slot) vs h(x,y)            first", () -> match(pat_free, h(x, y)))
pat_c3 = compile_pattern(g(slot(a), slot(b), slot(c)))
bench("matchall g(3 slots) vs g(x,y,z)         6 results", () -> matchall(pat_c3, g(x, y, z)))
pat_ac = compile_pattern(slot(a) + segment(s))
bench("matchall slot+seg under +               3 results", () -> matchall(pat_ac, p + q + r))
pat_nl = compile_pattern(f(slot(a), slot(a)))
bench("matchall f(a,a) vs f(p,q)               non-linear", () -> matchall(pat_nl, f(p, q)))
pat_seg2 = compile_pattern(f(segment(s), segment(t)))
bench("matchall f(2 segs) vs f(p,q,r)          8 results", () -> matchall(pat_seg2, f(p, q, r)))
pat_deep = compile_pattern(f(slot(a), f(slot(b), f(slot(c), segment(s)))))
sub_deep = f(x, f(y, f(z, p, q)))
bench("matchall nested f(a,f(b,f(c,s)))        deep", () -> matchall(pat_deep, sub_deep))
# AC with 4 slots and 4 args — 24 assignments
pat_4slot = compile_pattern(slot(a) + slot(b) + slot(c) + slot(d))
sub_4 = p + q + r + w
bench("matchall 4 slots + 4 args AC            24 results", () -> matchall(pat_4slot, sub_4))

println("── oracle (naive baseline) ────────────────────────────────")
bench("oracle   g(3 slots) vs g(x,y,z)         6 results", () -> oracle_matchall(g(slot(a), slot(b), slot(c)), g(x, y, z)))
bench("oracle   slot+seg under +               3 results", () -> oracle_matchall(slot(a) + segment(s), p + q + r))
bench("oracle   f(2 segs) vs f(p,q,r)          8 results", () -> oracle_matchall(f(segment(s), segment(t)), f(p, q, r)))
bench("oracle   4 slots + 4 args AC            24 results", () -> oracle_matchall(slot(a) + slot(b) + slot(c) + slot(d), sub_4))

println("── @acrule comparison (match once via rule) ───────────────")
r1 = @acrule ~xx + ~rr => nothing
subj_ac = p + q + r
bench("@acrule  ~x + ~rest applied             first-match", () -> r1(subj_ac))
bench("engine   slot+seg under +               match only", () -> match(pat_ac, subj_ac))

println("── allocation spot-checks ─────────────────────────────────")
eng_iter = MatchEngine(pat_c3, g(x, y, z), Constraint[])
bench("eachmatch g(3 slots)                    live-view loop", () -> eachmatch(v -> true, pat_c3, g(x, y, z)))
bench("matchall g(3 slots)                     materialized", () -> matchall(pat_c3, g(x, y, z)))

println("── _symtype_ok memo-vs-enumerate (§5.5b) ──────────────────")
# realistic (cand, want) pairs hit by slot binds in the above cases
pairs = Tuple{Any, Any}[
    (SymReal, Number), (SymReal, SymReal), (Int, Real), (Int, Number),
    (SymReal, Any), (Number, Any), (Real, Number), (SymReal, Real),
]
const _ST_MEMO = Dict{Tuple{Any, Any}, Bool}()
function _symtype_ok_memo(@nospecialize(cand), @nospecialize(want))
    return get!(_ST_MEMO, (cand, want)) do
        MatchMaker._symtype_ok(cand, want)
    end
end
function run_enum(n)
    acc = 0
    for _ in 1:n, (c, w) in pairs
        acc += MatchMaker._symtype_ok(c, w)
    end
    return acc
end
function run_memo(n)
    acc = 0
    for _ in 1:n, (c, w) in pairs
        acc += _symtype_ok_memo(c, w)
    end
    return acc
end
bench("_symtype_ok enum    8 pairs x 1e5", () -> run_enum(Int(1e5)))
bench("_symtype_ok memo    8 pairs x 1e5", () -> run_memo(Int(1e5)))
