# Benchmark suite (§9, §12) — AirspeedVelocity/PkgBenchmark format.
# `SUITE` is a BenchmarkGroup; run with AirspeedVelocity.jl's benchpkg,
# or manually: `using PkgBenchmark; benchmarkpkg(".")`.
#
# Baselines: the naive oracle (test/oracle.jl — §5.7's top-level seam)
# and SymbolicUtils' @acrule for AC first-match.

using BenchmarkTools
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const, BasicSymbolic, term

include(joinpath(@__DIR__, "..", "test", "oracle.jl"))

@syms x y z a b c d s t p q r w
h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
g = set_operation_traits(g; commutative = true)
f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
f = set_operation_traits(
    f; associative = true, commutative = true, identity = :f0
)

pat_free = compile_pattern(h(slot(a), slot(b)))
pat_c3 = compile_pattern(g(slot(a), slot(b), slot(c)))
pat_ac = compile_pattern(slot(a) + segment(s))
pat_nl = compile_pattern(f(slot(a), slot(a)))
pat_seg2 = compile_pattern(f(segment(s), segment(t)))
pat_deep = compile_pattern(f(slot(a), f(slot(b), f(slot(c), segment(s)))))
sub_deep = f(x, f(y, f(z, p, q)))
pat_4slot = compile_pattern(slot(a) + slot(b) + slot(c) + slot(d))
sub_4 = p + q + r + w
sub_h2 = h(x, y)
sub_g3 = g(x, y, z)
sub_pq = f(p, q)
sub_pqr = f(p, q, r)
sub_ac = p + q + r
sub_pat_g3 = g(slot(a), slot(b), slot(c))
sub_pat_acseg = slot(a) + segment(s)
sub_pat_seg2 = f(segment(s), segment(t))
sub_pat_4slot = slot(a) + slot(b) + slot(c) + slot(d)

SUITE = BenchmarkGroup()
SUITE["match"] = BenchmarkGroup()
SUITE["matchall"] = BenchmarkGroup()
SUITE["oracle"] = BenchmarkGroup()
SUITE["acrule"] = BenchmarkGroup()
SUITE["alloc"] = BenchmarkGroup()

SUITE["match"]["free h(slot,slot) vs h(x,y)"] =
    @benchmarkable match($pat_free, $sub_h2)
SUITE["match"]["AC slot+seg under +"] =
    @benchmarkable match($pat_ac, $sub_ac)

SUITE["matchall"]["g 3 slots vs g(x,y,z)"] =
    @benchmarkable matchall($pat_c3, $sub_g3)
SUITE["matchall"]["slot+seg under +"] =
    @benchmarkable matchall($pat_ac, $sub_ac)
SUITE["matchall"]["f(a,a) vs f(p,q) non-linear"] =
    @benchmarkable matchall($pat_nl, $sub_pq)
SUITE["matchall"]["f 2 segs vs f(p,q,r)"] =
    @benchmarkable matchall($pat_seg2, $sub_pqr)
SUITE["matchall"]["nested f(a,f(b,f(c,s)))"] =
    @benchmarkable matchall($pat_deep, $sub_deep)
SUITE["matchall"]["4 slots + 4 args AC"] =
    @benchmarkable matchall($pat_4slot, $sub_4)

SUITE["oracle"]["g 3 slots vs g(x,y,z)"] =
    @benchmarkable oracle_matchall($sub_pat_g3, $sub_g3)
SUITE["oracle"]["slot+seg under +"] =
    @benchmarkable oracle_matchall($sub_pat_acseg, $sub_ac)
SUITE["oracle"]["f 2 segs vs f(p,q,r)"] =
    @benchmarkable oracle_matchall($sub_pat_seg2, $sub_pqr)
SUITE["oracle"]["4 slots + 4 args AC"] =
    @benchmarkable oracle_matchall($sub_pat_4slot, $sub_4)

const _ACRULE = @acrule ~xx + ~rr => nothing
SUITE["acrule"]["~x + ~rest apply"] =
    @benchmarkable _ACRULE($sub_ac)

SUITE["alloc"]["eachmatch g(3 slots)"] =
    @benchmarkable eachmatch(v -> true, $pat_c3, $sub_g3)
SUITE["alloc"]["matchall g(3 slots)"] =
    @benchmarkable matchall($pat_c3, $sub_g3)

# ------------------------------------------------------------------
# Stress workloads (§12 follow-up) — scaling fronts the user asked
# for: AC assignment enumeration, non-linear rechecks, segment
# partitioning, identity coercion, and failing searches. Sizes keep
# matchall in the 10²–10³ result range.
#
# SU's ~y absorbs the leftover args under + — our translation is
# `segment` with min=1 (empty → the identity, covered by `optional`).
# Duplicate pattern vars can't be expressed under canonical + (x + x
# folds to 2x), and `term(+, …)` on ≥3 args keeps symtype `Any` → an
# ordered Call, not AC — so the non-linear/segment cases below use the
# trait-declared heads `f` (AC) and `g` (commutative), which keep their
# traits at any symtype.
# ------------------------------------------------------------------

@syms u v
isconst_pred = SymbolicUtils.isconst

# --- SU overhead port (overhead["acrule"]) -------------------------
# SU: @rule ~x::is_literal_number + ~y => ~y on 1, a, a+2, a+b, a+2+b
pat_su = compile_pattern(
    slot(a) + segment(s); vars = Dict(a => slotspec(isconst_pred))
)
sub_su_1 = Const{SymReal}(1)
sub_su_a = a
sub_su_a2 = a + 2
sub_su_ab = a + b
sub_su_a2b = a + 2 + b

SUITE["su_overhead"] = BenchmarkGroup()
SUITE["su_overhead"]["isconst + seg vs 1"] =
    @benchmarkable matchall($pat_su, $sub_su_1)
SUITE["su_overhead"]["isconst + seg vs a"] =
    @benchmarkable matchall($pat_su, $sub_su_a)
SUITE["su_overhead"]["isconst + seg vs a+2"] =
    @benchmarkable matchall($pat_su, $sub_su_a2)
SUITE["su_overhead"]["isconst + seg vs a+b"] =
    @benchmarkable matchall($pat_su, $sub_su_ab)
SUITE["su_overhead"]["isconst + seg vs a+2+b"] =
    @benchmarkable matchall($pat_su, $sub_su_a2b)

# --- AC assignment enumeration: k slots vs k args → k! -------------
pat_k5 = compile_pattern(slot(a) + slot(b) + slot(c) + slot(d) + slot(s))
pat_k6 = compile_pattern(
    slot(a) + slot(b) + slot(c) + slot(d) + slot(s) + slot(t)
)
sub_k5 = p + q + r + x + y
sub_k6 = p + q + r + x + y + z

# --- Segment partitioning ------------------------------------------
# two sub-multiset segments under + → 2^n ordered partitions
pat_seg2_ac = compile_pattern(segment(s) + segment(t))
sub_8args = p + q + r + x + y + z + a + b
# three contiguous segments under a free head → C(n+2, 2) splits
pat_seg3_f = compile_pattern(f(segment(s), segment(t), segment(w)))
sub_f8 = f(p, q, r, x, y, z, a, b)

# --- Non-linear AC (factor extraction) ------------------------------
# x must unify across the Mul terms; a segment absorbs leftovers.
pat_factor = compile_pattern(slot(w) * slot(y) + slot(w) * slot(z))
sub_fact2 = p * q + p * r
pat_factor_seg = compile_pattern(
    slot(w) * slot(y) + slot(w) * slot(z) + segment(s)
)
sub_fact4 = p * q + p * r + p * s + p * t
pat_factor3_seg = compile_pattern(
    slot(w) * slot(y) + slot(w) * slot(z) + slot(w) * slot(u) + segment(s)
)
sub_fact6 = p * q + p * r + p * s + p * t + p * u + p * v
# no shared factor → the full assignment space is searched, zero results
pat_nofact = compile_pattern(
    slot(w) * slot(y) + slot(w) * slot(z) + slot(w) * slot(u) +
        slot(w) * slot(v)
)
sub_nofact = p * q + r * s + t * u + v * x

# --- Non-linear slots, rechecked late -------------------------------
# a..d take 4 of 6 args, then s must pair the last two — fails on all
# distinct args (≈720 assignment attempts), succeeds on term-dups
pat_nl_late = compile_pattern(
    f(slot(a), slot(b), slot(c), slot(d), slot(s), slot(s))
)
sub_nl_late_fail = f(p, q, r, x, y, z)
sub_nl_late_hit = f(p, q, r, x, p, p)
# non-linear segment under AC: s must capture the same multiset twice
pat_nl_seg = compile_pattern(f(segment(s), segment(s)))
sub_nl_seg_hit = f(p, q, r, p, q, r)
sub_nl_seg_fail = f(p, q, r, p, q, x)
# non-linear segment under a commutative head (multiset recheck)
pat_nl_g = compile_pattern(g(segment(s), segment(s)))
sub_nl_g_hit = g(p, q, p, q)
# nested non-linear: a bound at depth 1, rechecked at depth 4 —
# comm-only `g` (an associative head would flatten the nesting away)
pat_nl_deep = compile_pattern(
    g(slot(a), g(slot(a), g(slot(a), slot(a))))
)
sub_nl_deep_hit = g(p, g(p, g(p, p)))
sub_nl_deep_fail = g(p, g(p, g(p, q)))

# --- Failing searches ------------------------------------------------
# missing literal → phase-1 candidate matrix rejects immediately
pat_fail_lit = compile_pattern(42 + slot(a) + slot(b))
# --- Identity coercion -----------------------------------------------
pat_coerce = compile_pattern(slot(a) + segment(s))
sub_coerce = p

SUITE["stress"] = BenchmarkGroup()
# AC enumeration
SUITE["stress"]["ac 5 slots matchall (5!)"] =
    @benchmarkable matchall($pat_k5, $sub_k5)
SUITE["stress"]["ac 6 slots matchall (6!)"] =
    @benchmarkable matchall($pat_k6, $sub_k6)
SUITE["stress"]["ac 6 slots first-match"] =
    @benchmarkable match($pat_k6, $sub_k6)
# segment partitioning
SUITE["stress"]["ac seg+seg on 8 args (2^8)"] =
    @benchmarkable matchall($pat_seg2_ac, $sub_8args)
SUITE["stress"]["free f 3 segs on 8 args"] =
    @benchmarkable matchall($pat_seg3_f, $sub_f8)
# non-linear factor extraction
SUITE["stress"]["ac factor x*y+x*z on 2 prods"] =
    @benchmarkable matchall($pat_factor, $sub_fact2)
SUITE["stress"]["ac factor+rest on 4 prods"] =
    @benchmarkable matchall($pat_factor_seg, $sub_fact4)
SUITE["stress"]["ac factor3+rest on 6 prods"] =
    @benchmarkable matchall($pat_factor3_seg, $sub_fact6)
SUITE["stress"]["ac factor4 no common factor"] =
    @benchmarkable matchall($pat_nofact, $sub_nofact)
# non-linear late rechecks
SUITE["stress"]["ac nl slots fail (distinct)"] =
    @benchmarkable matchall($pat_nl_late, $sub_nl_late_fail)
SUITE["stress"]["ac nl slots hit (dup args)"] =
    @benchmarkable matchall($pat_nl_late, $sub_nl_late_hit)
SUITE["stress"]["ac nl segment hit (2^6 subs)"] =
    @benchmarkable matchall($pat_nl_seg, $sub_nl_seg_hit)
SUITE["stress"]["ac nl segment fail (odd multiset)"] =
    @benchmarkable matchall($pat_nl_seg, $sub_nl_seg_fail)
SUITE["stress"]["comm nl segment g hit"] =
    @benchmarkable matchall($pat_nl_g, $sub_nl_g_hit)
SUITE["stress"]["nested nl depth-4 hit"] =
    @benchmarkable matchall($pat_nl_deep, $sub_nl_deep_hit)
SUITE["stress"]["nested nl depth-4 fail"] =
    @benchmarkable matchall($pat_nl_deep, $sub_nl_deep_fail)
# failing searches
SUITE["stress"]["ac missing literal fail-fast"] =
    @benchmarkable matchall($pat_fail_lit, $sub_8args)
# identity coercion
SUITE["stress"]["ac singleton coerce x+seg vs p"] =
    @benchmarkable matchall($pat_coerce, $sub_coerce)

# ------------------------------------------------------------------
# Workload benchmarks — batched passes sized to a few ms per sample,
# so ratios aren't dominated by timer noise on µs-scale cases.
#
# Model: a fixed rule set applied to a corpus of independent subject
# expressions — the rewrite-pass scenario (apply every rule to every
# expression, gather all results). Compilation and corpus construction
# happen once at suite setup; the timed body is one pass over
# pattern × subject pairs, counting results so nothing is
# dead-code-eliminated. Each pass exercises engine setup, frame
# dispatch, and backtracking across every matcher family.
#
# The corpus is deterministic — index arithmetic over an 8-symbol
# pool, no RNG — and mixes hit and miss shapes so a pass pays both
# fast head-mismatch rejections and deep backtracking:
#   * canonical Adds of 2–5 terms,
#   * factored-product sums (the w·y + w·z + rest shape),
#   * AC f / commutative g calls at arities 2–6,
#   * duplicate-arg f's (non-linear recheck hits),
#   * nested f's and g's,
#   * free-head h calls, including h over Add arguments.
# ------------------------------------------------------------------

const _WL_SYMS = (p, q, r, x, y, z, a, b)
_wl_arg(i) = _WL_SYMS[mod1(i, length(_WL_SYMS))]

const _WL_CORPUS = let s = _wl_arg
    corpus = Any[]
    for n in 2:5, seed in 1:12
        push!(corpus, +((s(seed + k * n) for k in 1:n)...))
    end
    for i in 1:8, j in 1:8
        push!(corpus, s(i) * s(j) + s(i) * s(j + 1) + s(3) * s(i + j))
    end
    for n in 2:6, seed in 1:8
        push!(corpus, f((s(seed + k) for k in 1:n)...))
        push!(corpus, g((s(seed * k + n) for k in 1:n)...))
    end
    for i in 1:8
        push!(corpus, f(s(i), s(i), s(i + 1), s(i + 1)))
        push!(corpus, f(s(i), s(i + 1), s(i + 2), s(i)))
    end
    for i in 1:12
        push!(corpus, f(s(i), f(s(i + 1), f(s(i + 2), s(i + 3), s(i + 4)))))
        push!(corpus, f(s(i), f(s(i), s(i + 1))))
        push!(corpus, g(s(i), g(s(i + 1), s(i + 2))))
        push!(corpus, g(s(i), g(s(i), s(i))))
    end
    for i in 1:8, j in 1:8
        push!(corpus, h(s(i), s(j)))
        push!(corpus, h(s(i) + s(j), s(i + 1)))
    end
    corpus
end

const _WL_PATS = (
    compile_pattern(h(slot(a), slot(b))),
    compile_pattern(g(slot(a), slot(b), slot(c))),
    compile_pattern(slot(a) + segment(s)),
    compile_pattern(slot(w) * slot(y) + slot(w) * slot(z) + segment(s)),
    compile_pattern(f(slot(a), slot(a), segment(s))),
    compile_pattern(g(slot(a), g(slot(b), slot(c)))),
)

function _wl_matchall(pats, corpus)
    n = 0
    for pat in pats, subj in corpus
        n += length(matchall(pat, subj))
    end
    return n
end

function _wl_match(pats, corpus)
    n = 0
    for pat in pats, subj in corpus
        match(pat, subj) === nothing || (n += 1)
    end
    return n
end

function _wl_eachmatch(pats, corpus)
    n = Ref(0)
    for pat in pats, subj in corpus
        eachmatch(b -> (n[] += 1), pat, subj)
    end
    return n[]
end

# --- single-match workloads -----------------------------------------
# One (pattern, subject) pair whose *search itself* is ms-scale — no
# batching. Sized empirically to ~3–8 ms per call:
#
#   * nl-pair fail: the last two slots must unify; 8 distinct args make
#     that impossible, so the engine burns the entire P(8,6) injection
#     space and returns nothing — pure backtracking, zero results.
#   * 3-seg AC partition: each of n args goes to one of 3 segments →
#     3^n ordered partitions (2187 / 6561 results).
#   * factor extraction: 4 non-linear `w·_` terms + rest segment over
#     7 products sharing a common factor.
#   * 2-seg AC partition on 10 args → 2^10 = 1024 sub-multiset splits.
#   * 5 contiguous segments under free head h on 11 args → C(14,4)
#     splits — the Seq matcher family rather than AC.
# eachmatch variants isolate engine time from result materialization.
# --------------------------------------------------------------------

pat_wl_nlpair = compile_pattern(
    f(slot(a), slot(b), slot(c), slot(d), slot(y), slot(x), slot(s), slot(s))
)
sub_wl_nl8 = f(p, q, r, x, y, z, a, b)

pat_wl_sss = compile_pattern(segment(s) + segment(v) + segment(w))
sub_wl_add7 = p + q + r + x + y + z + a
sub_wl_add9 = p + q + r + x + y + z + a + b + c

pat_wl_f4 = compile_pattern(
    slot(w) * slot(y) + slot(w) * slot(z) + slot(w) * slot(u) +
        slot(w) * slot(v) + segment(s)
)
sub_wl_f8 = p * q + p * r + p * x + p * y + p * z + p * a +
    p * b + p * c

pat_wl_ss = compile_pattern(segment(s) + segment(v))
sub_wl_add11 = p + q + r + x + y + z + a + b + c + d + u

pat_wl_h5 = compile_pattern(
    h(segment(s), segment(v), segment(w), segment(a), segment(b))
)
sub_wl_h11 = h(p, q, r, x, y, z, a, b, c, d, u)

function _wl_eachmatch_count(pat, subj)
    n = Ref(0)
    eachmatch(b -> (n[] += 1), pat, subj)
    return n[]
end

# --- deep tier: the same shapes scaled to ~40–85 ms -----------------
# Search spaces grow combinatorially in subject arity, so each family
# gets a second point on the ladder — a constant-factor regression
# holds its ratio across the two sizes; an algorithmic one grows.
pat_wl_nl9 = compile_pattern(
    f(
        slot(a), slot(b), slot(c), slot(d), slot(y), slot(x), slot(w),
        slot(s), slot(s)
    )
)
sub_wl_nl9 = f(p, q, r, x, y, z, a, b, c)

pat_wl_h6 = compile_pattern(
    h(segment(s), segment(v), segment(w), segment(a), segment(b), segment(c))
)
sub_wl_h14 = h(p, q, r, x, y, z, a, b, c, d, u, v, w, s)

sub_wl_add14 = p + q + r + x + y + z + a + b + c + d + u + v + w + s
sub_wl_f11 = p * q + p * r + p * x + p * y + p * z + p * a + p * b +
    p * c + p * d + p * u + p * v

SUITE["workload"] = BenchmarkGroup()
SUITE["workload"]["matchall batch (6 pats × $(length(_WL_CORPUS)) exprs)"] =
    @benchmarkable _wl_matchall($_WL_PATS, $_WL_CORPUS)
SUITE["workload"]["first-match batch (6 pats × $(length(_WL_CORPUS)) exprs)"] =
    @benchmarkable _wl_match($_WL_PATS, $_WL_CORPUS)
SUITE["workload"]["eachmatch batch (6 pats × $(length(_WL_CORPUS)) exprs)"] =
    @benchmarkable _wl_eachmatch($_WL_PATS, $_WL_CORPUS)

SUITE["workload"]["single ac nl-pair fail (P(8,6) backtrack)"] =
    @benchmarkable matchall($pat_wl_nlpair, $sub_wl_nl8)
SUITE["workload"]["single ac 3segs vs 7-arg add (2187)"] =
    @benchmarkable matchall($pat_wl_sss, $sub_wl_add7)
SUITE["workload"]["single ac 3segs vs 9-arg eachmatch (19683)"] =
    @benchmarkable _wl_eachmatch_count($pat_wl_sss, $sub_wl_add9)
SUITE["workload"]["single ac factor4+rest vs 8 prods"] =
    @benchmarkable matchall($pat_wl_f4, $sub_wl_f8)
SUITE["workload"]["single ac seg+seg vs 11-arg add (2048)"] =
    @benchmarkable matchall($pat_wl_ss, $sub_wl_add11)
SUITE["workload"]["single free h 5segs vs 11-arg (1365)"] =
    @benchmarkable matchall($pat_wl_h5, $sub_wl_h11)

SUITE["workload"]["deep ac nl-pair fail 9-arg (P(9,7) backtrack)"] =
    @benchmarkable matchall($pat_wl_nl9, $sub_wl_nl9)
SUITE["workload"]["deep ac 3segs vs 11-arg eachmatch (177147)"] =
    @benchmarkable _wl_eachmatch_count($pat_wl_sss, $sub_wl_add11)
SUITE["workload"]["deep ac seg+seg vs 14-arg add (16384)"] =
    @benchmarkable matchall($pat_wl_ss, $sub_wl_add14)
SUITE["workload"]["deep ac factor4+rest vs 11 prods (7920)"] =
    @benchmarkable matchall($pat_wl_f4, $sub_wl_f11)
SUITE["workload"]["deep free h 6segs vs 14-arg (11628)"] =
    @benchmarkable matchall($pat_wl_h6, $sub_wl_h14)

# ------------------------------------------------------------------
# Rewrite workloads — MatchMaker RuleSet/RuleWorkspace vs SymbolicUtils'
# @rule + Rewriters idiom (Postwalk(Chain) ≡ the old RuleSet). SU has
# no head-slot rules, so the set covers AC +/*, segments, free heads,
# 3-arg patterns, and literals only.
# ------------------------------------------------------------------
import SymbolicUtils.Rewriters
using SymbolicUtils.Rewriters: Chain, Postwalk, Fixpoint

const RW_MM_RULES = CompiledRule[
    mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
    mmrule(slot(a) * slot(b) => slot(a) + slot(b)),
    mmrule(segment(s) + slot(t) => slot(t)),
    mmrule(segment(s) * slot(t) => slot(t)),
    mmrule(sin(slot(a)) => slot(a)),
    mmrule(h(slot(a), slot(b)) => slot(a)),
    mmrule(slot(a) + slot(b) + slot(c) => slot(a)),
    mmrule(slot(a) * slot(b) * slot(c) => slot(a)),
]
const RW_SU_RULES = [
    (@rule ~a + ~b => ~a * ~b),
    (@rule ~a * ~b => ~a + ~b),
    (@rule ~~s + ~t => ~t),
    (@rule ~~s * ~t => ~t),
    (@rule sin(~a) => ~a),
    (@rule h(~a, ~b) => ~a),
    (@rule ~a + ~b + ~c => ~a),
    (@rule ~a * ~b * ~c => ~a),
]
const RW_RS = compile_rules(RW_MM_RULES)
const RW_WS = RuleWorkspace(RW_RS)
const RW_SU_CHAIN = Chain(RW_SU_RULES)
const RW_SU_POST = Postwalk(RW_SU_CHAIN)

# single site: rule dispatch on one node — bucket index vs sequential trial
sub_rw_site = x + y + z
# traversal: several rules fire across a ~20-node subject
sub_rw = h(sin(x + y), p * q) + cos(w) * (a + b + c) + sin(p + q)
# fixpoint subject under the convergent subset (a+b→a*b, sin→id)
sub_rw_fp = h(sin(x + y), sin(p + q))
const RW_MM_FP_RULES = CompiledRule[
    mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
    mmrule(sin(slot(a)) => slot(a)),
]
const RW_WS_FP = RuleWorkspace(compile_rules(RW_MM_FP_RULES))
const RW_SU_FP = Fixpoint(
    Postwalk(
        Chain(
            [
                (@rule ~a + ~b => ~a * ~b),
                (@rule sin(~a) => ~a),
            ]
        )
    )
)
# Phase-2: the same workloads through the DiscrimNet index
const RW_WS_NET = RuleWorkspace(compile_rules(RW_MM_RULES, DiscrimNet))
const RW_WS_NET_FP =
    RuleWorkspace(compile_rules(RW_MM_FP_RULES, DiscrimNet))

SUITE["rewrite"] = BenchmarkGroup()
SUITE["rewrite"]["site: mm ws(x)"] =
    @benchmarkable $RW_WS($sub_rw_site)
SUITE["rewrite"]["site: mm ws(x) net"] =
    @benchmarkable $RW_WS_NET($sub_rw_site)
SUITE["rewrite"]["site: su Chain(x)"] =
    @benchmarkable $RW_SU_CHAIN($sub_rw_site)
SUITE["rewrite"]["walk: mm rewrite(ws, x)"] =
    @benchmarkable rewrite($RW_WS, $sub_rw)
SUITE["rewrite"]["walk: mm rewrite(ws, x) net"] =
    @benchmarkable rewrite($RW_WS_NET, $sub_rw)
SUITE["rewrite"]["walk: mm Postwalk(ws)(x)"] =
    @benchmarkable ($RW_SU_POST === nothing ? nothing : Postwalk($RW_WS))($sub_rw)
SUITE["rewrite"]["walk: su Postwalk(Chain)(x)"] =
    @benchmarkable $RW_SU_POST($sub_rw)
SUITE["rewrite"]["fixp: mm fixpoint_rewrite(ws, x)"] =
    @benchmarkable fixpoint_rewrite($RW_WS_FP, $sub_rw_fp)
SUITE["rewrite"]["fixp: mm fixpoint net"] =
    @benchmarkable fixpoint_rewrite($RW_WS_NET_FP, $sub_rw_fp)
SUITE["rewrite"]["fixp: su Fixpoint∘Postwalk(x)"] =
    @benchmarkable $RW_SU_FP($sub_rw_fp)

# Occurrence search (milestone 4): `eachmatch_at` shares one engine +
# the populated IR across sites — the naive alternative descends and
# builds a fresh engine+IR per `match` call. Subject with DAG-shared
# subterms (sin(x+y), sin(p+q) occur twice) exercises node dedup.
sub_occ = h(x + y, sin(p + q)) * (sin(x + y) + sin(p + q)) * sin(x + y)
pat_occ = sin(slot(a))
function _naive_occ(pat, s)
    subj = SymbolicUtils.IRStructure{SymReal}()
    SymbolicUtils.populate_ir!(subj, s)
    n = 0
    for i in 1:length(subj)
        match(pat, subj[i]) === nothing || (n += 1)
    end
    return n
end
SUITE["rewrite"]["occ: boundmatches_at"] =
    @benchmarkable foreach(x -> nothing, boundmatches_at($pat_occ, $sub_occ))
SUITE["rewrite"]["occ: descend+match"] =
    @benchmarkable _naive_occ($pat_occ, $sub_occ)

# ------------------------------------------------------------------
# DiscrimNet vs BucketIndex at scale — the cases that exercise the
# net's leverage: many same-(op,arity) rules distinguished only by
# literals/deeper structure (each bucket candidate pays an engine
# reset+match; the net's literal edges prune before engines run),
# DAG-shared subterms (net_cache dedup), and fixpoint iterations
# (memo persistence across re-evaluation).
# ------------------------------------------------------------------
const CS = Const{SymReal}
const DN_MM_RULES = CompiledRule[
    # 40 literal-distinguished rules — bucket can't separate them by
    # (op, arity); the net's literal edges keep ~1 survivor
    [mmrule(h(slot(a), CS(k)) => CS(k)) for k in 1:10]...,
    [mmrule(h(CS(k), slot(b)) => CS(k)) for k in 1:10]...,
    [mmrule(sin(CS(k)) => CS(k)) for k in 1:10]...,
    [mmrule(g(CS(k), slot(b)) => slot(b)) for k in 1:10]...,
    # general rules every matcher has — structural checks only
    mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
    mmrule(segment(s) + slot(t) => slot(t)),
    mmrule(slot(a) * CS(1) => slot(a)),
    mmrule(slot(a) + CS(0) => slot(a)),
    mmrule(h(slot(a), slot(b)) => slot(a) + slot(b)),
    mmrule(g(slot(a), slot(b)) => slot(a)),
    mmrule(g(h(slot(a), slot(b)), slot(c)) => slot(c)),
    mmrule(sin(slot(a)) => slot(a)),
    mmrule(h(sin(slot(a)), slot(b)) => slot(b)),
    mmrule(h(slot(a), sin(slot(b))) => slot(a)),
]
const DN_WS_B = RuleWorkspace(compile_rules(DN_MM_RULES))
const DN_WS_N = RuleWorkspace(compile_rules(DN_MM_RULES, DiscrimNet))
const DN_WS_B2 = RuleWorkspace(compile_rules(DN_MM_RULES))
const DN_WS_N2 = RuleWorkspace(compile_rules(DN_MM_RULES, DiscrimNet))

# single site: h(x,7) — bucket: ~10 same-op candidates pay engine runs;
# net: literal edge prunes to ~2
sub_dn_site = h(x, CS(7))
# deep subject ~60 nodes with many literal-bearing call nodes
sub_dn_walk = h(sin(CS(3)), h(x + y, CS(5))) +
    g(CS(4), h(p, q)) * (a + b + c) +
    sin(CS(7)) + g(CS(9), sin(x)) +
    h(x * y, CS(2)) + h(CS(6), p + q) +
    g(h(x, y), z) + sin(w + CS(1))
# fixpoint: convergent pair over a subject with repeated subterms
sub_dn_fp = h(sin(x + y), sin(p + q)) + sin(CS(3)) + sin(x + y)

# deep multi-iteration fixpoint: nested sin/h/g chains converge over
# ~5 sweeps — exercises §7 dirty propagation (each sweep re-evals only
# stale parents + new nodes, not the whole subject)
const DN_FP_DEEP_RULES = CompiledRule[
    mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
    mmrule(sin(slot(a)) => slot(a)),
    mmrule(cos(slot(a)) => slot(a)),
    mmrule(h(slot(a), slot(b)) => slot(a)),
    mmrule(g(slot(a), slot(b)) => slot(a) * slot(b)),
]
const DN_WS_FP_DEEP = RuleWorkspace(compile_rules(DN_FP_DEEP_RULES))
sub_dn_fpdeep = h(sin(sin(sin(x + y))), cos(g(sin(p + q), sin(a + b)))) +
    sin(sin(w + z)) + g(cos(x + y), sin(p + q))

SUITE["discrimnet"] = BenchmarkGroup()
SUITE["discrimnet"]["site: ws(h(x,7)) bucket"] =
    @benchmarkable $DN_WS_B($sub_dn_site)
SUITE["discrimnet"]["site: ws(h(x,7)) net"] =
    @benchmarkable $DN_WS_N($sub_dn_site)
SUITE["discrimnet"]["walk: rewrite bucket"] =
    @benchmarkable rewrite($DN_WS_B, $sub_dn_walk)
SUITE["discrimnet"]["walk: rewrite net"] =
    @benchmarkable rewrite($DN_WS_N, $sub_dn_walk)
SUITE["discrimnet"]["fixp: fixpoint bucket"] =
    @benchmarkable fixpoint_rewrite($DN_WS_B2, $sub_dn_fp)
SUITE["discrimnet"]["fixp: fixpoint net"] =
    @benchmarkable fixpoint_rewrite($DN_WS_N2, $sub_dn_fp)
SUITE["discrimnet"]["fixp: deep"] =
    @benchmarkable fixpoint_rewrite($DN_WS_FP_DEEP, $sub_dn_fpdeep)
