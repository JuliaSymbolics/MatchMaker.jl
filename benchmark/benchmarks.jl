# Benchmark suite (§9, §12) — AirspeedVelocity/PkgBenchmark format.
# `SUITE` is a BenchmarkGroup; run with AirspeedVelocity.jl's benchpkg,
# or manually: `using PkgBenchmark; benchmarkpkg(".")`.
#
# Baselines: the naive oracle (test/oracle.jl — §5.7's top-level seam)
# and SymbolicUtils' @acrule for AC first-match.

using BenchmarkTools
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

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
