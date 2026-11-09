# perf notes (§9, §12)

The suite lives at `benchmark/benchmarks.jl` in
AirspeedVelocity/PkgBenchmark format (`SUITE::BenchmarkGroup`) — run it
with `benchpkg`/AirspeedVelocity, or manually:

```julia
using BenchmarkTools
include("benchmark/benchmarks.jl")
res = run(SUITE)
```

Baselines: the naive oracle (`test/oracle.jl`, §5.7's top-level seam)
and SymbolicUtils' `@acrule`/`Rewriters` for rule application. The
benchmark env resolves a **local checkout** of SymbolicUtils
(`../../SymbolicUtils.jl`), not a release.

Numbers below: minimums from a full `run(SUITE)` on Apple Silicon,
Julia 1.13, at `perf/seg-args` (post-`ArgsT` segment binds).

## Rewrite / many-to-one: MatchMaker vs SymbolicUtils

8-rule set, ~20-node traversal subject, 2-rule fixpoint subset.

| case | MatchMaker | SymbolicUtils | ratio |
|---|---|---|---|
| site: `ws(x)` vs `Chain(x)` | **375 ns** / 320 B | 1.04 μs / 1.31 KiB | **2.8×** |
| walk: `Postwalk(ws)(x)` | **13.1 μs** / 7.0 KiB | `Postwalk(Chain)` 30.3 μs / 24 KiB | **2.3×** |
| walk: native `rewrite(ws,x)` | 22.4 μs / 12 KiB | 30.3 μs | 1.35× |
| fixpoint: `fixpoint_rewrite` | 11.7 μs | `Fixpoint∘Postwalk` **8.7 μs** | 0.74× |

- Site dispatch is the index win: `BucketIndex` filters 8 rules to ~1–2
  candidates by `(op, arity)`; `Chain` tries all 8 sequentially.
- **Fixpoint is a loss** — `fixpoint_rewrite` pays the IR-driven
  `_rewrite_post` sweep per iteration; SU's recursive Walk is leaner per
  pass. The Phase-2 incremental fixpoint (dirty propagation, §7) is the
  designed answer: iterate only the changed subtrees.
- `Postwalk(ws)` beats native `rewrite` on this subject — the walk's
  copy-on-write rebuilds without IR bookkeeping; the native pass buys
  DAG-shared subterm dedup instead.

### DiscrimNet vs BucketIndex (same suite cases)

`compile_rules(rules; index = DiscrimNet)` — Phase-2 shared-frontier
trie + `net_cache` memoization, same workloads:

| case | BucketIndex | DiscrimNet | ratio |
|---|---|---|---|
| site: `ws(x)` | 333 ns / 320 B | **291 ns / 288 B** | ~14% faster |
| walk: `rewrite(ws,x)` | 24.4 μs / 12.4 KiB | 24.0 μs / 11.8 KiB | ~2% |
| fixpoint | 13.0 μs / 8.3 KiB | 12.0 μs / 7.3 KiB | ~8% |

Consistent but small: per-site `lookup!` was only ~6% of site cost, and
an engine `reset!`+fail costs ≈ a net evaluation — so the net wins the
lookup share (memo-hit ≈ dict get) and slightly less allocation, no
more. The design payoff is structural, not per-site speed: `net_cache`
persists across fixpoint iterations and DAG-shared subterms evaluate
once, which is what the incremental fixpoint (dirty propagation, §7)
stands on.

## Engine vs naive oracle (`matchall` workloads)

| workload | engine | oracle | ratio |
|---|---|---|---|
| `g` 3 slots / 3 args | **1.75 μs** | 2.50 μs | 1.4× |
| `slot + segment` under `+` | **3.46 μs** | 6.63 μs | 1.9× |
| `f` 2 segments / 3 args | **13.75 μs** | 31.6 μs | 2.3× |
| 4 slots + 4 args AC | **6.29 μs** | 9.08 μs | 1.4× |

## vs SU `@acrule` apply

`~x + ~rest` apply: **10.1 μs** — vs our `match` on the same AC pattern
shape: 1.63 μs (~6×) and `matchall`: 3.46 μs (~3×). Caveat: the SU
number includes rhs instantiation; the order is what matters.

## Runtime split, `ws(site)` application

Flat profile, 300k sites, `x + y + z` under the 8-rule set (rhs is a
bare `segment(s)` — the result *is* the materialized term, so this is
the materialization-heavy case):

| phase | share | notes |
|---|---|---|
| `_apply_rhs` / `_rhs_eval` | ~64% | `add_worker` + `Add` ctor + `hashcons` ≈ all of it |
| matching (`next_match!`/`step!`, `_step_ac!`) | ~17% | AC enumeration machinery |
| `reset!` + frame pools + `_init_root!` | ~8% | per-candidate engine reuse cost |
| `lookup!` (`BucketIndex`) | ~6% | bucket + arity filter |
| BSImpl `getproperty` | ~4% | SU's dynamic field dispatch |

Inside materialization: `NamedTuple`/`merge` ≈ 19% of the site (the
`Add(coeff, dict; type, shape)` kwcall), `hashcons`/`WeakCacheSets`
≈ 20%, `isequal_*` ≈ 10%. **The residual is SU term construction, not
MatchMaker** — producing canonical `BasicSymbolic`s is the floor.

## Materialization reduction (perf/seg-args)

`Bindings.seq` stores `ArgsT{SymReal}` (captured arg terms, head-neutral)
instead of subject-IR indices:

- `_rhs_eval` splices `b.seq[vid]` directly when `seg_op === newop` —
  the segment term is never built. A/B on `segment(s) + 2*slot(t)`:
  `_rhs_eval` 2.27 → **1.61 μs** (−30%), site 2.80 → **2.09 μs** (−25%).
- Singleton `+`/`*` capture fast path in `_seg_value`: ~600 ns → **1.1 ns**.
- `segval` per-match memo (`_bound_value`, cleared on `_unwind!`): an
  rhs referencing `s` twice materializes once — `f(s,s)` eval = 205 ns,
  site identical to single-ref (1.25 vs 1.28 μs). `BoundMatch` reads
  memoize into the snapshot too.

## Remaining overhead (ranked)

1. **SU term construction** — `add_worker`/`mul_worker`/`Term` ctor/
   `hashcons` is ~60% of a materializing site; it's SU's canonicalization
   floor (task-local worker buffers, `NamedTuple` kwcalls, WeakCacheSets
   `isequal` checks). Reducing it means fewer/simpler constructed terms,
   not faster code around it — e.g. reusing interned subtrees more
   aggressively (done: `updates` keeps `ir[i]` for ground subtrees).
2. **Matching + reset ~25%** — the Phase-2 `DiscrimNet` shares frontier
   work across rules and replaces per-candidate `reset!`/`next_match!`
   cycling; also the structural fix for the fixpoint loss (dirty sets
   instead of full re-walks).
3. **Traversal bookkeeping** — native `rewrite` carries IR sweep costs
   `Postwalk` doesn't; `net_cache` per-node apply memos (§4) target it.
4. **Scratch reuse** — `out`/`newargs` vectors per eval (~50–100 ns);
   could pool in `RuleWorkspace`.
5. **SU reflection** — `getproperty`/`isa_variant`/`NamedTuple` overheads
   ~5–7%; inherent to SU internals.

## Lazy enumeration wins (stress/workload absolute numbers)

- `ac 6 slots first-match`: **2.0 μs** vs `matchall` 175 μs — laziness
  pays when one match suffices.
- 177k-result `eachmatch` (deep AC 3-segs): **28.1 ms ≈ 160 ns/result**.
- `ac missing literal fail-fast`: **1.0 μs** — candidacy prunes early.
- Batch: 6 pats × 384 subjects first-match in 3.1 ms (~8 μs/subject).
- `eachmatch` vs `matchall` allocs: 12.4 vs 15.3 KiB per 6 results —
  the zero-materialization path.

## `_symtype_ok` memo-vs-enumerate (§5.5b) — decided: no memo

`Dict{Tuple{Any,Any},Bool}` memo on the `@nospecialize` fast-path
wrapper measured slower than plain enumeration (102.2 ms vs 69.7 ms
for 8 pairs × 1e5 calls) and allocates more — the memo *key tuple*
costs more than the `===`-fast-path checks it replaces. The common case
(`Any`/`Number`/`Real`, `cand === want`) never reaches `<:` anyway.

## `@code_typed`/JET

`test/jet.jl` runs `report_call` over the API paths — marker
constructors, compiler, `match`/`matchall`, `instantiate`, engine
internals, and the full `rules.jl` surface (`mmrule`, `_rhs_eval`,
`BucketIndex`, `RuleWorkspace`, `rewrite`, `fixpoint_rewrite`) —
30 checks, currently clean.
