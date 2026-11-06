# perf/hardening notes (§9, §12)

The suite lives at `benchmark/benchmarks.jl` in
AirspeedVelocity/PkgBenchmark format (`SUITE::BenchmarkGroup`) — run it
with `benchpkg`/AirspeedVelocity once set up, or
`PkgBenchmark.benchmarkpkg(".")`. Baselines: the naive oracle
(`test/oracle.jl`, §5.7's top-level seam) and `@acrule` for AC
first-match.

Indicative numbers from the initial hand-rolled run (best-of-5
`@elapsed`/`@allocated`):

## Engine vs naive oracle

| workload | engine | oracle |
|---|---|---|
| `g` 3 slots / 3 args (6 results) | 30.0 μs | 39.0 μs |
| `slot + segment` under `+` | 29.8 μs | 64.3 μs |
| `f` 2 segments / 3 args (8 results) | 66.5 μs | 92.7 μs |
| `f` 4 slots / 4 args AC (24 results) | 22.3 μs | 44.2 μs |

The oracle allocates `Any[]`/`Dict` per node and enumerates without the
AC candidate matrix — the engine's fail-fast candidacy shows in the
larger cases. `match` on the `slot + segment` pattern beats `@acrule`
rule-application (32.2 μs vs 40.7 μs) — different work (the rule also
substitutes) but the same order.

## `_symtype_ok` memo-vs-enumerate (§5.5b) — decided: no memo

`Dict{Tuple{Any,Any},Bool}` memo on top of the `@nospecialize` fast-path
wrapper measured slower than the plain enumeration (102.2 ms vs 69.7 ms
for 8 pairs × 1e5 calls) and allocates more — the memo *key tuple* costs
more than the `===`-fast-path checks it replaces. The common case
(`Any`/`Number`/`Real`, `cand === want`) never reaches `<:` anyway. The
wrapper seam stays; the memo is rejected by measurement.

## `eachmatch` zero-materialization path

`eachmatch(v -> true, ...)` over 6 results: 12.8 KB vs `matchall`'s
15.9 KB — the savings is ~500 B per produced `MarkersMap`. Per-match
allocation is `SubstitutionView` construction + engine state only, as
designed (§5.6): `matchall`/`matches` pay `materialize` per result.

## `@code_typed`/JET

`test/jet.jl` runs `@test_opt` over the API paths that exercise
`next_match!`, each `step!` frame, `compile_pattern`, `instantiate` and
`materialize` — currently clean (18 tests). The `@nospecialize` +
`FunctionWrapper` discipline holds: engine hot paths are monomorphic
modulo the `MatchFrame` union split at `step!` dispatch.
