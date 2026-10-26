# TODO

Open design/performance questions, roughly in the order they become
actionable. Milestone scoping lives in DESIGN.md §12.

## Engine

- **Bindings layout: SoA vs ADT vector.** Currently `Bindings` is
  struct-of-arrays (`node`/`seq`/`seg_op`/`extra`, one `Vector` each).
  Alternative: a single `Vector{BindingType}` where `BindingType` is a
  Moshi `@data` ADT with one variant per binding kind (node / segment /
  non-node value). Benchmark both once the AC machinery exists to give the
  workload meaning.

- **Bound the number of pattern markers.** If slots+segments are limited to
  `N` (e.g. 128), every "is var bound" check becomes a single `UInt128`
  bitmask test — `MatchEngine.var_constrs` all-bound checks become bitwise
  ANDs. If 128 is too strict, raise to 256/another power of two and use a
  static bitvector (e.g. `SmallCollections.jl` tuples of integers). A fixed
  bound lets the engine specialize on memory layout and cut allocations.
  Enforce at `compile_pattern` with a clear error.

- **Canonical `Add`/`Mul` reconstruction in `_seg_value`.** `+`/`*` heads
  go through `add_worker`/`mul_worker`; confirm empty-capture identity
  handling (`Const` vs workers' own zero-arg behaviour) once segments
  bind in milestone 5 (`feat/segments-free`).

- **Cache `_seg_value` materialization in `SubstitutionView`.** If segment
  values were cached, views could serve every lookup without allocating —
  explore whether `MarkersMap` materialization can then be skipped
  entirely for repeated `eachmatch`-style consumers.

- **`_identity_el` fallback may allocate / is not inferrable.** It returns
  `Any`; only called on segment materialization (cold).

- **Memoize `(pat_node, subj_node) -> outcome`?** Identical pairs recur
  across sibling positions (shared subject nodes) and across backtracks
  (fresh frames under new bindings) — with shared pattern nodes this is
  the worst-case combinatorial blowup for wide subjects. A sound key
  needs `(p, s)` plus the bound nodes of `p`'s free vars; the fixed
  `nvars` bound (above) makes a bound-node-vector key cheap. Ground
  subtrees are already free of this — they're `Literal` plans.

- **`step!` currently nests calls.** `step!(eng, kf)` inside
  `_step_call!` recurses one Julia frame per *pattern* depth — bounded
  by pattern size and independent of subject size/sharing, so not a
  scaling hazard for wide/shared subjects (the engine only indexes
  subject nodes). Still, pattern depth is unbounded and future
  `Assoc`/`AC` frames may want to queue several pending obligations —
  the alternative is a delegate-push protocol: `step!` returns
  `Union{MatchFrameT, FrameStatus.T}` (frame = push and step) plus
  `eng.last_pop` so a resumed parent knows whether its popped child
  produced or failed. Revisit if pattern depth or AC-phase structure
  demands it.

## Tests

- Port MatchPy's one_to_one tests into `test/matchpy/` as oracles.
- Add the generated fuzz suite (`test/fuzz/`) once Comm/Assoc/AC frames
  exist.
