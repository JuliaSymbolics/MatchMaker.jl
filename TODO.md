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
  in two places: sibling positions (shared *subject* nodes — a shared
  subexpr is one IR node, so e.g. `h(f(u), f(u))` vs `h(g(v), g(v))`
  puts `(f(u), g(v))` in both `kids[1]` and `kids[2]`) and across
  backtracks (a dropped `kids[pos]` is rebuilt fresh under the new
  binding context). With shared pattern nodes × shared subject nodes ×
  deep backtracking this is the worst-case combinatorial blowup for
  wide subjects — identical pairs recomputed exponentially many times.

  A naive `(p, s) -> Bool` cache is *unsafe*: a subtree containing
  `slot(a)` reads `binds[a]`, so its outcome depends on the live
  bindings (nonlinear rechecks, predicates, constraints). A sound key
  is `(p, s, bound-nodes-of-p's-free-vars)` — the set of `p`'s vars is
  known at compile time (plan traversal), and with the fixed `nvars`
  bound above, "bound node of each var" is a cheap `UInt128`-bitmasked
  vector to hash. Ground subtrees (`is_ground`) are already free of
  this — they're `Literal` plans resolved by one `isequal`.

  Implementation sketch: per-frame `Dict` on the engine keyed by the
  tuple above, populated on `FrameStatus` returns; check before
  `_new_frame`/`_leaf_obligation!`. Careful about *what* to cache —
  a subtree that bound vars must replay the same bindings, so cache
  either (a) failure only, or (b) full binding deltas (a `SmallV` of
  `(vid, node)` pairs) — (a) is the cheap sound variant.

- **`_step_*` helpers take every frame field as a separate argument.**
  Getting unwieldy — consider passing the `MatchFrame` as-is and
  destructuring inside the helper instead.

- **Segment positions as pseudo-frames?** The seek branch in
  `_assoc_backtrack` re-derives what a `MatchFrame.Segment` would
  carry — a `_seg_resume!` helper would unify the "resumable
  position" protocol without a real frame (the segment's state is
  parent-mediated: `arg_start`/`min_tail`/`navail` depend on sibling
  consumption, which only the parent tracks).

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
