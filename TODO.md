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

- **Abstract the FORWARD/BACKTRACK skeleton.** `_step_call!`,
  `_step_seq!`, `_step_comm!` share the same state machine (init →
  forward-dispatch → seek-deepest-resumable → fail-at-0). Could be
  unified behind a per-position interface (`first_alt!`/`resume!`
  returning a status, position kind dispatch inside the loop) — the
  seek would just call `resume!` on each position uniformly.

- **`_step_*` helpers take every frame field as a separate argument.**
  Getting unwieldy — consider passing the `MatchFrame` as-is and
  destructuring inside the helper instead.

- **Ambiguous segment materialization across binder heads.** When a
  segment var is captured under one head and rechecked under another —
  e.g. `h(h(segment(x)), g(segment(x)))` vs `h(h(x, y), g(y, x))` — the
  binding materializes through the *first* binder's operation
  (`x ↦ h(x, y)`). `x ↦ g(x, y)` is an equivalently valid answer
  (the multiset recheck passed under both), and which head wins is an
  implementation detail of dispatch order — there is no user-facing
  guarantee which materialization is produced. Triage: document
  first-binder-wins, pick a canonical materialization, or surface the
  ambiguity to the caller.

- **Bound segment capture length?** Segment-scale buffers grow with
  subject arity: per-frame `used`/`seg_sel`/`seg_pool`/`cands`, the
  captured run `binds.seq[vid]`, `segbuf` (sequence predicates), the
  `_seg_try!` recheck mask, and `_seg_value`'s materialized `args`.
  Investigate a practical bound on how long a segment can usefully be
  (spec-side cap or engine-level limit like `maxsteps`) — it would
  bound these allocations and could keep `SmallV` storage
  stack-resident.

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

- **Optional sequence wildcards (`oa__`/`oa___`, leftover-absorbing
  `oa_` under A/AC).** Capture-wise a `min = 0` segment; the deltas are
  a spec `default`, a bind-default-on-empty branch, and
  materialization. Per-case work/perf breakdown:
  `docs/optional-segments.md`.

- **Coefficient/numeric splitting under `+`/`*` (SymPy-style).**
  SymPy's `match` decomposes numeric args: `(x - p)^2` vs `(x - 2)^2`
  → `{p: 2}` because `Mul(-1, p)` matches `Const(-2)` as `(-1)·2`;
  `p*x` vs `x` → `{p: 1}` (implicit coefficient); `2*p` vs `6` →
  `{p: 3}` (divisor split); `3x + p` vs `4x + 5` → `{p: x + 5}`
  (additive term split). Our subject args are atomic IR nodes. The
  sign-split slice alone wants an alternate subject-arg view under `*`
  (`Const(-2)` → `[-1, 2]`); divisor splits want partial-arg
  consumption with synthesized `Const` leftovers (bound via `extra`,
  not subject nodes); additive splits under `+` are a second
  decomposition dimension. Worth supporting at least the
  sign/divisor-literal slice — it's what makes `x - p` match `x - 2`.
  Skipped cases live in `test/sympy/match.jl`.

- **First/all occurrences of a pattern *within* a subject (§4's
  `eachmatch_at` seam).** "Where does `p` match inside `s`?" is the
  common rewriter query — today it means descending the subject and
  calling `match` at every node, paying full `MatchEngine` setup
  (bindings, frame stack, pool) per attempt. A dedicated design should
  beat naive descend-and-match on several fronts:

  - **Compiled prefilter.** The pattern root's head, arity bounds, and
    literal structure are known at compile time — most subject nodes
    can be rejected by a cheap discriminator without entering the
    engine at all.
  - **DAG dedup.** Subject IR is interned — each root attempt starts
    from empty bindings, so `(root_plan, subj_node) -> results` is
    memoizable per node. Naive descent pays per *occurrence*; the
    specialized version pays per *node*. (Same key shape as the
    memoization item above, but safe by construction at root
    attempts — no live bindings to key on.)
  - **Engine reuse.** One `MatchEngine` (or its buffers) reset per
    candidate node instead of allocating fresh per attempt.
  - **Bottom-up marking (further out).** Propagating "which pattern
    nodes can this subject node match" up the subject DAG —
    tree-automaton style — would make occurrence search O(|subj
    nodes|) instead of per-node engine runs.

  Semantics to fix first: traversal order for "first" (preorder DFS?
  leftmost-outermost like rewriting systems?), whether nested matches
  inside a matched subtree are reported, and result shape (nodes vs
  substitution maps).

- **`matchall` materialize is the throughput ceiling.** Since
  `perf/segment-path` (fa91b5b — suffix-max bounds force the last
  segment's capture, pools are predicate-prefiltered, `_next_combo!`
  is an odometer) the engine costs ~0.2 μs/result on
  `seg+seg 14-arg` while `matchall` runs ~3 μs/result — the gap is
  almost entirely per-result `MarkersMap` + `_seg_value` →
  `add_worker`/hashconsing. `eachmatch`/`SubstitutionView` is the
  zero-alloc path; document it as the high-throughput API and
  consider a `matchall` variant returning interned bindings or
  views.

## Tests

- Port MatchPy's one_to_one tests into `test/matchpy/` as oracles.
  (`test/fuzz/` exists — the naive oracle in `test/oracle.jl` +
  `crosscheck.jl`/`generator.jl` cross-validate `matchall` result
  multisets on fixed and generated cases.)
