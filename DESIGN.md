# MatchMaker.jl — Design Document

Status: **draft, awaiting approval.** No implementation may begin before this
document is approved. Any change to the implementation that diverges from this
document must be reflected here first.

MatchMaker.jl is a MatchPy-inspired pattern matching library built on
SymbolicUtils.jl v4 (`BasicSymbolic{SymReal}` + `IRStructure`). Patterns are
ordinary symbolic expressions; pattern variables are `Sym`s carrying metadata
tags. The matcher is an explicitly iterative backtracking engine that enumerates
all matches, ordered deterministically.

---

## 1. Background: the SymbolicUtils v4 model

Facts about SymbolicUtils v4.53 (`BasicSymbolic{T}`, `T = SymReal` initially)
that drive every design decision below:

1. **ADT.** `BasicSymbolic{T}` is a `Moshi.@data` ADT with variants `Const`,
   `Sym`, `Term`, `AddMul`, `Div`, `ArrayOp`, `ArrayMaker`. Variant dispatch via
   `@match` + manual union splitting is the codebase's type-stability idiom; we
   adopt it verbatim.

2. **Canonicalization.** Under `SymReal`, `+` and `*` never appear as `Term`s:
   they produce `AddMul` (a coefficient plus `Dict{BasicSymbolic, Number}`).
   `/` produces `Div`; `^` produces `Term`. `arguments(::AddMul)` reconstructs
   the canonical flattened argument sequence: for `ADD`, the nonzero scalar
   coefficient becomes a leading `Const` and each dict pair `k => v` becomes
   `Mul{T}(v, dict(k))`; for `MUL`, each pair `k => v` becomes `k ^ v`. The
   reconstructed argument vector is cached on the node (`ArgumentCache`).

   **Consequence:** matching over the `iscall`/`operation`/`arguments` semantic
   interface (never the raw dict) gives us a flattened, canonically ordered
   argument multiset for `+`/`*` for free. `AddMul` *is* the AC node.

   **Consequence (pattern normalization caveat):** patterns are normalized by
   the algebra at construction time. `slot(:x) * slot(:x)` is `x_slot^2`, and
   `slot(:x) + slot(:x)` is `2 * x_slot`. A "repeated slot" inside the same
   `+`/`*` collapses before the matcher ever sees it. This matches Mathematica
   semantics (`x_ * x_` ≡ `x_^2`) and is *correct*, but it is non-obvious and
   must be documented in user docs. Users who need literal tree matching of
   un-normalized products need a `TreeReal` pattern (out of scope initially).

3. **Metadata.** `metadata` is `Base.ImmutableDict{DataType, Any}`, keyed by
   context *types*. `setmetadata`/`getmetadata`/`hasmetadata` are public.
   Crucially, `Base.hash` and `Base.isequal` on `BasicSymbolic` ignore metadata
   by default (metadata-aware comparison only under task-local `COMPARE_FULL`,
   used by the hash-cons table). Therefore:

   - A slot-tagged `Sym` is `isequal` to its untagged counterpart and hashes
     identically. Pattern variables behave exactly like ordinary variables in
     every algebraic operation — patterns can be built with ordinary `+`, `*`,
     `term`, function calls.
   - `hashcons` distinguishes tagged/untagged (via `hash2`), so both can
     coexist in an `IRStructure`.
   - `substitute(expr, Dict(slot_sym => v))` will also substitute plain `x`,
     since lookup is `isequal`-based. This is *desired* (the slot names a
     variable) but is a documented sharp edge: two slots that differ only in
     predicate are `isequal` to each other.

4. **IRStructure.** `IRStructure{T}` stores a DAG: `symbols::Vector{BasicSymbolic{T}}`
   indexed by `Int32`, `definition::IdDict` (`===` identity), `weak_definitions::Dict`
   (`isequal` classes → node lists), `dependency_graph::OrderedDiGraph{Int32}`
   with `outneighbors == [operation?, arguments...]` ordering, plus reusable
   `cached_mask`/`cached_idxs` scratch buffers and `get_reachability!` for
   topological-order sub-DAG traversal. `populate_ir!` interns expression
   DAGs. This gives the matcher:

   - O(1)-ish node-identity comparisons for non-linear re-checks.
   - A flat index space for memoization keys `(pattern_idx, subject_idx)`.
   - Iterative traversal (no recursion → no stack overflow on huge subjects).
   - Amortization: a subject's IR is built once and reused across patterns
     (the many-to-one story in §8).

5. **Existing matcher.** `src/matchers.jl` compiles `~x`/`~~x`/`~!x` patterns
   into nested CPS closures. It is dynamically typed throughout, handles AC
   only via argument permutation with a backtrack budget, and is the reference
   *behavioral* baseline (tests, not code reuse). The `^`/`sqrt`/`exp`/`1/x`
   "frankenstein" special cases in `pow_term_matcher`/`sqrt_matcher`/`exp_matcher`
   are **rewrite-domain normalizations, not matching semantics** — they are
   out of scope for the core matcher (see §10, Out of scope).

---

## 2. Terminology

| Term | Meaning |
|---|---|
| *pattern* | a `BasicSymbolic{SymReal}` containing zero or more pattern variables |
| *subject* | a `BasicSymbolic{SymReal}` matched against a pattern |
| *slot* | a pattern variable matching exactly one argument/term (`~x` analogue) |
| *optional slot* | a slot that may instead bind a declared default (`~!x` analogue) |
| *segment* | a pattern variable matching a contiguous run (A/free ops) or a sub-multiset (AC ops) of an argument list (`~~x` analogue; `min`/`max` length bounds replace MatchPy's star/plus distinction) |
| *ground* | a pattern (sub)node containing no pattern variables |
| *linear* | a pattern in which every pattern variable occurs at most once |
| *substitution* | a complete assignment slot→subject-term, segment→term-sequence |
| *AC node* | a call whose operation is associative+commutative for the relevant symtype |

---

## 3. Pattern variable representation

### 3.1 Metadata schema

A single metadata context key distinguishes pattern variables; the *value type*
carries the kind and constraints.

```julia
# Context key type — used as the ImmutableDict key.
struct PatternVariableCtx end   # getmetadata(sym, PatternVariableCtx)

# Metadata values. All fields concrete.
struct SlotInfo{P, D}
    predicate::P      # ::BasicSymbolic{SymReal} -> Bool; checked after symtype/shape
    default::D        # D === Nothing for required slots; otherwise the default value
end

struct SegmentInfo{P, SP}
    predicate::P              # elementwise ::BasicSymbolic{SymReal} -> Bool
    sequence_predicate::SP    # SP === Nothing, or ::AbstractVector -> Bool on the capture
    min::Int                  # minimum capture length (0 = MatchPy star, 1 = plus)
    max::Int                  # maximum capture length (typemax(Int) = unbounded)
end
```

**Decision:** one context key (`PatternVariableCtx`), kind discriminated by the
value's type (`SlotInfo` vs `SegmentInfo`). Rationale: a `Sym` cannot be both;
a single-key lookup with a two-way `isa` split is the smallest union we can
give the compiler and keeps `is_pattern_var` a single dict probe.

`SlotInfo.default`: stored unwrapped (e.g. `0`, or a `BasicSymbolic`); wrapped
to `Const{SymReal}` at binding time if not already symbolic. `default === nothing`
means "required slot". A `nothing` *value* as a deliberate default is
meaningless and rejected at construction.

**Invariants enforced at construction (`slot`/`segment`):**
- `min >= 0`, `max >= min`, `max >= 1` for segments.
- The base `Sym` is scalar-shaped (`ShapeVecT()`); non-scalar pattern variables
  are rejected for now (array-shape matching is future work).
- `predicate`/`sequence_predicate` are callable.

### 3.2 Constructors

```julia
slot(name::Symbol; type::Type = Number, shape = ShapeVecT(),
     predicate = Returns(true), default = nothing) -> Sym{SymReal}
slot(s::BasicSymbolic{SymReal}; predicate = ..., default = ...)  # retag an existing sym
segment(name::Symbol; type::Type = Number, predicate = Returns(true),
        sequence_predicate = nothing, min::Int = 0, max::Int = typemax(Int)) -> Sym{SymReal}
segment(s::BasicSymbolic{SymReal}; ...)                          # retag existing sym
optional(name_or_sym; default, ...)                              # slot(...; default)
is_pattern_var(x) -> Bool
pattern_var_info(x) -> Union{SlotInfo, SegmentInfo, Nothing}
```

Convenience macros bind tagged syms in local scope:

```julia
@slots x y::Real          # ≡ x = slot(:x); y = slot(:y; type = Real)
@segments xs ys::Real     # ≡ xs = segment(:xs); ys = segment(:ys; type = Real)
```

Macro grammar is deliberately minimal: `name` and `name::Type` only. Anything
richer (predicates, bounds, defaults) goes through the functions — macros that
half-support the feature set are worse than none.

### 3.3 Operation traits

Whether a call's arguments may be reordered/flattened is a property of the
*operation object* conditioned on the *result symtype* (`*` is AC for `Number`,
A-only for `AbstractMatrix`).

```julia
is_associative(f, ::Type{ST})::Bool   # default false
is_commutative(f, ::Type{ST})::Bool   # default false
identity_element(f, ::Type{ST})       # default nothing
```

Defaults: `+` and `*` are AC with identity (`0`/`1`) for `ST <: Number`.
Users extend by adding methods for their functions. For *symbolic* heads
(`f(x)` where `f` is itself a `Sym`), the trait lookup falls back to reading
an `OperationTraitsCtx` metadata entry on the head sym — this is the only
channel available for commutative symbolic functions and is exercised by tests.

**Decision:** traits take the result symtype, not the argument symtypes.
Rationale: it is a lookup, not a computation; the common distinctions
(`Number` vs `AbstractMatrix`) are result-visible. If a real case needs arg
types we can widen the signature in a minor revision — the call site is
internal.

---

## 4. Match semantics

1. **Whole-expression match.** `match(p, s)` succeeds iff the entire subject
   matches the entire pattern. Subterm rewriting is a rewriter's job, not the
   matcher's (a future `eachmatch_at` traversal helper is a candidate
   convenience, not core).

2. **Bindings.** A substitution maps each pattern variable to the subject
   node(s) it captured. Internally bindings are *subject IR node indices*
   (`Int32` for slots, `SmallV{Int32}` for segments); expr materialization
   happens only when a `Substitution` is produced.

3. **Slots** match exactly one term, subject to: symtype constraint
   (`symtype(candidate) <: symtype(slot)` — always checked, it is free static
   information), shape constraint (concrete `ShapeVecT` must equal the
   candidate's shape; `Unknown` is unconstrained), then `predicate`.

4. **Non-linear patterns.** A repeated slot sym is the same node in the
   pattern IR (hashconsed). Second and later occurrences check `isequal`
   against the bound value (`===` fast path first — subject subterms are
   interned, so structural equality usually resolves in O(1)).

5. **Segments** under a free or associative head capture a *contiguous run*;
   under a commutative or AC head they capture a *sub-multiset* materialized in
   the subject's canonical argument order. `min`/`max` bounds apply; element
   `predicate` applies to each captured element, `sequence_predicate` to the
   whole capture. Compile-time error: a segment as a non-final-or-final arg of
   a commutative-but-not-associative head is rejected only if the head's arity
   is provably fixed — since generic `f` is variadic in this system, C-only +
   segment is allowed and means "unordered subset capture"; this is
   deterministic because captures are reported in canonical order.

6. **Identity coercion.** If the pattern node is an `f(...)` AC/A call and the
   subject is *not* an `f`-call, the subject is treated as a singleton argument
   multiset `[subject]` iff `identity_element(f, ST) !== nothing`. Example:
   `slot(:a) + segment(:rest)` matches subject `x` as `a ↦ x, rest ↦ ()`. This
   is the MatchPy/ Mathematica Flat+OneIdentity behavior and is what makes
   `+`-headed patterns work on non-`Add` subjects.

7. **Optional slots** enumerate two alternatives at an AC/A node: consume one
   remaining argument (a normal slot match) or bind `default`. Enumeration
   order: consume first, default second (MatchPy order; deterministic).

8. **Enumeration order.** Fully deterministic: subject arguments are consumed
   in `arguments()` order (already canonical for `AddMul`); AC assignments
   enumerate right-side candidates in increasing subject index; segment splits
   enumerate by increasing captured length, left segment first. The *set* of
   results is what tests assert; order stability is a secondary guarantee we
   keep because it makes tests and debugging sane.

9. **Constraints.** `match(p, s; constraints = [Constraint(...)])` where
   `Constraint{F}` pairs a callable `f(bound_values...)::Bool` with the tuple
   of pattern variables it reads. A constraint is evaluated as soon as all its
   variables are bound (early pruning), not just at yield — non-negotiable for
   AC performance and cheap to implement via a per-variable "remaining
   dependents" counter.

10. **Literal heads.** A pattern whose head is a slot sym (`f_ = slot(:f)`;
    `f_(x)`) matches the *operation* position: subject head must satisfy the
    slot constraints and binds it. This is Mathematica's `f_[x_]` and falls
    out of treating the operation as another pattern position — but only when
    `is_associative`/`is_commutative` on a slot resolves via the bound head
    sym's metadata. Supported, flag explicitly in tests.

11. **Metadata on subject nodes** is ignored by matching (except operation-trait
    lookup on symbolic heads). Pattern vars embedded in a *subject* are treated
    as ordinary syms (they are `isequal` to untagged syms anyway).

---

## 5. Architecture

### 5.1 Pipeline

```
pattern:BasicSymbolic{SymReal}
   │  compile_pattern ────────────────────────────────────┐
   ▼                                                      ▼
CompiledPattern{T}   +   subject → IRStructure{T}   →   MatchEngine
   (pattern IR,                 (subject DAG)             (iterative
    per-node plans,                                       frame machine)
    slot table, ground flags)                                  │
                                                               ▼
                                              eachmatch / matches / match
                                                               │
                                                               ▼
                                          Substitution{BasicSymbolic→Any}
```

### 5.2 `CompiledPattern{T}`

Built once per pattern; shareable across subjects (the many-to-one hook).

```julia
struct CompiledPattern{T}
    ir::IRStructure{T}                       # pattern DAG
    root::Int32                              # node index of whole pattern
    plans::Vector{NodePlan}                  # indexed by node idx — see ADT below
    slot_syms::Vector{BasicSymbolic{T}}      # slot_id -> the tagged Sym
    slot_of::Dict{BasicSymbolic{T}, Int32}   # sym -> slot_id (isequal-consistent)
    is_ground::BitVector                     # subtree contains no pattern vars
    nslots::Int                              # number of distinct variables
end
```

`NodePlan` is a `@data` ADT (the BSImpl idiom), one variant per node kind:

```julia
@data NodePlan begin
    Literal()                       # match iff isequal (consts, plain syms)
    Slot(slot_id::Int32)
    Segment(slot_id::Int32)         # only legal inside arg lists; validated
    Call(op, children::SmallV{Int32}, order)   # free head: positional children
    ACCall(op, fixed::SmallV{Int32}, varslots, segments, optionals, ...)
    ...
end
```

`is_ground` precomputed bottom-up: `is_ground[n] = no var in descendants`.
A ground pattern node matches a subject node iff `isequal` — the engine checks
the flag *before* pushing a frame, turning whole-subtree matches into one
comparison. This is the single most valuable compile-time fact (real patterns
are mostly ground).

Compile-time validations (loud errors, not silent mismatches):
- segment directly under a non-variadic-illegal position (see §4.5);
- pattern variable used where a node isn't a `Sym` (e.g. tagged `Term` — rejected);
- `min > arity bound` where provable.

### 5.3 Bindings and trail

```julia
struct Bindings{T}
    node::Vector{Int32}            # slot_id -> subject node (0 = unbound)
    seq::Vector{SmallV{Int32}}     # slot_id -> captured subject nodes (segments)
end
```

One concrete struct; no unions in the store. A `trail::Vector{Int32}` records
which slot ids were bound, in order; backtracking pops a mark and clears.
Rebinding (non-linear check) never touches the trail.

### 5.4 The engine

`MatchEngine{T}` is a **defunctionalized backtracking machine**. Each
in-progress node match is a *frame*: a suspended single-result enumerator with
mutable resumption state. Frames are the `@data` ADT `MatchFrame`:

```julia
@data mutable MatchFrame begin
    # f(p1..pn) vs f(s1..sn), fixed arity, ordered — nested child enumeration
    Seq(pat_node, subj_node, active_child, trail_mark, ...)
    # commutative-only: permutation enumerator driving an inner Seq
    Comm(...)
    # associative: contiguous split-point enumerator (compositions)
    Assoc(...)
    # AC: bipartite assignment enumerator + leftover distribution
    AC(...)
    # singleton leaf obligations (slot recheck, literal compare) are applied
    # inline by the parent and never get frames.
end
```

Engine state:

```julia
mutable struct MatchEngine{T}
    pat::CompiledPattern{T}
    subj::IRStructure{T}
    frames::Vector{MatchFrame}     # stack; top = deepest obligation
    binds::Bindings{T}
    trail::Vector{Int32}
    constraints::Vector{Constraint}
    pending::BitVector             # constraint-ready bookkeeping
    steps::Int                     # work meter; compare against budget
end
```

`advance!` protocol — every frame kind implements:

```julia
step!(eng::MatchEngine{T}, f::<FrameKind>)::FrameStatus
# FrameStatus ∈ {:produced (a child obligation or partial binding happened),
#                :matched  (this frame's node fully matched — pop it),
#                :failed   (no more alternatives — pop + unwind trail)}
```

The engine loop pops `:matched`, retries `:failed` parents, and yields when the
stack empties — a complete match is *the stack reaching empty*. `next_match!`
runs the loop to the next yield; `Base.iterate(engine)` wraps it, copying out a
`Substitution`. Because all state is explicit and heap-resident, iteration is
resumable for free and nothing ever recurses — this is the property that lets
the engine scale to huge subjects, and the reason `IRStructure` is load-bearing
rather than cosmetic.

**Rejected alternative:** CPS closures like the existing `matcher()`. Cleaner
for small terms but the AC machinery needs explicit resumable state anyway,
closures make the enumeration order hard to audit, and every continuation
captures heap state opaquely. The frame machine is uniformly inspectable
(`eng.frames` *is* the search state).

**Rejected alternative:** `Channel`/task-based lazy iteration. Task switches
per match are disproportionately expensive and defeat reuse of engine state;
we keep `matches` as a plain `iterate` wrapper over `next_match!`.

### 5.5 Per-kind matching algorithms

**(a) Literal / ground subtree** — `isequal(p_subtree, s_node)`; interned DAG
makes this near-O(1). Never pushes a frame.

**(b) Slot** — bound → `isequal` recheck; unbound → symtype+shape+predicate,
bind, trail-record, then run ready constraints.

**(c) `Seq` (free head)** — `operation` must agree (`===`/`isequal` for
function heads, `isequal`/slot-match for symbolic heads); fixed arity; children
matched positionally as nested enumeration (child `i+1` initialized under
child `i`'s fresh bindings; on child `i+1` exhaustion, advance child `i`).

**(d) `Comm`** — `arity(p) == arity(s)` required; enumerate permutations of
subject args in index order; each permutation is an inner `Seq`.

**(e) `Assoc`** — pattern arg list is a sequence of fixed elements and
segments; subject is a fixed-size arg list. Segments consume contiguous runs;
enumerate compositions of the subject length into (fixed=1 | segment=variable)
parts honoring min/max, shortest-capture-first. Non-segment positions are
positional `Seq` obligations.

**(f) `AC`** — the core algorithm (MatchPy §4; Eker 1995 lineage):

```
pattern args partition into FIXED (ground and non-var subpatterns),
                         SLOTS (incl. already-bound slots, treated as fixed-
                                by-lookup), OPTIONALS, SEGMENTS.
subject args = arguments(subject) (or [subject] via identity coercion).

Phase 1 — candidates: for each fixed pattern arg, compute the set of subject
   indices it can match (each submatch is itself a nested frame obligation).
   Sort fixed parts by ascending candidate count (most constrained first).
   Fail fast on any empty candidate set.

Phase 2 — assignment: enumerate matchings of (fixed ∪ slots) → subject args,
   all distinct (bipartite backtracking; slots get the same candidate filtering
   via their constraints). Each complete assignment binds its vars (trail).

Phase 3 — leftovers: distribute remaining subject args among segments
   (unordered subsets; capture order = canonical order) honoring min/max.
   With one segment this is O(1): it takes everything left. Optionals that did
   not consume bind their defaults.

Failure anywhere unwinds the trail to the frame's mark and advances the
innermost non-exhausted enumerator.
```

Complexity honesty (documented in user docs): general AC matching is
NP-complete (Benanav–Kapur–Narendran 1985); with *linear* patterns it is
polynomial. We do not special-case linearity in v1 — the enumeration order
and pruning get most of the win in practice; a dedicated linear fast path is a
recorded optimization (§9).

**(g) Optional** — at an AC/A node: two-branch choice (consume | default).
Outside such a node: compile-time error (a lone optional has no "absence" to
fall back on).

### 5.6 Substitution & instantiation

`Substitution{T}` materializes per yielded match:

```julia
Dict{BasicSymbolic{T}, Any}   # slot sym -> BasicSymbolic{T};
                              # segment sym -> Vector{BasicSymbolic{T}}
```

Keyed by the *tagged* slot sym; `isequal`-lookup means `d[plain_x]` works and
`substitute(expr, d)` does the right thing.

`instantiate(template, subst)` rebuilds an expression splicing segment
sequences under their parent op — needed because `substitute` alone can't
splice sequences. This is also what a future rule layer needs to build RHS.

Public API (stable surface):

```julia
compile_pattern(p)          -> CompiledPattern{SymReal}
match(pat_or_cp, s; constraints=()) -> Union{Substitution, Nothing}
matches(pat_or_cp, s; constraints=())  # iterator (lazy, resumable)
matchall(...) = collect(matches(...))
eachmatch(f, pat_or_cp, s)  # f(::SubstitutionView)::Bool; false = stop early
instantiate(template, subst)
```

`SubstitutionView` is a read-only view over live engine state — documented
contract: valid only until the next `eachmatch`/`iterate` step; `materialize`
for a persistent `Substitution`. `eachmatch` is the zero-allocation hot path
rewriters should use.

---

## 6. File layout

```
MatchMaker.jl/
  DESIGN.md                 # this document
  DEVELOPING.md             # codebase navigation + implicit contracts (phase 0)
  Project.toml
  src/
    MatchMaker.jl           # module, includes, exports
    patternvars.jl          # §3.1–3.2: metadata schema, constructors, macros
    traits.jl               # §3.3: operation traits
    compile.jl              # §5.2: CompiledPattern, NodePlan ADT, validation
    bindings.jl             # §5.3, §5.6: Bindings, trail, Substitution(+View)
    engine.jl               # §5.4: MatchEngine, advance loop, iterate
    matchers/
      primitives.jl         # literal/ground/slot leaf logic (no frames)
      seq.jl                # free-head Seq frame
      commutative.jl        # Comm frame
      associative.jl        # Assoc frame (+ free-head segments)
      ac.jl                 # AC frame: candidates, assignment, leftovers
    instantiate.jl          # §5.6: instantiate
    api.jl                  # §5.6: public entry points
  test/
    runtests.jl  unit/...  oracle.jl  fuzz.jl  golden/...
  benchmark/benchmarks.jl
```

## 7. Testing strategy

Every feature branch ships its tests in the same merge.

- **Unit**: per construct — construction/metadata roundtrip, trait table,
  compile plans, each frame kind's enumeration semantics (e.g. `Assoc` split
  enumeration on a free `f`, AC distribution counts).
- **Oracle cross-validation** (`test/oracle.jl`): a deliberately naive,
  obviously-correct matcher (~150 lines, recursion + `permutations`/
  `combinations`, no IR, no sharing, correctness over speed). Property:
  `sort(materialize.(collect(matches(p,s)))) == sort(oracle_all(p,s))` on
  generated (pattern, subject) pairs. The oracle defines the semantics; the
  engine must equal it on *sets* of substitutions.
- **Fuzz** (`test/fuzz.jl`): seeded random pattern/subject generator over
  `+`,`*`,`^`,`/`,`sin`,`cos`,`f` with slots/segments/optionals at controlled
  rates; bounded subject size; fixed seed committed so failures reproduce.
- **Golden** (`test/golden/`): examples transcribed from MatchPy's test suite
  and the literature (`sin²+cos²`, `∫xⁿ`-style, distributivity, sequence
  captures) + the *negative* corpus: patterns that must NOT match (arity,
  symtype, non-linear inequality).
- **Type stability**: `@inferred` on `compile_pattern`, `next_match!`,
  `instantiate`; a `test/qa` env with JET for the hot paths; Cthulhu
  spot-checks documented in DEVELOPING.md.
- **Benchmarks** (`benchmark/`): vs `SymbolicUtils.@rule/@acrule` on the
  rewrite-suite patterns; large-subject stress (deep `Add` chains — where the
  non-recursive engine is the point); PkgBenchmark-compatible `benchmarks.jl`.

## 8. Many-to-one outlook (deferred, but designed-for)

After the one-to-one engine stabilizes: compile *sets* of `CompiledPattern`s
into a discrimination-net-style shared automaton (Bachmair–Chen–Ramakrishnan;
Krebber's generalization). Integration points already in the design:

- `CompiledPattern` plans are indexed instructions — a net state is just a
  *set of* `(pattern, node)` pairs sharing one subject cursor.
- `IRStructure` on the subject amortizes across all patterns.
- AC nodes map to MatchPy's `CommutativeMatcher` net nodes; our `AC` frame
  machinery is reused per net node rather than rewritten.

Rough shape: `ManyToOneMatcher{T}` holding shared pattern IR, net states as
`Vector{StateId}`, transitions keyed by node features (variant, op identity,
arity, leaf hash, wildcard-any). Wildcard/slot transitions become wild edges;
AC frames suspend per net-state. This is its own design doc when scheduled —
this section exists only to keep today's choices compatible.

## 9. Performance & type stability

- All engine fields concrete; `MatchFrame` is the only union (ADT), dispatched
  by `@match` — the same union-splitting model as `BSImpl`.
- Predicates are inherently dynamic (user callables): extracted from metadata
  once at compile time into the `NodePlan`, called through a single
  `call_predicate(::Any, x)::Bool` typeasserted helper; `Returns(true)` is
  elided statically at compile so unconstrained slots never pay for it.
- No `Vector{Any}` in the search state; bindings store `Int32` node ids.
- Buffers reused across matches of one engine; `Substitution` materialization
  is the only per-match allocation (and `eachmatch` avoids it).
- `maxsteps` budget parameter guards pathological AC searches (the
  `COMM_BACKTRACK_BUDGET` analogue), counted in `eng.steps`.
- Deferred optimizations (recorded, not scheduled): `(p_idx, s_idx)`-keyed
  submatch memoization once bindings-versioning is designed; linear-pattern
  fast path (BKN's polynomial case); direct `AddMul`-dict matching to skip
  `Mul`-wrapper materialization.
- Verification: `@code_typed`/`@descend` on `next_match!`, each `step!`,
  `compile_pattern`, `instantiate`; JET in CI-adjacent testset.

## 10. Out of scope (explicit)

- `SafeReal`/`TreeReal` subjects (design admits them; tests don't require).
- The old matcher's `^`/`sqrt`/`exp`/`1/x` semantic special cases (belong to a
  normalization layer that can sit on top).
- Unification (two-sided), e-graph matching, order-sorted matching, idempotence
  theory, home-embedding.
- `ArrayOp`/`ArrayMaker`/`getindex`-indexed pattern semantics — matched
  verbatim as generic calls.
- A `@rule`-style rewrite DSL; `instantiate` + `eachmatch` are the primitives.
- Non-scalar pattern variables (array-shape slots).

## 11. Repository & process conventions

- Conventional Commits; small atomic commits; feature branches merged to
  `master`; large features (AC) split into sub-branches off the feature branch.
- DocStringExtensions docstrings on every public function and every
  non-trivial internal type; `$TYPEDSIGNATURES`, `$TYPEDEF`, `$TYPEDFIELDS`.
- Narrow argument annotations; concrete/small-union returns; dynamic-dispatch
  boundaries typeasserted and commented.
- `DEVELOPING.md`: module map, the engine invariants (frame protocol, trail
  contract, enumeration order), how to run the fuzz oracle and Cthulhu checks.
- **Design doc governance:** implementation changes that alter behavior,
  semantics, or architecture update this file in the same PR; reviewed code
  changes that diverge are doc bugs until fixed.
- Dependencies: `SymbolicUtils` (dev'd to the local checkout),
  `DocStringExtensions`, `Moshi`, `Graphs` (IR access), `ReadOnlyArrays`.
  Test: `Test`, `SafeTestsets`, `Aqua`, `JET`, `BenchmarkTools`,
  `Combinatorics` (oracle).

## 12. Implementation milestones (branches in order)

Each `feat/*` merges to `master` with unit + oracle + (where cheap) fuzz
coverage before the next starts.

0. `chore/repo-bootstrap` — Project, module stub, test harness, DEVELOPING.md,
   .gitignore, Aqua suite. *Tests: package loads, QA green.*
1. `feat/pattern-variables` — §3.1–3.2. *Tests: tagged sym equality/hashcons
   behavior, constructor validation, macro expansion.*
2. `feat/op-traits` — §3.3. *Tests: +/* AC for Number, A-not-C for matrices,
   symbolic-head metadata fallback, user extension.*
3. `feat/pattern-compiler` — §5.2. *Tests: plan shape per node kind, ground
   flags, slot table, validation errors.*
4. `feat/match-core` — engine + literal/slot/`Seq`; `match`, `matches`,
   `eachmatch`, `Substitution`(+View). *Tests: unit per leaf logic; oracle on
   linear patterns; fuzz (free-heads only).*
5. `feat/segments-free` — `Assoc` frame restricted to free heads + segments.
   *Tests: split enumeration, min/max, predicates; oracle.*
6. `feat/commutative` — `Comm` frame. *Tests vs permutation oracle.*
7. `feat/associative` — A heads w/ identity coercion. *Tests: `f` declared
   associative, contiguous splits, singleton subjects; oracle.*
8. `feat/ac` — sub-branches `ac/candidates+assignment` then `ac/segments`.
   *Tests: unit on candidate matrix & distribution; oracle fuzz incl.
   non-linear; MatchPy golden cases; singleton coercion.*
9. `feat/optional-slots` — §4.7/§5.5g. *Tests: defaults under +,*; both
   enumeration branches; compile error outside AC/A.*
10. `feat/constraints` — §4.9. *Tests: early-prune call-count instrumentation,
    correctness vs post-hoc filtering.*
11. `feat/instantiate` — §5.6 remainder. *Tests: splice correctness, end-to-end
    rewrite examples.*
12. `perf/hardening` — allocation audit, `@code_typed` notes committed,
    benchmark suite vs `@acrule`, budget parameter.
13. `docs/user-guide` — pattern syntax & semantics incl. the normalization
    caveat and complexity notes.
