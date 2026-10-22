# MatchMaker.jl — Design Document

Status: **draft, awaiting approval.** No implementation may begin before this
document is approved. Any change to the implementation that diverges from this
document must be reflected here first.

MatchMaker.jl is a MatchPy-inspired pattern matching library built on
SymbolicUtils.jl v4 (`BasicSymbolic{SymReal}` + `IRStructure`). Patterns are
ordinary symbolic expressions; pattern variables are `Sym`s carrying metadata
tags. The matcher is an explicitly iterative backtracking engine that enumerates
all matches, ordered deterministically.

Algorithmic ideas adapted from MatchPy and the term-matching literature are
cited inline as `[Rx]`; the full citation list is in §13, and the citation
policy for source code is in §11.

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
   interface (never the raw dict) gives us a flattened argument multiset for
   `+`/`*` for free. `AddMul` *is* the AC node.

   **Ordering caveat (order-dependent behavior):** `arguments(::AddMul)`
   iterates the underlying `Dict`, so the argument order of `+`/`*` expressions
   is **hash-order-dependent**, not canonically sorted. `sorted_arguments`
   provides a deterministic `<ₑ`-sorted view (itself a `@cache`d function, so
   amortized O(1) per node). Any place where observable behavior depends on
   argument order — enumeration order, segment capture order, result order of
   `matches` — uses `sorted_arguments` where a canonical order is required, and
   is otherwise explicitly marked *order-dependent*. It is acceptable for
   results or performance to vary with this order; it is not acceptable for
   such dependence to be undocumented.

   **Consequence (pattern normalization caveat):** patterns are normalized by
   the algebra at construction time. `slot(x) * slot(x)` is `slot(x)^2`, and
   `slot(x) + slot(x)` is `2 * slot(x)`. A "repeated slot" inside the same
   `+`/`*` collapses before the matcher ever sees it. This matches Mathematica
   semantics (`x_ * x_` ≡ `x_^2`) and is *correct*, but it is non-obvious and
   must be documented in user docs. Users who need literal tree matching of
   un-normalized products need a `TreeReal` pattern (out of scope initially).

3. **Metadata.** `metadata` is `Base.ImmutableDict{DataType, Any}`, keyed by
   context *types*. `setmetadata`/`getmetadata`/`hasmetadata` are public.
   `Base.hash`/`Base.isequal` ignore metadata by default (metadata-aware
   comparison only under task-local `COMPARE_FULL`, used by the hash-cons
   table). We do *not* encode pattern variables in metadata (§3.4) — but the
   channel is still load-bearing in one place: operation traits on *symbolic*
   heads are read from an `OperationTraitsCtx` entry on the head `Sym` (§3.5),
   since a `Sym` has no marker term to hang data on.

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
   into nested CPS (continuation-passing style) closures — each matcher is a
   function `(subject, bindings, success)` where `success` is a callback
   invoked once per candidate match. It is dynamically typed throughout,
   handles AC only via argument permutation with a backtrack budget, and has
   **known behavioral sharp edges: its AC handling can produce incorrect
   results. It is not a behavioral oracle** — our oracle is the naive reference
   matcher we write ourselves (§7). Its tests are useful as a source of cases,
   not of expected values. The `^`/`sqrt`/`exp`/`1/x` "frankenstein" special
   cases in `pow_term_matcher`/`sqrt_matcher`/`exp_matcher` are
   **rewrite-domain normalizations, not matching semantics** — they are
   out of scope for the core matcher (see §10, Out of scope).

---

## 2. Terminology

| Term | Meaning |
|---|---|
| *pattern* | a `BasicSymbolic{SymReal}` containing zero or more pattern variables |
| *subject* | a `BasicSymbolic{SymReal}` matched against a pattern |
| *marker term* | a `Term` whose operation is the marker function `slot`, `segment`, or `optional` — declares a pattern variable |
| *variable* | the inner `Sym` of a marker term; all its occurrences in the pattern refer to the same variable |
| *slot* | a variable matching exactly one argument/term (`~x` analogue; MatchPy `Wildcard.dot`/`Wildcard.symbol`) |
| *optional slot* | a slot occurrence that may instead bind a declared default (`~!x` analogue; MatchPy `Optional`/`Wildcard.optional`) |
| *segment* | a variable matching a contiguous run (A/free ops) or a sub-multiset (C/AC ops) of an argument list (`~~x` analogue; MatchPy `Wildcard.plus`/`Wildcard.star`; our `min`/`max` bounds generalize `Wildcard.min_count`/`fixed_count`) |
| *VarSpec* | per-variable spec ADT (`Slot`/`Segment` variants) owned by the `Matcher` |
| *ground* | a pattern (sub)node containing no variables |
| *linear* | a pattern in which every variable occurs at most once |
| *substitution* | a complete assignment slot→subject-term, segment→`f(captured…)` |
| *AC node* | a call whose operation is associative+commutative for the relevant symtype |
| *CPS* | continuation-passing style: matchers as `(subject, bindings, success)->…` closures invoking `success` once per match — the `matchers.jl` architecture, rejected here (§5.4) |
| *order-dependent* | behavior that may vary with `Dict` hash order of `AddMul` args — permitted, always marked (§1.2) |

---

## 3. Pattern variable representation

### 3.1 Marker terms

Pattern variables are ordinary `Term`s headed by marker functions:

- `slot(x)` — matches exactly one term/argument.
- `segment(x)` — matches a contiguous run (free/associative heads) or a
  sub-multiset (commutative/AC heads) of an argument list.
- `optional(x)` — a slot occurrence that may instead bind the variable's
  declared `default` (per-occurrence marker; the default *value* lives in the
  `VarSpec`, not in the tree).

`slot`, `segment`, `optional` are bare generic functions (`function slot
end`): a marker call produces a `Term` whose `operation` is the function
itself. `promote_symtype`/`promote_shape` on the marker functions return the
inner arg's type/shape, so marker terms carry the inner `Sym`'s symtype and
shape for free (`term(m, x)` needs no kwargs). They take **exactly one
argument — the inner `Sym`** — and nothing else:

```julia
slot(x) isa BasicSymbolic{SymReal}        # a Term
operation(slot(x)) === slot               # object-identity detection — O(1),
                                          # no metadata lookup, no trait call
```

Because a marker term is a real expression node, pattern-variable declarations
are *visible in the tree*, require no metadata plumbing, and can be built with
plain symbolic arithmetic (`slot(x) + y`, `sin(segment(xs))`).

**Variable identity.** A *variable* is the inner `Sym` `x` — a plain symbolic
variable created by `@syms`/`Sym`, whose own `symtype` is the type constraint.
`unwrap_varspec(node)` strips a marker term to its inner sym. All marker-term
occurrences of `x` refer to the same variable. **A variable must appear only
inside marker terms: a bare occurrence of a marked sym anywhere in the pattern
is a compile error** — `sin(slot(x)) + x` is rejected, not silently non-linear.
Likewise a variable may not appear in both `slot`/`optional` and `segment`
markers (kind conflict → error). Both rules are cheap compile-time checks over
the pattern IR and remove an entire class of silent misreads.

**Spec data lives entirely outside the expression.** The compiled matcher is
independent of predicates: they affect which matches are accepted, never how
the search is structured — so they belong in a swappable table, not baked into
the expression. `compile_pattern(expr; vars::AbstractDict)` maps inner syms to
`VarSpec` variant objects; unlisted vars get unconstrained defaults
(`Slot(nothing, nothing)` / `Segment(nothing, nothing, 0, typemax(Int))`).
Specs keyed on syms that are not pattern variables are a compile error
(typo-catcher). Per-occurrence optionalness is the *only* spec fact that lives
in the tree (the `optional` marker itself); a var with any `optional`
occurrence must have `default !== nothing`.

```julia
@data VarSpec begin                  # Moshi ADT — concrete tagged type
    struct Slot
        predicate::Union{Nothing, PredT}
        default::Union{Nothing, BasicSymbolic{SymReal}}  # nothing = required
    end
    struct Segment
        predicate::Union{Nothing, PredT}
        sequence_predicate::Union{Nothing, SeqPredT}
        min::Int
        max::Int
    end
end
```

`VarSpec` is deliberately non-parametric: `PredT`/`SeqPredT` are already
`SymReal`-fixed, so a vartype parameter would only decorate `default` — and
it would be uninferrable at `default === nothing` (caught by Aqua's
unbound-args check). If `SafeReal`/`TreeReal` support lands, parameterize all
fields together or none.

Kind is the variant tag — no flag, no dead fields, and legality of each
spec field is structural (`default` literally cannot exist on a `Segment`).
The `vars` map binds inner syms to `VarSpec` variants (plain or via the
`slotspec`/`segmentspec` helper ctors that fix `T = SymReal`); validation is
variant↔marker agreement — a `VarSpec.Segment` mapped onto a `slot`-marked
var (or vice versa) is a compile error. Because `VarSpec` is a Moshi ADT —
one concrete type with a variant tag, the `BSImpl` idiom — `Vector{VarSpec{T}}`
is a plain concrete array: spec reads destructure via `@match` as a single
tag branch, identical in cost to the `kind` flag this replaces. (An earlier
draft priced this as a Julia `Union{SlotSpec, SegmentSpec}` in the array,
which would pay union splitting per read — that was the wrong comparison;
the ADT form has neither cost.)

### 3.2 Stored callables: `FunctionWrappers`

Predicates and constraint functions are user callables with *known signatures
but unknown types*. Storing them raw either bakes each concrete function type
into our structs (overspecialization → recompilation per pattern) or erases to
`Any` (dynamic dispatch per call + no inference). Instead:

```julia
const PredT    = FunctionWrapper{Bool, Tuple{BasicSymbolic{SymReal}}}
const SeqPredT = FunctionWrapper{Bool, Tuple{Vector{BasicSymbolic{SymReal}}}}
const ConstrT  = FunctionWrapper{Bool, Tuple{Vector{BasicSymbolic{SymReal}}}}
```

`Union{Nothing, FunctionWrapper}` fields stay small-union; a `nothing` field
is checked *before* calling so unconstrained vars pay zero predicate cost.
(FunctionWrappers.jl — MIT.)

### 3.3 Constructors and macros

```julia
slot(x)              # marker term wrapping Sym x
segment(x)
optional(x)
unwrap_varspec(x) -> BasicSymbolic             # strip marker term to inner sym
is_marker_term(x) -> Bool                      # is x a marker term?
is_marker_op(op) -> Bool
varsym(x) -> Sym                               # inner sym of a marker term
slotspec(predicate = nothing; default = nothing) -> VarSpec.Slot
segmentspec(predicate = nothing, sequence_predicate = nothing;
            min = 0, max = typemax(Int)) -> VarSpec.Segment
```

`x` may be a `Symbol` (a fresh `Sym` is created; `slot(:x; type, shape)`
keywords apply) or an existing `Sym`. Validation at construction: the argument
must be a `Sym` (`slot(f(x))`, `slot(slot(x))` → error). Wrapping an existing
`Sym` needs no macro — it is just `slot(x)`.

`is_marker_term`/`unwrap_varspec`/`varsym` `@match` the `Term` variant
directly (not `iscall`/`operation`, which dispatch over every symbolic
variant — the marker check only ever lives on a `Term`).

Macros create syms and wrap them — sharing `SymbolicUtils.@syms` parsing
(`parse_variable` + `sym_from_parse_result`), so `name`, `name::Type`,
`name[shape]`, and `f(args)` function-form arguments all work:

```julia
@slots x y::Real      # x = slot(Sym(:x)); y = slot(Sym(:y; type = Real))
@slots f(y)           # f = slot(FnType sym) — a head-slot variable
@segments xs ys::Real # xs = segment(Sym(:xs)); ys = segment(Sym(:ys; type=Real))
```

### 3.4 Rejected alternatives (analysis)

- **`Slot{T}`/`Segment{T,min,max}` as the variable's `symtype`.** Appealing
  (detection via `<:`, constraints in the type, bounds in `Int` type params),
  but rejected: (a) once spec data lives in the `VarSpec` table it duplicates
  the mechanism without adding capability; (b) a magic symtype leaks into
  `promote_symtype` — every operation on it returns `Any`, so pattern trees
  lose all symtype information rather than carrying meaningful types; (c)
  `Segment{Real, 0, 9223372036854775807}` is unreadable in `dump`/printing;
  (d) isbits type params cannot carry runtime values (defaults, predicates)
  so the marker term is needed anyway. The inner sym's *own* `symtype` is the
  type constraint — no wrapper type needed.
- **Metadata tags on `Sym`s** (the original draft). Works, but marker terms
  are strictly better where it matters: visible in the tree, `isequal`-
  distinguished, zero dict probes. Metadata remains the channel for *symbolic
  head* operation traits (§3.5), where there is no marker term to hang data on.
- **Inline spec args on marker terms** (`slot(x, pred, default)`). Rejected:
  the compiled matcher is independent of predicates, so baking them into the
  expression buys nothing; `VarSpec` + `vars` map is uniform, swappable
  without recompiling the plan, keeps `slot(x)` clean even for complicated
  functors, and stores callables as `FunctionWrapper`s. Same rejection for a
  standalone `predicate(x, f)` wrapper term.
- **Variable = whole marker term (per-occurrence identity).** Rejected in
  favor of sym-identity: `slot(x)` twice is one variable; a bare `x` is a
  compile error rather than a silent literal.
- **Occurrence-level predicates.** With specs in `VarSpec`, predicates are
  var-level only — checked once at binding; later occurrences only `isequal`-
  recheck. If a real use-case needs per-position predicates it would return
  as a plan-level field, not expression syntax.

### 3.5 Operation traits

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
(This is the analogue of MatchPy's per-`Operation` `associative`/`commutative`/
`one_identity` flags `[R1, R3]`; the metadata channel replaces MatchPy's
`CommutativeOperation` subclasses.)

**Design-for-extensibility, fast-path-internally.** The trait functions are
the extensible interface; the *engine never calls them directly*. Internal
wrappers enumerate the common cases with `===`/literal checks and only fall
back to the traits for the general case — dynamic dispatch on `(Any, DataType)`
is otherwise paid on every call node of every match:

```julia
_is_ac_head(@nospecialize(op), @nospecialize(ST::SymbolicUtils.TypeT)) =
    if op === (+) || op === (*)
        _is_number_st(ST) && return true     # enumerated common symtypes
    elseif op isa Function || op isa Type    # etc — cheap negative fast paths
        false
    end;
    is_associative(op, ST) && is_commutative(op, ST)

_is_number_st(@nospecialize(T::SymbolicUtils.TypeT)) =
    T === Number || T === Real || T === Integer || T === Int ||
    T === Float64 || T === Float32 || T === Rational{Int} ||
    T === Bool  || T <: Number
```

Both are `@nospecialize`d: at every call site `op` and `ST` are uninferrable,
so a specialized method would only be reached through dynamic dispatch —
there is no point fast-pathing inside a function the compiler can't inline
into. `@nospecialize` keeps one compiled body; the enumeration runs *inside*
that body. (Schematic — the real wrappers enumerate the combos that dominate,
ending in the general `<:`/trait fallback.) The same pattern recurs for
`symtype <:` checks (§5.5b) and is stated once as a rule in §9: **subtype
checks are not free — they call into the compiler runtime — so hot paths
enumerate common concrete cases and memoize the rest.**

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
   happens only when a `MarkersMap` is produced.

3. **Slots** match exactly one term, subject to: symtype constraint
   (`symtype(candidate) <: symtype(inner_sym)`), shape constraint (concrete
   `ShapeVecT` must equal the candidate's shape; `Unknown` is unconstrained),
   then the variable's `predicate` (the FunctionWrapper'd check, skipped
   entirely when none is declared). `<:` calls into the compiler runtime —
   it is **not** free — so the check goes through the fast-path wrapper +
   (optionally) the memo described in §5.5b.

4. **Non-linear patterns.** Every occurrence of a variable is a marker-term
   node; the first binds, later occurrences check `isequal` against the bound
   value (`===` fast path first — subject subterms are interned, so
   structural equality usually resolves in O(1)). Var-level predicates are
   evaluated once, at binding — there are no occurrence-level predicates
   (§3.4).

5. **Segments** under a free or associative head capture a *contiguous run*;
   under a commutative or AC head they capture a *sub-multiset* materialized
   in `sorted_arguments` order (canonical for `AddMul`; for other ops the
   term's own argument order — deterministic per subject). `min`/`max` bounds
   apply; `predicate` applies to each captured element, `sequence_predicate`
   to the whole capture (a `Vector{BasicSymbolic{SymReal}}`). C-only +
   segment is allowed and means "unordered subset capture" — deterministic
   for the same reason.

6. **Identity coercion.** If the pattern node is an `f(...)` AC/A call and the
   subject is *not* an `f`-call, the subject is treated as a singleton argument
   multiset `[subject]` iff `identity_element(f, ST) !== nothing`. Example:
   `slot(a) + segment(rest)` matches subject `x` as `a ↦ x, rest ↦ ()`. This
   is Mathematica's `Flat`+`OneIdentity` behavior, adapted from MatchPy
   (`matchpy/matching/one_to_one.py::_match_one_identity` and
   `matchpy/matching/_common.py::check_one_identity` `[R5]`), and is what makes
   `+`-headed patterns work on non-`Add` subjects.

7. **Optional slots.** An `optional(x)` occurrence at an AC/A node enumerates
   two alternatives: consume one remaining argument (a normal slot match) or
   bind the var's `VarSpec.default`. Enumeration order: consume first,
   default second — adapted from MatchPy's `Optional`/`Wildcard.optional`
   semantics and its use in `one_to_one.py::_fixed_var_iter_factory` `[R5]`.
   A var carrying `optional` occurrences must declare `default` in its spec;
   outside an AC/A node an `optional` occurrence is a compile error.

8. **Enumeration order.** Deterministic *and* canonical where it counts:
   AC/A subject arguments are iterated in `sorted_arguments` order (`<ₑ` —
   deterministic across processes, `@cache`d), so the AC phases never touch
   `AddMul`'s hash-ordered `arguments`. AC assignments enumerate right-side
   candidates in increasing subject index; segment splits enumerate by
   increasing captured length, left segment first. *Order-dependent:* the
   argument order of any reconstructed `f(captured…)` segment binding follows
   the canonical constructor's own order (dict order for `AddMul` — marked
   order-dependent, §1.2). The *set* of results is what tests assert.

9. **Constraints.** `match(p, s; constraints = [Constraint(...)])` where
   `Constraint(fn, vars)` pairs a `ConstrT`-wrapped callable with the
   `Vector` of variable syms it reads; the engine calls
   `fn(vals::Vector{BasicSymbolic{SymReal}})::Bool` — a **collection**, not
   splatted args, so no per-signature specialization is forced and the
   signature stays `FunctionWrapper`-stable. The argument vector is an engine
   buffer refilled per evaluation. A constraint fires as soon as all its
   variables are bound (early pruning via a per-variable "remaining
   dependents" counter — non-negotiable for AC performance). (MatchPy's
   `CustomConstraint`/`Constraint` machinery:
   `matchpy/expressions/constraints.py`, enforced in
   `one_to_one.py::_check_constraints` `[R5]`.)

10. **Literal heads.** A pattern whose head position is a marker term
    (`slot(f)(x)`) matches the *operation* position: the subject head must
    satisfy the slot constraints and binds `f`. This is Mathematica's
    `f_[x_]` and falls out of treating the operation as another pattern
    position — with `is_associative`/`is_commutative` on a bound head sym
    resolved via its `OperationTraitsCtx` metadata (§3.5). Supported, flag
    explicitly in tests.

11. **Marker terms embedded in a *subject*** are ordinary terms: they can
    only be captured by variables or matched by an identical literal
    `slot(x)` node. Subject-node metadata is otherwise ignored (except the
    operation-trait lookup on symbolic heads, §3.5).

---

## 5. Architecture

### 5.1 Pipeline

```
pattern:BasicSymbolic{SymReal}
   │  compile_pattern ────────────────────────────────────┐
   ▼                                                      ▼
Matcher{T}           +   subject → IRStructure{T}   →   MatchEngine
   (pattern IR,                 (subject DAG)             (iterative
    per-node plans,                                       frame machine)
    VarSpec table, ground flags)                               │
                                                               ▼
                                              eachmatch / matches / match
                                                               │
                                                               ▼
                        MarkersMap <: AbstractDict{BasicSymbolic,
                                                     BasicSymbolic}
```

### 5.2 `Matcher{T}` (the compiled pattern)

Built once per `(pattern, varspecs)` pair; shareable across subjects (the
many-to-one hook). `compile_pattern(expr; vars = Dict())` → `Matcher`.

```julia
struct Matcher{T}
    ir::IRStructure{T}                        # pattern DAG
    root::Int32                               # node index of whole pattern
    plans::Vector{NodePlan}                   # indexed by node idx — ADT below
    var_syms::Vector{BasicSymbolic{T}}        # var_id -> inner Sym
    var_specs::Vector{VarSpec}                # var_id -> spec (§3.1)
    var_of::IdDict{BasicSymbolic{T}, Int32}   # inner sym -> var_id (=== identity)
    is_ground::BitVector                      # subtree contains no variables
    nvars::Int                                # number of distinct variables
end
```

`var_of` is an `IdDict`: the same variable is the same interned `Sym` object
(hashconsed), so `===` identity is both correct and cheaper than an
`isequal`-keyed `Dict`. Marker terms themselves never become keys — plans map
each marker node to `var_of[unwrap_varspec(node)]`.

`NodePlan` is a `@data` ADT (the BSImpl idiom), one variant per node kind:

```julia
@data NodePlan begin
    Literal()                          # match iff isequal (consts, plain syms)
    Slot(var_id::Int32, optional::Bool)
    Segment(var_id::Int32)
    Call(op, head, children::SmallV{Int32})        # free head: positional
    AssocCall(op, head, children::SmallV{Int32})   # A-not-C: ordered
    CommCall(op, head, fixed, slots, optionals, segments)  # C-not-A
    ACCall(op, head, fixed, slots, optionals, segments)    # AC
end
```

`op` is `operation(node)` — needed for head equality, identity coercion, and
segment binding reconstruction. `head` is the node index of a symbolic-head
obligation (`0` when the operation is not symbolic): `IRStructure` prefixes
a symbolic operation to `outneighbors`, so the head is just another child
obligation — this is how head-slots (`slot(f)(x)`, §4.10) fall out. Comm/AC
plans partition children at compile time into `fixed`/`slots`/`optionals`/
`segments`; `Call` and `AssocCall` keep ordered children (associative
matching is position-sensitive).

`is_ground` precomputed bottom-up: `is_ground[n] = no var in descendants`.
A ground pattern node matches a subject node iff `isequal` — the engine checks
the flag *before* pushing a frame, turning whole-subtree matches into one
comparison. This is the single most valuable compile-time fact (real patterns
are mostly ground).

Compile-time validations (loud errors, not silent mismatches):
- **bare occurrence of a marked sym** (`sin(slot(x)) + x` → error);
- kind conflicts across occurrences of one variable (slot/optional vs segment);
- `vars`-map `VarSpec` variant mismatches the marker kind;
- `optional` occurrence of a var without `default` in its spec;
- `vars` map entries keyed on syms that are not pattern variables;
- segment under a position where capture is undefined (see §4.5), including
  `segment`/`optional` at the pattern root (no enclosing argument list);
- `segment`/`optional` markers in head position (`slot` heads are *allowed*
  — §4.10);
- `optional` outside an AC/A node (§4.7);
- `min > arity bound` where provable (fixed-arity parents).

### 5.3 Bindings and trail

```julia
struct Bindings{T}
    node::Vector{Int32}            # var_id -> subject node (0 = unbound)
    seq::Vector{SmallV{Int32}}     # var_id -> captured subject nodes (segments)
    seg_op::Vector{Any}            # var_id -> the head under which it captured
end
```

One concrete struct; `seg_op` is `Any` because ops are heterogeneous callables
— read once per materialization, never in the hot loop. It is needed to
rebuild `f(captured…)` for the external `MarkersMap` (§5.6). A
`trail::Vector{Int32}` records which var ids were bound, in order; backtracking
pops a mark and clears. Rebinding (non-linear check) never touches the trail.

### 5.4 The engine

`MatchEngine{T}` is a **defunctionalized backtracking machine**. Each
in-progress node match is a *frame*: a suspended single-result enumerator with
mutable resumption state. This is the compiled analogue of MatchPy's
generator-based matchers (`matchpy/matching/many_to_one.py::_MatchIter`,
`CommutativeMatcher.match` `[R5]`) — Python generators are resumable
coroutines; Julia lacks cheap coroutines, so we make the suspension state
explicit and inspectable instead. Frames are the `@data` ADT `MatchFrame`:

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
    const pat::Matcher{T}
    const subj::IRStructure{T}
    const frames::Vector{MatchFrame}  # stack; top = deepest obligation
    const binds::Bindings{T}
    const trail::Vector{Int32}
    const constraints::Vector{Constraint}
    const pending::BitVector          # constraint-ready bookkeeping
    steps::Int                        # work meter; compare against budget
end
```

`const` on every field that names a container (they're mutated *through* the
reference, never rebound — `push!`/`pop!` on `frames`, element writes on
`binds.node` etc. all work fine under `const`). Only `steps`, a plain `Int`
counter, needs interior mutability.

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
`MarkersMap`. Because all state is explicit and heap-resident, iteration is
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

**(b) Slot** — bound → `isequal` recheck; unbound → symtype+shape+var
predicates, bind, trail-record, then run ready constraints. The
`symtype <: ` check goes through the `@nospecialize` fast-path wrapper
(`cand === want`, `want === Any`, enumerated concrete combos — most
real-world specs are `Any`/`Number`/`Real`, so enumeration alone should
carry most of the win). Whether a per-variable memo
(`Dict{Tuple{DataType,DataType},Bool}`) pays for its own bookkeeping vs
simply paying the enumerated check is an open question — it is a benchmark
item in `perf/hardening` (§12), and the wrapper seam is exactly the kind of
component the modular design below lets us swap for measurement.

**(c) `Seq` (free head)** — `operation` must agree (`===`/`isequal` for
function heads, `isequal`/slot-match for symbolic heads); fixed arity; children
matched positionally as nested enumeration (child `i+1` initialized under
child `i`'s fresh bindings; on child `i+1` exhaustion, advance child `i`).

**(d) `Comm`** — `arity(p) == arity(s)` required; enumerate permutations of
subject args in index order; each permutation is an inner `Seq`. (As in
MatchPy's ordered fall-through for commutative operations,
`one_to_one.py::_non_commutative_match` `[R5]`.)

**(e) `Assoc`** — pattern arg list is a sequence of fixed elements and
segments; subject is a fixed-size arg list. Segments consume contiguous runs;
enumerate compositions of the subject length into (fixed=1 | segment=variable)
parts honoring min/max, shortest-capture-first. Non-segment positions are
positional `Seq` obligations. (The segment-splitting machinery is adapted from
`one_to_one.py::_build_full_partition`/`_count_seq_vars` `[R5]`.)

**(f) `AC`** — the core algorithm, adapted from MatchPy's commutative matcher
`[R3 §4, R5]` which is itself in the Eker bipartite-matching lineage `[R6]`:

```
pattern args partition into FIXED (ground and non-var subpatterns),
                         SLOTS (incl. already-bound slots, treated as fixed-
                                by-lookup), OPTIONALS, SEGMENTS.
subject args = sorted_arguments(subject) (or [subject] via identity coercion)
             — canonical <ₑ order, never the hash-ordered raw arguments().

Phase 1 — candidates: for each fixed pattern arg, compute the set of subject
   indices it can match (each submatch is itself a nested frame obligation).
   Sort fixed parts by ascending candidate count (most constrained first).
   Fail fast on any empty candidate set.
   (Cf. `CommutativeMatcher._build_bipartite`/`_extract_sequence_wildcards`
   in `matchpy/matching/many_to_one.py` and `_match_commutative_operation` in
   `matchpy/matching/one_to_one.py` `[R5]`.)

Phase 2 — assignment: enumerate matchings of (fixed ∪ slots) → subject args,
   all distinct. Slots get the same candidate filtering via their constraints.
   Each complete assignment binds its vars (trail).
   Implemented as maximal-matching enumeration on a bipartite graph, after
   `matchpy/matching/bipartite.py::enum_maximum_matchings_iter`, which is Uno's
   alternating-cycle enumeration `[R7]` on top of a Hopcroft–Karp seed matching
   (`matchpy/matching/hopcroft_karp.py`, `[R8]`).

Phase 3 — leftovers: distribute remaining subject args among segments
   (unordered subsets; capture order = canonical order) honoring min/max.
   With one segment this is O(1): it takes everything left. Optionals that did
   not consume bind their defaults.
   (Cf. `CommutativeMatcher._match_sequence_variables` `[R5]`.)

Failure anywhere unwinds the trail to the frame's mark and advances the
innermost non-exhausted enumerator.
```

Complexity honesty (documented in user docs): general AC matching is
NP-complete `[R9]`; with *linear* patterns it is polynomial (O(|p|·|s|³)
`[R9]`).

**Is a dedicated linear fast path in scope?** Not in v1, and deliberately so:
the machinery is already ~80% shared. `is_linear` is computed free at compile
time (var occurrence counts). For a *linear* pattern with no segments, the
Phase-2 assignment needs no non-linear recheck, and a *first*-match query can
stop at the Hopcroft–Karp seed matching without running Uno enumeration —
a cheap add-on later, reusing the bipartite graph wholesale. Two cheaper
variants worth recording now: (a) the linearize-then-check prefilter of
Bachmair et al.'s experiments `[R10]` — replace repeated var occurrences by
fresh vars, match linearly, then consistency-check — which bolts onto our
engine as a candidate-ordering/pruning layer; (b) ordering fixed parts by
candidate count already approximates the practical win. The full BKN cubic
algorithm is a different decomposition (not an extension of bipartite
enumeration) and is out of scope unless a profiling case demands it.

**(g) Optional** — at an AC/A node: two-branch choice (consume | default).
Outside such a node: compile-time error (a lone optional has no "absence" to
fall back on).

### 5.6 MarkersMap & instantiation

**`MarkersMap` is a concrete `AbstractDict` wrapper** — value type
`BasicSymbolic{SymReal}` uniformly, no `Any`, no union:

```julia
struct MarkersMap <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
    dict::Dict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}  # inner sym -> expr
end
```

- **Slots** bind to the captured `BasicSymbolic{SymReal}`.
- **Segments** bind to the *reconstructed* `f(captured…)` — the parent op
  `f` (recorded per-binding in `seg_op`) applied to the captured args via the
  canonical constructor. This single choice removes the value union entirely:
  every binding is a `BasicSymbolic`. Consequences:
  - Empty capture under an identity-having op materializes as
    `Const{T}(identity)` (`0` for `+`, `1` for `*`) — Mathematica-consistent
    (`Plus[] === 0`); under a generic head it is `f()` (a zero-arg `Term`).
  - `instantiate` splices by reading `arguments(bound)` when
    `operation(bound) === f`; a `Const` binding must equal `identity_element`
    (else a hard internal error). `f()` splices to zero args.
  - Reconstructed `AddMul` argument order is dict/hash order — marked
    *order-dependent*.
  - The bound value is a first-class expression users can keep manipulating.
- **Key normalization** (`unwrap_varspec` on lookup): `d[x]`, `d[slot(x)]`,
  `d[segment(x)]`, `d[optional(x)]` all resolve to the same variable —
  implemented on `getindex`/`get`/`haskey`/`setindex!`/`iterate`.
  Keys are stored as inner syms only; because `isequal` ignores nothing here,
  `d[plain_sym]` also hits (wanted: substitute works on the plain variable).

`SubstitutionView` — a read-only `AbstractDict` view over *live* engine state
(`binds`, `var_syms`, `seg_op`, subject IR): `keys`/`iterate`/`getindex`
resolve lazily without materializing the output dict. **Contract:** valid only
until the next `eachmatch`/`iterate` step mutates the bindings; `materialize(v)`
produces a persistent `MarkersMap`. A debug flag (`Ref{Bool}`, off by
default) stamps each view with the engine's step counter and throws on stale
access — cheap insurance against the classic view-dangling bug.

`instantiate(template, subst)` rebuilds an expression over the pattern's
marker terms: marker nodes resolve via `unwrap_varspec`; `slot`/`optional`
vars substitute their bound expr; `segment` vars splice `arguments(bound)`
into the parent call's arg list. `substitute(expr, subst)` also works for
slot-only substitutions (segment bindings would be inserted wholesale —
documented; `instantiate` is the correct entry point).

Public API (stable surface):

```julia
compile_pattern(expr; vars::AbstractDict = Dict()) -> Matcher{SymReal}
match(m_or_expr, s; constraints = ()) -> Union{MarkersMap, Nothing}
matches(m_or_expr, s; constraints = ())       # lazy resumable iterator
matchall(...) = collect(matches(...))
eachmatch(f, m_or_expr, s)                    # f(::SubstitutionView)::Bool; false = stop
instantiate(template, subst)
materialize(view) -> MarkersMap
```

`eachmatch` is the zero-allocation hot path rewriters should use.

### 5.7 Swappable algorithms

The design is not built around pluggable algorithms, but two seams make
swapping cheap where it matters:

- **Plan-level seam.** `NodePlan` variants are the unit of algorithm choice:
  at compile time an AC node could produce `ACCall` (Uno+HK bipartite
  enumeration) or, say, an `ACBrute` plan (naive permutation/subset
  enumeration for benchmarking or verification) or a future `ACLinear` plan
  (§5.5f analysis) — the engine does not care which frame it executes.
  `compile_pattern(...; alg = :default | :naive)` (or a per-head table) is a
  small surface addition that costs nothing when unused. This is the natural
  home for the §5.5b memo-vs-enumerate experiment and any future linear-path
  or AddMul-dict matcher.
- **Top-level seam.** A wholly different matcher (e.g. our own naive oracle
  for cross-validation, or a recursive baseline for benchmarks) is simply a
  different entry point with the same `match`/`matches` signature — no
  engine internals shared, no coupling.

Anything more invasive (e.g. swapping the frame machine itself) is out of
scope by intent — two seams cover the interesting variation points without
paying an abstraction tax in the hot loop.

---

## 6. File layout

```
MatchMaker.jl/
  DESIGN.md                 # this document
  DEVELOPING.md             # codebase navigation + implicit contracts (phase 0)
  README.md                 # includes the §13 reference list (phase 0)
  Project.toml
  src/
    MatchMaker.jl           # module, includes, exports
    patternvars.jl          # §3.1–3.3: marker terms, VarSpec, unwrap_varspec,
                            #   constructors, macros, FunctionWrapper aliases
    traits.jl               # §3.5: operation traits + fast-path wrappers
    compile.jl              # §5.2: Matcher, NodePlan ADT, spec merge, validation
    bindings.jl             # §5.3, §5.6: Bindings, trail, MarkersMap + SubstitutionView
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
    runtests.jl
    unit/...                # per-source-file unit suites
    oracle.jl               # the naive reference matcher (self-contained)
    fuzz.jl                 # seeded randomized cross-validation vs oracle
    matchpy/                # tests translated from MatchPy's test suite;
                            #   each file cites the original file::test `[R5]`
    literature/             # cases taken from the matching literature
                            #   (Eker, BKN, MatchPy papers…) with citations
  benchmark/benchmarks.jl
```

## 7. Testing strategy

Every feature branch ships its tests in the same merge.

- **Unit**: per construct — construction/metadata roundtrip, trait table,
  compile plans, each frame kind's enumeration semantics (e.g. `Assoc` split
  enumeration on a free `f`, AC distribution counts).
- **Oracle cross-validation** (`test/oracle.jl`): a deliberately naive,
  obviously-correct matcher (~200 lines, recursion + hand-rolled
  permutations/compositions helpers — no Combinatorics dep, no IR, no
  sharing, correctness over speed). Property:
  `sort(materialize.(collect(matches(p,s)))) == sort(oracle_all(p,s))` on
  generated (pattern, subject) pairs. The oracle defines the semantics; the
  engine must equal it on *sets* of substitutions.
- **Fuzz** (`test/fuzz.jl`): seeded random pattern/subject generator over
  `+`,`*`,`^`,`/`,`sin`,`cos`,`f` with slots/segments/optionals at controlled
  rates; bounded subject size; fixed seed committed so failures reproduce.
- **`test/matchpy/`** — all relevant MatchPy tests translated to our API;
  each file/function cites the original (`tests/test_matching.py::test_…`
  `[R5]`) so coverage of MatchPy semantics can be audited side-by-side.
- **`test/literature/`** — reference cases taken from the matching literature
  (Eker's worked examples, BKN's pathological instances, MatchPy paper
  figures), each annotated with its source.
- **Negative corpus** — patterns that must NOT match (arity, symtype,
  non-linear inequality, malformed specs).
- **Type stability**: `@inferred` on `compile_pattern`, `next_match!`,
  `instantiate`; a `test/qa` env with JET for the hot paths; Cthulhu
  spot-checks documented in DEVELOPING.md.
- **Benchmarks** (`benchmark/`): vs `SymbolicUtils.@rule/@acrule` on the
  rewrite-suite patterns; large-subject stress (deep `Add` chains — where the
  non-recursive engine is the point); PkgBenchmark-compatible `benchmarks.jl`.

## 8. Many-to-one outlook (deferred, but designed-for)

After the one-to-one engine stabilizes: compile *sets* of `Matcher`s
into a discrimination-net-style shared automaton — the AC discrimination-net
lineage `[R10]` generalized by Krebber to sequence variables and non-linear
patterns `[R3]`, as realized in `matchpy/matching/many_to_one.py::ManyToOneMatcher`
(with the purely syntactic variant in `matchpy/matching/syntactic.py::
DiscriminationNet`) `[R5]`. Integration points already in the design:

- `Matcher` plans are indexed instructions — a net state is just a
  *set of* `(pattern, node)` pairs sharing one subject cursor.
- `IRStructure` on the subject amortizes across all patterns.
- AC nodes map to MatchPy's `CommutativeMatcher` net states (states whose
  `matcher` field is a `CommutativeMatcher` in `many_to_one.py` `[R5]`); our
  `AC` frame machinery is reused per net node rather than rewritten.

Rough shape: `ManyToOneMatcher{T}` holding shared pattern IR, net states as
`Vector{StateId}`, transitions keyed by node features (variant, op identity,
arity, leaf hash, wildcard-any). Wildcard/slot transitions become wild edges;
AC frames suspend per net-state. This is its own design doc when scheduled —
this section exists only to keep today's choices compatible.

## 9. Performance & type stability

- All engine fields concrete; `MatchFrame` is the only union (ADT), dispatched
  by `@match` — the same union-splitting model as `BSImpl`.
- Stored callables are `FunctionWrapper`s with declared signatures (§3.2) —
  inference works, no overspecialization, no `Any` call; a `nothing` check
  skips the call entirely when unconstrained.
- **Subtype checks are not free** (they enter the compiler runtime). Hot
  checks — `symtype(candidate) <: T`, op-trait lookups — go through
  `@nospecialize`d wrappers that enumerate common concrete cases (`===`,
  literal tables) before the general `<:`/trait fallback. Whether a
  `Dict{Tuple{DataType,DataType},Bool}` memo on top of that is a net win vs
  the enumeration alone (most real specs are `Any`/`Number`/`Real`) is
  decided by the §12 benchmark, not assumed. Stated once as a rule: *design
  for extensibility; internally fast-path common cases.*
- No `Vector{Any}` in the search state; bindings store `Int32` node ids;
  `seg_op` is the sole `Any` field and is cold (materialization only).
- Buffers reused across matches of one engine; `MarkersMap` materialization
  is the only per-match allocation (and `eachmatch` avoids it).
- `maxsteps` budget parameter guards pathological AC searches (the
  `COMM_BACKTRACK_BUDGET` analogue), counted in `eng.steps`.
- `sorted_arguments` on `AddMul` nodes is `@cache`d — canonical order is
  amortized-free per node.
- Deferred optimizations (recorded, not scheduled): `(p_idx, s_idx)`-keyed
  submatch memoization once bindings-versioning is designed; linear-pattern
  fast path (§5.5f analysis); direct `AddMul`-dict matching to skip
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
- **Citation policy:** algorithms, data structures, and semantics adapted from
  MatchPy or the matching literature are credited in three places — the paper
  in `README.md`'s reference list (§13), the `[Rx]` tag in this document, and a
  source comment naming the MatchPy file::function or paper section adjacent
  to the adapted code (e.g. `# Adapted from matchpy/matching/bipartite.py::
  enum_maximum_matchings_iter (Uno 1997)`).
- **Design doc governance:** implementation changes that alter behavior,
  semantics, or architecture update this file in the same PR; reviewed code
  changes that diverge are doc bugs until fixed.
- Dependencies: `SymbolicUtils` (dev'd to the local checkout),
  `DocStringExtensions`, `Moshi`, `Graphs` (IR access), `ReadOnlyArrays`,
  `FunctionWrappers` (§3.2). Test extras: `Test`, `SafeTestsets`, `Aqua`,
  `JET`, `BenchmarkTools`. The oracle is deliberately self-contained (own
  enumeration helpers), so no `Combinatorics` dep.
- Licensing: all adopted references/deps are MIT or BSD-2-Clause — see §14.

## 12. Implementation milestones (branches in order)

Each `feat/*` merges to `master` with unit + oracle + (where cheap) fuzz
coverage before the next starts.

0. `chore/repo-bootstrap` — Project, module stub, test harness, DEVELOPING.md,
   README.md (with §13 refs + §14 licenses), .gitignore, Aqua suite.
   *Tests: package loads, QA green.*
1. `feat/pattern-vars` — §3.1–3.3: marker singletons, `unwrap_varspec`,
   `VarSpec`, constructors, macros, `MarkersMap` dict wrapper.
   *Tests: marker-term identity/equality, constructor validation, macro
   expansion, dict key normalization.*
2. `feat/op-traits` — §3.5 incl. fast-path wrappers. *Tests: +/* AC for
   Number, A-not-C for matrices, symbolic-head metadata fallback, user
   extension, fast-path equivalence vs trait fallback.*
3. `feat/pattern-compiler` — §5.2: `Matcher`, `NodePlan`, `vars` map →
   `VarSpec` variants, validation. *Tests: plan shape per node kind, ground
   flags, bare-occurrence error, marker-kind conflict, variant-mismatch
   error, spec-key errors.*
4. `feat/match-core` — engine + literal/slot/`Seq`; `match`, `matches`,
   `eachmatch`, `MarkersMap`(+View). *Tests: unit per leaf logic; oracle on
   linear patterns; fuzz (free-heads only).*
5. `feat/segments-free` — `Assoc` frame restricted to free heads + segments.
   *Tests: split enumeration, min/max, predicates; oracle.*
6. `feat/commutative` — `Comm` frame. *Tests vs permutation oracle.*
7. `feat/associative` — A heads w/ identity coercion. *Tests: `f` declared
   associative, contiguous splits, singleton subjects; oracle.*
8. `feat/ac` — sub-branches `ac/candidates+assignment` then `ac/segments`.
   *Tests: unit on candidate matrix & distribution; oracle fuzz incl.
   non-linear; `test/matchpy/` suite; singleton coercion.*
9. `feat/optional-slots` — §4.7/§5.5g. *Tests: defaults under +,*; both
   enumeration branches; `optional` w/o default → compile error; outside
   AC/A → compile error.*
10. `feat/constraints` — §4.9. *Tests: early-prune call-count instrumentation,
    correctness vs post-hoc filtering.*
11. `feat/instantiate` — §5.6 remainder. *Tests: splice correctness, end-to-end
    rewrite examples.*
12. `perf/hardening` — allocation audit, `@code_typed` notes committed,
    benchmark suite vs `@acrule`, budget parameter, memo-vs-enumerate
    experiment for `symtype <:` (§5.5b), `:naive` plan variants for
    benchmarking (§5.7).
13. `docs/user-guide` — pattern syntax & semantics incl. the normalization
    caveat and complexity notes.

## 13. References

Adapted algorithms and their sources. In the source code, `[Rx]` tags are
expanded to these entries; MatchPy code is referenced by path within
`[R5]` (repository root) plus function/class name.

- `[R1]` M. Krebber, H. Barthels, P. Bientinesi. *MatchPy: A Pattern Matching
  Library*. Proc. 15th Python in Science Conf. (SciPy 2017).
  <https://proceedings.scipy.org/articles/shinma-7f4c6e7-00b>
- `[R2]` M. Krebber, H. Barthels, P. Bientinesi. *Efficient Pattern Matching in
  Python*. PyHPC/SC workshops 2017. <https://doi.org/10.1145/3149869.3149871>,
  arXiv:1710.00077
- `[R3]` M. Krebber. *Non-linear Associative-Commutative Many-to-One Pattern
  Matching with Sequence Variables*. MSc thesis, RWTH Aachen, 2017.
  arXiv:1705.00907 — primary algorithmic reference for the AC frame (§5.5f)
  and the many-to-one net (§8).
- `[R4]` M. Krebber, H. Barthels. *MatchPy: Pattern Matching in Python*. JOSS
  3(26), 2018. <https://doi.org/10.21105/joss.00670>
- `[R5]` MatchPy source code, <https://github.com/HPAC/matchpy> —
  `matchpy/matching/one_to_one.py` (one-to-one matcher: `_match`,
  `_match_commutative_operation`, `_match_one_identity`, `_build_full_partition`,
  `_check_constraints`), `matchpy/matching/many_to_one.py` (`ManyToOneMatcher`,
  `CommutativeMatcher`, `_MatchIter`), `matchpy/matching/bipartite.py`
  (`BipartiteGraph`, `enum_maximum_matchings_iter`),
  `matchpy/matching/hopcroft_karp.py`, `matchpy/matching/syntactic.py`
  (`DiscriminationNet`), `matchpy/matching/_common.py`
  (`CommutativePatternsParts`, `check_one_identity`),
  `matchpy/expressions/constraints.py`.
- `[R6]` S. Eker. *Associative-Commutative Matching via Bipartite Graph
  Matching*. Computer Journal 38(5):381–399, 1995.
  <https://doi.org/10.1093/comjnl/38.5.381> — origin of the
  candidates→assignment→rest decomposition used by `CommutativeMatcher` and
  our `AC` frame.
- `[R7]` T. Uno. *Algorithms for Enumerating All Perfect, Maximum and Maximal
  Matchings in Bipartite Graphs*. ISAAC '97, LNCS 1350:92–101.
  <https://doi.org/10.1007/3-540-63890-3_11> — the algorithm inside
  `enum_maximum_matchings_iter` our Phase-2 assignment enumerator follows.
- `[R8]` J. E. Hopcroft, R. M. Karp. *An n^{5/2} Algorithm for Maximum
  Matchings in Bipartite Graphs*. SIAM J. Comput. 2(4):225–231, 1973.
  <https://doi.org/10.1137/0202019> — seed matching for Phase 2.
- `[R9]` D. Benanav, D. Kapur, P. Narendran. *Complexity of Matching Problems*.
  RTA 1985; JSC 3(1–2):203–216, 1987.
  <https://doi.org/10.1007/3-540-15976-2_22> — NP-completeness of AC matching;
  polynomial bound for linear patterns.
- `[R10]` L. Bachmair, T. Chen, I. V. Ramakrishnan. *Associative-Commutative
  Discrimination Nets*. TAPSOFT 1993, LNCS 668.
  <https://doi.org/10.1007/3-540-56610-4_56> — the net architecture deferred
  in §8; see also the experiments paper (IJCAI 1995) for the
  linearize-then-check two-stage strategy.
- `[R11]` R. Sekar, R. Ramesh, I. V. Ramakrishnan. *Adaptive Pattern Matching*.
  SIAM J. Comput. 24(6):1207–1234, 1995.
  <https://doi.org/10.1137/S0097539793246252> — traversal-order synthesis for
  pattern-set automata; relevant when §8 becomes a real design.

## 14. Licenses

| Dependency / reference | License |
|---|---|
| MatchPy (`HPAC/matchpy`) | MIT (© 2016 Manuel Krebber) |
| SymbolicUtils.jl | MIT |
| Moshi.jl | MIT |
| FunctionWrappers.jl | MIT |
| DocStringExtensions.jl | MIT |
| OrderedCollections.jl | MIT |
| ReadOnlyArrays.jl | MIT |
| Graphs.jl | **BSD-2-Clause** |
| Aqua.jl, JET.jl, BenchmarkTools.jl, SafeTestsets.jl (test-only) | MIT |

Compliance notes:

- **MatchPy is MIT.** We port *algorithms*, not source lines (different
  language), and every adapted component carries a file::function citation
  per §11 — MIT attribution obligations are satisfied by the README license
  notice + reference list and the inline source comments.
- **Papers** are cited, not reproduced; algorithm descriptions reimplemented
  from the literature carry no license constraint.
- **Graphs.jl is BSD-2-Clause** — compatible with an MIT package; its license
  is carried transitively as a dependency (we vendor nothing).
- **MatchMaker.jl itself will be MIT** (declared in README + LICENSE file in
  the repo-bootstrap commit), consistent with the whole chain.
