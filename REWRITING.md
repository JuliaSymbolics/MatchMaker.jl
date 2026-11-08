# Rewriting & many-to-one matching — design

This designs the `simplify`-scale use case: large rule sets applied to
large subjects under `SymbolicUtils.Rewriters`-style combinators. It
elaborates DESIGN.md §8 ("many-to-one outlook") and subsumes the
`eachmatch_at` TODO item — the shared workspace and the net evaluation
*are* the specialized occurrence-search machinery that item asks for.

**Compatibility constraint: none.** Nothing here is released, so the
design deliberately reshapes rather than wraps: `MatchEngine`'s
`const` subject/pattern fields become workspace-provided
(`reset!` takes an externally-owned `IRStructure`), the rewrite
traversal is MatchMaker-native rather than SU's `Walk`, rule RHSs are
compiled template plans instead of dict substitutions, and every name
in this document is provisional. SU-combinator interoperability is
kept where it is free (the applier is a plain callable), not where it
costs.

Sections 1–4 are the near-term deliverable; §5 is the phased
many-to-one plan; §6–8 cover the shared workspace and growth bounds.

## 1. Semantics contract (port of `SymbolicUtils.Rewriters`)

A **rewriter** is `x -> Union{expr′, nothing}`: `nothing` means "did not
fire", anything else is the rewritten term. MatchMaker rule objects
satisfy this contract so the existing combinator ecosystem applies
verbatim.

The **primary traversal is MatchMaker-native** (§6) — it walks the
workspace `IRStructure` bottom-up and rebuilds only changed subtrees,
rather than `arguments()`/`maketerm` per node. `SymbolicUtils.
Rewriters` combinators interoperate for free where the contract is
already right (`Chain`, `IfElse`, `RestartedChain`, `Fixpoint`,
`Empty`, `Filter` — generic callables, reusable verbatim); the
`Walk`/`Postwalk`/`Prewalk` rebuild loop is *not* the foundation —
it's available through the applier-as-callable when needed. The
semantic contract we mirror:

| Combinator | Semantics (SU source) |
|---|---|
| `Empty()` | always `nothing` |
| `Chain(rws; stop_on_match=false)` | sequential pipeline — each `rw` sees the previous output; `nothing` passes `x` through. `stop_on_match=true` returns at the first result that differs from input — the "first rule wins" mode |
| `RestartedChain(rws)` | first `rw` producing `y !== nothing` → `Chain(rws)(y)` |
| `IfElse(cond, yes, no)` | `cond(x)::Bool ? yes(x) : no(x)`; `If(cond, rw)` ≡ `IfElse(cond, rw, Empty())` |
| `Fixpoint(rw)` | iterate until `isequal`-stable or `nothing` |
| `FixpointNoCycle(rw)` | fixpoint with a seen-set against cycles |
| `Filter(cond, rw)` | `rw` only where `cond(x)` |
| `PassThrough(rw)` | apply `rw` at a node without recursing |
| `Postwalk/Prewalk(rw; filter, maketerm, threaded, thread_cutoff)` | `Walk{ord}` traversal — apply `rw` bottom-up/top-down at every node, rebuilding via `maketerm` |
| `instrument(x, f)` | instrumentation hook over the combinator tree |

The `IfElse`/`Chain`/`RestartedChain` requirement therefore needs no
new semantics: `MatchMaker` supplies rule objects; users compose them
with the standard combinators. We re-export the SU names under
`MatchMaker.Rewriters` so a downstream `using MatchMaker.Rewriters`
gives the whole vocabulary (fallback: vendor the ~10 small combinators
if re-export collides with `SymbolicUtils.Rewriters` in downstream
code that uses both).

## 2. Rule objects

```julia
rule = mmrule(lhs => rhs;
              vars = Dict{Sym,VarSpec}(),
              constraints = Constraint[])
```

- `lhs` is compiled once via `compile_pattern` — segments, optionals,
  non-linear vars, head slots all supported as in one-to-one matching.
- `rhs` is a **compiled template plan** (`RhsPlan`) or a callable
  `f(view) -> expr` — stored as `Union{RhsPlan, RhsT}` (a
  `FunctionWrapper`, same convention as `PredT`/`ConstrT` in §3.2), so
  `apply` union-splits on a 2-member concrete union instead of calling
  `Any`. `RhsPlan` is the rhs expression compiled *against the lhs
  var ids* at `compile_rules` time — instantiation reads `binds` by
  index and splices segment captures positionally, bypassing the
  `Sym → value` dict that `instantiate`/`MarkersMap` would build per
  rewrite.
- `constraints` are the existing early-firing `Constraint`s — this is
  where `@rule … where …` guards map; they prune during the match,
  not after.

Application: `rule(x)` → `match(pat, x)` first result; `nothing` on
failure. First-result enumeration order is deterministic (§4), so a
`RuleSet` applies rules in declaration order.

For RHS consumers we hand the `SubstitutionView` straight through —
`instantiate(rhs, view)` never materializes a `MarkersMap` per call —
with `materialize(view)` only when the RHS needs a persistent dict.
`BoundMatch` is *not* the right per-site result: a rule application
takes the first match and reads all its vars.

## 3. `RuleSet` — the shared immutable structure

```julia
# Mirrors the stored-callable convention (§3.2: PredT/SeqPredT/ConstrT):
# a callable RHS gets the result view, returns the rewritten expr —
# `nothing` signals "matched but produce nothing" (SU rule semantics).
const RhsT = FunctionWrapper{
    Union{BasicSymbolic{SymReal}, Nothing}, Tuple{SubstitutionView}
}

struct CompiledRule
    pat::Matcher
    rhs::Union{RhsPlan, RhsT}   # compiled template or callable
    name::Symbol
end

abstract type RuleIndex end
# lookup(ws, idx::RuleIndex, node) -> SmallV{Int32} of candidate rule ids

struct RuleSet{I <: RuleIndex}
    rules::Vector{CompiledRule}
    index::I                  # §5 — BucketIndex now, DiscrimNet later
    maxsteps::Int             # per-site search budget
end

compile_rules(rules; maxsteps = typemax(Int)) -> RuleSet
```

`RuleSet` is parametric on the index: an abstract `index::RuleIndex`
field would force dynamic dispatch on every `lookup` — the hot call
per subject node — while `RuleSet{I}` keeps the whole call chain
concrete (`BucketIndex` and `DiscrimNet` compile to distinct code).

`RuleIndex` is the dispatch seam, not a concrete layout: Phase 1's
`BucketIndex` is a small op→rule-ids map plus spill lists; Phase 2's
`DiscrimNet` carries net states and transition tables. `lookup` is
the only operation both must implement, so the phases are A/B-able
behind one call site.

`RuleSet` is immutable after construction and safe to share across
tasks and calls — all mutable state lives in the workspace (§6). This
is the "shared global data structure": one `const`-held `RuleSet`,
compiled once, read by every rewrite pass.

`RuleSet` is pure data — it is deliberately **not** callable, since
applying rules requires mutable state (engines, memo cache) that an
immutable shared artifact shouldn't smuggle through a global. The
`x -> expr′ | nothing` callable a traversal needs is the workspace
(§4): `Postwalk(RuleWorkspace(rs))` makes the state being created
visible at the call site. Per-site `maxsteps` lives on the `RuleSet`
because combinators call `rw(x)` with no kwargs — options must ride
on an object, and a differently-budgeted variant is a second
`RuleSet` sharing the compiled `rules`/`index`.

## 4. `RuleWorkspace` — bounded reuse

```julia
mutable struct RuleWorkspace
    set::RuleSet                        # the ruleset it serves
    subj::IRStructure{SymReal}          # one per application site, shared
    engines::Vector{Union{Nothing,MatchEngine}}  # per rule id, lazy
    net_cache::Dict{Tuple{Int32,Int32}, SmallV{Int32}}  # Phase-2 only;
                                                        # persists across iterations (§7)
end
```

**The workspace is the callable.** It already needs `set` (engines
are per-rule, `lookup`/`apply` need `set.index`/`set.rules`), so it
holds the ruleset ref and is itself the `x -> expr′ | nothing` a
traversal applies:

```julia
(ws::RuleWorkspace)(x) = begin
    rs = ws.set
    for id in lookup(ws, rs.index, x)     # index → candidate rule ids
        y = apply(ws, rs.rules[id], x)
        y !== nothing && return y         # first-match semantics
    end
    return nothing
end
```

This makes the layering honest: `RuleSet` is the immutable compiled
artifact; `RuleWorkspace` is the mutable application context — *and*
the rewriter callable. `const ws = RuleWorkspace(rs)` is the
global-shared-engine answer: one long-lived workspace per ruleset,
reset-and-reused, bounded in size; users who want per-task instances
create them (or TLS-wrap their own), users who don't, don't.

The workspace holds **engine state only** — the rules themselves are
immutable in `RuleSet`. Concretely: one subject `IRStructure`
populated once per application site and shared by every rule engine;
a lazily-created `MatchEngine` per rule id (`reset!` between sites,
not re-allocated); and `net_cache`, used only by Phase 2 — a memo
`(net_state_id, subj_node) → surviving rule ids`. Because subject IR
nodes are interned, a DAG-shared subterm evaluates the net once per
state instead of once per occurrence — and because entries are pure
functions of structure it also persists across fixpoint iterations
and `rewrite` calls on the same workspace (§7). Phase 1 leaves
`net_cache` empty — the bucket `lookup` needs no per-node memo.

Workspaces are **explicitly created**: `RuleWorkspace(rs)` is a plain
constructor — call it inline per pass (`Postwalk(RuleWorkspace(rs))`),
hold one in a `const` for a long-lived global, hand one out per task,
or wrap it in `TaskLocalValue`/`ScopedValues` yourself if you want
task-local pooling. No hidden task-local default exists to resolve —
whoever holds the workspace owns its lifetime and thread-safety. The
native `rewrite` pass takes it:

```julia
rewrite(ws::RuleWorkspace, expr; order = :post) -> expr′   # bottom-up
```

- Same `RuleSet` across threads → distinct workspaces; no locks.
- One IR per subject *per pass*: `populate_ir!` runs once per
  application site and every rule engine + the net share it — the
  `O(rules × |subject|)` IR cost collapses to `O(|subject|)`.

### `reset!` protocol (the reuse mechanism)

Today `MatchEngine` *owns* its subject (`const subj`, `const sroot`,
populated at construction). In a rewrite pass that is backwards: the
subject belongs to the workspace, engines borrow it. So the engine
reshapes — `subj`/`sroot` become workspace-provided fields and
`reset!` accepts an externally-owned IR:

```julia
reset!(eng::MatchEngine, subj::IRStructure{SymReal}, sroot::Int32)
```

- `eng.subj = subj; eng.sroot = sroot` (fields no longer `const`).

Every rule engine points at the *same* workspace `IRStructure` —
`populate_ir!` runs once per site, total.
- `sp = 0`, `root_done = false`, `steps = 0`, `empty!(trail)`;
  `binds.node .= 0`, `binds.seg_op .= nothing`, `binds.extra .= nothing`,
  `empty!` each `binds.seq`.
- Frames in `stk` are released to the pool (already the retraction
  path); buffers keep their capacity.

Growth bounds: every buffer (`stk`, pool freelists, `binds` vectors,
`net_cache`) is *reset, not accumulated* — workspace size plateaus at
`max(|pattern|, |subject|)` over all subjects seen. That is the
"doesn't continually grow" guarantee; a `shrink!(ws)` can release
capacity after an atypical giant subject.

Rejected alternative: fresh `MatchEngine` per site — that is today's
per-attempt allocation cost verbatim; the workspace exists to remove it.

## 5. Many-to-one dispatch — two phases behind one interface

`lookup(ws, rs, node) -> rule_ids` is the seam; both phases share it.

### Phase 1: `RuleIndex` bucket dispatch (initial deliverable)

Group rules by root-obligation signature at `compile_rules` time:

- fixed op head → bucket per `op` identity
- head-slot (`~f` over args) → `:any_head`
- leaf/literal root → `:leaf`
- plus arity bounds (Seq `min…max`, Comm position count) as a range check

```julia
struct BucketIndex <: RuleIndex
    by_op::Dict{Any, SmallV{Int32}}   # root op identity -> rule ids
    any_head::SmallV{Int32}           # rules whose root head is a slot
    leaf_rules::SmallV{Int32}         # rules whose root is ground/literal
    arity::Vector{Tuple{Int,Int}}     # per-rule (min, max) arg bounds
end
```

At a site, one `signature(node)` probe selects the bucket — typically
1–3 survivors out of ~100 rules; each survivor runs `match` in order.

What it eliminates vs. naïvely looping `match(rule_i, x)` per rule,
which pays three costs **per rule per site**: a fresh `MatchEngine`'s
buffers, `populate_ir!` (O(|subject|) *every time*), and the match
itself. Phase 1 removes all three: the IR is populated once per site
and shared, engines are `reset!` rather than constructed, and the
bucket probe rejects almost every rule by root head alone — the
dominant win on `simplify`-shaped rule sets, where only a handful of
~100 rules can match any given node's head. It is intentionally
shallow: no shared traversal, no memoization — those are Phase 2,
behind the same `lookup` interface.

### Phase 2: discrimination net (DESIGN.md §8)

A shared trie over `(rule, pattern_node)` frontier states:

- **Net state** = set of open obligations across rules sharing a subject
  cursor.
- **Transitions** keyed by subject-node features: `(variant, op,
  arity-class)`, `literal`, wildcard-catch-all (slot edges record
  `vid → node` captures into the frontier).
- **Memoization**: `(state, node)` → surviving rule set in
  `ws.net_cache`. Subject IR interning means DAG-shared subterms
  evaluate once — this is the `eachmatch_at` item's "DAG dedup" and
  "bottom-up marking" folded into the net evaluation.
- **AC/segment/optional subtrees**: the net confirms *deterministic
  structure only*. Reaching a leaf state hands `(rule, frontier
  captures)` to the existing engine — multiset assignment, segment
  backtracking, and constraints run there, unchanged (MatchPy's own
  split: `CommutativeMatcher` states inside `ManyToOneMatcher`).

**Pattern-IR sharing and var specs.** The net itself stores
`(rule, pat_node)` frontier entries pointing into each pattern's own
IR — a shared pattern `IRStructure` is an *optional* further dedup
(identical subtrees across rules collapse to one node and share
frontier work), never a requirement. Either way, `VarSpec` semantics
stay **per-rule**: `CompiledRule.pat` keeps its own `var_of`/
`var_specs` tables, so a shared `slot(x)` node dedupes the *term*
only. A slot-edge transition for that node produces one capture *per
surviving rule*, each bound to that rule's own var id and checked
against that rule's spec — `slot(x)` with a predicate in rule A and
`slot(x)` without in rule B coexist cleanly: same structural node,
two semantic captures, two spec lookups. The trap to avoid is
attaching specs to shared nodes — the design never does; all
binding-state resolution goes through `(rule, node) → rule's var
tables`.

The net is never the whole matcher — it is a subject-structure filter
feeding the existing frame machine. Phase 1 is the correctness
reference for Phase 2's `lookup` results (same survivors, net does it
in one walk).

## 6. Traversal — native rewrite pass

The canonical call is a MatchMaker-native bottom-up pass over the
workspace IR, not `Postwalk(applier)`:

```julia
rewrite(ws::RuleWorkspace, expr; order = :post) -> expr′   # bottom-up
```

The pass walks `ws.subj`'s dependency graph once: at each node
`lookup` selects candidates → `apply` → on a changed result, mark the
node and rebuild only its ancestors (identity-unchanged nodes keep
their interned nodes). Top-down (`:pre`) applies the same loop in the
opposite direction before descending. This *is* the net's evaluation
walk under Phase 2 — one traversal serves the whole rule set, not one
traversal per candidate.

SU interop stays free: `Postwalk(RuleWorkspace(rs))(expr)` works
unmodified because `ws` is a plain callable — use it where SU
combinator composition matters (`instrument`, `threaded`), prefer
the native pass where it doesn't.

- `IfElse` conditions that are *patterns* become `x -> match(m, x) !== nothing`
  — a `PatternCond` convenience wraps this.
- `RestartedChain`/`Fixpoint` resubjection: the produced term is a new
  subject → the workspace repopulates its IR per application site
  (cheap; interned terms dedup inside `populate_ir!`).
- `maxsteps` budgets per application site, shared across the site's
  candidate rules — not a global rewrite budget (that's a rewriter
  concern: `FixpointNoCycle` exists for termination).
- `threaded` walks (SU `Walk` path): give each task its own
  `RuleWorkspace` — the callable is the workspace, so thread-safety
  is literally which `ws` object the task holds.

## 7. Fixpoint & incremental rewriting

`Fixpoint` over a workspace iterates the rewrite pass until
`isequal`-stable — the common case changes a small subtree per
iteration, so the design accumulates rather than restarts:

- **IR accumulation.** `rewrite` iterations repopulate the *same*
  workspace `IRStructure`: unchanged subtrees are the same interned
  `BasicSymbolic`s, so `populate_ir!` hits `definition` for them —
  cost per iteration is the *new* nodes only. Old nodes are never
  invalidated (terms are immutable); bindings/memos referencing node
  ids stay correct. Workspace growth is bounded by total distinct
  terms the pass produces.
- **Memo persistence.** `net_cache` entries keyed `(state, node)` are
  pure functions of structure — valid for the workspace's lifetime,
  not per subject or per iteration. Only nodes created by rewriting
  evaluate fresh.
- **Dirty propagation.** A node whose rewrite result changes marks
  only its ancestors for re-evaluation — iteration k+1 re-runs
  `lookup`/`apply` on O(Δ·depth) nodes, not the whole tree. (The
  memoized net makes even a full re-walk cheap; the dirty set makes
  it precise.)
- **`FixpointNoCycle` for free.** A rewrite producing a previously
  seen term hits the same interned node id — cycle detection is
  `node_id ∈ seen` set membership, no `isequal` walks.
- **Budget.** A `maxiterations` bound caps the loop; per-iteration
  `maxsteps` stays per site as before.

The same machinery serves `RestartedChain`: its "restart on change"
is exactly a one-level fixpoint — restart marks the produced term's
ancestors dirty and re-evaluates.

## 8. Result/binding semantics for rules

- Determinism: candidate order = declaration order; match enumeration
  = engine order — `simplify`-grade determinism.
- RHS receives `SubstitutionView` (fast path) or `MarkersMap` via
  `materialize` when it needs persistence.
- `RhsPlan` splices segment captures positionally from `binds` —
  no dict involved; `instantiate` remains for the public template
  path.

## 9. Milestones

1. `feat/rule-objects` — `mmrule`, `RhsPlan` templates, callable
   `RuleSet` + Phase-1 index, engine `reset!` (workspace-owned subject),
   task-local workspace, native `rewrite` pass, `Fixpoint` with dirty
   propagation (§7). *Tests: SU combinator compatibility where reused
   (Chain/IfElse/RestartedChain via SymbolicUtils.Rewriters), workspace
   reuse invariants, fixpoint incremental-evaluation oracle vs full
   re-walk.*
2. `feat/rewrite-bench` — simplify-shaped workload benchmark
   (~50–100 rules × deep subjects) vs SU's `@rule`/`@acrule` path.
3. `feat/discrim-net` — Phase-2 net + `net_cache`; oracle: `lookup`
   survivors identical to Phase-1 buckets on the fuzz corpus.
4. `feat/eachmatch_at` — expose the workspace traversal as the public
   occurrence-search API (TODO item) built on the same machinery.

## 10. Open questions

- Multi-result rules: SU's `acrule` applies on permutations — for a
  `match` (first-result) contract the deterministic order may pick a
  different first match than SU's enumeration; decide whether
  `mmrule` needs a `try_all` mode emitting all results.
- Net states for `optional` positions need parallel with/without
  edges — arity-class accounting gets subtle; confirm against §4.7.
- Whether `RuleSet` should dedup identical LHS patterns (map one
  `Matcher` to several RHSs) — cheap at compile time, worth doing in
  Phase 1.
