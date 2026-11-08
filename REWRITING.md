# Rewriting & many-to-one matching — design

This designs the `simplify`-scale use case: large rule sets applied to
large subjects under `SymbolicUtils.Rewriters`-style combinators. It
elaborates DESIGN.md §8 ("many-to-one outlook") and subsumes the
`eachmatch_at` TODO item — the shared workspace and the net evaluation
*are* the specialized occurrence-search machinery that item asks for.

Sections 1–4 are the near-term deliverable; §5 is the phased
many-to-one plan; §6–8 cover the shared workspace and growth bounds.

## 1. Semantics contract (port of `SymbolicUtils.Rewriters`)

A **rewriter** is `x -> Union{expr′, nothing}`: `nothing` means "did not
fire", anything else is the rewritten term. MatchMaker rule objects
satisfy this contract so the existing combinator ecosystem applies
verbatim.

We **reuse `SymbolicUtils.Rewriters` combinators directly** rather than
reimplementing them — they are generic over callables and already
carry the semantics `simplify` depends on. The port surface:

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
- `rhs` is either a symbolic template (`instantiate`'d per result) or
  a callable `f(view) -> expr` receiving the result view — stored as
  `Union{BasicSymbolic{SymReal}, RhsT}` (a `FunctionWrapper`, same
  convention as `PredT`/`ConstrT` in §3.2), so `apply` union-splits on
  a 2-member concrete union instead of calling `Any`.
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
    rhs::Union{BasicSymbolic{SymReal}, RhsT}   # template or callable
    name::Symbol
end
```

abstract type RuleIndex end
# lookup(ws, idx::RuleIndex, node) -> SmallV{Int32} of candidate rule ids

struct RuleSet{I <: RuleIndex}
    rules::Vector{CompiledRule}
    index::I                  # §5 — BucketIndex now, DiscrimNet later
end

compile_rules(rules) -> RuleSet     # build once, share globally, thread-safe
```

`RuleSet` is parametric on the index: an abstract `index::RuleIndex`
field would force dynamic dispatch on every `lookup` — the hot call
per subject node — while `RuleSet{I}`/`RuleApplier{I}` keep the whole
dispatch chain concrete (`BucketIndex` and `DiscrimNet` compile to
distinct applier code).

`RuleIndex` is the dispatch seam, not a concrete layout: Phase 1's
`BucketIndex` is a small op→rule-ids map plus spill lists; Phase 2's
`DiscrimNet` carries net states and transition tables. `lookup` is
the only operation both must implement, so the phases are A/B-able
behind one call site.

`RuleSet` is immutable after construction and safe to share across
tasks and calls — all mutable state lives in the workspace (§6). This
is the "shared global data structure": one `const`-held `RuleSet`,
compiled once, read by every rewrite pass.

`RuleApplier(ruleset; maxsteps = typemax(Int))` is a thin *callable*
binding a `RuleSet` to its task-local workspace — it exists so a
traversal has a plain `x -> expr′ | nothing` to invoke per node:

```julia
struct RuleApplier{I <: RuleIndex}
    set::RuleSet{I}
    maxsteps::Int
end

(rw::RuleApplier)(x) = begin
    ws = workspace(rw.set)            # task-local, §4
    for id in lookup(ws, rw.set.index, x)   # index → candidate rule ids
        y = apply(ws, rw.set.rules[id], x)
        y !== nothing && return y     # Chain(rws, true) semantics
    end
    return nothing
end
```

(`ws` is resolved per call rather than stored: a cached reference
would pin the wrong task's workspace if the applier crosses tasks.)


It is **not** the workspace — it carries no mutable state, only
`set`, the resolved `ws`, and per-use options (`maxsteps`). The
alternative shape `(rs::RuleSet)(x)` resolving `workspace(rs)`
internally is equivalent when no per-use options are needed; the
wrapper exists so options can vary per call site without touching
the shared ruleset.

## 4. `RuleWorkspace` — bounded reuse

```julia
mutable struct RuleWorkspace
    subj::IRStructure{SymReal}          # one per application site, shared
    engines::Vector{Union{Nothing,MatchEngine}}  # per rule id, lazy
    net_cache::Dict{Tuple{Int32,Int32}, SmallV{Int32}}  # Phase-2 only
end
```

The workspace holds **engine state only** — the rules themselves are
immutable in `RuleSet`. Concretely: one subject `IRStructure`
populated once per application site and shared by every rule engine;
a lazily-created `MatchEngine` per rule id (`reset!` between sites,
not re-allocated); and `net_cache`, used only by Phase 2 — a memo
`(net_state_id, subj_node) → surviving rule ids`. Because subject IR
nodes are interned, a DAG-shared subterm evaluates the net once per
state instead of once per occurrence. Phase 1 leaves `net_cache`
empty — the bucket `lookup` needs no per-node memo.

One workspace per `RuleSet` **per task**, keyed by the `RuleSet` object
in `task_local_storage` (project compat is Julia 1.10, so
`task_local_storage`, not `Base.ScopedValues`):

```julia
workspace(rs::RuleSet) =
    get!(task_local_storage(), rs)::RuleWorkspace
```

- Same `RuleSet` across threads → distinct workspaces; no locks.
- One IR per subject *per pass*: `populate_ir!` runs once per
  application site and every rule engine + the net share it — the
  `O(rules × |subject|)` IR cost collapses to `O(|subject|)`.

### `reset!` protocol (the reuse mechanism)

`MatchEngine` gets `reset!(eng, sroot)`:

- `sroot` becomes a mutable field (the only `const` that changes).
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

## 6. Traversal integration

`Postwalk(RuleApplier(rs))(expr)` is the canonical call: bottom-up, at
each rebuilt node the index selects candidates and each gets a real
`match`. `Prewalk`, `PassThrough`, `Fixpoint`, `Filter`, `IfElse`,
`Chain`, `RestartedChain` compose unchanged — they see a plain
callable.

- `IfElse` conditions that are *patterns* become `x -> match(m, x) !== nothing`
  — a `PatternCond` convenience wraps this.
- `RestartedChain`/`Fixpoint` resubjection: the produced term is a new
  subject → the workspace repopulates its IR per application site
  (cheap; interned terms dedup inside `populate_ir!`).
- `maxsteps` budgets per application site, shared across the site's
  candidate rules — not a global rewrite budget (that's a rewriter
  concern: `FixpointNoCycle` exists for termination).
- `threaded` walks: task-local workspaces make threaded `Walk` safe;
  document that `RuleApplier` must not be shared with an explicit
  workspace across tasks.

## 7. Result/binding semantics for rules

- Determinism: candidate order = declaration order; match enumeration
  = engine order — `simplify`-grade determinism.
- RHS receives `SubstitutionView` (fast path) or `MarkersMap` via
  `materialize` when it needs persistence.
- `instantiate` already splices segment captures — RHS templates need
  no new machinery.

## 8. Milestones

1. `feat/rule-objects` — `mmrule`, `RuleApplier`, `RuleSet` Phase-1
   index, `reset!` protocol, task-local workspace. *Tests: SU
   combinator compatibility (Chain/IfElse/RestartedChain via
   SymbolicUtils.Rewriters), workspace reuse invariants.*
2. `feat/rewrite-bench` — simplify-shaped workload benchmark
   (~50–100 rules × deep subjects) vs SU's `@rule`/`@acrule` path.
3. `feat/discrim-net` — Phase-2 net + `net_cache`; oracle: `lookup`
   survivors identical to Phase-1 buckets on the fuzz corpus.
4. `feat/eachmatch_at` — expose the workspace traversal as the public
   occurrence-search API (TODO item) built on the same machinery.

## 9. Open questions

- Multi-result rules: SU's `acrule` applies on permutations — for a
  `match` (first-result) contract the deterministic order may pick a
  different first match than SU's enumeration; decide whether
  `mmrule` needs a `try_all` mode emitting all results.
- Net states for `optional` positions need parallel with/without
  edges — arity-class accounting gets subtle; confirm against §4.7.
- Whether `RuleSet` should dedup identical LHS patterns (map one
  `Matcher` to several RHSs) — cheap at compile time, worth doing in
  Phase 1.
