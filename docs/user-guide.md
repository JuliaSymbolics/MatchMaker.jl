# MatchMaker.jl user guide

MatchPy-style symbolic pattern matching for
[SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl):
literals, slots, sequence captures, optional positions, and
associative/commutative (AC) matching with deterministic enumeration.

```julia
using MatchMaker, SymbolicUtils
```

## Patterns

A pattern is an ordinary `BasicSymbolic{SymReal}` expression containing
*marker terms* — calls to the marker functions `slot`, `segment`, and
`optional` wrapping a plain symbolic variable:

```julia
@syms x y a b s t

slot(a)        # matches exactly one term        (MatchPy Wildcard.dot)
segment(s)     # matches a run of ≥0 args        (MatchPy Wildcard.star/plus)
optional(a)    # may be absent, binding a default (MatchPy Optional)
```

Everything else in the pattern is matched literally: other calls match
subject calls with the same operation, plain syms match themselves.

```julia
pat = slot(a) + b * slot(t)          # a + b*t — b is a literal here
m = compile_pattern(pat)
match(m, x + b * z)                  # MarkersMap(a => x, t => z)
```

Marker terms can be built inline (`slot(a)`) or declared up front with
[`@slots`](@ref)/[`@segments`](@ref), which create the variable and bind
its marker form in one call:

```julia
@slots a::Real b    # a ≡ slot(a), b ≡ slot(b) — already markers
@segments s         # s ≡ segment(s)
pat = a + s
```

A variable's `symtype` *is* its type constraint: `slot(a::Real)` built
from an `a` of `symtype <: Real` only binds `Real`-typed subjects.
The same `Sym` used in two marker occurrences is *the same variable* —
see [non-linear patterns](#non-linear-patterns).

## The `vars` table

Predicates, bounds, and defaults live outside the expression, in the
`vars` map passed to `compile_pattern` — patterns stay readable and
specs stay swappable:

```julia
vars = Dict(
    a => slotspec(predicate = p -> p > 0),
    s => segmentspec(SymbolicUtils.issym; min = 1),
    b => slotspec(default = 5),
)
m = compile_pattern(pat; vars)
```

**`slotspec(predicate = nothing; default = nothing)`**

- `predicate` — `f(e) -> Bool` applied to the candidate before binding.
- `default` — the value bound by an `optional` position when the slot
  isn't consumed; non-symbolic values are `Const`-wrapped automatically.

**`segmentspec(predicate = nothing, sequence_predicate = nothing; min = 0, max = typemax(Int))`**

- `predicate` — `f(e) -> Bool` applied to *each* captured element.
- `sequence_predicate` — `f(vec) -> Bool` applied to the complete
  capture; sees the whole collection at once.
- `min`/`max` — capture-length bounds.

The two predicates have different pruning power. Under an **ordered**
head the capture is a contiguous run: if `predicate` rejects element
`i`, every run including `i` fails, so the run stops growing there —
`predicate` is a hard prune and `sequence_predicate` only invalidates
the current length (matching retries longer runs). Under an
**unordered** head the capture is a sub-multiset: a `predicate`-failing
element rejects only the combinations that contain it — other
selections still bind.

## Operation traits

A pattern head's behavior is declared with
`set_operation_traits(headsym; commutative, associative, identity)`;
the builtins `+` and `*` are already AC with identities `0`/`1`:

```julia
g = set_operation_traits(g; commutative = true)
f = set_operation_traits(f; associative = true, commutative = true,
                           identity = :f0)      # f() ≡ :f0
```

- **Associative**: nested same-head calls flatten —
  `f(p, f(q, r))` has the arg view `[p, q, r]`. Additionally, a
  non-`f` subject (or a zero-arg `f` subject) coerces to the
  one-argument view `[subject]` whenever `f` declares an `identity` —
  so `x + segment(s)` matches `x` with `s ↦ 0`.
- **Commutative**: positions dispatch over any unused subject arg;
  segments capture *sub-multisets* rather than contiguous runs.
- Both together give AC matching (the `+`/`*` behavior).

## Matching semantics

**Ordered heads** (free or associative-only) match children
positionally; `segment` captures contiguous runs, `optional` positions
try to consume the next arg first and enumerate the default second.

**Unordered heads** (commutative or AC) assign non-segment positions
to distinct subject args; `segment` positions take sub-multisets of
the leftover pool; `optional` positions try any leftover arg first,
then the default.

**Segments under `+`/`*` and declared identities.** An empty capture
materializes as the head's identity: `x + segment(s)` on `x` binds
`s ↦ 0`, `f(...)` on `f()` binds `s ↦ f0` for `identity = :f0`. An
empty capture under a generic head with no identity materializes as
the zero-arg term `f()`. A *single-element* capture materializes as
the element itself (`+(x) ≡ x`); `segment` values are otherwise the
head applied to the captures — `s ↦ f(p, q)`.

**`optional` positions** are only legal under associative or AC heads
(the head must be able to "grow" an argument list to accommodate the
slot being present or absent) and the variable must have a `default`
in `vars` — both checked at `compile_pattern` time.

## Non-linear patterns

The same variable `Sym` in two or more marker occurrences binds once
and is rechecked by `isequal` at subsequent occurrences:

```julia
matchall(compile_pattern(f(slot(a), slot(a))), f(p, p))  # a ↦ p
matchall(compile_pattern(f(slot(a), slot(a))), f(p, q))  # []
matchall(compile_pattern(f(segment(s), segment(s))), f(x, x, y, y))
```

A bound *segment* rechecks its captured run elementwise — under
unordered heads the run must appear as a sub-multiset of the
remaining pool, in pool order.

## Head slots

A slot can match the *operation* itself: `slot(hd)(slot(a))` binds
`hd` to the subject's operation and `a` to its single argument —
`slot(hd)(slot(a))` on `sin(x)` gives `hd ↦ sin, a ↦ x`. Bound head
variables carry their traits: a `slot(hd)(...)` binding `+` is
treated as an AC head for that match.

## Constraints

`Constraint(fn, vars)` registers a cross-variable check: `fn` is
called with the bound values in `vars` order and must return `Bool`.
Constraints fire *as soon as* every listed variable is bound —
pruning partial assignments before deeper positions dispatch:

```julia
cn = Constraint(v -> !isequal(v[1], v[2]), [a, b])
matchall(pat, subj; constraints = [cn])
```

## Querying

| API | Result |
|---|---|
| `match(m, s)` | first `MarkersMap` or `nothing` |
| `matches(m, s)` | lazy iterator of `MarkersMap` |
| `matchall(m, s)` | `collect(matches(...))` |
| `eachmatch(f, m, s)` | zero-materialization callback; stops when `f` returns `false` |
| `instantiate(rhs, subst)` | substitute bindings into a template |

All query entry points accept a pattern expression *or* a compiled
`Matcher` (compile once, match many), plus the kwargs
`constraints = Constraint[]` and `maxsteps = typemax(Int)` — a hard
budget on total engine steps; the iterator simply ends early when it
runs out, yielding a truncated result set.

`match` and `matches` items are persistent `MarkersMap`s.
`eachmatch` hands `f` a `SubstitutionView` — a live read-only view
valid only inside the callback; copy with `materialize(view)` to keep
a result without paying `MarkersMap` construction per step.

Enumeration is **deterministic**: positions dispatch left-to-right
over raw `arguments` order, and distinct assignments produce distinct
result entries — so `matchall` may contain identical binding maps
when two assignments bind the same values (MatchPy semantics).

## Instantiation

`instantiate(rhs, subst)` substitutes bindings into a template
expression, splicing segment captures into `segment` positions:

```julia
instantiate(slot(a) + segment(s), {a => x, s => p + q})   # x + p + q
```

- a `segment` position splices its captured args into the parent call;
  an identity-valued capture (e.g. `s ↦ 0` under `+`) splices nothing.
- a *single-element* capture materializes as one arg (`s ↦ p` splices
  `p`), never dropped — including non-identity `Const`s.
- head-slot binds (`hd ↦ +`) materialize as the bound operation.

## The normalization caveat

Patterns are normalized by the algebra at **construction** time, before
the matcher sees them:

```julia
slot(x) * slot(x)   # ≡ slot(x)^2      — one pow node, not two slots
slot(x) + slot(x)   # ≡ 2 * slot(x)    — coefficient, not two slots
```

This matches Mathematica semantics (`x_ * x_` ≡ `x_^2`) and is correct,
but non-obvious: a "repeated slot" inside the same `+`/`*` collapses
before matching. Similarly `p * slot(a)` is a `Mul` whose pattern
children are the coefficient `p` and `slot(a)`, and subject `Mul`s
canonicalize the same way — which is why coefficient-splitting behaves
predictably under `*`. Literal matching of un-normalized trees is out
of scope (it would need a `TreeReal` pattern domain).

## Complexity notes

General AC matching is **NP-complete** — bipartite-assignment
enumeration can blow up exponentially in pathological cases. With
*linear* patterns (each variable occurs at most once) it is polynomial —
`O(|p|·|s|³)`, where `|p|` is the number of pattern positions and `|s|`
the number of subject arguments under the AC head — and the engine
front-loads candidate rejection (fail-fast before dispatch) so linear
patterns are fast in practice. `maxsteps` bounds the search when a
pattern/subject pair would otherwise enumerate forever — the result is a
truncated prefix of the deterministic enumeration, not an error.

Matching is otherwise linear-in-`matchall`-output in the same way as
MatchPy: sequence captures and unordered assignment are the dominant
costs; `eachmatch` over a compiled `Matcher` is the zero-allocation
iteration path.
