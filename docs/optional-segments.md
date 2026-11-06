# Optional sequence wildcards — support analysis

MatchPy's `Optional(wildcard, default)` wraps any wildcard; ours supports
optional *slots* only (`optional(x)` → `VarSpec.Slot` with a `default`).
The MatchPy one-to-one port (`test/matchpy/one_to_one.jl`) therefore
skips the optional-sequence cases (`oa__`/`oa___`, and `oa_` cases
where the subject leaves ≥2 args for an optional dot under A/AC).

Capture-wise, an optional sequence is a `min = 0` segment. The two
deltas:

1. **Empty capture binds `default`**, not the empty run/identity —
   which is also why MatchPy allows `oa__` under heads with *no*
   identity (`f(oa__)` vs `f()` → `o ↦ a`). `VarSpec.Segment` currently
   has no `default` field and `optional(x)` is slot-kind, so the
   spec/marker layer needs extending regardless.
2. **`oa_` under A/AC absorbs multi-arg leftovers** — MatchPy's dot is
   a sequence matcher under associative heads: it takes *all* leftover
   args and materializes 1 → bare element, ≥2 → `head(...)`, 0 →
   default. Our slot optional consumes at most one arg.

## Per-case work breakdown

| Case | MatchPy semantics | Required work | Size | Perf impact |
|---|---|---|---|---|
| Optional slot, free head `f(a, oa_)` | consume 1 arg else default | Route free-head calls containing optionals to `SeqCall` (the Seq frame's `is_opt_pos`/`_opt_default!` already implements consume-or-default); lift compile restriction | Small (~15 lines) | Negligible — one extra alternative per optional |
| Optional slot, comm head `f_c(a, oa_)` | same, unordered | `CommCall` already partitions `optionals` and `min_tail` counts them as 0; `_step_comm!` needs AC's default branch (`ac.jl` ~lines 176–183) + lift restriction | Small-medium (~30 lines) | Negligible |
| Optional sequence, free head `f(a, oa__)` → `o ↦ (b,c)` or default | run capture; empty → default | Spec: `default` on `VarSpec.Segment` (or a new marker); engine: `_seg_advance!` len-0 → `_opt_default!`-style `extra` bind; materialization via `extra`, not `_seg_value`; non-linear recheck defines extra-vs-run | Medium (~100 lines) | None vs `x___` — the empty alternative is already enumerated |
| Optional sequence, assoc/AC `f_a(oa__)`, `f_ac(oa___)` | sub-multiset capture; empty → default | Same spec/engine work; the Comm/AC combination machinery already emits the empty selection for `min=0` — add bind-default-on-empty | Medium (shared with above) | None — enumeration space unchanged |
| Optional dot absorbing leftovers `f_a(a,b,c)` vs `f_a(a,oa_)` → `o ↦ f_a(b,c)` | under A/AC a dot is a sequence: takes *all* leftovers; 1 → bare, ≥2 → `head(...)`, 0 → default | Optional segment + head-wrap materialization. Under Seq: capture-all-leftover (no length enumeration needed when last). Under AC: dispatches as a segment position (leftover machinery exists) | Medium, on top of optional segments | Same as a `min=0` segment position |
| Multiple / same-var optionals `f(a, oa_, oa_)` → `o ↦ a` | second occurrence rechecks the bound *value* (default) | `_opt_default!` already rechecks bound slots vs default; optional segments need extra-vs-run recheck semantics — the fiddliest decision, small code | Small addendum | Negligible |
| `f(a,b,c)` vs `f(a,oa_)` → `[]` | dot takes ≤1 under non-assoc | Free — falls out of slot-optional support | — | — |
| Identity heads `f_i`/`f_ci` | subject coerces to a singleton under a non-assoc identity head | Orthogonal feature: `_seq_args`-style coercion in `Call`/`Comm` arg views + 0-arity subjects | Medium | One branch at frame init |

## Notes

- **Ordering.** MatchPy tries the consume-alternative before the
  default and dispatches optional positions before sequence positions —
  matching our `optionals`-then-`segments` phase order, so enumeration
  order is preserved.
- **Perf summary.** Everything optional-segment-related is marginal
  cost on top of the existing `min = 0` machinery — the enumeration
  space is already generated; the deltas are a spec field, a
  bind-default branch, and materialization. Under AC an optional
  sequence would dispatch in the segment phase (sub-multiset
  enumeration), which is already the dominant combinatorial cost.
- **Design question.** The empty-capture binding representation:
  `extra = default` vs empty-run + a default-aware `_seg_value`. This
  decides how non-linear rechecks compare a defaulted occurrence
  against a captured run — see the ambiguous-materialization item in
  `TODO.md` for the related recheck question.
