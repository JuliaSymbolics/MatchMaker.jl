# Developing MatchMaker.jl

Navigation and implicit contracts. The *why* lives in `DESIGN.md` — source
comments reference its sections as `DESIGN.md §x.y`; this file covers the
*where* and the cross-file invariants you must not break.

## File map (DESIGN.md §6)

| File | Owns |
|---|---|
| `src/patternvars.jl` | Marker singletons (`slot`/`segment`/`optional`), `unwrap_varspec`, `is_pattern_var`, `varsym`, the `VarSpec` ADT, `slotspec`/`segmentspec`, `@slot`/`@slots`/`@segments` |
| `src/traits.jl` | `is_associative`/`is_commutative`/`identity_element` + `@nospecialize`d fast-path wrappers |
| `src/compile.jl` | `compile_pattern`, `Matcher`, `NodePlan` ADT, `vars`-map merge, all compile-time validation |
| `src/bindings.jl` | `Bindings`, trail ops, `MarkersMap`, `SubstitutionView`, `materialize` |
| `src/engine.jl` | `MatchEngine`, `MatchFrame` ADT, the advance loop, `iterate`/`next_match!` |
| `src/matchers/primitives.jl` | Leaf logic: literal/ground compare, slot bind/recheck — *no frames* |
| `src/matchers/seq.jl` | `Seq` frame (free heads, positional children) |
| `src/matchers/commutative.jl` | `Comm` frame (C-not-A heads: permutations → inner `Seq`) |
| `src/matchers/associative.jl` | `Assoc` frame (A heads: contiguous split enumeration; also free-head segments) |
| `src/matchers/ac.jl` | `AC` frame: Phase-1 candidates, Phase-2 bipartite assignment (Hopcroft–Karp + Uno enumeration), Phase-3 leftover distribution |
| `src/instantiate.jl` | `instantiate` (segment splicing) |
| `src/api.jl` | Public entry points: `match`, `matches`, `matchall`, `eachmatch`, `compile_pattern` |

`src/MatchMaker.jl` declares deps and includes only — no logic.

## Test map

| Location | Contents |
|---|---|
| `test/unit/` | Per-source-file unit suites |
| `test/oracle.jl` | The naive reference matcher (~200 lines, self-contained enumeration helpers) — **defines the semantics** |
| `test/fuzz.jl` | Seeded generator cross-validating engine vs oracle on *sets* of substitutions |
| `test/matchpy/` | Tests translated from MatchPy's suite; each cites `tests/test_*.py::test_…` |
| `test/literature/` | Cases from the matching literature, source-annotated |
| `test/qa.jl`, `test/jet.jl` | Aqua + JET |

## Implicit contracts

These are the invariants that are *not* expressed in types — violating one
produces silent misbehavior, not a compile error:

1. **Frame protocol** (§5.4): a `step!` must return exactly one of
   `:produced` / `:matched` / `:failed`. On `:failed` the frame must leave the
   trail unwound to its own mark; on `:produced` every new binding must be
   trail-recorded. A frame may not allocate a new enumerator object per step —
   its resumption state lives in the frame itself.
2. **Trail contract** (§5.3): bindings are restored by *marks*, not by
   copying the store. `binds.node[i] == 0` means unbound; `binds.seq[i]` is
   meaningful only while the frame that filled it is alive; `seg_op[i]` is
   set on segment bind (even empty captures) and cleared on unwind.
3. **Variable identity** (§3.1): a variable is the inner `Sym` — an `IdDict`
   key, `===`-identity. Marker terms never appear in `var_of`. Any `Sym` in
   the pattern that is a marked var anywhere must be marker-wrapped
   everywhere (compile error otherwise).
4. **Bindings are indices** (§4.2): `Int32` subject-node ids / `SmallV{Int32}`
   captures. Expressions are materialized only at `MarkersMap` time.
   Never store `BasicSymbolic`s in engine state.
5. **Enumeration order** (§4.8): AC/A subject args in `sorted_arguments`
   order; AC candidates by ascending count; splits shortest-first; optional
   consume-then-default. `AddMul`'s raw `arguments()` order is *never* used
   for matching decisions — only `sorted_arguments` (hash-order-dependent
   behavior is a doc bug unless marked order-dependent).
6. **`SubstitutionView` staleness** (§5.6): a view is valid only until the
   next engine step. The debug staleness flag exists to catch violations;
   `materialize` for anything that outlives the step.
7. **IR assumptions** (§1.4): pattern and subject IRs are immutable for the
   life of the engine; hashconsing means `===` implies `isequal` (fast path),
   not the converse. `===` on heads is valid for function heads only.
8. **Spec reads** (§3.1): `VarSpec` is an ADT — `@match` destructure, don't
   test variant tags with `isa`. Predicate fields are `Union{Nothing,FW}` —
   check `nothing` before calling; never call unconditionally.

## Verification commands

```bash
# tests (full suite) — test deps live in [extras]/[targets] of Project.toml
julia --project=. -e 'using Pkg; Pkg.test()'

# or with jld (warm, per project):
jld --test run test/runtests.jl

# type-stability spot checks (see §9)
jld eval 'using MatchMaker; @code_typed MatchMaker.compile_pattern(...)'
jld eval 'using Cthulhu; descend(MatchMaker.next_match!, ...)'
```

Conventions: Conventional Commits, feature branches, DocStringExtensions
docstrings on public API + non-trivial types, narrow arg annotations,
concrete or small-union returns. Adapted MatchPy algorithms carry a
`# Adapted from matchpy/<file>::<function>` comment.

Formatting: all source is formatted with Runic (`runic --inplace src test
benchmark`) — run it before every commit. DESIGN.md/DEVELOPING.md changes go
in their own `docs:` commits, never mixed with code.
