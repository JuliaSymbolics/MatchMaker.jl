# MatchMaker.jl

MatchPy-style symbolic pattern matching for [SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl),
built on its `IRStructure` DAG representation.

The user-facing guide is [`docs/src/guide.md`](docs/src/guide.md)
(`julia docs/make.jl` builds the full Documenter site, including a
tutorial and organized API reference); the governing design document
is [`DESIGN.md`](DESIGN.md); developer-facing documentation is
[`DEVELOPING.md`](DEVELOPING.md).

## What it is

Patterns are ordinary symbolic expressions containing *marker terms* —

```julia
slot(x)      # matches exactly one term            (MatchPy Wildcard.dot)
segment(x)   # matches a run/sub-multiset of args  (MatchPy Wildcard.star/plus)
optional(x)  # may be absent, binding a default    (MatchPy Optional)
```

where `x` is a plain symbolic variable whose `symtype` is the type
constraint. Predicates, `min`/`max` bounds, and defaults live in an external
`VarSpec` table supplied to `compile_pattern(expr; vars)`, not in the
expression — so patterns stay readable and specs stay swappable.

```julia
m = compile_pattern(slot(a) + slot(b) * sin(slot(c));
                    vars = Dict(c => slotspec(predicate = iszero)))
match(m, expr)
matches(m, expr)        # lazy, resumable
boundmatches(m, expr)   # persistent lazy snapshots — cheap to collect
eachmatch(f, m, expr)   # zero-allocation iteration
matches_at(m, expr)     # where in expr does m match? — (bindings, subterm)
instantiate(rhs, subst)
```

`compile_pattern` produces a `Matcher` once and any query runs it
repeatedly; queries also take the raw pattern expression for one-shot
use. `matchall` enumerates every match deterministically; `maxsteps`
bounds the search; `Constraint`s prune partial assignments early.

Rules and rewriting are built on the same machinery:

```julia
rules = compile_rules(CompiledRule[
    mmrule(slot(a) + 0 => slot(a)),
    mmrule(slot(a) + slot(a) => 2 * slot(a)),
], DiscrimNet)             # or default BucketIndex
ws = RuleWorkspace(rules)  # the mutable application context
ws(x + 0)                  # => x  (first-match site application)
rewrite(ws, expr)          # full-tree pass (:post or :pre)
fixpoint_rewrite(ws, expr) # iterate to a fixed point (incremental)
```

Matching is done by a non-recursive frame machine over `IRStructure`, with
associative/commutative/AC matching implemented via bipartite-assignment
enumeration in the Eker/MatchPy lineage. Semantics, caveats, and the full
API are in [`docs/src/guide.md`](docs/src/guide.md); correctness is
cross-validated against a naive recursive oracle under randomized fuzzing.

## Why

- Patterns are symbolic expressions, not `@rule`-style syntax — slot/segment/
  optional declarations are visible in the tree and disambiguated by
  `isequal`.
- `IRStructure` gives the whole subject DAG up front: interned nodes,
  O(1)-ish identity checks, no recursion, and amortization across patterns
  — the many-to-one story behind `RuleSet`/`DiscrimNet` dispatch.
- Type-stable internals: Moshi ADTs, `FunctionWrappers`-stored callables,
  fast-pathed trait/symtype checks.

## References

Algorithms adapted from MatchPy and the matching literature are cited inline
in the source (`file::function` for MatchPy, section for papers).

- M. Krebber, H. Barthels, P. Bientinesi. *MatchPy: A Pattern Matching
  Library*. SciPy 2017.
- M. Krebber, H. Barthels, P. Bientinesi. *Efficient Pattern Matching in
  Python*. PyHPC/SC workshops 2017. arXiv:1710.00077
- M. Krebber. *Non-linear Associative-Commutative Many-to-One Pattern
  Matching with Sequence Variables*. MSc thesis, RWTH Aachen, 2017.
  arXiv:1705.00907
- M. Krebber, H. Barthels. *MatchPy: Pattern Matching in Python*. JOSS 3(26),
  2018.
- [HPAC/matchpy source tree](https://github.com/HPAC/matchpy) (MIT)
- S. M. Eker. *Associative-Commutative Matching Via Bipartite Graph
  Matching*. Computer Journal 38(5), 1995.
- T. Uno. *Algorithms for Enumerating All Perfect, Maximum and Maximal
  Matchings in Bipartite Graphs*. ISAAC 1997.
- J. E. Hopcroft, R. M. Karp. *An n^{5/2} Algorithm for Maximum Matchings in
  Bipartite Graphs*. SIAM J. Comput. 2(4), 1973.
- D. Benanav, D. Kapur, P. Narendran. *Complexity of Matching Problems*.
  RTA 1985 / J. Symb. Comput. 3(1–2), 1987.
- L. Bachmair, T. Chen, I. V. Ramakrishnan. *Associative-Commutative
  Discrimination Nets*. TAPSOFT 1993.
- R. Sekar, R. Ramesh, I. V. Ramakrishnan. *Adaptive Pattern Matching*.
  SIAM J. Comput. 24(6), 1995.

## License

MIT — see `LICENSE`. Adopted references and dependencies: all MIT except
Graphs.jl (BSD-2-Clause); see `DESIGN.md` §14 for the full table.
