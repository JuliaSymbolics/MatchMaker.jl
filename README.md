# MatchMaker.jl

[![Dev docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://juliasymbolics.github.io/MatchMaker.jl/dev/)
[![Build Status](https://github.com/JuliaSymbolics/MatchMaker.jl/workflows/Tests/badge.svg)](https://github.com/JuliaSymbolics/MatchMaker.jl/actions?query=workflow%3ATests)

MatchPy-style symbolic pattern matching and rewriting for
[SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl),
built on its `IRStructure` DAG representation.

Patterns are ordinary symbolic expressions containing slot, segment, and
optional marker terms — not `@rule`-style syntax — compiled once into a
reusable `Matcher`. Matching is performed by a non-recursive frame machine
with associative/commutative/AC matching via bipartite-assignment
enumeration in the Eker/MatchPy lineage, and rules/rewriting (discrimination
networks, workspaces, fixpoint rewriting) are built on the same machinery.

## Why

- Pattern declarations are visible in the expression tree and disambiguated
  by `isequal`; predicates, bounds, and defaults live in a swappable
  `VarSpec` table.
- `IRStructure` exposes the whole subject DAG up front — interned nodes,
  identity checks, no recursion — enabling many-to-one matching via
  `RuleSet`/`DiscrimNet` dispatch.
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
