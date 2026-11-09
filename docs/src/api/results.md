```@meta
CurrentModule = MatchMaker
```

# Results

Match results are bindings from variable `Sym` to bound expression,
exposed at three price points:

- **`SubstitutionView`** — zero-cost live view, valid only inside
  `eachmatch`'s callback or until the next `iterate` step.
- **`BoundMatch`** — frozen snapshot, lazy per-variable resolution;
  the cheap thing to *collect*.
- **`MarkersMap`** — fully materialized dictionary; the simple,
  self-contained result.

```@docs
MarkersMap
SubstitutionView
BoundMatch
materialize
MatchIterator
BoundMatchIterator
```
