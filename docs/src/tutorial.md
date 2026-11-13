```@meta
CurrentModule = MatchMaker
```

# Tutorial

```@example tut
using MatchMaker, SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType
@syms x y z a b s t p q
```

## Patterns and matching

A pattern is an ordinary expression containing *marker terms*. `slot`
matches one term; `segment` matches a run of arguments; `optional`
binds a default when absent:

```@example tut
pat = slot(a) + b * slot(t)
m = compile_pattern(pat)
match(m, x + b * z)
```

The same `Sym` in two markers is one variable — non-linear patterns
just work:

```@example tut
match(slot(a) + slot(a), x + x)
match(slot(a) + slot(a), x + y) # nothing — different values
```

## Enumerating matches

`match` gives the first; `matchall` gives every binding:

```@example tut
matchall(segment(s) + slot(t), x + y + z)
```

Collect lazily to skip the dict-building — `boundmatches` yields
frozen `BoundMatch` snapshots you index like dictionaries:

```@example tut
[bm[t] for bm in boundmatches(segment(s) + slot(t), x + y + z)]
```

## Occurrence search

`boundmatches_at` / `matches_at` answer "where does this pattern match
inside the subject" — `(bindings, subterm)` pairs, deduplicated by
shared structure:

```@example tut
collect(matches_at(sin(slot(a)), x + sin(y) * sin(z)))
```

## Instantiation

Feed bindings back into a template with `instantiate` — segments
splice into the parent argument list:

```@example tut
subst = match(segment(s) + slot(t), x + y + z)
instantiate(slot(t) + y, subst)
```

## Rewriting

`mmrule` compiles `lhs => rhs` pairs; `RuleSet` bundles them
into an immutable rule set; a `RuleWorkspace` owns the mutable state and is
the rewriter callable:

```@example tut
rules = ruleset(CompiledRule[
    mmrule(slot(a) + slot(b) => slot(a) * slot(b)),
    mmrule(sin(slot(a)) => slot(a)),
])
ws = RuleWorkspace(rules)
ws(x + y)          # first match wins: x + y → x * y
ws(sin(p + q))     # one rule application per call: → p + q
```

`rewrite` walks the whole tree bottom-up; `fixpoint_rewrite` iterates
to a fixed point:

```@example tut
rewrite(ws, sin(x + y) * sin(p + q))
fixpoint_rewrite(ws, sin(x + y) + cos(p + q))
```

## Operation traits

Symbolic heads need declared traits — `set_operation_traits` marks a
function `Sym` associative/commutative so the matcher can reorder and
flatten:

```@example tut
myop = Sym{SymReal}(:myop; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
set_operation_traits(myop; associative = true)
match(myop(segment(s), slot(t)), myop(x, y, z))
```
