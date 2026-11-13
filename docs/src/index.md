```@meta
CurrentModule = MatchMaker
```

# MatchMaker.jl

Julia-native symbolic pattern matching and rewriting for
[SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl)
expressions: literals, slots, sequence captures, optional positions,
and associative/commutative matching with deterministic enumeration.

```@example
using MatchMaker, SymbolicUtils
```

## Which API should I use?

| I want to… | Use |
|---|---|
| test whether a pattern matches a subject | [`match`](@ref) |
| get every match as dictionaries | [`matchall`](@ref) |
| stream matches lazily | [`matches`](@ref) / [`boundmatches`](@ref) |
| count or compare matches cheaply | [`boundmatches`](@ref) / [`boundmatchall`](@ref) |
| find *where* a pattern matches inside a subject | [`boundmatches_at`](@ref) / [`matches_at`](@ref) |
| substitute bindings into a template | [`instantiate`](@ref) |
| rewrite a term with rules | [`mmrule`](@ref) + [`RuleWorkspace`](@ref) |
| rewrite a whole tree | [`rewrite`](@ref) |
| rewrite to a fixed point | [`fixpoint_rewrite`](@ref) |
| customize matching engine internals | [`MatchEngine`](@ref) + [`next_match!`](@ref) |

## The mental model

1. **Compile once** — [`compile_pattern`](@ref) builds a [`Matcher`](@ref)
   (or [`mmrule`](@ref)/[`ruleset`](@ref) for rewriting); the
   compiled form is immutable and shareable.
2. **Match at sites** — the match functions drive a [`MatchEngine`](@ref)
   over the pattern; results arrive as bindings keyed by variable `Sym`.
3. **Consume results** — lazily (`SubstitutionView`, `BoundMatch`) or
   materialized (`MarkersMap`), then [`instantiate`](@ref) into a
   template or feed [`RuleWorkspace`](@ref) rewrites.

See the [Tutorial](tutorial.md) for a worked end-to-end example and the
[user guide](guide.md) for the semantics reference.
