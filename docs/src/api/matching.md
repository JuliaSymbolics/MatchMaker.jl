```@meta
CurrentModule = MatchMaker
```

# Matching

Compile a pattern once, then match it against subjects. All match
functions accept a `Matcher` or a raw expression (compiled via
[`compile_pattern`](@ref)); `constraints` takes cross-variable
[`Constraint`](@ref)s and `maxsteps` bounds engine work.

## Compilation

```@docs
compile_pattern
Matcher
```

## First match

```@docs
match
```

## Enumerating matches

```@docs
matches
matchall
boundmatches
boundmatchall
eachmatch
```

## Occurrence search — match sites inside a subject

```@docs
boundmatches_at
matches_at
BoundMatchAtIterator
```

## Cross-variable constraints

```@docs
Constraint
```

## Instantiation

```@docs
instantiate
```
