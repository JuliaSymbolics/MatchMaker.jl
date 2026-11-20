```@meta
CurrentModule = MatchMaker
```

# Rewriting

`mmrule` compiles rules (bare `lhs => rhs` pairs also convert — see
[`CompiledRule`](@ref)); `RuleSet(rules, index)` bundles them; a
`RuleWorkspace` owns the mutable state and is itself the first-match
rewriter callable. `rewrite`/`fixpoint_rewrite` are the native tree
passes. [`set_rhs!`](@ref) replaces a rule's rhs in place — every
workspace on the set observes the update, so swap only between passes;
`copy` the set first to isolate the original.

## Rules

```@docs
mmrule
CompiledRule
RhsPlan
RhsT
copy(::CompiledRule)
```

## Compiled rule sets and dispatch

```@docs
RuleSet
RuleIndex
BucketIndex
DiscrimNet
set_rhs!
copy(::RuleSet)
```

## The workspace and rewrite passes

```@docs
RuleWorkspace
rewrite
fixpoint_rewrite
```

## Deprecated

```@docs
compile_rules
```
