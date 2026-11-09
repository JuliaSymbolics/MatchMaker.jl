```@meta
CurrentModule = MatchMaker
```

# Rewriting

`mmrule` compiles rules; `compile_rules` builds an immutable
`RuleSet`; a `RuleWorkspace` owns the mutable state and is itself the
first-match rewriter callable. `rewrite`/`fixpoint_rewrite` are the
native tree passes.

## Rules

```@docs
mmrule
CompiledRule
RhsPlan
RhsT
```

## Compiled rule sets and dispatch

```@docs
compile_rules
RuleSet
RuleIndex
BucketIndex
DiscrimNet
```

## The workspace and rewrite passes

```@docs
RuleWorkspace
rewrite
fixpoint_rewrite
```
