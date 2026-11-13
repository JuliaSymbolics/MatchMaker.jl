```@meta
CurrentModule = MatchMaker
```

# Rewriting

`mmrule` compiles rules; `RuleSet(rules, index)` bundles them
into an immutable rule set; a `RuleWorkspace` owns the mutable state and is itself the
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

## Deprecated

```@docs
compile_rules
```
