```@meta
CurrentModule = MatchMaker
```

# The match engine

The engine is the mutable driver behind every match function — most
users never touch it. Reuse it via [`reset!`](@ref) when matching the
same pattern against many subjects, or drive it manually via
[`next_match!`](@ref) for custom enumeration.

```@docs
MatchEngine
next_match!
reset!
step!
MatchFrame
FrameStatus
```
