```@meta
CurrentModule = MatchMaker
```

# Patterns

Marker terms build patterns out of ordinary `BasicSymbolic`
expressions; `VarSpec`s in the `vars` map of [`compile_pattern`](@ref)
attach predicates, bounds, and defaults.

## Marker terms

```@docs
slot
segment
optional
param
```

## Variable specs

```@docs
VarSpec
slotspec
segmentspec
```

## Macros

```@docs
@slots
@segments
```

## Marker predicates and accessors

```@docs
is_marker_term
is_marker_op
is_slot_marker
is_segment_marker
is_param_term
is_param_op
unwrap_varspec
varsym
```
