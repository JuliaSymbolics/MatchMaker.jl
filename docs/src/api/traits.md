```@meta
CurrentModule = MatchMaker
```

# Operation traits

Traits describe algebraic structure of operation heads — associativity
and commutativity change how pattern children match subject arguments;
`identity_element` supplies the element a segment binds under an
"empty" capture where the head has one.

```@docs
is_associative
is_commutative
identity_element
OperationTraits
OperationTraitsCtx
set_operation_traits
```
