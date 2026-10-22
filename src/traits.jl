# DESIGN.md §3.5: operation traits + @nospecialize'd fast-path wrappers.

###
### OperationTraitsCtx — the metadata channel for symbolic heads
###

"""
    OperationTraitsCtx

Metadata context key (a `DataType`, per the SymbolicUtils metadata
convention) under which an [`OperationTraits`](@ref) value is stored on a
symbolic head `Sym`. This is the only channel that can mark a *symbolic*
function as associative/commutative — the analogue of MatchPy's per-
`Operation` flags (DESIGN.md §3.5).
"""
struct OperationTraitsCtx end

"""
    OperationTraits(; associative = false, commutative = false,
                    identity = nothing)

Value stored under [`OperationTraitsCtx`](@ref) on a symbolic head:
associativity/commutativity flags and an optional `identity` element used for
singleton-subject coercion (DESIGN.md §4.6).
"""
struct OperationTraits
    associative::Bool
    commutative::Bool
    identity::Any
end
OperationTraits(;
    associative::Bool = false, commutative::Bool = false,
    identity = nothing
) =
    OperationTraits(associative, commutative, identity)

"""
    set_operation_traits(f::BasicSymbolic{SymReal}; associative = false,
                         commutative = false, identity = nothing)

Attach an [`OperationTraits`](@ref) entry to the symbolic head `f` (must be a
`Sym`, typically with `FnType` symtype) and return it. The returned `Sym` is
used as the operation in patterns/subjects; trait lookups read its metadata.
"""
function set_operation_traits(
        f::BasicSymbolic{SymReal}; associative::Bool = false,
        commutative::Bool = false, identity = nothing
    )
    issym(f) || throw(
        ArgumentError(
            lazy"operation traits attach to a Sym head, got: $f"
        )
    )
    return setmetadata(
        f, OperationTraitsCtx,
        OperationTraits(associative, commutative, identity)
    )
end

###
### Public traits (§3.5)
###

"""
    is_associative(f, ::Type{ST}) -> Bool

Whether `f(x, f(y, z)) ≡ f(f(x, y), z)` for calls whose result symtype is
`ST`. Extension point: add methods for your own functions. For *symbolic*
heads, traits come from [`OperationTraitsCtx`](@ref) metadata on the head
`Sym` (MatchPy per-`Operation` `associative` flag, [R1, R3]).
"""
is_associative(@nospecialize(f), ::Type) = false

"""
    is_commutative(f, ::Type{ST}) -> Bool

Whether `f(x, y) ≡ f(y, x)` for calls whose result symtype is `ST`.
See [`is_associative`](@ref).
"""
is_commutative(@nospecialize(f), ::Type) = false

"""
    identity_element(f, ::Type{ST}) -> Union{Any, Nothing}

An `e` such that `f(e, x) ≡ x` for result symtype `ST`, or `nothing` if none
is declared. Used for singleton-subject coercion (DESIGN.md §4.6).
"""
identity_element(@nospecialize(f), ::Type) = nothing

# `+`/`*` are AC with identity 0/1 for numeric result types (§3.5).
is_associative(::Union{typeof(+), typeof(*)}, ::Type{<:Number}) = true
is_commutative(::Union{typeof(+), typeof(*)}, ::Type{<:Number}) = true
identity_element(::typeof(+), ::Type{<:Number}) = 0
identity_element(::typeof(*), ::Type{<:Number}) = 1

# Symbolic heads read traits from OperationTraitsCtx metadata on the head
# `Sym` — the only channel available for commutative symbolic functions.
function is_associative(f::BasicSymbolic{SymReal}, ::Type{ST}) where {ST}
    issym(f) && hasmetadata(f, OperationTraitsCtx) || return false
    return (getmetadata(f, OperationTraitsCtx)::OperationTraits).associative
end
function is_commutative(f::BasicSymbolic{SymReal}, ::Type{ST}) where {ST}
    issym(f) && hasmetadata(f, OperationTraitsCtx) || return false
    return (getmetadata(f, OperationTraitsCtx)::OperationTraits).commutative
end
function identity_element(f::BasicSymbolic{SymReal}, ::Type{ST}) where {ST}
    issym(f) && hasmetadata(f, OperationTraitsCtx) || return nothing
    return getmetadata(f, OperationTraitsCtx).identity
end

###
### Fast-path wrappers — the engine calls these, never the traits directly
###

# @nospecialize: `op`/`ST` are uninferrable at call sites, so a specialized
# method would be reached only through dynamic dispatch anyway. One compiled
# body; the common-case enumeration runs inside it (§3.5, §9). Unlike the
# design's schematic there is deliberately no `op isa Function → false` path:
# users extend traits on their own functions, so any op we do not enumerate
# must reach the trait fallback.

"""
    _is_number_st(T::SymbolicUtils.TypeT) -> Bool

Common numeric symtypes checked by `===` first; the general `<: Number`
check is the cold fallback (subtype checks are not free — §9).
"""
_is_number_st(@nospecialize(T::SymbolicUtils.TypeT)) =
    T === Number || T === Real || T === Integer || T === Int ||
    T === Float64 || T === Float32 || T === Rational{Int} ||
    T === Bool || T <: Number

"""
    _is_ac_head(op, ST::SymbolicUtils.TypeT) -> Bool

Whether `op` is associative *and* commutative for result symtype `ST` —
`+`/`*` on numeric symtypes take the fast path; everything else falls through
to the extensible traits (including `OperationTraitsCtx` symbolic heads).
"""
function _is_ac_head(@nospecialize(op), @nospecialize(ST::SymbolicUtils.TypeT))
    if op === (+) || op === (*)
        _is_number_st(ST) && return true
    end
    return is_associative(op, ST) && is_commutative(op, ST)
end

"""
    _is_associative_head(op, ST::SymbolicUtils.TypeT) -> Bool

See [`_is_ac_head`](@ref). Fast path for `+`/`*` on numeric symtypes.
"""
function _is_associative_head(@nospecialize(op), @nospecialize(ST::SymbolicUtils.TypeT))
    (op === (+) || op === (*)) && _is_number_st(ST) && return true
    return is_associative(op, ST)
end

"""
    _is_commutative_head(op, ST::SymbolicUtils.TypeT) -> Bool

See [`_is_ac_head`](@ref). Fast path for `+`/`*` on numeric symtypes.
"""
function _is_commutative_head(@nospecialize(op), @nospecialize(ST::SymbolicUtils.TypeT))
    (op === (+) || op === (*)) && _is_number_st(ST) && return true
    return is_commutative(op, ST)
end

"""
    _identity_el(op, ST::SymbolicUtils.TypeT)

The declared identity element for `op` at result symtype `ST`, or `nothing`.
Fast path: `+`/`0`, `*`/`1` on numeric symtypes.
"""
function _identity_el(@nospecialize(op), @nospecialize(ST::SymbolicUtils.TypeT))
    op === (+) && _is_number_st(ST) && return 0
    op === (*) && _is_number_st(ST) && return 1
    return identity_element(op, ST)
end
