# DESIGN.md §3.1–3.3: marker terms, VarSpec ADT, constructors, macros,
# FunctionWrapper aliases.

###
### Marker functions (§3.1)
###

# The markers are bare generic functions — not singleton structs — so a
# marker term is a `Term` whose `operation` is the function itself. Detection
# is the O(1) identity check `operation(ex) === slot`; printing, hashing, and
# `isequal` all handle generic-function heads natively.

"""
    slot(x)

Create a *slot* marker term wrapping the symbolic variable `x` (MatchPy
`Wildcard.dot`): a `BasicSymbolic{SymReal}` `Term` whose `operation` is the
`slot` function. `x` may be a `Sym` (wrapped as-is) or a `Symbol` (a fresh
`Sym` is created; `type`/`shape` keywords apply). The inner `Sym`'s
`symtype` is the type constraint — see DESIGN.md §3.1.
"""
function slot end

"""
    segment(x)

Create a *segment* marker term wrapping `x` (MatchPy `Wildcard.star`/`plus`):
matches a contiguous run (free/associative heads) or a sub-multiset
(commutative/AC heads) of an argument list. See [`slot`](@ref).
"""
function segment end

"""
    optional(x)

Create an *optional* marker term wrapping `x` (MatchPy `Optional`): a slot
occurrence that may instead bind the variable's `VarSpec.Slot.default` (the
default lives in the spec, not in the tree). See [`slot`](@ref).
"""
function optional end

"""
    _Marker

Union of the three marker-function types — the common signature for their
call methods and for `promote_symtype`/`promote_shape` extensions.
"""
const _Marker = Union{typeof(slot), typeof(segment), typeof(optional)}

# A marker term stands in for a value of the inner sym's type/shape at its
# position, so `term(m, x)` and `maketerm`-driven rebuilds inherit it. The
# `TypeT`/`ShapeT` annotations keep these strictly more specific than
# SymbolicUtils' varargs fallbacks (no ambiguity).
SymbolicUtils.promote_symtype(::_Marker, t::SymbolicUtils.TypeT) = t
SymbolicUtils.promote_shape(::_Marker, s::SymbolicUtils.ShapeT) = s

# Built directly on BSImpl.Term with an explicit ArgsT/type/shape — skips
# `term`'s promote_symtype/promote_shape calls (we already know both are the
# inner sym's). The promote_* methods above still matter for maketerm-driven
# rebuilds.
function (m::_Marker)(x::BasicSymbolic{SymReal})
    issym(x) || throw(ArgumentError(lazy"$m expects a Sym, got: $x"))
    return BSImpl.Term{SymReal}(m, ArgsT{SymReal}((x,));
                                type = symtype(x), shape = shape(x))
end

function (m::_Marker)(x::Symbol; type = Number, shape = nothing)
    s = shape === nothing ? Sym{SymReal}(x; type) : Sym{SymReal}(x; type, shape)
    return BSImpl.Term{SymReal}(m, ArgsT{SymReal}((s,));
                                type = symtype(s), shape = SymbolicUtils.shape(s))
end

###
### Marker predicates and accessors
###

"""
    is_marker_op(op) -> Bool

Whether `op` is one of the pattern-variable marker functions (`slot`,
`segment`, `optional`). Identity comparison only — never allocates.
"""
is_marker_op(@nospecialize(op)) = op === slot || op === segment || op === optional

"""
    is_slot_marker(op) -> Bool

Whether `op` declares a *slot-kind* variable (`slot` or `optional`).
"""
is_slot_marker(@nospecialize(op)) = op === slot || op === optional

"""
    is_segment_marker(op) -> Bool

Whether `op` declares a *segment-kind* variable.
"""
is_segment_marker(@nospecialize(op)) = op === segment

"""
    is_marker_term(x::BasicSymbolic) -> Bool

Whether `x` is a marker term — a `Term` headed by `slot`, `segment`, or
`optional`. Matches the `Term` variant directly (rather than
`iscall`/`operation`, which `@match` over every symbolic variant).
"""
is_marker_term(x::BasicSymbolic) = @match x begin
    BSImpl.Term(; f) => is_marker_op(f)
    _ => false
end

"""
    unwrap_varspec(x::BasicSymbolic) -> BasicSymbolic

If `x` is a marker term, return its inner `Sym`; otherwise return `x`.
Used for key normalization in `Substitution` (DESIGN.md §5.6). Variable
*identity* does not need this — equal marker terms hashcons to the same
node, so `===`/`isequal` on the terms themselves suffices (§3.1).
"""
function unwrap_varspec(x::BasicSymbolic)
    return @match x begin
        BSImpl.Term(; f, args) => is_marker_op(f) ? args[1] : x
        _ => x
    end
end

"""
    varsym(x::BasicSymbolic) -> Sym

The inner `Sym` of a marker term. Throws `ArgumentError` if `x` is not a
marker term.
"""
function varsym(x::BasicSymbolic)
    return @match x begin
        BSImpl.Term(; f, args) => is_marker_op(f) ? args[1] :
            throw(ArgumentError(lazy"not a pattern variable marker term: $x"))
        _ => throw(ArgumentError(lazy"not a pattern variable marker term: $x"))
    end
end

###
### FunctionWrapper aliases (§3.2)
###

"""
    PredT

`FunctionWrapper` signature for per-variable predicates:
`(candidate::BasicSymbolic{SymReal}) -> Bool`.
"""
const PredT = FunctionWrapper{Bool, Tuple{BasicSymbolic{SymReal}}}

"""
    SeqPredT

`FunctionWrapper` signature for segment whole-capture predicates:
`(capture::Vector{BasicSymbolic{SymReal}}) -> Bool`.
"""
const SeqPredT = FunctionWrapper{Bool, Tuple{Vector{BasicSymbolic{SymReal}}}}

"""
    ConstrT

`FunctionWrapper` signature for cross-variable constraints (DESIGN.md §4.9):
`(bindings::Vector{BasicSymbolic{SymReal}}) -> Bool`. A collection, not
splatted args — keeps the signature stable and avoids per-arity
specialization.
"""
const ConstrT = FunctionWrapper{Bool, Tuple{Vector{BasicSymbolic{SymReal}}}}

_to_pred(@nospecialize(f)) = f === nothing ? nothing : PredT(f)
_to_seqpred(@nospecialize(f)) = f === nothing ? nothing : SeqPredT(f)

###
### VarSpec ADT (§3.1)
###

"""
    VarSpec

Per-variable spec record owned by a `Matcher` (DESIGN.md §3.1). A Moshi ADT —
kind is the variant tag, so per-kind field legality is structural:

- `VarSpec.Slot(predicate, default)` — `default === nothing` means required.
- `VarSpec.Segment(predicate, sequence_predicate, min, max)` — `min`/`max`
  bound capture cardinality (`0`/`typemax(Int)` = unbounded).

Non-parametric (`SymReal`-fixed) by choice: the predicate signatures are
`SymReal`-hardcoded regardless, so a type parameter would only decorate
`default` while being uninferrable at `nothing` — a future multi-vartype
revision should parameterize all fields together or none.

Destructure with `@match`; do not tag-check with `isa` (DEVELOPING.md §8).
"""
@data VarSpec begin
    struct Slot
        predicate::Union{Nothing, PredT}
        default::Union{Nothing, BasicSymbolic{SymReal}}
    end
    struct Segment
        predicate::Union{Nothing, PredT}
        sequence_predicate::Union{Nothing, SeqPredT}
        min::Int
        max::Int
    end
end

"""
    slotspec(; predicate = nothing, default = nothing) -> VarSpec.Slot

Build a slot `VarSpec` for the `vars` map of `compile_pattern`. `predicate`
is wrapped as a [`PredT`](@ref) `FunctionWrapper`; a non-symbolic `default`
is wrapped in `Const{SymReal}`.
"""
function slotspec(; predicate = nothing, default = nothing)
    d = if default === nothing
        nothing
    elseif default isa BasicSymbolic{SymReal}
        default
    else
        Const{SymReal}(default)
    end
    return VarSpec.Slot(_to_pred(predicate), d)
end

"""
    segmentspec(; predicate = nothing, sequence_predicate = nothing,
                min = 0, max = typemax(Int)) -> VarSpec.Segment

Build a segment `VarSpec` for the `vars` map of `compile_pattern`.
`predicate` applies to each captured element, `sequence_predicate` to the
whole capture. `0 <= min <= max` is enforced.
"""
function segmentspec(; predicate = nothing, sequence_predicate = nothing,
                     min::Integer = 0, max::Integer = typemax(Int))
    min >= 0 || throw(ArgumentError(lazy"segment min must be >= 0, got: $min"))
    max >= min || throw(ArgumentError(lazy"segment max must be >= min, got: $max < $min"))
    return VarSpec.Segment(
        _to_pred(predicate), _to_seqpred(sequence_predicate), Int(min), Int(max))
end

###
### Macros (§3.3)
###

"""
    @slots x y::Real f(a) ...

Create slot variables: `x = slot(Sym(:x))`, `y = slot(Sym(:y; type = Real))`,
`f = slot(Sym(:f; type = FnType{Tuple{...},...}))` for function-like heads.
Parsing is shared with `SymbolicUtils.@syms` (`parse_variable` +
`sym_from_parse_result`), so the grammar is the `@syms` one — `name`,
`name::Type`, `[shape]` suffixes, and `f(args)` function forms all work.
Predicates/bounds/defaults go through the `vars` map of `compile_pattern`,
not the macro (DESIGN.md §3.3).
"""
macro slots(xs...)
    _vars_macro(GlobalRef(@__MODULE__, :slot), xs)
end

"""
    @segments xs ys::Real ...

Create segment variables. See [`@slots`](@ref).
"""
macro segments(xs...)
    _vars_macro(GlobalRef(@__MODULE__, :segment), xs)
end

# Shared expansion for `@slots`/`@segments`: each argument is parsed with
# `SymbolicUtils.parse_variable`, built via `sym_from_parse_result` (the same
# code path `@syms` uses), and wrapped in the marker call.
function _vars_macro(marker::GlobalRef, xs)
    isempty(xs) && return Expr(:tuple)
    assigns = Any[]
    names = Any[]
    for x in xs
        nts = SymbolicUtils.parse_variable(x)
        create = SymbolicUtils.sym_from_parse_result(nts, SymReal)
        vname = (nts[:isruntime]::Bool) ? Symbol(nts[:name]) : esc(nts[:name])
        call = Expr(:call)
        append!(call.args, (marker, create))
        push!(assigns, Expr(:(=), vname, call))
        push!(names, vname)
    end
    blk = Expr(:block)
    append!(blk.args, assigns)
    tup = Expr(:tuple)
    append!(tup.args, names)
    push!(blk.args, tup)
    return blk
end
