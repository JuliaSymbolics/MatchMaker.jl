# DESIGN.md §3.1–3.3: marker terms, VarSpec ADT, constructors, macros,
# FunctionWrapper aliases.

###
### Marker singletons (§3.1)
###

"""
    SlotMarker

Singleton type of the `slot` pattern-variable marker (MatchPy
`Wildcard.dot`). The marker object itself is the `operation` of the marker
term, so detection is the O(1) identity check `operation(ex) === slot`.
"""
struct SlotMarker end

"""
    SegmentMarker

Singleton type of the `segment` pattern-variable marker (MatchPy
`Wildcard.star`/`plus`). See [`SlotMarker`](@ref).
"""
struct SegmentMarker end

"""
    OptionalMarker

Singleton type of the `optional` pattern-variable marker (MatchPy
`Optional`). An `optional(x)` occurrence is a slot that may instead bind the
variable's `VarSpec.Slot.default`. See [`SlotMarker`](@ref).
"""
struct OptionalMarker end

"""
    slot(x)

Create a *slot* marker term wrapping the symbolic variable `x`: a
`BasicSymbolic{SymReal}` `Term` whose `operation` is the `slot` singleton.
`x` may be a `Sym` (wrapped as-is) or a `Symbol` (a fresh `Sym` is created;
`type`/`shape` keywords apply). The inner `Sym`'s `symtype` is the type
constraint — see DESIGN.md §3.1.
"""
const slot = SlotMarker()

"""
    segment(x)

Create a *segment* marker term wrapping `x`: matches a contiguous run
(free/associative heads) or a sub-multiset (commutative/AC heads) of an
argument list. See [`slot`](@ref).
"""
const segment = SegmentMarker()

"""
    optional(x)

Create an *optional* marker term wrapping `x`: a slot occurrence that may
instead bind the variable's `VarSpec.Slot.default` (the default lives in the
spec, not in the tree). See [`slot`](@ref).
"""
const optional = OptionalMarker()

Base.show(io::IO, ::SlotMarker) = print(io, "slot")
Base.show(io::IO, ::SegmentMarker) = print(io, "segment")
Base.show(io::IO, ::OptionalMarker) = print(io, "optional")

"""
    is_marker_op(op) -> Bool

Whether `op` is one of the pattern-variable marker objects (`slot`,
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
    is_marker_term(x) -> Bool

Whether `x` is a marker term — a call headed by `slot`, `segment`, or
`optional`.
"""
is_marker_term(@nospecialize(x)) = iscall(x) && is_marker_op(operation(x))

"""
    is_pattern_var(x) -> Bool

Alias of [`is_marker_term`](@ref): whether `x` is a pattern-variable
declaration (`slot(x)`, `segment(x)`, `optional(x)`). A bare `Sym` always
returns `false` — variable-ness is only known relative to a pattern (see
DESIGN.md §3.1).
"""
is_pattern_var(@nospecialize(x)) = is_marker_term(x)

"""
    unwrap_varspec(x)

If `x` is a marker term, return its inner `Sym`; otherwise return `x`
unchanged. Used for variable identity (DESIGN.md §3.1) and for key
normalization in `Substitution` (§5.6).
"""
unwrap_varspec(x::BasicSymbolic) = is_marker_term(x) ? arguments(x)[1] : x
unwrap_varspec(@nospecialize(x)) = x

"""
    varsym(x) -> Sym

The inner `Sym` of a marker term. Throws `ArgumentError` if `x` is not a
marker term.
"""
function varsym(@nospecialize(x))
    is_marker_term(x) || throw(ArgumentError("not a pattern variable marker term: $x"))
    return arguments(x)[1]
end

###
### Marker term construction
###

"""
    _marker_term(m, x::BasicSymbolic{SymReal}) -> BasicSymbolic{SymReal}

Build the marker term `m(x)` — a `Term` whose operation is `m` and whose
symtype/shape mirror the inner `Sym` (the marker stands in for a value of
that type at its position). `x` must be a `Sym`; terms and other nodes are
rejected.
"""
function _marker_term(m, x::BasicSymbolic{SymReal})
    issym(x) || throw(ArgumentError(
        "pattern variable argument must be a Sym, got: $x"))
    return term(m, x; type = symtype(x), shape = shape(x))
end
_marker_term(m, @nospecialize(x)) = throw(ArgumentError(
    "pattern variable argument must be a Sym or a Symbol name, got: $x"))

function _make_varsym(name::Symbol, type, shape)
    if shape === nothing
        Sym{SymReal}(name; type)
    else
        Sym{SymReal}(name; type, shape)
    end
end

(::SlotMarker)(x::BasicSymbolic{SymReal}) = _marker_term(slot, x)
(::SegmentMarker)(x::BasicSymbolic{SymReal}) = _marker_term(segment, x)
(::OptionalMarker)(x::BasicSymbolic{SymReal}) = _marker_term(optional, x)
(m::Union{SlotMarker, SegmentMarker, OptionalMarker})(x::Symbol;
        type = Number, shape = nothing) =
    _marker_term(m, _make_varsym(x, type, shape))
(m::Union{SlotMarker, SegmentMarker, OptionalMarker})(@nospecialize x) =
    _marker_term(m, x)

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
    min >= 0 || throw(ArgumentError("segment min must be >= 0, got: $min"))
    max >= min || throw(ArgumentError("segment max must be >= min, got: $max < $min"))
    return VarSpec.Segment(
        _to_pred(predicate), _to_seqpred(sequence_predicate), Int(min), Int(max))
end

###
### Macros (§3.3)
###

"""
    @slot x

Produce the expression `slot(x)` for an existing symbolic `x`.
"""
macro slot(ex)
    ex isa Symbol || error("@slot expects a variable name, got: $ex")
    return Expr(:call, GlobalRef(@__MODULE__, :slot), esc(ex))
end

function _vars_macro(marker::GlobalRef, xs)
    isempty(xs) && return Expr(:tuple)
    assigns = Expr[]
    names = Symbol[]
    for x in xs
        if Meta.isexpr(x, :(::), 2)
            name, T = x.args
            name isa Symbol ||
                error("@slots/@segments expect `name` or `name::Type`, got: $x")
            push!(assigns, :($(esc(name)) =
                ($marker)($(QuoteNode(name)); type = $(esc(T)))))
            push!(names, name)
        elseif x isa Symbol
            push!(assigns, :($(esc(x)) = ($marker)($(QuoteNode(x)))))
            push!(names, x)
        else
            error("@slots/@segments expect `name` or `name::Type`, got: $x")
        end
    end
    return Expr(:block, assigns..., Expr(:tuple, esc.(names)...))
end

"""
    @slots x y::Real ...

Create slot variables: `x = slot(Sym(:x))`, `y = slot(Sym(:y; type = Real))`.
Minimal grammar — `name` and `name::Type` only; richer specs go through the
`vars` map of `compile_pattern` (DESIGN.md §3.3).
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
