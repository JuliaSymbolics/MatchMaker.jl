# DESIGN.md §3.1–3.3: marker terms, VarSpec ADT, constructors, macros,
# FunctionWrapper aliases.

###
### Marker functions (§3.1)
###

# The markers are bare generic functions so a marker term is a `Term` whose
# `operation` is the function itself.

"""
    $TYPEDSIGNATURES

Create a *slot* marker term wrapping the symbolic variable `x` —
matches exactly one subject term. `x` may be a `Sym` (wrapped as-is)
or a `Symbol` (a fresh `Sym` is created; `type`/`shape` keywords
apply). The inner `Sym`'s `symtype` is the type constraint.
"""
function slot end

"""
    $TYPEDSIGNATURES

Create a *segment* marker term wrapping `x`: matches a contiguous run (free/associative heads) or a sub-multiset
(commutative/AC heads) of an argument list. See [`slot`](@ref).
"""
function segment end

"""
    $TYPEDSIGNATURES

Create an *optional* marker term wrapping `x`: a slot occurrence that may instead bind the variable's `VarSpec.Slot.default` (the
default lives in the spec, not in the tree). See [`slot`](@ref).
"""
function optional end

"""
    _Marker

Union of the three marker-function types — the common signature for their
call methods and for `promote_symtype`/`promote_shape` extensions.
"""
const _Marker = Union{typeof(slot), typeof(segment), typeof(optional)}

SymbolicUtils.promote_symtype(::_Marker, t::SymbolicUtils.TypeT) = t
SymbolicUtils.promote_shape(::_Marker, @nospecialize(s::SymbolicUtils.ShapeT)) = s

# NOTE: `(m::_Marker)(x)` functor methods are not definable on Julia <1.11
# (method dispatch is unimplemented for Union-of-function signatures), so
# the call methods live on each concrete marker function type.
function _marker_term(m, x::BasicSymbolic{SymReal})
    issym(x) || throw(ArgumentError(lazy"$m expects a Sym, got: $x"))
    return BSImpl.Term{SymReal}(
        m, ArgsT{SymReal}((x,));
        type = symtype(x), shape = shape(x)
    )
end

function _marker_term(m, x::Symbol; type = Number, shape = nothing)
    s = shape === nothing ? Sym{SymReal}(x; type) : Sym{SymReal}(x; type, shape)
    return BSImpl.Term{SymReal}(
        m, ArgsT{SymReal}((s,));
        type = symtype(s), shape = SymbolicUtils.shape(s)
    )
end

(m::typeof(slot))(x; kw...) = _marker_term(m, x; kw...)
(m::typeof(segment))(x; kw...) = _marker_term(m, x; kw...)
(m::typeof(optional))(x; kw...) = _marker_term(m, x; kw...)

###
### Marker predicates and accessors
###

"""
    $TYPEDSIGNATURES

Whether `op` is one of the pattern-variable marker functions (`slot`,
`segment`, `optional`). Identity comparison only — never allocates.
"""
is_marker_op(@nospecialize(op)) = op === slot || op === segment || op === optional

"""
    $TYPEDSIGNATURES

Whether `op` declares a *slot-kind* variable (`slot` or `optional`).
"""
is_slot_marker(@nospecialize(op)) = op === slot || op === optional

"""
    $TYPEDSIGNATURES

Whether `op` declares a *segment-kind* variable.
"""
is_segment_marker(@nospecialize(op)) = op === segment

"""
    $TYPEDSIGNATURES

Whether `x` is a marker term — a `Term` headed by `slot`, `segment`, or
`optional`. Matches the `Term` variant directly (rather than
`iscall`/`operation`, which `@match` over every symbolic variant).
"""
is_marker_term(x::BasicSymbolic) = @match x begin
    BSImpl.Term(; f) => is_marker_op(f)
    _ => false
end

_is_slot_term(x::BasicSymbolic) = @match x begin
    BSImpl.Term(; f) => f === slot
    _ => false
end
_is_optional_term(x::BasicSymbolic) = @match x begin
    BSImpl.Term(; f) => f === optional
    _ => false
end
_is_segment_term(x::BasicSymbolic) = @match x begin
    BSImpl.Term(; f) => f === segment
    _ => false
end

"""
    $TYPEDSIGNATURES

If `x` is a marker term, return its inner `Sym`; otherwise return `x`.
Used for key normalization in `Substitution` (DESIGN.md §5.6).
"""
function unwrap_varspec(x::BasicSymbolic)
    return @match x begin
        BSImpl.Term(; f, args) => is_marker_op(f) ? args[1] : x
        _ => x
    end
end

"""
    $TYPEDSIGNATURES

The inner `Sym` of a marker term. Throws if `x` is not a marker term.
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

Per-variable spec record owned by a `Matcher` (DESIGN.md §3.1):

- `VarSpec.Slot(predicate, default)` — `default === nothing` means required.
- `VarSpec.Segment(predicate, sequence_predicate, min, max)` — `min`/`max`
  bound capture cardinality (`0`/`typemax(Int)` = unbounded).
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

# The `@data` ADT type (the module is `VarSpec`; its variants live inside).
const VarSpecT = VarSpec.Type

"""
    $TYPEDSIGNATURES

Build a slot `VarSpec` for the `vars` map of `compile_pattern`. A non-symbolic `default`
is wrapped in `Const{SymReal}`.
"""
function slotspec(predicate = nothing; default = nothing)
    # callables are stored in FunctionWrapper — no point specializing on them
    @nospecialize predicate
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
    $TYPEDSIGNATURES

Build a segment `VarSpec` for the `vars` map of `compile_pattern`.
`0 <= min <= max` is enforced.

Two predicate roles:

- `predicate` — applied to each captured element. A failing element
  rejects any capture containing it: under an ordered head (contiguous
  runs) the run stops growing entirely; under an unordered head
  (sub-multisets) only the combinations containing it are rejected.
- `sequence_predicate` — applied to the whole captured `Vector`.
  Failure only invalidates the current capture; the matcher retries
  with other lengths/selections, since another collection may satisfy
  it.

Prefer `predicate` for per-element checks — it prunes strictly more.
"""
function segmentspec(
        predicate = nothing, sequence_predicate = nothing;
        min::Integer = 0, max::Integer = typemax(Int)
    )
    @nospecialize predicate sequence_predicate
    min >= 0 || throw(ArgumentError(lazy"segment min must be >= 0, got: $min"))
    max >= min || throw(ArgumentError(lazy"segment max must be >= min, got: $max < $min"))
    return VarSpec.Segment(
        _to_pred(predicate), _to_seqpred(sequence_predicate), Int(min), Int(max)
    )
end

###
### Macros (§3.3)
###

"""
    @slots x y::Real f(a) ...

Create slot variables: `x = slot(Sym(:x))`, `y = slot(Sym(:y; type = Real))`,
`f = slot(Sym(:f; type = FnType{Tuple{...},...}))` for function-like heads.
Parsing is the same as `SymbolicUtils.@syms`.
"""
macro slots(xs...)
    return _vars_macro(GlobalRef(@__MODULE__, :slot), xs)
end

"""
    @segments xs ys::Real ...

Create segment variables. See [`@slots`](@ref).
"""
macro segments(xs...)
    return _vars_macro(GlobalRef(@__MODULE__, :segment), xs)
end

function _vars_macro(marker::GlobalRef, xs)
    isempty(xs) && return Expr(:tuple)
    blk = Expr(:block)
    tup = Expr(:tuple)
    for x in xs
        nts = SymbolicUtils.parse_variable(x)
        create = SymbolicUtils.sym_from_parse_result(nts, SymReal)
        vname = (nts[:isruntime]::Bool) ? Symbol(nts[:name]) : esc(nts[:name])
        call = Expr(:call)
        append!(call.args, (marker, create))
        push!(blk.args, Expr(:(=), vname, call))
        push!(tup.args, vname)
    end
    push!(blk.args, tup)
    return blk
end
