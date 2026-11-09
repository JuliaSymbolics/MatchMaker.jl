# DESIGN.md §5.3, §5.6: Bindings, trail, MarkersMap + SubstitutionView.

###
### Bindings and trail (§5.3)
###

"""
    Bindings

Engine binding state (DESIGN.md §5.3). Slot binds are *subject IR indices*
— materialization happens only at `MarkersMap` time. Segment binds store
the captured argument list itself (`ArgsT`), head-neutral: a non-linear
segment re-checked under a different head compares the same arg list, and
`_rhs_eval` splices it without materializing a term first.
"""
struct Bindings
    "var_id -> bound subject node (`0` = unbound)."
    node::Vector{Int32}
    "var_id -> captured arg terms for segment vars."
    seq::Vector{ArgsT{SymReal}}
    "var_id -> the head a segment var captured under."
    seg_op::Vector{Any}
    "var_id -> non-node bound value (e.g. a head-slot var bound to a raw op)."
    extra::Vector{Any}
end

Bindings(nvars::Integer) = Bindings(
    zeros(Int32, nvars), [ArgsT{SymReal}() for _ in 1:nvars],
    fill(nothing, nvars), fill(nothing, nvars)
)

is_bound_node(b::Bindings, vid::Int32) = b.node[vid] != 0
is_bound_seq(b::Bindings, vid::Int32) = b.seg_op[vid] !== nothing
is_bound_extra(b::Bindings, vid::Int32) = b.extra[vid] !== nothing

"""
    Constraint(fn, vars)

A cross-variable constraint (DESIGN.md §4.9): `fn` is called with a
`Vector{BasicSymbolic{SymReal}}` of bound values in `vars` order and must
return `Bool`. Fires as soon as every variable in `vars` is bound.
`vars` elements are variable `Sym`s or marker terms.
"""
struct Constraint
    fn::ConstrT
    vars::Vector{BasicSymbolic{SymReal}}
end
Constraint(@nospecialize(fn), vars::AbstractVector{<:BasicSymbolic{SymReal}}) =
    Constraint(
    ConstrT(fn), BasicSymbolic{SymReal}[unwrap_varspec(v) for v in vars]
)

# Engine-compiled constraint: resolved var ids.
struct EngineConstraint
    fn::ConstrT
    var_ids::SmallV{Int32}
end

###
### MarkersMap (§5.6)
###

const _MarkersMapDict = Dict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

"""
    MarkersMap <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

A materialized match: variable `Sym` → bound expression. Segment variables
bind to the reconstructed `f(captured…)` under their parent head (§5.6), so
the value type is uniformly `BasicSymbolic{SymReal}`.

Key lookup is normalized through [`unwrap_varspec`](@ref): `d[x]`,
`d[slot(x)]`, `d[segment(x)]`, `d[optional(x)]` all resolve to the same
variable. Keys are stored as inner `Sym`s only — `keys`/`iterate` therefore
yield plain symbolic variables.
"""
struct MarkersMap <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
    dict::_MarkersMapDict
end

MarkersMap() = MarkersMap(_MarkersMapDict())
function MarkersMap(kvs::Pair...)
    d = _MarkersMapDict()
    for (k, v) in kvs
        d[unwrap_varspec(k)] = v
    end
    return MarkersMap(d)
end

Base.getindex(s::MarkersMap, k::BasicSymbolic{SymReal}) =
    s.dict[unwrap_varspec(k)]
Base.get(s::MarkersMap, k::BasicSymbolic{SymReal}, dflt) =
    get(s.dict, unwrap_varspec(k), dflt)
Base.get!(s::MarkersMap, k::BasicSymbolic{SymReal}, dflt) =
    get!(s.dict, unwrap_varspec(k), dflt)
Base.haskey(s::MarkersMap, k::BasicSymbolic{SymReal}) =
    haskey(s.dict, unwrap_varspec(k))
Base.setindex!(s::MarkersMap, v::BasicSymbolic{SymReal}, k::BasicSymbolic{SymReal}) =
    setindex!(s.dict, v, unwrap_varspec(k))
Base.delete!(s::MarkersMap, k::BasicSymbolic{SymReal}) =
    (delete!(s.dict, unwrap_varspec(k)); s)
Base.empty!(s::MarkersMap) = (empty!(s.dict); s)
Base.isequal(s::MarkersMap, o::MarkersMap) = begin
    length(s.dict) == length(o.dict) || return false
    for (k, v) in s.dict
        haskey(o.dict, k) && isequal(o.dict[k], v) || return false
    end
    return true
end
Base.iterate(s::MarkersMap, state...) = iterate(s.dict, state...)
Base.length(s::MarkersMap) = length(s.dict)
Base.isempty(s::MarkersMap) = isempty(s.dict)
Base.keys(s::MarkersMap) = keys(s.dict)
Base.values(s::MarkersMap) = values(s.dict)
Base.copy(s::MarkersMap) = MarkersMap(copy(s.dict))
