# DESIGN.md §5.3, §5.6: Bindings, trail, MarkersMap + SubstitutionView.

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
Base.iterate(s::MarkersMap, state...) = iterate(s.dict, state...)
Base.length(s::MarkersMap) = length(s.dict)
Base.isempty(s::MarkersMap) = isempty(s.dict)
Base.keys(s::MarkersMap) = keys(s.dict)
Base.values(s::MarkersMap) = values(s.dict)
Base.copy(s::MarkersMap) = MarkersMap(copy(s.dict))
