# DESIGN.md §5.3, §5.6: Bindings, trail, Substitution + SubstitutionView.

###
### Substitution (§5.6)
###

"""
    Substitution <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

A materialized match: variable `Sym` → bound expression. Segment variables
bind to the reconstructed `f(captured…)` under their parent head (§5.6), so
the value type is uniformly `BasicSymbolic{SymReal}`.

Key lookup is normalized through [`unwrap_varspec`](@ref): `d[x]`,
`d[slot(x)]`, `d[segment(x)]`, `d[optional(x)]` all resolve to the same
variable. Keys are stored as inner `Sym`s only — `keys`/`iterate` therefore
yield plain symbolic variables.
"""
struct Substitution <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
    dict::Dict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
end

const _SubDict = Dict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

Substitution() = Substitution(_SubDict())
function Substitution(kvs::Pair...)
    d = _SubDict()
    for (k, v) in kvs
        d[unwrap_varspec(k)] = v
    end
    return Substitution(d)
end

Base.getindex(s::Substitution, @nospecialize(k)) = s.dict[unwrap_varspec(k)]
Base.get(s::Substitution, @nospecialize(k), @nospecialize(dflt)) =
    get(s.dict, unwrap_varspec(k), dflt)
Base.get!(s::Substitution, @nospecialize(k), @nospecialize(dflt)) =
    get!(s.dict, unwrap_varspec(k), dflt)
Base.haskey(s::Substitution, @nospecialize(k)) = haskey(s.dict, unwrap_varspec(k))
Base.setindex!(s::Substitution, v::BasicSymbolic{SymReal}, @nospecialize(k)) =
    setindex!(s.dict, v, unwrap_varspec(k))
Base.delete!(s::Substitution, @nospecialize(k)) = (delete!(s.dict, unwrap_varspec(k)); s)
Base.empty!(s::Substitution) = (empty!(s.dict); s)
Base.iterate(s::Substitution, state...) = iterate(s.dict, state...)
Base.length(s::Substitution) = length(s.dict)
Base.isempty(s::Substitution) = isempty(s.dict)
Base.keys(s::Substitution) = keys(s.dict)
Base.values(s::Substitution) = values(s.dict)
Base.copy(s::Substitution) = Substitution(copy(s.dict))
