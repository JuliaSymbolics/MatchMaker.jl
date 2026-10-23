# DESIGN.md §5.6: SubstitutionView + public match API.

###
### SubstitutionView (§5.6)
###

# Debug staleness flag (§5.6): when true, views verify their step stamp on
# access and throw on stale reads.
const _STRICT_VIEWS = Ref{Bool}(false)

"""
    SubstitutionView <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

A read-only view of a match's live engine bindings (DESIGN.md §5.6): variable
`Sym` → bound expression, resolved lazily. Valid only until the next
`eachmatch`/`iterate` step mutates the bindings — copy with
[`materialize`](@ref) to keep results. With `_STRICT_VIEWS[] = true` stale
access throws.
"""
struct SubstitutionView <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
    eng::MatchEngine
    stamp::Int
end

function _check_stale(v::SubstitutionView)
    _STRICT_VIEWS[] && v.stamp != v.eng.steps && throw(
        AssertionError("stale SubstitutionView — engine advanced past this view")
    )
    return nothing
end

function _var_bound(eng::MatchEngine, vid::Int32)
    b = eng.binds
    return is_bound_node(b, vid) || b.seg_op[vid] !== nothing ||
        is_bound_extra(eng.binds, vid)
end

Base.getindex(v::SubstitutionView, k::BasicSymbolic{SymReal}) = begin
    _check_stale(v)
    ks = unwrap_varspec(k)
    vid = v.eng.pat.var_of[ks]
    _var_bound(v.eng, vid) || throw(KeyError(ks))
    return _bound_value(v.eng, vid)
end
Base.haskey(v::SubstitutionView, k::BasicSymbolic{SymReal}) = begin
    _check_stale(v)
    ks = unwrap_varspec(k)
    haskey(v.eng.pat.var_of, ks) || return false
    return _var_bound(v.eng, v.eng.pat.var_of[ks])
end
function Base.iterate(v::SubstitutionView, state = 1)
    _check_stale(v)
    nvars = v.eng.pat.nvars
    i = state
    while i <= nvars && !_var_bound(v.eng, Int32(i))
        i += 1
    end
    i > nvars && return nothing
    sym = v.eng.pat.var_syms[i]
    return (sym => _bound_value(v.eng, Int32(i))), i + 1
end
Base.length(v::SubstitutionView) = begin
    _check_stale(v)
    return count(vid -> _var_bound(v.eng, Int32(vid)), 1:v.eng.pat.nvars)
end

"""
    $TYPEDSIGNATURES

Copy a [`SubstitutionView`](@ref) into a persistent [`MarkersMap`](@ref).
"""
function Base.materialize(v::SubstitutionView)
    _check_stale(v)
    d = _MarkersMapDict()
    eng = v.eng
    for vid in Int32(1):Int32(eng.pat.nvars)
        _var_bound(eng, vid) || continue
        d[eng.pat.var_syms[vid]] = _bound_value(eng, vid)
    end
    return MarkersMap(d)
end

###
### Public API (§5.6)
###

"""
    MatchIterator

Lazy iterator over successive matches — one [`MarkersMap`](@ref) per state.
"""
struct MatchIterator
    eng::MatchEngine
end
Base.IteratorSize(::Type{MatchIterator}) = Base.SizeUnknown()
function Base.iterate(it::MatchIterator, state = nothing)
    next_match!(it.eng) || return nothing
    return materialize(SubstitutionView(it.eng, it.eng.steps)), nothing
end

"""
    $TYPEDSIGNATURES

The first match of pattern `m` (a `Matcher` or a raw expression, compiled
via [`compile_pattern`](@ref)) against subject `s`, as a [`MarkersMap`](@ref)
or `nothing`. `constraints` is a collection of [`Constraint`](@ref)s.
"""
function match(m::Matcher, s::BasicSymbolic{SymReal}; constraints = Constraint[])
    eng = MatchEngine(m, s, constraints)
    next_match!(eng) || return nothing
    return materialize(SubstitutionView(eng, eng.steps))
end
match(p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; constraints = Constraint[]) =
    match(compile_pattern(p), s; constraints)

"""
    $TYPEDSIGNATURES

Lazy iterator of all matches of `m` against `s`; each item is a
[`MarkersMap`](@ref).
"""
matches(m::Matcher, s::BasicSymbolic{SymReal}; constraints = Constraint[]) =
    MatchIterator(MatchEngine(m, s, constraints))
matches(p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; constraints = Constraint[]) =
    matches(compile_pattern(p), s; constraints)

"""
    $TYPEDSIGNATURES

`collect(matches(m, s))` — all matches as a `Vector{MarkersMap}`.
"""
matchall(m, s::BasicSymbolic{SymReal}; constraints = Constraint[]) =
    collect(matches(m, s; constraints))

"""
    $TYPEDSIGNATURES

Call `f(::SubstitutionView)` on each successive match of `m` against `s`;
stops when `f` returns `false`. The zero-allocation hot path for rewriters —
the view is valid only inside `f` (DESIGN.md §5.6).
"""
function eachmatch(
        f::F, m::Matcher, s::BasicSymbolic{SymReal};
        constraints = Constraint[]
    ) where {F}
    eng = MatchEngine(m, s, constraints)
    while next_match!(eng)
        f(SubstitutionView(eng, eng.steps)) === false && break
    end
    return nothing
end
eachmatch(
    f::F, p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal};
    constraints = Constraint[]
) where {F} =
    eachmatch(f, compile_pattern(p), s; constraints)
