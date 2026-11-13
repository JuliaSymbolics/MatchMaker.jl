# DESIGN.md §5.6: SubstitutionView + public match API.

###
### SubstitutionView (§5.6)
###

# Debug staleness flag (§5.6): a compile-time preference — enable with
# `Preferences.set_preferences!(MatchMaker, "strict_views" => true)` and
# restart. When true, views verify their step stamp on access and throw
# on stale reads; when false the check folds away entirely.
const _STRICT_VIEWS = @load_preference("strict_views", false)

"""
    SubstitutionView <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

A read-only view of a match's live engine bindings, resolved lazily.
Valid only until the next `eachmatch`/`iterate` step mutates the
bindings — copy with [`materialize`](@ref) to keep results. With the
`strict_views` preference enabled, stale access throws.
"""
struct SubstitutionView <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
    eng::MatchEngine
    stamp::Int
end

function _check_stale(v::SubstitutionView)
    _STRICT_VIEWS && v.stamp != v.eng.steps && throw(
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
### BoundMatch — persistent lazy result
###

# Freeze the engine's binding state for a produced match. Per-var `seq`
# arg lists are copied so later search steps can't mutate the snapshot.
function _snapshot_binds(b::Bindings)
    seq = Vector{ArgsT{SymReal}}(undef, length(b.seq))
    for i in eachindex(seq)
        seq[i] = copy(b.seq[i])
    end
    return Bindings(
        copy(b.node), seq, copy(b.seg_op), copy(b.segval), copy(b.extra)
    )
end

"""
    BoundMatch <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}

A persistent match result — a frozen copy of the bindings, resolved
lazily on access. Returned by [`boundmatches`](@ref),
[`boundmatchall`](@ref), and [`boundmatches_at`](@ref); cheap to
collect when the consumer inspects only a few bound values per match.
Copy into a [`MarkersMap`](@ref) with [`materialize`](@ref).
"""
struct BoundMatch <: AbstractDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}
    pat::Matcher
    subj::IRStructure{SymReal}
    "symtype of the subject root (identity reconstruction)."
    sty::DataType
    binds::Bindings
end

function _bm_value(m::BoundMatch, vid::Int32)
    b = m.binds
    is_bound_extra(b, vid) && return Const{SymReal}(b.extra[vid])
    if b.seg_op[vid] !== nothing
        v = b.segval[vid]
        v === nothing && (
            v = b.segval[vid] = _seg_value(m.sty, b.seg_op[vid], b.seq[vid])
        )
        return v
    end
    is_bound_node(b, vid) || error(lazy"var $vid is not bound")
    return m.subj[b.node[vid]]
end

_bm_bound(m::BoundMatch, vid::Int32) = begin
    b = m.binds
    is_bound_node(b, vid) || b.seg_op[vid] !== nothing ||
        is_bound_extra(b, vid)
end

Base.getindex(m::BoundMatch, k::BasicSymbolic{SymReal}) = begin
    ks = unwrap_varspec(k)
    vid = m.pat.var_of[ks]
    _bm_bound(m, vid) || throw(KeyError(ks))
    return _bm_value(m, vid)
end
Base.haskey(m::BoundMatch, k::BasicSymbolic{SymReal}) = begin
    ks = unwrap_varspec(k)
    haskey(m.pat.var_of, ks) || return false
    return _bm_bound(m, m.pat.var_of[ks])
end
function Base.iterate(m::BoundMatch, state = 1)
    nvars = m.pat.nvars
    i = state
    while i <= nvars && !_bm_bound(m, Int32(i))
        i += 1
    end
    i > nvars && return nothing
    return (m.pat.var_syms[i] => _bm_value(m, Int32(i))), i + 1
end
Base.length(m::BoundMatch) = begin
    count(vid -> _bm_bound(m, Int32(vid)), 1:m.pat.nvars)
end

"""
    $TYPEDSIGNATURES

Copy a [`BoundMatch`](@ref) into a persistent [`MarkersMap`](@ref).
"""
function Base.materialize(m::BoundMatch)
    d = _MarkersMapDict()
    for vid in Int32(1):Int32(m.pat.nvars)
        _bm_bound(m, vid) || continue
        d[m.pat.var_syms[vid]] = _bm_value(m, vid)
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
Base.eltype(::Type{MatchIterator}) = MarkersMap
function Base.iterate(it::MatchIterator, state = nothing)
    next_match!(it.eng) || return nothing
    return materialize(SubstitutionView(it.eng, it.eng.steps)), nothing
end

"""
    BoundMatchIterator

Lazy iterator over successive matches — one [`BoundMatch`](@ref)
snapshot per state. Much cheaper per result than [`MatchIterator`](@ref)
(frozen binding state, no term reconstruction); materialize individual
results with [`materialize`](@ref).
"""
struct BoundMatchIterator
    eng::MatchEngine
end
Base.IteratorSize(::Type{BoundMatchIterator}) = Base.SizeUnknown()
Base.eltype(::Type{BoundMatchIterator}) = BoundMatch
function Base.iterate(it::BoundMatchIterator, state = nothing)
    next_match!(it.eng) || return nothing
    return (
        BoundMatch(
            it.eng.pat, it.eng.subj,
            symtype(it.eng.subj[it.eng.sroot]),
            _snapshot_binds(it.eng.binds)
        ),
        nothing,
    )
end

"""
    $TYPEDSIGNATURES

The first match of pattern `m` (a `Matcher` or a raw expression, compiled
via [`compile_pattern`](@ref)) against subject `s`, as a [`MarkersMap`](@ref)
or `nothing`. `constraints` is a collection of [`Constraint`](@ref)s.
"""
function match(
        m::Matcher, s::BasicSymbolic{SymReal};
        constraints = Constraint[], maxsteps::Int = typemax(Int)
    )
    eng = MatchEngine(m, s, constraints; maxsteps)
    next_match!(eng) || return nothing
    return materialize(SubstitutionView(eng, eng.steps))
end
match(
    p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; kwargs...
) = match(compile_pattern(p), s; kwargs...)

"""
    $TYPEDSIGNATURES

Lazy iterator of all matches of `m` against `s`; each item is a
[`MarkersMap`](@ref). `maxsteps` bounds total search steps — the iterator
ends when the budget is exhausted (a truncated result set).
"""
matches(
    m::Matcher, s::BasicSymbolic{SymReal};
    constraints = Constraint[], maxsteps::Int = typemax(Int)
) = MatchIterator(MatchEngine(m, s, constraints; maxsteps))
matches(p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; kwargs...) =
    matches(compile_pattern(p), s; kwargs...)

"""
    $TYPEDSIGNATURES

`collect(matches(m, s))` — all matches as a `Vector{MarkersMap}`.
"""
matchall(m, s; kwargs...) = collect(matches(m, s; kwargs...))

"""
    $TYPEDSIGNATURES

Lazy iterator of all matches of `m` against `s` like [`matches`](@ref),
but each item is a [`BoundMatch`](@ref): a persistent snapshot of the
index-only binding state that reconstructs segment terms on access.
Far cheaper per result than materializing a [`MarkersMap`](@ref) —
use it when collecting many results, or when the consumer reads only
a few bound values per match.
"""
boundmatches(
    m::Matcher, s::BasicSymbolic{SymReal};
    constraints = Constraint[], maxsteps::Int = typemax(Int)
) = BoundMatchIterator(MatchEngine(m, s, constraints; maxsteps))
boundmatches(p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; kwargs...) =
    boundmatches(compile_pattern(p), s; kwargs...)

"""
    $TYPEDSIGNATURES

`collect(boundmatches(m, s))` — all matches as a `Vector{BoundMatch}`.
The cheap `matchall` for enumeration-heavy workloads (~10× faster on
segment-heavy cases); [`materialize`](@ref) individual results to get
the same `MarkersMap`s `matchall` returns.
"""
boundmatchall(m, s; kwargs...) = collect(boundmatches(m, s; kwargs...))

"""
    $TYPEDSIGNATURES

Call `f(::SubstitutionView)` on each successive match of `m` against `s`;
stop when `f` returns `false`. The zero-allocation hot path (§5.6): the
view is only valid inside `f` — copy with `materialize` to keep results.
"""
function eachmatch(
        f::F, m::Matcher, s::BasicSymbolic{SymReal};
        constraints = Constraint[], maxsteps::Int = typemax(Int)
    ) where {F}
    eng = MatchEngine(m, s, constraints; maxsteps)
    while next_match!(eng)
        f(SubstitutionView(eng, eng.steps)) === false && return nothing
    end
    return nothing
end
eachmatch(f, p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; kwargs...) =
    eachmatch(f, compile_pattern(p), s; kwargs...)

"""
    BoundMatchAtIterator

Lazy iterator over match sites — yields `(BoundMatch, t)` pairs: a
frozen binding snapshot and the matched subterm, one per
(pattern-match, node) in postorder. `materialize(bm)` a pair's first
element for a `MarkersMap`.

The subject is interned once into the engine's shared IR, so a
structurally shared subterm is one node and yields one hit — sites are
deduplicated by `===`-identity, not by syntactic position (REWRITING.md
milestone 4).
"""
struct BoundMatchAtIterator
    eng::MatchEngine
end
Base.IteratorSize(::Type{BoundMatchAtIterator}) = Base.SizeUnknown()
Base.eltype(::Type{BoundMatchAtIterator}) = Tuple{BoundMatch, BasicSymbolic{SymReal}}

# Continue the inner enumeration at the bound site, else reset! onward
# to the next node producing a match; returns the node's index or 0.
function _next_hit_site!(eng::MatchEngine, j::Int32)
    subj = eng.subj
    n = Int32(length(subj))
    while j <= n
        reset!(eng, subj, j)
        next_match!(eng) && return j
        j += Int32(1)
    end
    return Int32(0)
end

function Base.iterate(it::BoundMatchAtIterator, i::Int32 = Int32(0))
    eng = it.eng
    if i == 0
        i = _next_hit_site!(eng, Int32(1))
    elseif !next_match!(eng)
        i = _next_hit_site!(eng, i + Int32(1))
    end
    i == 0 && return nothing
    bm = BoundMatch(
        eng.pat, eng.subj, symtype(eng.subj[i]),
        _snapshot_binds(eng.binds)
    )
    return ((bm, eng.subj[i]), i)
end

"""
    $TYPEDSIGNATURES

Lazy `(BoundMatch, t)` pairs for each match of `m` at each node of
`s` — occurrence search in the [`boundmatches`](@ref) idiom. Sites
deduplicated by `===`-identity; postorder (bottom-up) traversal.
"""
boundmatches_at(
    m::Matcher, s::BasicSymbolic{SymReal};
    constraints = Constraint[], maxsteps::Int = typemax(Int)
) = BoundMatchAtIterator(MatchEngine(m, s, constraints; maxsteps))
boundmatches_at(p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; kwargs...) =
    boundmatches_at(compile_pattern(p), s; kwargs...)

"""
    $TYPEDSIGNATURES

Lazy `(MarkersMap, t)` pairs for each match of `m` at each node of
`s` — the materializing variant of [`boundmatches_at`](@ref).
"""
matches_at(m::Matcher, s::BasicSymbolic{SymReal}; kwargs...) =
    Iterators.map(t -> (materialize(t[1]), t[2]), boundmatches_at(m, s; kwargs...))
matches_at(p::BasicSymbolic{SymReal}, s::BasicSymbolic{SymReal}; kwargs...) =
    matches_at(compile_pattern(p), s; kwargs...)
