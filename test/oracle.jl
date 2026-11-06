# Naive oracle matcher (§5.7) — a deliberately simple recursive
# enumerator used to cross-validate the frame engine. Operates on the
# pattern *expression* plus the `vars` spec map — no plans, no frames,
# no trail: continuation-passing enumeration over a bindings dict
# restored by explicit `delete!` on the way back. Produces `matchall`
# semantics only; distinct assignments surface as duplicate binding
# dicts exactly as the engine produces them.
#
# `b` maps sym => materialized value (what the result map shows);
# `sruns` maps segment sym => captured arg exprs (the engine's `b.seq`)
# so bound-elsewhere rechecks compare raw captures, not
# reconstructions.

using MatchMaker: VarSpec, varsym, is_marker_term, MData,
    _is_associative_head, _is_commutative_head, _identity_el, _symtype_ok,
    _is_segment_term, _is_optional_term
using SymbolicUtils
using SymbolicUtils: BSImpl, ArgsT, symtype, shape, iscall, operation,
    arguments, isconst, unwrap_const, promote_symtype, BasicSymbolic,
    SymReal, Const

"""
    oracle_matchall(pat, subj; vars = Dict())

Naive recursive enumerator — every consistent `sym => value` binding
dict matching `pat` to `subj`. `vars` takes the same per-variable
specs as `compile_pattern`.
"""
function oracle_matchall(
        pat::BasicSymbolic{SymReal}, subj::BasicSymbolic{SymReal};
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}()
    )
    st = (
        b = Dict{BasicSymbolic{SymReal}, Any}(),
        sruns = Dict{BasicSymbolic{SymReal}, Vector}(),
        res = Dict{BasicSymbolic{SymReal}, Any}[]
    )
    _o_match(pat, subj, vars, st) do
        push!(st.res, copy(st.b))
        return nothing
    end
    return st.res
end

# Call `k()` for every consistent extension of `st.b` matching `pat` to
# `subj`.
function _o_match(k::F, pat, subj, vars, st) where {F}
    is_marker_term(pat) && return _o_slot(k, varsym(pat), subj, vars, st)
    iscall(pat) || return (isequal(pat, subj) && k(); nothing)
    return _o_call(k, pat, subj, vars, st)
end

function _o_spec(vars, vs)
    return get(vars, vs, VarSpec.Slot(nothing, nothing))
end

function _o_segspec(vars, vs)
    spec = get(vars, vs, nothing)
    spec !== nothing && MData.isa_variant(spec, VarSpec.Segment) &&
        return spec
    return VarSpec.Segment(nothing, nothing, 0, typemax(Int))
end

# Bind (or recheck) slot var `vs` to `subj`, applying spec checks.
function _o_slot(k::F, vs, subj, vars, st) where {F}
    b = st.b
    haskey(b, vs) && return (isequal(b[vs], subj) && k(); nothing)
    spec = _o_spec(vars, vs)
    if MData.isa_variant(spec, VarSpec.Slot)
        _symtype_ok(symtype(subj), symtype(vs)) || return nothing
        isequal(shape(subj), shape(vs)) || return nothing
        spec.predicate !== nothing &&
            !spec.predicate(subj) &&
            return nothing
    end
    b[vs] = subj
    k()
    delete!(b, vs)
    return nothing
end

# Bind `vs` to `val` (defaults, head ops) or recheck `isequal` when
# already bound.
function _o_bind(k::F, vs, val, st) where {F}
    b = st.b
    haskey(b, vs) && return (isequal(b[vs], val) && k(); nothing)
    b[vs] = val
    k()
    delete!(b, vs)
    return nothing
end

# Bind segment var `vs` to its captured run: `run` is the list of
# captured subject exprs; the map value is the reconstructed
# `effop(captured…)`.
function _o_seg_bind(k::F, vs, effop, run, st, ST) where {F}
    b = st.b
    if haskey(b, vs)
        isequal(st.sruns[vs], run) || return nothing
        return k()
    end
    b[vs] = _o_seg_value(effop, ST, run)
    st.sruns[vs] = copy(run)
    k()
    delete!(b, vs)
    delete!(st.sruns, vs)
    return nothing
end

# Reconstruct `op(captured…)` for a segment binding (mirrors
# `_seg_value`): canonical workers for `+`/`*`, declared-identity Const
# or `f()` for an empty generic capture.
function _o_seg_value(@nospecialize(op), ST, caps)
    if op === (+)
        return SymbolicUtils.add_worker(
            SymReal, BasicSymbolic{SymReal}[caps...]
        )
    elseif op === (*)
        return SymbolicUtils.mul_worker(
            SymReal, BasicSymbolic{SymReal}[caps...]
        )
    elseif isempty(caps)
        e = _identity_el(op, ST)
        e !== nothing && return Const{SymReal}(e)
        return BSImpl.Term{SymReal}(
            op, ArgsT{SymReal}(); type = promote_symtype(op)
        )
    else
        return BSImpl.Term{SymReal}(
            op, ArgsT{SymReal}(caps);
            type = promote_symtype(op, map(symtype, caps)...)
        )
    end
end

# The subject arg view for head `effop` (mirrors `_seq_args`): a same-op
# call gives its args — flattened when `effop` is associative; a
# non-call or head-mismatched subject coerces to a singleton iff `effop`
# is associative with a declared identity (§4.6).
function _o_sargs(@nospecialize(effop), subj, ST)
    if iscall(subj) && operation(subj) === effop
        _is_associative_head(effop, ST) || return collect(arguments(subj))
        flat = Any[]
        function pushflat(a)
            if iscall(a) && operation(a) === effop
                foreach(pushflat, arguments(a))
            else
                push!(flat, a)
            end
        end
        foreach(pushflat, arguments(subj))
        return flat
    end
    _is_associative_head(effop, ST) || return nothing
    _identity_el(effop, ST) === nothing && return nothing
    return Any[subj]
end

function _o_call(k::F, pat, subj, vars, st) where {F}
    ST = symtype(subj)
    patop = operation(pat)
    if patop isa BasicSymbolic{SymReal} && is_marker_term(patop)
        # head-slot (§4.10): subject must be a call; the var binds the
        # subject's operation and traits resolve on the bound head
        iscall(subj) || return nothing
        hs = varsym(patop)
        sop = operation(subj)
        spec = _o_spec(vars, hs)
        MData.isa_variant(spec, VarSpec.Slot) && spec.predicate !== nothing &&
            !spec.predicate(Const{SymReal}(sop)) && return nothing
        return _o_bind(hs, sop, st) do
            _o_positions(k, st.b[hs], pat, subj, vars, st, ST)
        end
    end
    return _o_positions(k, patop, pat, subj, vars, st, ST)
end

function _o_positions(k::F, effop, pat, subj, vars, st, ST) where {F}
    sargs = _o_sargs(effop, subj, ST)
    sargs === nothing && return nothing
    kids = Any[
        if _is_segment_term(c)
            (:seg, c)
        elseif _is_optional_term(c)
            (:opt, c)
        else
            (:fix, c)
        end for c in arguments(pat)
    ]
    if _is_commutative_head(effop, ST)
        _o_comm!(k, effop, kids, sargs, vars, st, ST)
    else
        _o_seq!(k, effop, kids, sargs, vars, st, ST, 1, 1)
    end
    return nothing
end

# Minimum subject args `kids[i:end]` require: segment min, optional 0,
# anything else 1.
function _o_min_tail(kids, i::Int, vars)
    t = 0
    for j in i:length(kids)
        kd, c = kids[j]
        kd === :fix && (t += 1; continue)
        kd === :opt && continue
        t += _o_segspec(vars, varsym(c)).min
    end
    return t
end

# Ordered enumeration: kids consume `sargs` left-to-right; `i` is the
# position, `sidx` the next subject arg index.
function _o_seq!(
        k::F, effop, kids, sargs, vars, st, ST, i::Int, sidx::Int
    ) where {F}
    n = length(sargs)
    if i > length(kids)
        sidx > n && k()
        return nothing
    end
    kd, c = kids[i]
    tail = _o_min_tail(kids, i + 1, vars)
    if kd === :seg
        vs = varsym(c)
        spec = _o_segspec(vars, vs)
        if haskey(st.b, vs)
            run = st.sruns[vs]
            len = length(run)
            sidx + len - 1 <= n &&
                isequal(run, sargs[sidx:(sidx + len - 1)]) &&
                _o_seq!(k, effop, kids, sargs, vars, st, ST, i + 1, sidx + len)
            return nothing
        end
        hi = min(spec.max, n - sidx + 1 - tail)
        for len in spec.min:hi
            caps = sargs[sidx:(sidx + len - 1)]
            spec.predicate !== nothing &&
                !all(spec.predicate, caps) &&
                break   # contiguous: longer runs contain the failing element
            seq = spec.sequence_predicate
            seq !== nothing &&
                !seq(BasicSymbolic{SymReal}[caps...]) &&
                continue
            _o_seg_bind(vs, effop, caps, st, ST) do
                _o_seq!(k, effop, kids, sargs, vars, st, ST, i + 1, sidx + len)
            end
        end
        return nothing
    end
    if kd === :opt
        vs = varsym(c)
        spec = _o_spec(vars, vs)
        sidx <= n - tail && _o_slot(vs, sargs[sidx], vars, st) do
            _o_seq!(k, effop, kids, sargs, vars, st, ST, i + 1, sidx + 1)
        end
        MData.isa_variant(spec, VarSpec.Slot) && spec.default !== nothing &&
            _o_bind(vs, spec.default, st) do
                _o_seq!(k, effop, kids, sargs, vars, st, ST, i + 1, sidx)
            end
        return nothing
    end
    sidx <= n || return nothing
    _o_match(c, sargs[sidx], vars, st) do
        _o_seq!(k, effop, kids, sargs, vars, st, ST, i + 1, sidx + 1)
    end
    return nothing
end

# Unordered enumeration (Comm/AC): non-segment positions take any unused
# arg, segments take sub-multisets of the leftover pool, optionals take
# an unused arg or their default. `used` marks consumed subject args.
function _o_comm!(k::F, effop, kids, sargs, vars, st, ST) where {F}
    n = length(sargs)
    used = falses(n)
    # dispatch order: fixed/slot, then optionals, then segments
    ord = vcat(
        findall(kd -> kd[1] === :fix, kids),
        findall(kd -> kd[1] === :opt, kids),
        findall(kd -> kd[1] === :seg, kids)
    )
    function rec(j::Int)
        if j > length(ord)
            all(used) && k()
            return nothing
        end
        kd, c = kids[ord[j]]
        if kd === :seg
            tail = _o_min_after(kids, ord, j, vars)
            return _o_comm_seg!(
                k, effop, c, vars, st, ST, sargs, used, tail, rec, j
            )
        end
        if kd === :opt
            vs = varsym(c)
            spec = _o_spec(vars, vs)
            for a in 1:n
                used[a] && continue
                used[a] = true
                _o_slot(vs, sargs[a], vars, st) do
                    rec(j + 1)
                end
                used[a] = false
            end
            MData.isa_variant(spec, VarSpec.Slot) && spec.default !== nothing &&
                _o_bind(vs, spec.default, st) do
                    rec(j + 1)
                end
            return nothing
        end
        for a in 1:n
            used[a] && continue
            used[a] = true
            _o_match(c, sargs[a], vars, st) do
                rec(j + 1)
            end
            used[a] = false
        end
        return nothing
    end
    rec(1)
    return nothing
end

# Minimum subject args the positions dispatched *after* j require.
function _o_min_after(kids, ord, j::Int, vars)
    t = 0
    for p in (j + 1):length(ord)
        kd, c = kids[ord[p]]
        kd === :fix && (t += 1; continue)
        kd === :opt && continue
        t += _o_segspec(vars, varsym(c)).min
    end
    return t
end

# Enumerate subsets of the currently-unused subject args for one segment
# position, in increasing size — combinations in pool order, the
# `_next_combo!` enumeration the engine uses.
function _o_comm_seg!(
        k::F, effop, c, vars, st, ST, sargs, used, tail, rec, j
    ) where {F}
    vs = varsym(c)
    spec = _o_segspec(vars, vs)
    pool = findall(!, used)
    if haskey(st.b, vs)
        # bound elsewhere: its captured run must appear in the pool in
        # pool order — the single viable selection (greedy subsequence)
        run = st.sruns[vs]
        sel = Int[]
        si = 1
        for a in pool
            si <= length(run) || break
            isequal(run[si], sargs[a]) || continue
            si += 1
            push!(sel, a)
        end
        si > length(run) || return nothing
        foreach(a -> used[a] = true, sel)
        rec(j + 1)
        foreach(a -> used[a] = false, sel)
        return nothing
    end
    hi = min(spec.max, length(pool) - tail)
    for d in spec.min:hi
        sel = collect(pool[1:d])
        while true
            caps = BasicSymbolic{SymReal}[sargs[a] for a in sel]
            ok = (
                spec.predicate === nothing || all(spec.predicate, caps)
            ) && (
                spec.sequence_predicate === nothing ||
                    spec.sequence_predicate(caps)
            )
            if ok
                foreach(a -> used[a] = true, sel)
                _o_seg_bind(vs, effop, caps, st, ST) do
                    rec(j + 1)
                end
                foreach(a -> used[a] = false, sel)
            end
            _o_next_combo!(sel, pool) || break
        end
    end
    return nothing
end

# Advance `sel` (pool values, ascending) to the next combination; false
# when exhausted (mirrors `_next_combo!`; `pool` is sorted).
function _o_next_combo!(sel::Vector{Int}, pool::Vector{Int})
    n = length(pool)
    k = length(sel)
    for i in k:-1:1
        sel[i] == pool[n - k + i] && continue
        idx = searchsortedfirst(pool, sel[i]) + 1
        sel[i] = pool[idx]
        for t in (i + 1):k
            sel[t] = pool[idx + (t - i)]
        end
        return true
    end
    return false
end
