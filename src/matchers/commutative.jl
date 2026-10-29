# DESIGN.md §5.5d: Comm frame — commutative-not-associative head.
# Positions dispatch in MatchPy's phase order fixed → slots → optionals →
# segments (`optionals` is always empty for C-only heads, §4.7). Non-segment
# positions consume one subject argument each (a bipartite assignment over
# remaining args); segments consume a disjoint sub-multiset of what's left.

###
### Combination iteration for segment sub-multisets
###

# Sorted `pool` of available arg positions; `sel` is the current sorted
# subset. Advance to the next combination in lexicographic pool order —
# returns false when `sel` is the last combination of its size.
function _next_combo!(sel::SmallV{Int32}, pool::Vector{Int32})
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

###
### Comm frame (§5.5d)
###

# Same two-state machine as `Seq` (FORWARD dispatch / BACKTRACK seek),
# plus candidate enumeration: positions dispatch in `order` (fixed, then
# slots, then optionals, then segments) and each position iterates its
# alternatives — non-segment positions iterate remaining subject args,
# segment positions iterate sub-multiset combinations of their pool.

# Dispatch position j onto the next unused subject arg. Returns true when
# the position produced an alternative (obligation applied and used[i]
# marked); false when no remaining arg satisfies it.
function _comm_next!(
        eng::MatchEngine, child_pat::Int32, child_plan::NodePlanT,
        j::Int, snbs, sstart::Int, used::BitVector,
        scan::Vector{Int32}, assigned::Vector{Int32},
        kids::Vector{Union{Nothing, MatchFrameT}}
    )
    m = length(used)
    while scan[j] <= m
        i = scan[j]
        scan[j] += 1
        used[i] && continue
        snode = snbs[sstart + i - 1]
        isleaf = MData.isa_variant(child_plan, NodePlan.Literal) ||
            MData.isa_variant(child_plan, NodePlan.Slot)
        if isleaf
            if _leaf_obligation!(eng, child_pat, snode)
                assigned[j] = i
                used[i] = true
                return true
            end
        elseif eng.pat.is_ground[child_pat]
            if isequal(eng.pat.ir[child_pat], eng.subj[snode])
                assigned[j] = i
                used[i] = true
                return true
            end
        else
            kf = _new_frame(child_plan, child_pat, snode, _nchildren(child_plan))
            if step!(eng, kf) === FrameStatus.Produced
                assigned[j] = i
                used[i] = true
                kids[j] = kf
                return true
            end
        end
    end
    return false
end

# Try binding segment var `vid` to the arg positions `sel` selects from
# `snbs` (arg position i → node snbs[sstart+i-1]).
function _comm_seg_bind!(
        eng::MatchEngine, vid::Int32, @nospecialize(op),
        snbs, sstart::Int, sel::SmallV{Int32}
    )
    b = eng.binds
    seq = b.seq[vid]
    empty!(seq)
    for i in sel
        push!(seq, snbs[sstart + i - 1])
    end
    b.seg_op[vid] = op
    push!(eng.trail, vid)
    if !_ready_constraints!(eng, vid)
        _unwind!(eng, length(eng.trail) - 1)
        return SegResult.Longer
    end
    return SegResult.Bound
end

# Bind the first alternative for a segment position. `pool` is the sorted
# list of arg positions available at this position's dispatch; fills
# `seg_sel`/`owns_bind`/`used` on success. A var bound elsewhere must
# capture exactly its bound set (in pool order).
function _comm_seg_first!(
        eng::MatchEngine, vid::Int32, @nospecialize(op), snbs,
        sstart::Int, j::Int, used::BitVector,
        seg_sel::Vector{SmallV{Int32}}, seg_pool::Vector{Vector{Int32}},
        min_tail::Vector{Int}, owns_bind::BitVector
    )
    pool = Int32[]
    for i in 1:length(used)
        used[i] || push!(pool, i)
    end
    seg_pool[j] = pool
    sel = seg_sel[j]
    b = eng.binds
    if b.seg_op[vid] !== nothing
        # bound elsewhere: exactly one viable selection — the bound set,
        # aligned in pool order
        bound = b.seq[vid]
        empty!(sel)
        length(pool) >= length(bound) || return false
        k = 1
        for i in pool
            k > length(bound) && break
            if isequal(eng.subj[bound[k]], eng.subj[snbs[sstart + i - 1]])
                push!(sel, i)
                k += 1
            end
        end
        length(sel) == length(bound) || return false
        for i in sel
            used[i] = true
        end
        owns_bind[j] = false
        return true
    end
    lo = _seg_min(eng, vid)
    hi = min(_seg_max(eng, vid), length(pool) - min_tail[j + 1])
    lo > hi && return false
    empty!(sel)
    for t in 1:lo
        push!(sel, pool[t])
    end
    while true
        if _comm_sel_ok(eng, vid, snbs, sstart, sel)
            st = _comm_seg_bind!(eng, vid, op, snbs, sstart, sel)
            if st === SegResult.Bound
                for i in sel
                    used[i] = true
                end
                owns_bind[j] = true
                return true
            end
        end
        # advance to the next combination; at the last combo of a size,
        # grow to the next size (the grown selection is tried next pass)
        if !_next_combo!(sel, pool)
            length(sel) == hi && return false
            resize!(sel, length(sel) + 1)
            for t in 1:length(sel)
                sel[t] = pool[t]
            end
        end
    end
    return
end

# Does the selection `sel` satisfy vid's element and sequence
# predicates? An element-predicate failure only kills this selection —
# other combinations may exclude the failing element.
function _comm_sel_ok(
        eng::MatchEngine, vid::Int32, snbs, sstart::Int, sel::SmallV{Int32}
    )
    (pred, seqpred) = _seg_preds(eng, vid)
    if pred !== nothing
        for i in sel
            pred(eng.subj[snbs[sstart + i - 1]])::Bool || return false
        end
    end
    if seqpred !== nothing
        buf = eng.segbuf
        resize!(buf, length(sel))
        for (t, i) in enumerate(sel)
            buf[t] = eng.subj[snbs[sstart + i - 1]]
        end
        seqpred(buf)::Bool || return false
    end
    return true
end

# Resume a segment position: free its previous capture, then take the
# next combination (or grow toward `hi`) of its recorded pool. Returns
# the new bound length or `nothing` when no alternatives are left.
function _comm_seg_resume!(
        eng::MatchEngine, vid::Int32, @nospecialize(op), snbs,
        sstart::Int, j::Int, used::BitVector,
        seg_sel::Vector{SmallV{Int32}}, seg_pool::Vector{Vector{Int32}},
        min_tail::Vector{Int}, owns_bind::BitVector,
        bind_marks::Vector{Int}
    )
    owns_bind[j] || return nothing
    pool = seg_pool[j]
    sel = seg_sel[j]
    for i in sel
        used[i] = false
    end
    hi = min(_seg_max(eng, vid), length(pool) - min_tail[j + 1])
    while true
        if !_next_combo!(sel, pool)
            length(sel) == hi && return nothing
            resize!(sel, length(sel) + 1)
            for t in 1:length(sel)
                sel[t] = pool[t]
            end
        end
        if _comm_sel_ok(eng, vid, snbs, sstart, sel)
            _unwind!(eng, bind_marks[j])
            st = _comm_seg_bind!(eng, vid, op, snbs, sstart, sel)
            if st === SegResult.Bound
                for i in sel
                    used[i] = true
                end
                return length(sel)
            end
        end
    end
    return
end


function _step_comm!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        order::Vector{Int32}, kids::Vector{Union{Nothing, MatchFrameT}},
        bind_marks::Vector{Int}, assigned::Vector{Int32},
        scan::Vector{Int32}, used::BitVector,
        seg_sel::Vector{SmallV{Int32}}, seg_pool::Vector{Vector{Int32}},
        min_tail::Vector{Int}, owns_bind::BitVector
    )
    plan = eng.pat.plans[pat_node]
    (op, head) = @match plan begin
        NodePlan.CommCall(; op, head) => (op, head)
        _ => error(lazy"Comm frame got a non-CommCall plan at node $pat_node")
    end
    snbs = Graphs.outneighbors(eng.subj.dependency_graph, subj_node)
    sexpr = eng.subj[subj_node]
    sstart = @match sexpr begin
        BSImpl.Term(; f) => f isa BasicSymbolic{SymReal} ? 2 : 1
        _ => 1
    end
    m = length(snbs) - (sstart - 1)
    np = length(order)
    backtrack = false

    if iszero(child_pos[])
        mark[] = length(eng.trail)
        _comm_min_tail!(eng, order, min_tail)
        resize!(used, m)
        fill!(used, false)
        ok = iscall(sexpr) && m >= min_tail[1] && m <= _comm_upper(eng, order)
        if ok
            sop = operation(sexpr)
            ok = if iszero(head)
                op === sop
            else
                _head_obligation!(eng, head, sop)
            end
        end
        ok || return _call_fail!(eng, mark)
        child_pos[] = 1
    elseif child_pos[] > np
        child_pos[] = np
        backtrack = true
    else
        error(lazy"Comm frame re-entered at child_pos $(child_pos[])")
    end

    while true
        if child_pos[] > np
            # whole match: every subject arg assigned (§4.1)
            if all(used)
                return FrameStatus.Produced
            end
            child_pos[] = np
            backtrack = true
        end
        if backtrack
            while child_pos[] >= 1
                j = child_pos[]
                cplan = eng.pat.plans[order[j]]
                is_seg_pos = MData.isa_variant(cplan, NodePlan.Segment)
                if is_seg_pos
                    vid = @match cplan begin
                        NodePlan.Segment(; var_id) => var_id
                    end
                    len = _comm_seg_resume!(
                        eng, vid, op, snbs, sstart, j, used,
                        seg_sel, seg_pool, min_tail, owns_bind, bind_marks
                    )
                    len === nothing || begin
                        child_pos[] += 1
                        break
                    end
                else
                    kf = kids[j]
                    produced = kf !== nothing &&
                        step!(eng, kf) === FrameStatus.Produced
                    if !produced
                        kids[j] = nothing
                        if assigned[j] != 0
                            used[assigned[j]] = false
                            assigned[j] = 0
                        end
                        _unwind!(eng, bind_marks[j])
                        produced = _comm_next!(
                            eng, order[j], cplan, j, snbs, sstart,
                            used, scan, assigned, kids
                        )
                    end
                    if produced
                        child_pos[] += 1
                        break
                    end
                end
                child_pos[] -= 1
            end
            child_pos[] == 0 && return _call_fail!(eng, mark)
            backtrack = false
            continue
        end
        j = child_pos[]
        bind_marks[j] = length(eng.trail)
        child_pat = order[j]
        child_plan = eng.pat.plans[child_pat]
        is_seg_pos = MData.isa_variant(child_plan, NodePlan.Segment)
        if is_seg_pos
            vid = @match child_plan begin
                NodePlan.Segment(; var_id) => var_id
            end
            if _comm_seg_first!(
                    eng, vid, op, snbs, sstart, j, used,
                    seg_sel, seg_pool, min_tail, owns_bind
                )
                child_pos[] += 1
            else
                backtrack = true
            end
        else
            bind_marks[j] = length(eng.trail)
            scan[j] = 1    # fresh dispatch: all remaining args are candidates
            if _comm_next!(
                    eng, child_pat, child_plan, j, snbs, sstart,
                    used, scan, assigned, kids
                )
                child_pos[] += 1
            else
                backtrack = true
            end
        end
    end
    return
end

# Suffix minimum over `order` (non-segment positions need 1, segments
# need spec.min) and the absolute upper bound for arity checks.
function _comm_min_tail!(eng::MatchEngine, order::Vector{Int32}, min_tail::Vector{Int})
    min_tail[end] = 0
    for j in length(order):-1:1
        min_tail[j] = min_tail[j + 1] + @match eng.pat.plans[order[j]] begin
            NodePlan.Segment(; var_id) => _seg_min(eng, var_id)
            _ => 1
        end
    end
    return min_tail
end

function _comm_upper(eng::MatchEngine, order::Vector{Int32})
    u = 0
    for cp in order
        add = @match eng.pat.plans[cp] begin
            NodePlan.Segment(; var_id) => _seg_max(eng, var_id)
            _ => 1
        end
        u = add > typemax(Int) - u ? typemax(Int) : u + add
    end
    return u
end
