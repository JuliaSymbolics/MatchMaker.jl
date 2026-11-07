# DESIGN.md §5.5f: AC frame — candidates, bipartite assignment, leftovers.
# Subject args are iterated in `arguments` order (dict order for `AddMul`,
# positional for `Term`) — enumeration/capture order is order-dependent
# (§3 ordering caveat). The arg view (head check, A-flattening, identity
# coercion) is `_seq_args`, shared with the Seq frame.

###
### Phase 1 — candidate matrix
###

# Can the pattern position at `child_pat` match subject node `snode` at
# all? Applies the obligation sandboxed — existence only, any binds are
# unwound — so the phase-1 edge records "this pairing can produce a
# match" under the bindings in force when the frame was entered.
function _ac_cand!(
        eng::MatchEngine, child_pat::Int32, snode::Int32
    )
    child_plan = eng.pat.plans[child_pat]
    mk = length(eng.trail)
    ok = if MData.isa_variant(child_plan, NodePlan.Literal) ||
            MData.isa_variant(child_plan, NodePlan.Slot)
        _leaf_obligation!(eng, child_pat, snode)
    elseif eng.pat.is_ground[child_pat]
        isequal(eng.pat.ir[child_pat], eng.subj[snode])
    else
        sp0 = eng.sp
        ki = _push_frame!(
            eng, _new_frame(child_plan, child_pat, snode, _nchildren(child_plan))
        )
        produced = step!(eng, eng.stk[ki]) === FrameStatus.Produced
        eng.sp = sp0
        produced
    end
    _unwind!(eng, mk)
    return ok::Bool
end

###
### AC frame (§5.5f)
###

# Same two-state machine as `Comm` (FORWARD dispatch / BACKTRACK seek),
# plus phases from §5.5f:
#
#   init (child_pos = 0) — arity bounds, then phase 1: each assignment
#     position (fixed ∪ slots, order[1:nassign]) gets its candidate arg
#     indices in `cands[j]`; an empty set fails fast. Positions are then
#     sorted by ascending candidate count (most-constrained-first;
#     deterministic ties by initial position), permuting `order`/`cands`.
#
#   FORWARD — assignment positions (order[1:nassign]) dispatch via
#     `_assign_next!` over their candidate list. Phase 3 positions
#     (optionals, then segments) dispatch over leftover args: an optional
#     consumes one leftover arg first, then its spec default
#     (assigned[j] = -1 marks the default branch); a segment takes a
#     sub-multiset of what's left via the shared `_comm_seg_*`
#     combination machinery. Reaching child_pos = np+1 produces iff
#     every subject arg was consumed.
#
#   BACKTRACK — resume the deepest position with alternatives left (a
#     live kid frame, the next candidate, the next combination, or the
#     optional's one-time default), unwind to its mark, and continue
#     FORWARD. Nothing resumable → fail to the frame's mark.

function _step_ac!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        order::Vector{Int32}, kids::Vector{Int32},
        bind_marks::Vector{Int}, assigned::Vector{Int32},
        scan::Vector{Int32}, used::BitVector,
        cands::Vector{SmallV{Int32}}, seg_sel::Vector{SmallV{Int32}},
        seg_pool::Vector{Vector{Int32}},
        min_tail::Vector{Int}, owns_bind::BitVector
    )
    plan = eng.pat.plans[pat_node]
    (op, head, nassign) = @match plan begin
        NodePlan.ACCall(; op, head, fixed, slots, optionals, segments) =>
            (op, head, length(fixed) + length(slots))
        _ => error(lazy"AC frame got a non-ACCall plan at node $pat_node")
    end
    # fresh frames take their trail mark before any obligation runs —
    # `_seq_args` applies the head obligation, and an early failure must
    # unwind to *this* frame's entry mark, never past it
    iszero(child_pos[]) && (mark[] = length(eng.trail))
    got = _seq_args(eng, op, head, subj_node)
    got === nothing && return _call_fail!(eng, mark)
    (snbs, sstart) = got
    m = length(snbs) - (sstart - 1)
    np = length(order)
    backtrack = false

    if iszero(child_pos[])
        _comm_min_tail!(eng, order, min_tail)
        ok = m >= min_tail[1] && m <= _comm_upper(eng, order)
        ok || return _call_fail!(eng, mark)
        resize!(used, m)
        fill!(used, false)
        # phase 1 — candidates per assignment position; fail fast on an
        # empty set, then dispatch most-constrained positions first
        for j in 1:nassign
            empty!(cands[j])
            for i in 1:m
                _ac_cand!(eng, order[j], snbs[sstart + i - 1]) &&
                    push!(cands[j], i)
            end
            isempty(cands[j]) && return _call_fail!(eng, mark)
        end
        # most-constrained first — insertion-sort the assignment prefix
        # by candidate count, keeping order/cands permuted identically
        # (stable: ties keep plan order; nassign is small, and this avoids
        # allocating a perm vector or permuted temporaries)
        for i in 2:nassign
            o = order[i]
            ci = cands[i]
            ni = length(ci)
            j = i - 1
            while j >= 1 && length(cands[j]) > ni
                order[j + 1] = order[j]
                cands[j + 1] = cands[j]
                j -= 1
            end
            order[j + 1] = o
            cands[j + 1] = ci
        end
        child_pos[] = 1
    elseif child_pos[] > np
        child_pos[] = np
        backtrack = true
    else
        error(lazy"AC frame re-entered at child_pos $(child_pos[])")
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
                child_pat = order[j]
                cplan = eng.pat.plans[child_pat]
                is_seg_pos = MData.isa_variant(cplan, NodePlan.Segment)
                is_opt_pos = MData.isa_variant(cplan, NodePlan.Slot) &&
                    _is_opt_pos(eng, child_pat)
                produced = false
                if is_seg_pos
                    vid = @match cplan begin
                        NodePlan.Segment(; var_id) => var_id
                    end
                    len = _comm_seg_resume!(
                        eng, vid, op, snbs, sstart, j, used,
                        seg_sel, seg_pool, min_tail, owns_bind, bind_marks
                    )
                    produced = len !== nothing
                elseif j <= nassign || is_opt_pos
                    # a defaulted optional has no alternatives left
                    exhausted = is_opt_pos && assigned[j] == -1
                    kf = _kid(eng, kids, j)
                    if !exhausted && kf !== nothing
                        produced = step!(eng, kf) === FrameStatus.Produced
                    end
                    if !produced && !exhausted
                        _drop_kid!(eng, kids, j)
                        if assigned[j] > 0
                            used[assigned[j]] = false
                            assigned[j] = 0
                        end
                        _unwind!(eng, bind_marks[j])
                        produced = _assign_next!(
                            eng, child_pat, cplan, j, snbs, sstart,
                            is_opt_pos ? nothing : cands[j],
                            used, scan, assigned, kids
                        )
                        if !produced && is_opt_pos
                            # consume-alternatives exhausted: §4.7 default
                            vid = _slot_vid(eng, child_pat)
                            if _opt_default!(eng, vid)
                                assigned[j] = -1
                                produced = true
                            end
                        end
                    end
                end
                if produced
                    child_pos[] += 1
                    break
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
        cplan = eng.pat.plans[child_pat]
        is_seg_pos = MData.isa_variant(cplan, NodePlan.Segment)
        if j <= nassign
            scan[j] = 1    # fresh dispatch: retry all remaining candidates
            produced = _assign_next!(
                eng, child_pat, cplan, j, snbs, sstart, cands[j],
                used, scan, assigned, kids
            )
        elseif is_seg_pos
            vid = @match cplan begin
                NodePlan.Segment(; var_id) => var_id
            end
            produced = _comm_seg_first!(
                eng, vid, op, snbs, sstart, j, used,
                seg_sel, seg_pool, min_tail, owns_bind
            )
        else
            # optional (§4.7): consume one leftover arg first, then the
            # spec default (assigned[j] = -1 marks the default branch)
            @assert _is_opt_pos(eng, child_pat)
            vid = _slot_vid(eng, child_pat)
            scan[j] = 1
            assigned[j] = 0
            produced = _assign_next!(
                eng, child_pat, cplan, j, snbs, sstart, nothing,
                used, scan, assigned, kids
            )
            if !produced && _opt_default!(eng, vid)
                assigned[j] = -1
                produced = true
            end
        end
        produced ? (child_pos[] += 1) : (backtrack = true)
    end
    return
end
