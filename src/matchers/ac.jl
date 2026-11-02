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
        step!(
            eng,
            _new_frame(child_plan, child_pat, snode, _nchildren(child_plan))
        ) === FrameStatus.Produced
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
#   FORWARD — assignment positions dispatch via `_assign_next!` over
#     their candidate list; reaching child_pos = np+1 produces iff every
#     subject arg was consumed.
#
#   BACKTRACK — resume the deepest position with alternatives left (a
#     live kid frame, then the next candidate), unwind to its mark, and
#     continue FORWARD. Nothing resumable → fail to the frame's mark.
#
# Optional and segment positions land in the next sub-branch; for now
# they make the frame error rather than silently misassign.

function _step_ac!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        order::Vector{Int32}, kids::Vector{Union{Nothing, MatchFrameT}},
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
    got = _seq_args(eng, op, head, subj_node)
    got === nothing && return _call_fail!(eng, mark)
    (snbs, sstart) = got
    m = length(snbs) - (sstart - 1)
    np = length(order)
    backtrack = false

    if iszero(child_pos[])
        mark[] = length(eng.trail)
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
        perm = sortperm([(length(cands[j]), j) for j in 1:nassign])
        order[1:nassign] = order[perm]
        cands[1:nassign] = cands[perm]
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
                if j <= nassign
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
                        produced = _assign_next!(
                            eng, order[j], eng.pat.plans[order[j]], j,
                            snbs, sstart, cands[j], used, scan, assigned, kids
                        )
                    end
                    if produced
                        child_pos[] += 1
                        break
                    end
                end
                # positions past nassign have no resumable state yet
                child_pos[] -= 1
            end
            child_pos[] == 0 && return _call_fail!(eng, mark)
            backtrack = false
            continue
        end
        j = child_pos[]
        j > nassign && error(
            lazy"AC optional/segment positions are unimplemented (ac/segments)"
        )
        bind_marks[j] = length(eng.trail)
        scan[j] = 1    # fresh dispatch: retry all remaining candidates
        if _assign_next!(
                eng, order[j], eng.pat.plans[order[j]], j,
                snbs, sstart, cands[j], used, scan, assigned, kids
            )
            child_pos[] += 1
        else
            backtrack = true
        end
    end
    return
end
