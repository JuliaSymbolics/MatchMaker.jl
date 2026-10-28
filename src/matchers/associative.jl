# DESIGN.md §5.5e: Assoc frame — contiguous-run segment capture under a
# free head (identity coercion for A-heads is milestone 7).

###
### Segment spec helpers
###

function _seg_min(eng::MatchEngine, vid::Int32)
    return @match eng.pat.var_specs[vid] begin
        VarSpec.Segment(; min) => min
        _ => 0
    end
end

function _seg_max(eng::MatchEngine, vid::Int32)
    return @match eng.pat.var_specs[vid] begin
        VarSpec.Segment(; max) => max
        _ => typemax(Int)
    end
end

function _seg_preds(eng::MatchEngine, vid::Int32)
    return @match eng.pat.var_specs[vid] begin
        VarSpec.Segment(; predicate, sequence_predicate) =>
            (predicate, sequence_predicate)
        _ => (nothing, nothing)
    end
end

# Minimum subject args positions j..n require: suffix sums of 1 per
# non-segment position and spec.min per segment position.
function _assoc_min_tail!(
        eng::MatchEngine, children::SmallV{Int32}, min_tail::Vector{Int}
    )
    min_tail[end] = 0
    for j in length(children):-1:1
        min_tail[j] = min_tail[j + 1] + @match eng.pat.plans[children[j]] begin
            NodePlan.Segment(; var_id) => _seg_min(eng, var_id)
            _ => 1
        end
    end
    return min_tail
end

###
### Segment obligations (§4.5)
###

# Result of trying a single segment capture length, or of advancing a
# segment position through its allowed lengths.
@enumx SegResult begin
    "Bound (or an identical non-linear recheck passed)."
    Bound
    "This length fails but a longer capture may succeed."
    Longer
    "Position dead: an element predicate or a non-linear recheck failed."
    Dead
end

# Try binding segment var `vid` to `len` subject args starting at index
# `sidx` of `snbs`. See `SegResult` for the return contract.
function _seg_try!(
        eng::MatchEngine, vid::Int32, @nospecialize(op),
        snbs, sidx::Int, len::Int
    )
    b = eng.binds
    if b.seg_op[vid] !== nothing
        # non-linear recheck: the captured run must be identical. The IR
        # interns by === (weak_definitions can hold isequal-different
        # nodes), so compare exprs, not node indices.
        seq = b.seq[vid]
        length(seq) == len || return SegResult.Dead
        for i in 1:len
            isequal(
                eng.subj[seq[i]], eng.subj[snbs[sidx + i - 1]]
            ) || return SegResult.Dead
        end
        return SegResult.Bound
    end
    (pred, seqpred) = _seg_preds(eng, vid)
    if pred !== nothing
        for i in 1:len
            pred(eng.subj[snbs[sidx + i - 1]])::Bool || return SegResult.Dead
        end
    end
    if seqpred !== nothing
        buf = eng.segbuf
        resize!(buf, len)
        for i in 1:len
            buf[i] = eng.subj[snbs[sidx + i - 1]]
        end
        seqpred(buf)::Bool || return SegResult.Longer
    end
    seq = b.seq[vid]
    empty!(seq)
    for i in 1:len
        push!(seq, snbs[sidx + i - 1])
    end
    b.seg_op[vid] = op
    push!(eng.trail, vid)
    if !_ready_constraints!(eng, vid)
        _unwind!(eng, length(eng.trail) - 1)
        return SegResult.Longer
    end
    return SegResult.Bound
end

# Try lengths `first_len` upward at a segment position; `amax` is
# `min(spec.max, avail - required_after)`. Returns `SegResult.Bound` or
# `SegResult.Dead`.
# A var bound elsewhere has exactly one viable length — its bound run.
function _seg_advance!(
        eng::MatchEngine, vid::Int32, @nospecialize(op), snbs,
        sidx::Int, min_tail_next::Int, first_len::Int
    )
    navail = length(snbs) - sidx + 1
    amax = min(_seg_max(eng, vid), navail - min_tail_next)
    if eng.binds.seg_op[vid] !== nothing
        len = length(eng.binds.seq[vid])
        len <= amax || return SegResult.Dead
        return _seg_try!(eng, vid, op, snbs, sidx, len)
    end
    len = first_len
    while len <= amax
        st = _seg_try!(eng, vid, op, snbs, sidx, len)
        st !== SegResult.Longer && return st
        len += 1
    end
    return SegResult.Dead
end

###
### Assoc frame (§5.5e)
###

# The frame is a two-state machine over its child positions:
#
#   FORWARD — dispatch position child_pos: record bind_marks[j] and
#     arg_start[j], then apply the position's obligation. A segment
#     consumes `capture_len[j]` contiguous subject args starting at
#     spec.min; every other position consumes exactly one. Success
#     advances child_pos; reaching child_pos = n+1 produces an
#     alternative *iff* every subject arg was consumed — otherwise it
#     falls through to BACKTRACK.
#
#   BACKTRACK — entered on any dispatch failure or on re-entry after a
#     Produced: seek the deepest position with remaining alternatives
#     (a live kid frame, or a segment that owns its bind with one more
#     allowed length), resume it, and continue FORWARD. Nothing
#     resumable → unwind to the frame's mark and return Failed.
#
# `step!` is called in exactly two states: `child_pos == 0` (init: check
# head and arity lower bound, then FORWARD) and `child_pos > n`
# (a previous Produced — seek the next alternative).

function _step_assoc!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        kids::Vector{Union{Nothing, MatchFrameT}},
        bind_marks::Vector{Int}, arg_start::Vector{Int}, capture_len::Vector{Int},
        min_tail::Vector{Int}, owns_bind::BitVector
    )
    plan = eng.pat.plans[pat_node]
    (op, head, children) = @match plan begin
        NodePlan.AssocCall(; op, head, children) => (op, head, children)
        _ => error(lazy"Assoc frame got a non-AssocCall plan at node $pat_node")
    end
    snbs = Graphs.outneighbors(eng.subj.dependency_graph, subj_node)
    sexpr = eng.subj[subj_node]
    sstart = @match sexpr begin
        BSImpl.Term(; f) => f isa BasicSymbolic{SymReal} ? 2 : 1
        _ => 1
    end
    n = length(children)
    m = length(snbs) - (sstart - 1)   # subject arg count
    backtrack = false

    if iszero(child_pos[])
        # init: head/arity lower bound; no identity coercion (milestone 7)
        mark[] = length(eng.trail)
        _assoc_min_tail!(eng, children, min_tail)
        ok = iscall(sexpr) && m >= min_tail[1]
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
    elseif child_pos[] > n
        # re-pushed for the next alternative: seek back — each resumed
        # position unwinds to its own mark (never a frame-level unwind)
        child_pos[] = n
        backtrack = true
    else
        # unreachable: this frame only re-enters after Produced (child_pos
        # left > n) — the engine drives the frame, not child pops
        error(lazy"Assoc frame re-entered at child_pos $(child_pos[])")
    end

    # index into `snbs` of the next subject arg to consume. Forward
    # dispatch only ever starts at position 1 (soff = sstart); every
    # other entry resumes via the backtrack seek, which sets soff
    # explicitly before breaking out to the forward loop.
    soff = sstart

    while true
        if child_pos[] > n
            # whole match: every subject arg must be consumed (§4.1)
            if soff == sstart + m
                return FrameStatus.Produced
            end
            child_pos[] = n
            backtrack = true
        end
        if backtrack
            # seek the deepest resumable position and resume it
            while child_pos[] >= 1
                j = child_pos[]
                kf = kids[j]
                if kf !== nothing
                    if step!(eng, kf) === FrameStatus.Produced
                        soff = arg_start[j] + 1
                        child_pos[] += 1
                        break
                    else
                        kids[j] = nothing
                    end
                elseif MData.isa_variant(
                        eng.pat.plans[children[j]], NodePlan.Segment
                    )
                    vid = @match eng.pat.plans[children[j]] begin
                        NodePlan.Segment(; var_id) => var_id
                    end
                    sidx = arg_start[j]
                    navail = length(snbs) - sidx + 1
                    amax = min(_seg_max(eng, vid), navail - min_tail[j + 1])
                    # a bound-elsewhere segment has no alternatives of
                    # its own — skip; resumable only if it owns the bind
                    if owns_bind[j] && capture_len[j] + 1 <= amax
                        _unwind!(eng, bind_marks[j])
                        st = _seg_advance!(
                            eng, vid, op, snbs, sidx, min_tail[j + 1], capture_len[j] + 1
                        )
                        if st === SegResult.Bound
                            owns_bind[j] = true
                            capture_len[j] = length(eng.binds.seq[vid])
                            soff = arg_start[j] + capture_len[j]
                            child_pos[] += 1
                            break
                        end
                    end
                    capture_len[j] = 0
                end
                child_pos[] -= 1
            end
            child_pos[] == 0 && return _call_fail!(eng, mark)
            backtrack = false
            continue
        end
        j = child_pos[]
        bind_marks[j] = length(eng.trail)
        arg_start[j] = soff
        child_pat = children[j]
        child_plan = eng.pat.plans[child_pat]
        is_seg_pos = MData.isa_variant(child_plan, NodePlan.Segment)
        is_leaf_pos = MData.isa_variant(child_plan, NodePlan.Literal) ||
            MData.isa_variant(child_plan, NodePlan.Slot)
        if is_seg_pos
            vid = @match child_plan begin
                NodePlan.Segment(; var_id) => var_id
            end
            was_bound = eng.binds.seg_op[vid] !== nothing
            st = _seg_advance!(
                eng, vid, op, snbs, soff, min_tail[j + 1], _seg_min(eng, vid)
            )
            if st === SegResult.Bound
                owns_bind[j] = !was_bound
                capture_len[j] = length(eng.binds.seq[vid])
                soff += capture_len[j]
                child_pos[] += 1
            else
                backtrack = true
            end
        elseif is_leaf_pos
            if _leaf_obligation!(eng, child_pat, snbs[soff])
                soff += 1
                child_pos[] += 1
            else
                backtrack = true
            end
        elseif eng.pat.is_ground[child_pat]
            # a ground subtree needs no frames — one isequal decides it
            if isequal(eng.pat.ir[child_pat], eng.subj[snbs[soff]])
                soff += 1
                child_pos[] += 1
            else
                backtrack = true
            end
        else
            kf = kids[j]
            if kf === nothing
                kf = _new_frame(child_plan, child_pat, snbs[soff], _nchildren(child_plan))
                kids[j] = kf
            end
            if step!(eng, kf) === FrameStatus.Produced
                soff += 1
                child_pos[] += 1
            else
                kids[j] = nothing
                backtrack = true
            end
        end
    end
    return
end
