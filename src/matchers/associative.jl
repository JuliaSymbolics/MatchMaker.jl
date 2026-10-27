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

# Try binding segment var `vid` to `len` subject args starting at index
# `sidx` of `snbs`. Returns:
#   :ok    — bound (or an identical non-linear recheck passed)
#   :next  — this length fails but a longer capture may succeed
#   :fail  — position dead (per-element predicate or non-linear recheck)
function _seg_try!(
        eng::MatchEngine, vid::Int32, @nospecialize(op),
        snbs, sidx::Int, len::Int
    )
    b = eng.binds
    if b.seg_op[vid] !== nothing
        seq = b.seq[vid]
        length(seq) == len || return :fail
        for i in 1:len
            seq[i] == snbs[sidx + i - 1] || return :fail
        end
        return :ok
    end
    (pred, seqpred) = _seg_preds(eng, vid)
    if pred !== nothing
        for i in 1:len
            pred(eng.subj[snbs[sidx + i - 1]])::Bool || return :fail
        end
    end
    if seqpred !== nothing
        buf = BasicSymbolic{SymReal}[
            eng.subj[snbs[sidx + i - 1]] for i in 1:len
        ]
        seqpred(buf)::Bool || return :next
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
        return :next
    end
    return :ok
end

# Try lengths `first_len` upward at a segment position; `amax` is
# `min(spec.max, avail - required_after)`. Returns :ok or :fail.
# A var bound elsewhere has exactly one viable length — its bound run.
function _seg_advance!(
        eng::MatchEngine, vid::Int32, @nospecialize(op), snbs,
        sidx::Int, min_tail_next::Int, first_len::Int
    )
    navail = length(snbs) - sidx + 1
    amax = min(_seg_max(eng, vid), navail - min_tail_next)
    if eng.binds.seg_op[vid] !== nothing
        len = length(eng.binds.seq[vid])
        len <= amax || return :fail
        return _seg_try!(eng, vid, op, snbs, sidx, len)
    end
    len = first_len
    while len <= amax
        st = _seg_try!(eng, vid, op, snbs, sidx, len)
        st === :ok && return :ok
        st === :fail && return :fail
        len += 1
    end
    return :fail
end

###
### Assoc frame (§5.5e)
###

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

    # subject-arg offset for the current dispatch position: everything
    # before it consumed `capture_len[p]` (segments) or 1 arg each
    soff = sstart
    for p in 1:(child_pos[] - 1)
        soff += MData.isa_variant(eng.pat.plans[children[p]], NodePlan.Segment) ?
            capture_len[p] : 1
    end

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
                        if st === :ok
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
        cp = children[j]
        cplan = eng.pat.plans[cp]
        cplan_is_seg = MData.isa_variant(cplan, NodePlan.Segment)
        cplan_is_leaf = !cplan_is_seg && (
            MData.isa_variant(cplan, NodePlan.Literal) ||
                MData.isa_variant(cplan, NodePlan.Slot)
        )
        if cplan_is_seg
            vid = @match cplan begin
                NodePlan.Segment(; var_id) => var_id
            end
            was_bound = eng.binds.seg_op[vid] !== nothing
            st = _seg_advance!(
                eng, vid, op, snbs, soff, min_tail[j + 1], _seg_min(eng, vid)
            )
            if st === :ok
                owns_bind[j] = !was_bound
                capture_len[j] = length(eng.binds.seq[vid])
                soff += capture_len[j]
                child_pos[] += 1
            else
                backtrack = true
            end
        elseif cplan_is_leaf
            if _leaf_obligation!(eng, cp, snbs[soff])
                soff += 1
                child_pos[] += 1
            else
                backtrack = true
            end
        elseif eng.pat.is_ground[cp]
            # a ground subtree needs no frames — one isequal decides it
            if isequal(eng.pat.ir[cp], eng.subj[snbs[soff]])
                soff += 1
                child_pos[] += 1
            else
                backtrack = true
            end
        else
            kf = kids[j]
            if kf === nothing
                kf = _new_frame(cplan, cp, snbs[soff], _nchildren(cplan))
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
