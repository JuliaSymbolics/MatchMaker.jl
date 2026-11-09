# DESIGN.md §5.5e: Seq frame — contiguous-run segment capture under a
# free or associative head (A-heads also flatten and coerce, §4.5/§4.6).

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
function _is_opt_pos(eng::MatchEngine, child_pat::Int32)
    return @match eng.pat.plans[child_pat] begin
        NodePlan.Slot(; optional) => optional
        _ => false
    end
end

function _slot_vid(eng::MatchEngine, child_pat::Int32)
    return @match eng.pat.plans[child_pat] begin
        NodePlan.Slot(; var_id) => var_id
    end
end

function _seq_min_tail!(
        eng::MatchEngine, children::SmallV{Int32}, min_tail::Vector{Int}
    )
    min_tail[end] = 0
    for j in length(children):-1:1
        min_tail[j] = min_tail[j + 1] + @match eng.pat.plans[children[j]] begin
            NodePlan.Segment(; var_id) => _seg_min(eng, var_id)
            NodePlan.Slot(; optional) => optional ? 0 : 1
            _ => 1
        end
    end
    return min_tail
end

# Maximum subject args positions `from..end` can consume (saturating) —
# the suffix counterpart of `_seq_min_tail!`. A match must consume every
# arg, so a segment position j captures at least
# `navail - _seq_tail_cap(eng, children, j + 1)`; the last segment
# position's length is forced to the whole remainder.
function _seq_tail_cap(eng::MatchEngine, children::SmallV{Int32}, from::Int)
    cap = 0
    for k in from:length(children)
        add = @match eng.pat.plans[children[k]] begin
            NodePlan.Segment(; var_id) => _seg_max(eng, var_id)
            _ => 1
        end
        cap = add > typemax(Int) - cap ? typemax(Int) : cap + add
    end
    return cap
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
        # non-linear recheck: the captured arg list must be identical —
        # compare exprs (bound terms, not node indices: the IR interns by
        # === but weak_definitions can hold isequal-different nodes).
        seq = b.seq[vid]
        length(seq) == len || return SegResult.Dead
        if iszero(len)
            return SegResult.Bound
        end
        if _is_commutative_head(b.seg_op[vid], symtype(eng.subj[snbs[sidx]]))
            # bound under an unordered head — the capture is a multiset,
            # so the recheck compares multisets rather than the run's
            # incidental pool order (MatchPy `try_add_variable`)
            used = falses(len)
            for e in seq
                found = false
                for k in 1:len
                    if !used[k] &&
                            isequal(e, eng.subj[snbs[sidx + k - 1]])
                        used[k] = true
                        found = true
                        break
                    end
                end
                found || return SegResult.Dead
            end
            return SegResult.Bound
        end
        for i in 1:len
            isequal(
                seq[i], eng.subj[snbs[sidx + i - 1]]
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
        push!(seq, eng.subj[snbs[sidx + i - 1]])
    end
    b.seg_op[vid] = op
    push!(eng.trail, vid)
    if !_ready_constraints!(eng, vid)
        _unwind!(eng, length(eng.trail) - 1)
        return SegResult.Longer
    end
    return SegResult.Bound
end

# Resume the segment at position `j`: unwind to its mark and rebind at
# the next allowed length. Returns the new bound length, or `nothing`
# when the position has no alternatives left — either it doesn't own the
# var's bind (bound elsewhere: rechecks only), it's at `amax`, or the
# rebind attempt fails.
function _seq_seg_resume!(
        eng::MatchEngine, @nospecialize(op), snbs, vid::Int32, j::Int,
        bind_marks::Vector{Int}, arg_start::Vector{Int},
        capture_len::Vector{Int}, min_tail::Vector{Int}, owns_bind::BitVector
    )
    sidx = arg_start[j]
    navail = length(snbs) - sidx + 1
    amax = min(_seg_max(eng, vid), navail - min_tail[j + 1])
    owns_bind[j] && capture_len[j] + 1 <= amax || return nothing
    _unwind!(eng, bind_marks[j])
    st = _seg_advance!(
        eng, vid, op, snbs, sidx, min_tail[j + 1], capture_len[j] + 1
    )
    if st !== SegResult.Bound
        capture_len[j] = 0
        return nothing
    end
    owns_bind[j] = true
    capture_len[j] = length(eng.binds.seq[vid])
    return capture_len[j]
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
### Seq frame (§5.5e)
###

# Flatten nested same-op calls for an associative head: `f(a, f(b, c))`
# under A is `f(a, b, c)`. Returns the flattened node-id vector, or
# `nothing` when no arg nests `op` (the caller keeps `snbs` — the common
# case, since canonical `Add`/`Mul` args are flat by construction).
function _flat_args(
        eng::MatchEngine, @nospecialize(op), snbs, sstart::Int
    )
    flat = true
    for i in sstart:length(snbs)
        e = eng.subj[snbs[i]]
        if iscall(e) && operation(e) === op
            flat = false
            break
        end
    end
    flat && return nothing
    args = Int32[]
    for i in sstart:length(snbs)
        _push_flat!(eng, op, snbs[i], args)
    end
    return args
end

function _push_flat!(eng::MatchEngine, @nospecialize(op), node::Int32, args)
    e = eng.subj[node]
    if iscall(e) && operation(e) === op
        nbs = Graphs.outneighbors(eng.subj.dependency_graph, node)
        ss = @match e begin
            BSImpl.Term(; f) => f isa BasicSymbolic{SymReal} ? 2 : 1
            _ => 1
        end
        for k in ss:length(nbs)
            _push_flat!(eng, op, nbs[k], args)
        end
    else
        push!(args, node)
    end
    return args
end

# Bind `vid` to its spec's default (§4.7). A var bound elsewhere checks
# the bound value against the default; a free var binds `extra` (the
# default may be a literal — not a subject node).
function _opt_default!(eng::MatchEngine, vid::Int32)
    dflt = @match eng.pat.var_specs[vid] begin
        VarSpec.Slot(; default) => default
        _ => nothing
    end
    b = eng.binds
    if is_bound_extra(b, vid)
        return isequal(b.extra[vid], dflt)::Bool
    end
    if is_bound_node(b, vid)
        return isequal(eng.subj[b.node[vid]], dflt)
    end
    spec = eng.pat.var_specs[vid]
    pred = spec.predicate
    if MData.isa_variant(spec, VarSpec.Slot) && dflt !== nothing &&
            pred !== nothing && !pred(dflt)
        return false
    end
    b.extra[vid] = dflt
    push!(eng.trail, vid)
    if !_ready_constraints!(eng, vid)
        _unwind!(eng, length(eng.trail) - 1)
        return false
    end
    return true
end

# Compute the subject argument view for this obligation: `(sargs,
# sstart)`, or `nothing` when the subject can't satisfy the head. Under
# an A head, nested same-op calls are flattened (§4.5) and a non-f-call
# subject coerces to `[subject]` when the head declares an identity
# (§4.6). Applies the head obligation on success.
function _seq_args(
        eng::MatchEngine, @nospecialize(op), head::Int32, subj_node::Int32
    )
    snbs = Graphs.outneighbors(eng.subj.dependency_graph, subj_node)
    sexpr = eng.subj[subj_node]
    sstart = @match sexpr begin
        BSImpl.Term(; f) => f isa BasicSymbolic{SymReal} ? 2 : 1
        _ => 1
    end
    assoc = _is_associative_head(op, symtype(sexpr))
    if iscall(sexpr)
        sop = operation(sexpr)
        ok = iszero(head) ? (op === sop) :
            _head_obligation!(eng, head, sop)
        if ok
            if assoc
                flat = _flat_args(eng, op, snbs, sstart)
                flat === nothing ||
                    return (flat, 1)
            end
            # collect to keep the return type `Vector{Int32}` — the
            # flattened/coerced paths allocate anyway
            return (collect(snbs), sstart)
        end
    end
    assoc || return nothing
    # identity coercion (§4.6): the subject becomes its own only argument
    _identity_el(op, symtype(sexpr)) === nothing && return nothing
    return (Int32[subj_node], 1)
end

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

function _step_seq!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        kids::Vector{Int32},
        bind_marks::Vector{Int}, arg_start::Vector{Int}, capture_len::Vector{Int},
        min_tail::Vector{Int}, owns_bind::BitVector
    )
    plan = eng.pat.plans[pat_node]
    (op, head, children) = @match plan begin
        NodePlan.SeqCall(; op, head, children) => (op, head, children)
        _ => error(lazy"Seq frame got a non-SeqCall plan at node $pat_node")
    end
    n = length(children)

    # fresh frames take their trail mark before any obligation runs —
    # `_seq_args` applies the head obligation, and an early failure must
    # unwind to *this* frame's entry mark, never past it
    iszero(child_pos[]) && (mark[] = length(eng.trail))

    # subject arg view — recomputed each step: cheap when the subject is
    # a flat f-call (snbs reused); allocated only for flattened A-subjects
    # or singleton coercion
    got = _seq_args(eng, op, head, subj_node)
    got === nothing && return _call_fail!(eng, mark)
    (snbs, sstart) = got
    m = length(snbs) - (sstart - 1)   # subject arg count
    backtrack = false

    if iszero(child_pos[])
        # init: arity lower bound; head/coercion/flattening done above
        _seq_min_tail!(eng, children, min_tail)
        m >= min_tail[1] || return _call_fail!(eng, mark)
        child_pos[] = 1
    elseif child_pos[] > n
        # re-pushed for the next alternative: seek back — each resumed
        # position unwinds to its own mark (never a frame-level unwind)
        child_pos[] = n
        backtrack = true
    else
        # unreachable: this frame only re-enters after Produced (child_pos
        # left > n) — the engine drives the frame, not child pops
        error(lazy"Seq frame re-entered at child_pos $(child_pos[])")
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
                kf = _kid(eng, kids, j)
                if kf !== nothing
                    if step!(eng, kf) === FrameStatus.Produced
                        soff = arg_start[j] + 1
                        child_pos[] += 1
                        break
                    else
                        _drop_kid!(eng, kids, j)
                    end
                elseif MData.isa_variant(
                        eng.pat.plans[children[j]], NodePlan.Segment
                    )
                    vid = @match eng.pat.plans[children[j]] begin
                        NodePlan.Segment(; var_id) => var_id
                    end
                    len = _seq_seg_resume!(
                        eng, op, snbs, vid, j,
                        bind_marks, arg_start, capture_len, min_tail, owns_bind
                    )
                    if len !== nothing
                        soff = arg_start[j] + len
                        child_pos[] += 1
                        break
                    end
                elseif _is_opt_pos(eng, children[j])
                    # consume-alternative already used — try the default
                    if capture_len[j] == 1
                        vid = _slot_vid(eng, children[j])
                        _unwind!(eng, bind_marks[j])
                        if _opt_default!(eng, vid)
                            capture_len[j] = 0
                            soff = arg_start[j]
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
        is_opt_pos = MData.isa_variant(child_plan, NodePlan.Slot) &&
            _is_opt_pos(eng, child_pat)
        is_leaf_pos = MData.isa_variant(child_plan, NodePlan.Literal) ||
            MData.isa_variant(child_plan, NodePlan.Slot)
        if is_seg_pos
            vid = @match child_plan begin
                NodePlan.Segment(; var_id) => var_id
            end
            was_bound = eng.binds.seg_op[vid] !== nothing
            # Coverage forces a lower bound too: positions j+1.. take at
            # most _seq_tail_cap args — the last segment takes the rest.
            first_len = max(
                _seg_min(eng, vid),
                length(snbs) - soff + 1 - _seq_tail_cap(eng, children, j + 1)
            )
            st = _seg_advance!(
                eng, vid, op, snbs, soff, min_tail[j + 1], first_len
            )
            if st === SegResult.Bound
                owns_bind[j] = !was_bound
                capture_len[j] = length(eng.binds.seq[vid])
                soff += capture_len[j]
                child_pos[] += 1
            else
                backtrack = true
            end
        elseif is_opt_pos
            # §4.7: consume one arg first, then the default alternative
            vid = _slot_vid(eng, child_pat)
            if soff <= sstart + m - 1 &&
                    _leaf_obligation!(eng, child_pat, snbs[soff])
                capture_len[j] = 1
                soff += 1
                child_pos[] += 1
            elseif _opt_default!(eng, vid)
                capture_len[j] = 0
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
            kf = _kid(eng, kids, j)
            if kf === nothing
                kf = _acquire_frame!(eng, child_plan, child_pat, snbs[soff])
                kids[j] = _push_frame!(eng, kf)
            end
            if step!(eng, kf) === FrameStatus.Produced
                soff += 1
                child_pos[] += 1
            else
                _drop_kid!(eng, kids, j)
                backtrack = true
            end
        end
    end
    return
end
