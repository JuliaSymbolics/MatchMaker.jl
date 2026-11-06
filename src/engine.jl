# DESIGN.md §5.3–5.5: MatchEngine, MatchFrame ADT, leaf obligations, Call frame.

###
### FrameStatus (§5.4)
###

"""
    FrameStatus

Result of one [`step!`](@ref) call on a [`MatchFrame`](@ref) (DESIGN.md §5.4).

- `Produced` — the frame finished one complete alternative for its subtree:
  that alternative's bindings are on `eng.trail`, and the frame stays live —
  the next `step!` resumes the search for further alternatives.
- `Matched` — the frame's obligation is fully satisfied and it produced no
  resumable alternatives; the engine pops it. (Reserved for single-shot
  frames; `Call` frames never return it.)
- `Failed` — the frame is exhausted: no more alternatives exist. Its
  bindings were already unwound to its trail mark; the engine pops it.
"""
@enumx FrameStatus Produced Matched Failed
const FrameStatusT = FrameStatus.T

###
### MatchFrame (§5.4)
###

"""
    MatchFrame

Mutable state for one in-progress node match — a frame (DESIGN.md §5.4).
Julia has no cheap coroutines, so instead of a generator that yields each
alternative, a frame *is* the suspended enumeration: it remembers where the
search left off, and [`step!`](@ref) advances it to the next alternative.
Each call frame owns per-position child frames, so a parent's state survives
backtracking — `eng.root` therefore only ever holds the root.

`Call(pat_node, subj_node, child_pos, trail_mark, kids)` — the frame for a
`NodePlan.Call` (free head, positional children): `child_pos` is the
argument position currently being enumerated (`0` = uninitialized),
`trail_mark` the trail length at frame creation (its unwind target), and
`kids` the live child frame per position — `nothing` for leaf positions,
since literal/slot obligations are applied inline by the parent and never
get frames.

`Seq(pat_node, subj_node, child_pos, trail_mark, kids, bind_marks,
arg_start, capture_len, min_tail, owns_bind)` — the frame for a
`NodePlan.SeqCall`: an argument list where each position either consumes
exactly one subject argument or is a `segment` that consumes a contiguous
run. `child_pos` is the pattern position currently being dispatched;
`trail_mark` is the trail length when the frame was created — its unwind
target on failure; `kids` holds live child frames (one per position).

`bind_marks[i]` — the trail length before position `i` bound anything;
unwinding to it clears position `i`'s bind and every later position's.
`arg_start[i]` — the subject argument offset position `i` begins at.
`capture_len[i]` — the length a segment position currently captures
(`0` = unbound). `min_tail[i]` — the minimum number of subject args
positions `i..n` still require (`min_tail[n+1]` is the zero sentinel;
computed once at init). `owns_bind[i]` — whether position `i` *created*
its segment var's current bind; a var bound elsewhere can only recheck,
so it has no alternatives of its own.
"""
@data mutable MatchFrame begin
    struct Call
        pat_node::Int32
        subj_node::Int32
        child_pos::Base.RefValue{Int}
        trail_mark::Base.RefValue{Int}
        kids::Vector{Union{Nothing, MatchFrame.Type}}
    end
    struct Seq
        pat_node::Int32
        subj_node::Int32
        child_pos::Base.RefValue{Int}
        trail_mark::Base.RefValue{Int}
        kids::Vector{Union{Nothing, MatchFrame.Type}}
        bind_marks::Vector{Int}
        arg_start::Vector{Int}
        capture_len::Vector{Int}
        min_tail::Vector{Int}
        owns_bind::BitVector
    end
    struct Comm
        pat_node::Int32
        subj_node::Int32
        child_pos::Base.RefValue{Int}
        trail_mark::Base.RefValue{Int}
        "Pattern children in dispatch order: fixed, slots, optionals, segments."
        order::Vector{Int32}
        kids::Vector{Union{Nothing, MatchFrame.Type}}
        "Trail mark before each position's binds."
        bind_marks::Vector{Int}
        "Subject arg index assigned to each non-segment position (0=none)."
        assigned::Vector{Int32}
        "Next candidate arg index to try per position."
        scan::Vector{Int32}
        "Which subject args are consumed."
        used::BitVector
        "Selected arg indices per segment position."
        seg_sel::Vector{SmallV{Int32}}
        "Available arg pool recorded per segment position."
        seg_pool::Vector{Vector{Int32}}
        "Suffix minimum args required from each position onward."
        min_tail::Vector{Int}
        "Whether a segment position created its var's bind."
        owns_bind::BitVector
    end
    struct AC
        pat_node::Int32
        subj_node::Int32
        child_pos::Base.RefValue{Int}
        trail_mark::Base.RefValue{Int}
        """Pattern children in dispatch order: fixed ∪ slots (sorted by
        ascending candidate count at init), then optionals, then segments.
        Every per-position array below (kids/bind_marks/assigned/scan/
        cands/seg_*) is indexed by dispatch position j — `order[j]` is the
        pattern child dispatched there — not by pattern-child index."""
        order::Vector{Int32}
        kids::Vector{Union{Nothing, MatchFrame.Type}}
        "Trail mark before each position's binds."
        bind_marks::Vector{Int}
        """Subject arg index assigned to each non-segment position
        (0=none; -1 = an optional position bound its default instead)."""
        assigned::Vector{Int32}
        "Next candidate index to try per position."
        scan::Vector{Int32}
        "Which subject args are consumed."
        used::BitVector
        "Phase-1 candidate arg indices per assignment position (§5.5f)."
        cands::Vector{SmallV{Int32}}
        "Selected arg indices per segment position."
        seg_sel::Vector{SmallV{Int32}}
        "Available arg pool recorded per segment position."
        seg_pool::Vector{Vector{Int32}}
        "Suffix minimum args required from each position onward."
        min_tail::Vector{Int}
        "Whether a segment position created its var's bind."
        owns_bind::BitVector
    end
end
const MatchFrameT = MatchFrame.Type

"""
    _new_frame(plan, pat_node, subj_node, nchildren) -> MatchFrameT

Build the frame for the non-leaf plan at `pat_node` against subject node
`subj_node`. `nchildren` sizes the per-position `kids` storage (children
count of `plan`'s argument list). Leaf plans never get frames.
"""
function _new_frame(
        plan::NodePlanT, pat_node::Int32, subj_node::Int32,
        nchildren::Int
    )
    return @match plan begin
        NodePlan.Call(; op, head) => MatchFrame.Call(
            pat_node, subj_node, Ref(0), Ref(0),
            fill!(Vector{Union{Nothing, MatchFrameT}}(undef, nchildren), nothing)
        )
        NodePlan.SeqCall(; op, head) => MatchFrame.Seq(
            pat_node, subj_node, Ref(0), Ref(0),
            fill!(Vector{Union{Nothing, MatchFrameT}}(undef, nchildren), nothing),
            zeros(Int, nchildren), zeros(Int, nchildren),
            zeros(Int, nchildren), zeros(Int, nchildren + 1),
            falses(nchildren)
        )
        NodePlan.CommCall(; fixed, slots, optionals, segments) => begin
            order = Int32[]
            append!(order, fixed, slots, optionals, segments)
            np = length(order)
            MatchFrame.Comm(
                pat_node, subj_node, Ref(0), Ref(0), order,
                fill!(Vector{Union{Nothing, MatchFrameT}}(undef, np), nothing),
                zeros(Int, np), zeros(Int32, np), ones(Int32, np),
                BitVector(), [SmallV{Int32}() for _ in 1:np],
                Vector{Int32}[Int32[] for _ in 1:np],
                zeros(Int, np + 1), falses(np)
            )
        end
        NodePlan.ACCall(; fixed, slots, optionals, segments) => begin
            order = Int32[]
            append!(order, fixed, slots, optionals, segments)
            np = length(order)
            MatchFrame.AC(
                pat_node, subj_node, Ref(0), Ref(0), order,
                fill!(Vector{Union{Nothing, MatchFrameT}}(undef, np), nothing),
                zeros(Int, np), zeros(Int32, np), ones(Int32, np),
                BitVector(), [SmallV{Int32}() for _ in 1:np],
                [SmallV{Int32}() for _ in 1:np],
                Vector{Int32}[Int32[] for _ in 1:np],
                zeros(Int, np + 1), falses(np)
            )
        end
        _ => error(
            lazy"pattern node $pat_node has an unsupported plan for this milestone"
        )
    end
end

###
### MatchEngine (§5.4)
###

"""
    MatchEngine

A defunctionalized backtracking machine (DESIGN.md §5.4). `root` is the
live root frame (`nothing` for leaf roots, which `next_match!` applies
inline); `binds`/`trail` hold index-only binding state; `argbuf` is a
reusable argument buffer for constraint evaluation. `steps` meters work.
"""
mutable struct MatchEngine
    "Compiled pattern."
    const pat::Matcher
    "Subject DAG."
    const subj::IRStructure{SymReal}
    "Node index of the subject root."
    const sroot::Int32
    "Live root frame; `nothing` for leaf-root patterns."
    root::Union{Nothing, MatchFrameT}
    "Index-only binding state."
    const binds::Bindings
    "Var ids bound, in order — backtracking unwinds to a mark."
    const trail::Vector{Int32}
    "Compiled constraints (var syms resolved to ids)."
    const constraints::Vector{EngineConstraint}
    "Whether a constraint has fired under current bindings."
    const constr_fired::BitVector
    "var_id -> constraint indices mentioning it."
    const var_constrs::Vector{SmallV{Int32}}
    "Reusable arg vector for constraint calls."
    const argbuf::Vector{BasicSymbolic{SymReal}}
    "Reusable arg vector for segment sequence_predicates."
    const segbuf::Vector{BasicSymbolic{SymReal}}
    "Whether the (leaf) root obligation has already yielded."
    root_done::Bool
    "Work meter; compare against `maxsteps`."
    steps::Int
    "Step budget; the search ends once `steps` reaches it."
    const maxsteps::Int
end

"""
    $TYPEDSIGNATURES

Build a [`MatchEngine`](@ref) for `pat` on subject `s`. `constraints` is a
collection of [`Constraint`](@ref)s; variable syms are resolved to ids —
unknown syms throw `ArgumentError`.
"""
function MatchEngine(
        pat::Matcher, s::BasicSymbolic{SymReal},
        constraints::AbstractVector{Constraint}; maxsteps::Int = typemax(Int)
    )
    subj = IRStructure{SymReal}()
    sroot = populate_ir!(subj, s)
    binds = Bindings(pat.nvars)
    trail = Int32[]
    argbuf = BasicSymbolic{SymReal}[]
    segbuf = BasicSymbolic{SymReal}[]

    econstrs = EngineConstraint[]
    var_constrs = [SmallV{Int32}() for _ in 1:pat.nvars]
    for c in constraints
        var_ids = SmallV{Int32}()
        for v in c.vars
            haskey(pat.var_of, v) || throw(
                ArgumentError(
                    lazy"constraint variable $v is not a pattern variable"
                )
            )
            push!(var_ids, pat.var_of[v])
        end
        ci = Int32(length(econstrs) + 1)
        push!(econstrs, EngineConstraint(c.fn, var_ids))
        for vid in var_ids
            push!(var_constrs[vid], ci)
        end
    end

    eng = MatchEngine(
        pat, subj, sroot, nothing, binds, trail, econstrs,
        falses(length(econstrs)), var_constrs, argbuf, segbuf, false, 0,
        maxsteps
    )

    # Leaf roots (a bare slot/literal pattern) are applied inline by
    # `next_match!` — there is no parent to host the obligation.
    root_plan = pat.plans[pat.root]
    isleaf = MData.isa_variant(root_plan, NodePlan.Literal) ||
        MData.isa_variant(root_plan, NodePlan.Slot)
    if !isleaf
        eng.root = _root_frame(root_plan, pat.root, sroot)
    end
    return eng
end

function _root_frame(plan::NodePlanT, pat_node::Int32, subj_node::Int32)
    return @match plan begin
        NodePlan.Call(; children) => _new_frame(
            plan, pat_node, subj_node, length(children)
        )
        NodePlan.SeqCall(; children) => _new_frame(
            plan, pat_node, subj_node, length(children)
        )
        NodePlan.CommCall(; fixed, slots, optionals, segments) => _new_frame(
            plan, pat_node, subj_node,
            length(fixed) + length(slots) + length(optionals) + length(segments)
        )
        NodePlan.ACCall(; fixed, slots, optionals, segments) => _new_frame(
            plan, pat_node, subj_node,
            length(fixed) + length(slots) + length(optionals) + length(segments)
        )
        _ => _new_frame(plan, pat_node, subj_node, 0)
    end
end

###
### Trail (§5.3)
###

# Pop bindings back to `mark`, clearing node/seq/seg_op/extra and any
# constraints whose fired bit depended on an unbound var.
function _unwind!(eng::MatchEngine, mark::Int)
    while length(eng.trail) > mark
        vid = pop!(eng.trail)
        b = eng.binds
        b.node[vid] = 0
        b.seg_op[vid] = nothing
        b.extra[vid] = nothing
        for ci in eng.var_constrs[vid]
            eng.constr_fired[ci] = false
        end
    end
    return nothing
end

###
### Constraints (§4.9)
###

# Fire every not-yet-fired constraint mentioning `vid` whose vars are all
# bound. Returns false on the first violated constraint.
function _ready_constraints!(eng::MatchEngine, vid::Int32)
    for ci in eng.var_constrs[vid]
        eng.constr_fired[ci] && continue
        c = eng.constraints[ci]
        allbound = true
        for v in c.var_ids
            allbound = is_bound_node(eng.binds, v) ||
                is_bound_extra(eng.binds, v) || is_bound_seq(eng.binds, v)
            allbound || break
        end
        allbound || continue
        resize!(eng.argbuf, length(c.var_ids))
        for (i, v) in enumerate(c.var_ids)
            eng.argbuf[i] = _bound_value(eng, v)
        end
        c.fn(eng.argbuf)::Bool || return false
        eng.constr_fired[ci] = true
    end
    return true
end

# The materialized value of a bound var (single expr; segments reconstruct).
function _bound_value(eng::MatchEngine, vid::Int32)
    is_bound_extra(eng.binds, vid) && return Const{SymReal}(eng.binds.extra[vid])
    b = eng.binds
    b.seg_op[vid] !== nothing && return _seg_value(eng, vid)
    is_bound_node(b, vid) || error(lazy"var $vid is not bound")
    return eng.subj[b.node[vid]]
end

# Reconstruct `f(captured…)` for a segment binding (§5.6). Built with
# BSImpl.Term directly (no `term`/`promote_*` dispatch); note this produces a
# `Term` even for canonical `+`/`*` heads — Add/Mul reconstruction lands with
# segment binds in a later milestone.
function _seg_value(eng::MatchEngine, vid::Int32)
    b = eng.binds
    f = b.seg_op[vid]
    args = ArgsT{SymReal}()
    sizehint!(args, length(b.seq[vid]))
    for i in b.seq[vid]
        push!(args, eng.subj[i])
    end
    if f === (+)
        return SymbolicUtils.add_worker(SymReal, args)
    elseif f === (*)
        return SymbolicUtils.mul_worker(SymReal, args)
    elseif isempty(args)
        e = _identity_el(f, symtype(eng.subj[eng.sroot]))
        e !== nothing && return Const{SymReal}(e)
        return BSImpl.Term{SymReal}(f, args; type = promote_symtype(f))
    else
        return BSImpl.Term{SymReal}(
            f, args; type = promote_symtype(f, map(symtype, args)...)
        )
    end
end

###
### Leaf obligations (§5.5a,b) — applied inline by parents, never framed
###

# `symtype <: ` through the @nospecialize fast-path wrapper (§5.5b):
# enumerate the wants that dominate (Any/Number/Real) and fall back to `<:`.
function _symtype_ok(
        @nospecialize(cand::SymbolicUtils.TypeT),
        @nospecialize(want::SymbolicUtils.TypeT)
    )
    want === Any && return true
    cand === want && return true
    want === Number && return _is_number_st(cand)
    want === Real && return (
        cand === Int || cand === Float64 || cand === Float32 ||
            cand === Integer || cand === Rational{Int} || cand === Bool ||
            cand <: Real
    )
    return cand <: want
end

# Apply the leaf plan at `pnode` against subject node `snode`.
# Returns whether the obligation succeeded; any binding is trail-recorded.
function _leaf_obligation!(eng::MatchEngine, pnode::Int32, snode::Int32)
    return @match eng.pat.plans[pnode] begin
        NodePlan.Literal() => isequal(eng.pat.ir[pnode], eng.subj[snode])
        NodePlan.Slot(; var_id) => _slot_obligation!(eng, var_id, snode)
        _ => error(lazy"leaf obligation got a non-leaf plan at node $pnode")
    end
end

function _slot_obligation!(eng::MatchEngine, vid::Int32, snode::Int32)
    b = eng.binds
    if is_bound_extra(b, vid)
        return isequal(b.extra[vid], eng.subj[snode])
    end
    if is_bound_node(b, vid)
        return isequal(eng.subj[b.node[vid]], eng.subj[snode])
    end
    ex = eng.subj[snode]
    spec = eng.pat.var_specs[vid]
    vsym = eng.pat.var_syms[vid]
    _symtype_ok(symtype(ex), symtype(vsym)) || return false
    isequal(shape(ex), shape(vsym)) || return false
    pred = @match spec begin
        VarSpec.Slot(; predicate) => predicate
        _ => nothing
    end
    if pred !== nothing
        pred(ex)::Bool || return false
    end
    b.node[vid] = snode
    push!(eng.trail, vid)
    if !_ready_constraints!(eng, vid)
        _unwind!(eng, length(eng.trail) - 1)   # drop just this bind
        return false
    end
    return true
end

# Bind a head-slot var to a non-symbolic operation value (§4.10).
function _slot_bind_op!(eng::MatchEngine, vid::Int32, @nospecialize(op))
    b = eng.binds
    if is_bound_extra(b, vid)
        return b.extra[vid] === op
    end
    is_bound_node(b, vid) && return false
    spec = eng.pat.var_specs[vid]
    pred = @match spec begin
        VarSpec.Slot(; predicate) => predicate
        _ => nothing
    end
    if pred !== nothing
        pred(Const{SymReal}(op))::Bool || return false
    end
    b.extra[vid] = op
    push!(eng.trail, vid)
    return _ready_constraints!(eng, vid)
end

###
### step! protocol (§5.4)
###

# See `FrameStatus` for the contract of each return value.
function step!(eng::MatchEngine, f::MatchFrameT)
    return @match f begin
        MatchFrame.Call(; pat_node, subj_node, child_pos, trail_mark, kids) =>
            _step_call!(eng, pat_node, subj_node, child_pos, trail_mark, kids)
        MatchFrame.Seq(;
            pat_node, subj_node, child_pos, trail_mark, kids, bind_marks,
            arg_start, capture_len, min_tail, owns_bind
        ) =>
            _step_seq!(
            eng, pat_node, subj_node, child_pos, trail_mark, kids,
            bind_marks, arg_start, capture_len, min_tail, owns_bind
        )
        MatchFrame.Comm(;
            pat_node, subj_node, child_pos, trail_mark, order, kids,
            bind_marks, assigned, scan, used, seg_sel, seg_pool, min_tail,
            owns_bind
        ) =>
            _step_comm!(
            eng, pat_node, subj_node, child_pos, trail_mark, order,
            kids, bind_marks, assigned, scan, used, seg_sel, seg_pool,
            min_tail, owns_bind
        )
        MatchFrame.AC(;
            pat_node, subj_node, child_pos, trail_mark, order, kids,
            bind_marks, assigned, scan, used, cands, seg_sel, seg_pool,
            min_tail, owns_bind
        ) =>
            _step_ac!(
            eng, pat_node, subj_node, child_pos, trail_mark, order,
            kids, bind_marks, assigned, scan, used, cands, seg_sel,
            seg_pool, min_tail, owns_bind
        )
    end
end

###
### Call frame (§5.5c) — free head, positional children
###

function _step_call!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        kids::Vector{Union{Nothing, MatchFrameT}}
    )
    plan = eng.pat.plans[pat_node]
    (op, head, children) = @match plan begin
        NodePlan.Call(; op, head, children) => (op, head, children)
        _ => error(lazy"Call frame got a non-Call plan at node $pat_node")
    end
    snbs = Graphs.outneighbors(eng.subj.dependency_graph, subj_node)
    sexpr = eng.subj[subj_node]
    # Argument offset: symbolic ops precede args in the subject's nbs.
    sstart = @match sexpr begin
        BSImpl.Term(; f) => f isa BasicSymbolic{SymReal} ? 2 : 1
        _ => 1
    end
    n = length(children)
    backtrack = false

    if iszero(child_pos[])
        # init: call-shape, arity, op equality (or head obligation, §4.10)
        mark[] = length(eng.trail)
        ok = iscall(sexpr) &&
            length(snbs) - (sstart - 1) == length(children)
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
    else
        # re-entry: resume — seek the deepest live child for its next
        # alternative. No unwind here: the resumed child unwinds to its
        # own mark, preserving earlier siblings' binds; this frame's
        # own binds unwind only at _call_fail!.
        child_pos[] = n
        backtrack = true
    end

    while true
        if child_pos[] > n
            return FrameStatus.Produced
        end
        if backtrack
            # find the deepest live child and resume its enumerator
            while child_pos[] >= 1
                kf = kids[child_pos[]]
                if kf === nothing
                    child_pos[] -= 1
                    continue
                end
                if step!(eng, kf) === FrameStatus.Produced
                    child_pos[] += 1
                    break
                else
                    kids[child_pos[]] = nothing
                    child_pos[] -= 1
                end
            end
            child_pos[] == 0 && return _call_fail!(eng, mark)
            backtrack = false
            continue
        end
        cp = children[child_pos[]]
        cs = snbs[sstart + child_pos[] - 1]
        cplan = eng.pat.plans[cp]
        isleaf = MData.isa_variant(cplan, NodePlan.Literal) ||
            MData.isa_variant(cplan, NodePlan.Slot)
        # a ground subtree needs no frames — one isequal decides it (§5.2)
        if eng.pat.is_ground[cp]
            if isequal(eng.pat.ir[cp], eng.subj[cs])
                child_pos[] += 1
            else
                backtrack = true
            end
        elseif isleaf
            if _leaf_obligation!(eng, cp, cs)
                child_pos[] += 1
            else
                backtrack = true
            end
        else
            kf = kids[child_pos[]]
            if kf === nothing
                kf = _new_frame(cplan, cp, cs, _nchildren(cplan))
                kids[child_pos[]] = kf
            end
            if step!(eng, kf) === FrameStatus.Produced
                child_pos[] += 1
            else
                kids[child_pos[]] = nothing
                backtrack = true
            end
        end
    end
    return
end

function _call_fail!(eng::MatchEngine, mark::Base.RefValue{Int})
    _unwind!(eng, mark[])
    return FrameStatus.Failed
end

function _nchildren(plan::NodePlanT)
    return @match plan begin
        NodePlan.Call(; children) => length(children)
        NodePlan.SeqCall(; children) => length(children)
        NodePlan.CommCall(; fixed, slots, optionals, segments) =>
            length(fixed) + length(slots) + length(optionals) + length(segments)
        NodePlan.ACCall(; fixed, slots, optionals, segments) =>
            length(fixed) + length(slots) + length(optionals) + length(segments)
        _ => 0
    end
end

# Head obligation (§4.10): the subject's operation is itself a pattern
# position. Symbolic ops live in the subject IR; non-symbolic ops bind
# through `binds.extra` (slot plans only).
function _head_obligation!(eng::MatchEngine, head::Int32, @nospecialize(sop))
    if sop isa BasicSymbolic{SymReal}
        return _leaf_obligation!(eng, head, eng.subj[sop])
    end
    return @match eng.pat.plans[head] begin
        NodePlan.Slot(; var_id) => _slot_bind_op!(eng, var_id, sop)
        _ => false
    end
end

###
### next_match! (§5.4)
###

"""
    $TYPEDSIGNATURES

Advance `eng` to the next complete alternative. Returns `false` when the
search space is exhausted. A complete match leaves bindings on the trail;
the frames stay live so a further call resumes enumeration.
"""
function next_match!(eng::MatchEngine)
    eng.steps >= eng.maxsteps && return false
    root = eng.root
    if root === nothing
        # leaf root: single-shot obligation, applied inline (§5.4)
        eng.root_done && return false
        eng.root_done = true
        return _leaf_obligation!(eng, eng.pat.root, eng.sroot)
    end
    st = step!(eng, root)
    eng.steps += 1
    if st === FrameStatus.Produced
        return true
    else
        # Matched/Failed: the root frame is done
        eng.root = nothing
        return false
    end
end
