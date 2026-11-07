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
`kids` the stack index of the live child frame per position — `0` for
leaf positions and for positions with no live kid, since literal/slot
obligations are applied inline by the parent and never get frames.

`Seq(pat_node, subj_node, child_pos, trail_mark, kids, bind_marks,
arg_start, capture_len, min_tail, owns_bind)` — the frame for a
`NodePlan.SeqCall`: an argument list where each position either consumes
exactly one subject argument or is a `segment` that consumes a contiguous
run. `child_pos` is the pattern position currently being dispatched;
`trail_mark` is the trail length when the frame was created — its unwind
target on failure; `kids` holds each position's live child frame stack
index (one per position).

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
mutable struct CallFrame
    pat_node::Int32
    subj_node::Int32
    child_pos::Base.RefValue{Int}
    trail_mark::Base.RefValue{Int}
    kids::Vector{Int32}
end

mutable struct SeqFrame
    pat_node::Int32
    subj_node::Int32
    child_pos::Base.RefValue{Int}
    trail_mark::Base.RefValue{Int}
    kids::Vector{Int32}
    bind_marks::Vector{Int}
    arg_start::Vector{Int}
    capture_len::Vector{Int}
    min_tail::Vector{Int}
    owns_bind::BitVector
end

mutable struct CommFrame
    pat_node::Int32
    subj_node::Int32
    child_pos::Base.RefValue{Int}
    trail_mark::Base.RefValue{Int}
    "Pattern children in dispatch order: fixed, slots, optionals, segments."
    order::Vector{Int32}
    kids::Vector{Int32}
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

mutable struct ACFrame
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
    kids::Vector{Int32}
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

"""A match frame — the union of the concrete per-variant structs; `step!`
dispatches on the concrete type directly (small-union dispatch is a tag
check + jump)."""
const MatchFrameT = Union{CallFrame, SeqFrame, CommFrame, ACFrame}
const MatchFrame = MatchFrameT


###
### FramePool
###

"""
    FramePool

Per-variant freelists of dead frames. When `sp` retracts past index `i`,
every frame in `stk[i:sp]` is dead and can be recycled: `pool_release!`
returns them to the matching freelist and `pool_acquire!` hands out a
reset one — its buffers (`kids`, `assigned`, `seg_sel`, …) are resized
and cleared in place instead of reallocating per dispatch.
"""
struct FramePool
    call::Vector{CallFrame}
    seq::Vector{SeqFrame}
    comm::Vector{CommFrame}
    ac::Vector{ACFrame}
end
FramePool() = FramePool(CallFrame[], SeqFrame[], CommFrame[], ACFrame[])

"    _reset!(v, n, x) -> v — resize to `n`, fill with `x`."
function _reset!(v::AbstractVector, n::Int, x)
    resize!(v, n)
    fill!(v, x)
    return v
end

"_reset! for nested SmallV/Vector buffers: reuse live objects, empty them."
function _reset!(v::Vector{T}, n::Int) where T <: Union{SmallV{Int32}, Vector{Int32}}
    while length(v) < n
        push!(v, T())
    end
    resize!(v, n)
    foreach(empty!, v)
    return v
end

"""
    pool_release!(pool::FramePool, f::MatchFrameT)

Return `f` to the freelist for its variant. The frame's buffers keep
their capacity; `pool_acquire!` reinitializes every field on reuse, so
stale contents are never observed.
"""
pool_release!(pool::FramePool, f::CallFrame) = push!(pool.call, f)
pool_release!(pool::FramePool, f::SeqFrame) = push!(pool.seq, f)
pool_release!(pool::FramePool, f::CommFrame) = push!(pool.comm, f)
pool_release!(pool::FramePool, f::ACFrame) = push!(pool.ac, f)

"""
    pool_acquire!(pool, ::Type{CallFrame}, pat_node, subj_node, nchildren)
    pool_acquire!(pool, ::Type{CommFrame}, pat_node, subj_node,
                  fixed, slots, optionals, segments)

Return a frame of the requested variant — a reset pooled frame if one is
available, else a fresh allocation.
"""
function pool_acquire!(
        pool::FramePool, ::Type{CallFrame},
        pat_node::Int32, subj_node::Int32, n::Int
    )
    isempty(pool.call) && return CallFrame(
        pat_node, subj_node, Ref(0), Ref(0), zeros(Int32, n)
    )
    f = pop!(pool.call)
    f.pat_node = pat_node
    f.subj_node = subj_node
    f.child_pos[] = 0
    f.trail_mark[] = 0
    _reset!(f.kids, n, Int32(0))
    return f
end

function pool_acquire!(
        pool::FramePool, ::Type{SeqFrame},
        pat_node::Int32, subj_node::Int32, n::Int
    )
    isempty(pool.seq) && return SeqFrame(
        pat_node, subj_node, Ref(0), Ref(0),
        zeros(Int32, n),
        zeros(Int, n), zeros(Int, n), zeros(Int, n),
        zeros(Int, n + 1), falses(n)
    )
    f = pop!(pool.seq)
    f.pat_node = pat_node
    f.subj_node = subj_node
    f.child_pos[] = 0
    f.trail_mark[] = 0
    _reset!(f.kids, n, Int32(0))
    _reset!(f.bind_marks, n, 0)
    _reset!(f.arg_start, n, 0)
    _reset!(f.capture_len, n, 0)
    _reset!(f.min_tail, n + 1, 0)
    resize!(f.owns_bind, n)
    f.owns_bind .= false
    return f
end

function _reset_order!(f::Union{CommFrame, ACFrame}, fixed, slots, optionals, segments)
    np = length(fixed) + length(slots) + length(optionals) + length(segments)
    resize!(f.order, np)
    i = 0
    for g in (fixed, slots, optionals, segments), c in g
        f.order[i += 1] = c
    end
    return np
end

function _reset_comm_fields!(
        f::Union{CommFrame, ACFrame}, pat_node::Int32, subj_node::Int32,
        fixed, slots, optionals, segments
    )
    f.pat_node = pat_node
    f.subj_node = subj_node
    f.child_pos[] = 0
    f.trail_mark[] = 0
    np = _reset_order!(f, fixed, slots, optionals, segments)
    _reset!(f.kids, np, Int32(0))
    _reset!(f.bind_marks, np, 0)
    _reset!(f.assigned, np, Int32(0))
    _reset!(f.scan, np, Int32(1))
    empty!(f.used)
    _reset!(f.seg_sel, np)
    _reset!(f.seg_pool, np)
    _reset!(f.min_tail, np + 1, 0)
    resize!(f.owns_bind, np)
    f.owns_bind .= false
    return np
end

function pool_acquire!(
        pool::FramePool, ::Type{CommFrame},
        pat_node::Int32, subj_node::Int32,
        fixed, slots, optionals, segments
    )
    if isempty(pool.comm)
        order = Int32[]
        append!(order, fixed, slots, optionals, segments)
        np = length(order)
        return CommFrame(
            pat_node, subj_node, Ref(0), Ref(0), order,
            zeros(Int32, np),
            zeros(Int, np), zeros(Int32, np), ones(Int32, np),
            BitVector(), [SmallV{Int32}() for _ in 1:np],
            Vector{Int32}[Int32[] for _ in 1:np],
            zeros(Int, np + 1), falses(np)
        )
    end
    f = pop!(pool.comm)
    _reset_comm_fields!(f, pat_node, subj_node, fixed, slots, optionals, segments)
    return f
end

function pool_acquire!(
        pool::FramePool, ::Type{ACFrame},
        pat_node::Int32, subj_node::Int32,
        fixed, slots, optionals, segments
    )
    if isempty(pool.ac)
        order = Int32[]
        append!(order, fixed, slots, optionals, segments)
        np = length(order)
        return ACFrame(
            pat_node, subj_node, Ref(0), Ref(0), order,
            zeros(Int32, np),
            zeros(Int, np), zeros(Int32, np), ones(Int32, np),
            BitVector(), [SmallV{Int32}() for _ in 1:np],
            [SmallV{Int32}() for _ in 1:np],
            Vector{Int32}[Int32[] for _ in 1:np],
            zeros(Int, np + 1), falses(np)
        )
    end
    f = pop!(pool.ac)
    np = _reset_comm_fields!(
        f, pat_node, subj_node, fixed, slots, optionals, segments
    )
    _reset!(f.cands, np)
    return f
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
    "DFS stack of live frames; `stk[1]` is the root when `sp >= 1`."
    stk::Vector{Union{Nothing, MatchFrameT}}
    "Top of `stk` — the deepest live frame index."
    sp::Int
    "Freelist of dead frames by variant — see [`FramePool`](@ref)."
    pool::FramePool
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
    "Indices of constraints over no vars — applied at every produce."
    const global_constrs::SmallV{Int32}
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
    global_constrs = SmallV{Int32}()
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
        if isempty(var_ids)
            push!(global_constrs, ci)
        else
            for vid in var_ids
                push!(var_constrs[vid], ci)
            end
        end
    end

    eng = MatchEngine(
        pat, subj, sroot, Union{Nothing, MatchFrameT}[], 0, FramePool(),
        binds, trail, econstrs,
        falses(length(econstrs)), var_constrs, global_constrs,
        argbuf, segbuf, false, 0,
        maxsteps
    )

    # Leaf roots (a bare slot/literal pattern) are applied inline by
    # `next_match!` — there is no parent to host the obligation.
    root_plan = pat.plans[pat.root]
    isleaf = MData.isa_variant(root_plan, NodePlan.Literal) ||
        MData.isa_variant(root_plan, NodePlan.Slot)
    if !isleaf
        _push_frame!(eng, _acquire_frame!(eng, root_plan, pat.root, sroot))
    end
    return eng
end

"""
    _push_frame!(eng, kf) -> Int32

Push `kf` onto `eng`'s DFS frame stack; returns its stack index. Frames
are pushed in depth-first order — when a frame at index `i` fails, every
frame above `i` is dead (its own subtree plus already-dropped later
positions), so `sp` retracts to `i - 1` on failure.
"""
function _push_frame!(eng::MatchEngine, kf::MatchFrameT)
    ki = (eng.sp += 1)
    ki > length(eng.stk) ? push!(eng.stk, kf) : (eng.stk[ki] = kf)
    return ki
end

"Live child frame at position `j` of `kids`, or `nothing`."
function _kid(eng::MatchEngine, kids::Vector{Int32}, j::Int)
    ki = kids[j]
    return ki == 0 ? nothing : eng.stk[ki]
end

"Drop position `j`'s kid: release the dead range and retract `sp`."
function _drop_kid!(eng::MatchEngine, kids::Vector{Int32}, j::Int)
    ki = kids[j]
    kids[j] = Int32(0)
    ki == 0 && return
    _pool_release_range!(eng, ki, eng.sp)
    eng.sp = ki - 1
    return
end

"Return every frame in `stk[lo:hi]` to the pool and clear the slots."
function _pool_release_range!(eng::MatchEngine, lo::Integer, hi::Integer)
    for i in lo:hi
        f = eng.stk[i]
        f === nothing && continue
        eng.stk[i] = nothing
        pool_release!(eng.pool, f)
    end
    return
end

"""
    _acquire_frame!(eng, plan, pat_node, subj_node) -> MatchFrameT

Acquire the frame for the non-leaf `plan` — from `eng.pool` when a dead
frame of the right variant is available, else freshly allocated.
"""
function _acquire_frame!(
        eng::MatchEngine, plan::NodePlanT, pat_node::Int32, subj_node::Int32
    )
    return @match plan begin
        NodePlan.Call(; children) => pool_acquire!(
            eng.pool, CallFrame, pat_node, subj_node, length(children)
        )
        NodePlan.SeqCall(; children) => pool_acquire!(
            eng.pool, SeqFrame, pat_node, subj_node, length(children)
        )
        NodePlan.CommCall(; fixed, slots, optionals, segments) => pool_acquire!(
            eng.pool, CommFrame, pat_node, subj_node,
            fixed, slots, optionals, segments
        )
        NodePlan.ACCall(; fixed, slots, optionals, segments) => pool_acquire!(
            eng.pool, ACFrame, pat_node, subj_node,
            fixed, slots, optionals, segments
        )
        _ => error(
            lazy"pattern node $pat_node has an unsupported plan for this milestone"
        )
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

# See `FrameStatus` for the contract of each return value. An `isa`
# chain rather than method dispatch: the 5-type stk element union
# exceeds Julia's union-split limit, so method dispatch on it costs a
# generic call per step — `isa` folds to a tag check + jump instead.
@inline function step!(eng::MatchEngine, f::MatchFrameT)
    return if f isa ACFrame
        _step_ac!(
            eng, f.pat_node, f.subj_node, f.child_pos, f.trail_mark,
            f.order, f.kids, f.bind_marks, f.assigned, f.scan, f.used,
            f.cands, f.seg_sel, f.seg_pool, f.min_tail, f.owns_bind
        )
    elseif f isa CallFrame
        _step_call!(
            eng, f.pat_node, f.subj_node, f.child_pos, f.trail_mark, f.kids
        )
    elseif f isa SeqFrame
        _step_seq!(
            eng, f.pat_node, f.subj_node, f.child_pos, f.trail_mark,
            f.kids, f.bind_marks, f.arg_start, f.capture_len, f.min_tail,
            f.owns_bind
        )
    else
        _step_comm!(
            eng, f.pat_node, f.subj_node, f.child_pos, f.trail_mark,
            f.order, f.kids, f.bind_marks, f.assigned, f.scan, f.used,
            f.seg_sel, f.seg_pool, f.min_tail, f.owns_bind
        )
    end
end

###
### Call frame (§5.5c) — free head, positional children
###

function _step_call!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        child_pos::Base.RefValue{Int}, mark::Base.RefValue{Int},
        kids::Vector{Int32}
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
                kf = _kid(eng, kids, child_pos[])
                if kf === nothing
                    child_pos[] -= 1
                    continue
                end
                if step!(eng, kf) === FrameStatus.Produced
                    child_pos[] += 1
                    break
                else
                    _drop_kid!(eng, kids, child_pos[])
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
            kf = _kid(eng, kids, child_pos[])
            if kf === nothing
                kf = _acquire_frame!(eng, cplan, cp, cs)
                kids[child_pos[]] = _push_frame!(eng, kf)
            end
            if step!(eng, kf) === FrameStatus.Produced
                child_pos[] += 1
            else
                _drop_kid!(eng, kids, child_pos[])
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

# Fire every constraint over no vars — MatchPy's "global" constraints.
# Called once per produced alternative; the fn sees an empty arg vector.
function _global_constraints_ok!(eng::MatchEngine)
    isempty(eng.global_constrs) && return true
    resize!(eng.argbuf, 0)
    for ci in eng.global_constrs
        eng.constraints[ci].fn(eng.argbuf)::Bool || return false
    end
    return true
end

"""
    $TYPEDSIGNATURES

Advance `eng` to the next complete alternative. Returns `false` when the
search space is exhausted. A complete match leaves bindings on the trail;
the frames stay live so a further call resumes enumeration.
"""
function next_match!(eng::MatchEngine)
    eng.steps >= eng.maxsteps && return false
    if iszero(eng.sp)
        # leaf root: single-shot obligation, applied inline (§5.4)
        eng.root_done && return false
        eng.root_done = true
        return _leaf_obligation!(eng, eng.pat.root, eng.sroot) &&
            _global_constraints_ok!(eng)
    end
    while eng.steps < eng.maxsteps
        st = step!(eng, something(eng.stk[1]))
        eng.steps += 1
        if st === FrameStatus.Produced
            _global_constraints_ok!(eng) && return true
            # rejected: the frame resumes for the next alternative
            continue
        else
            # Matched/Failed: the root frame is done
            _pool_release_range!(eng, 1, eng.sp)
            eng.sp = 0
            eng.root_done = true
            return false
        end
    end
    return false
end
