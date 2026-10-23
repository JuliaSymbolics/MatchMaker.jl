# DESIGN.md §5.3–5.5: MatchEngine, MatchFrame ADT, leaf obligations, Seq frame.

###
### MatchFrame (§5.4)
###

"""
    MatchFrame

A suspended single-result enumerator for one pattern-node obligation — the
defunctionalized backtracking unit of [`MatchEngine`](@ref) (DESIGN.md §5.4).
`@data mutable` because frame state mutates between `step!` calls: resumption
fields are `Ref`s.

`Seq(pat_node, subj_node, k, trail_mark, kids)` — a free-head (`NodePlan.Call`)
frame: `k` is the child position currently being enumerated (`0` =
uninitialized), `trail_mark` the trail length at frame creation (unwind
target), `kids` the per-position live child frames (`nothing` for leaf
positions — literal/slot obligations are applied inline by the parent and
never get frames). Children are owned by their parent frame and driven
directly through [`step!`](@ref); `eng.frames` therefore holds only the
root-level stack.
"""
@data mutable MatchFrame begin
    struct Seq
        pat_node::Int32
        subj_node::Int32
        k::Ref{Int}
        trail_mark::Ref{Int}
        kids::Vector{Any}    # Union{Nothing, MatchFrameT} per child position
    end
end
const MatchFrameT = MatchFrame.Type

# Frame construction by plan variant. Leaf plans never get frames; AC/Comm/
# Assoc variants land in later milestones.
function _new_frame(
        plan::NodePlanT, pat_node::Int32, subj_node::Int32,
        nchildren::Int
    )
    return @match plan begin
        NodePlan.Call(; op, head) => MatchFrame.Seq(
            pat_node, subj_node, Ref(0), Ref(0),
            fill!(Vector{Any}(undef, nchildren), nothing)
        )
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

A defunctionalized backtracking machine (DESIGN.md §5.4). `frames` is the
live frame stack (root at bottom); `binds`/`trail` hold index-only binding
state; `extras` is the cold non-node binding channel (e.g. a head-slot var
bound to a non-symbolic operation); `argbuf` is a reusable argument buffer
for constraint evaluation. `steps` meters work.
"""
mutable struct MatchEngine
    "Compiled pattern."
    const pat::Matcher
    "Subject DAG."
    const subj::IRStructure{SymReal}
    "Node index of the subject root."
    const sroot::Int32
    "Live frame stack; top = deepest obligation."
    const frames::Vector{MatchFrameT}
    "Index-only binding state."
    const binds::Bindings
    "Var ids bound, in order — backtracking unwinds to a mark."
    const trail::Vector{Int32}
    "Compiled constraints (var syms resolved to ids)."
    const constraints::Vector{_EConstraint}
    "Whether a constraint has fired under current bindings."
    const constr_fired::BitVector
    "var_id -> constraint indices mentioning it."
    const var_constrs::Vector{SmallV{Int32}}
    "Non-node bindings (var_id -> raw value, e.g. head ops)."
    const extras::Dict{Int32, Any}
    "Reusable arg vector for constraint calls."
    const argbuf::Vector{BasicSymbolic{SymReal}}
    "Whether the (leaf) root obligation has already yielded."
    root_done::Bool
    "Work meter; compare against budget."
    steps::Int
end

"""
    $TYPEDSIGNATURES

Build a [`MatchEngine`](@ref) for `pat` on subject `s`. `constraints` is a
collection of [`Constraint`](@ref)s; variable syms are resolved to ids —
unknown syms throw `ArgumentError`.
"""
function MatchEngine(pat::Matcher, s::BasicSymbolic{SymReal}, constraints)
    subj = IRStructure{SymReal}()
    sroot = populate_ir!(subj, s)
    frames = MatchFrameT[]
    binds = Bindings(pat.nvars)
    trail = Int32[]
    extras = Dict{Int32, Any}()
    argbuf = BasicSymbolic{SymReal}[]

    econstrs = _EConstraint[]
    var_constrs = [SmallV{Int32}() for _ in 1:pat.nvars]
    for c in constraints
        c isa Constraint || throw(
            ArgumentError(
                lazy"constraints must be Constraint objects, got: $c"
            )
        )
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
        push!(econstrs, _EConstraint(c.fn, var_ids))
        for vid in var_ids
            push!(var_constrs[vid], ci)
        end
    end

    eng = MatchEngine(
        pat, subj, sroot, frames, binds, trail, econstrs,
        falses(length(econstrs)), var_constrs, extras, argbuf, false, 0
    )

    # Leaf roots (a bare slot/literal pattern) are applied inline by
    # `next_match!` — there is no parent to host the obligation.
    root_plan = pat.plans[pat.root]
    isleaf = @match root_plan begin
        NodePlan.Literal() => true
        NodePlan.Slot(; var_id) => true
        _ => false
    end
    if !isleaf
        push!(frames, _root_frame(root_plan, pat.root, sroot))
    end
    return eng
end

function _root_frame(plan::NodePlanT, pat_node::Int32, subj_node::Int32)
    return @match plan begin
        NodePlan.Call(; children) => _new_frame(
            plan, pat_node, subj_node, length(children)
        )
        _ => _new_frame(plan, pat_node, subj_node, 0)
    end
end

###
### Trail (§5.3)
###

# Pop bindings back to `mark`, clearing node/seq/seg_op/extras and any
# constraints whose fired bit depended on an unbound var.
function _unwind!(eng::MatchEngine, mark::Int)
    while length(eng.trail) > mark
        vid = pop!(eng.trail)
        b = eng.binds
        b.node[vid] = 0
        b.seg_op[vid] = nothing
        delete!(eng.extras, vid)
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
            is_bound_node(eng.binds, v) || haskey(eng.extras, v) ||
                (allbound = false; break)
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
    haskey(eng.extras, vid) && return Const{SymReal}(eng.extras[vid])
    b = eng.binds
    b.seg_op[vid] !== nothing && return _seg_value(eng, vid)
    is_bound_node(b, vid) || error(lazy"var $vid is not bound")
    return eng.subj[b.node[vid]]
end

# Reconstruct `f(captured…)` for a segment binding (§5.6).
function _seg_value(eng::MatchEngine, vid::Int32)
    b = eng.binds
    f = b.seg_op[vid]
    args = BasicSymbolic{SymReal}[eng.subj[i] for i in b.seq[vid]]
    if isempty(args)
        e = _identity_el(f, symtype(eng.subj[eng.sroot]))
        e !== nothing && return Const{SymReal}(e)
        return term(f, BasicSymbolic{SymReal}[]...)
    end
    return term(f, args...)
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
            cand === Integer || cand === Rational{Int} || cand === Bool
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
    if haskey(eng.extras, vid)
        return isequal(eng.extras[vid], eng.subj[snode])
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
    if haskey(eng.extras, vid)
        return eng.extras[vid] === op
    end
    is_bound_node(eng.binds, vid) && return false
    spec = eng.pat.var_specs[vid]
    pred = @match spec begin
        VarSpec.Slot(; predicate) => predicate
        _ => nothing
    end
    if pred !== nothing
        pred(Const{SymReal}(op))::Bool || return false
    end
    eng.extras[vid] = op
    push!(eng.trail, vid)
    return _ready_constraints!(eng, vid)
end

###
### step! protocol (§5.4)
###

# :produced — a complete alternative for this frame's subtree is on the trail.
# :failed   — exhausted; trail already unwound to this frame's mark.
# (:matched reserved for single-shot frames in later milestones.)
function step!(eng::MatchEngine, f::MatchFrameT)
    return @match f begin
        MatchFrame.Seq(; pat_node, subj_node, k, trail_mark, kids) =>
            _step_seq!(eng, pat_node, subj_node, k, trail_mark, kids)
    end
end

###
### Seq frame (§5.5c) — free head, positional children
###

function _step_seq!(
        eng::MatchEngine, pat_node::Int32, subj_node::Int32,
        k::Ref{Int}, mark::Ref{Int}, kids::Vector{Any}
    )
    plan = eng.pat.plans[pat_node]
    (op, head, children) = @match plan begin
        NodePlan.Call(; op, head, children) => (op, head, children)
        _ => error(lazy"Seq frame got a non-Call plan at node $pat_node")
    end
    snbs = Graphs.outneighbors(eng.subj.dependency_graph, subj_node)
    sexpr = eng.subj[subj_node]
    sstart = iscall(sexpr) && operation(sexpr) isa BasicSymbolic{SymReal} ? 2 : 1
    n = length(children)
    backtrack = false

    if iszero(k[])
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
        ok || return _seq_fail!(eng, mark)
        k[] = 1
    else
        # re-entry: resume — unwind this frame's bindings and seek the
        # deepest live child for its next alternative (never re-forward)
        _unwind!(eng, mark[])
        k[] = length(children)
        backtrack = true
    end

    while true
        if k[] > n
            return :produced
        end
        if backtrack
            # find the deepest live child and resume its enumerator
            while k[] >= 1
                kf = kids[k[]]
                if kf === nothing
                    k[] -= 1
                    continue
                end
                if step!(eng, kf) === :produced
                    k[] += 1
                    break
                else
                    kids[k[]] = nothing
                    k[] -= 1
                end
            end
            k[] == 0 && return _seq_fail!(eng, mark)
            backtrack = false
            continue
        end
        cp = children[k[]]
        cs = snbs[sstart + k[] - 1]
        isleaf = @match eng.pat.plans[cp] begin
            NodePlan.Literal() => true
            NodePlan.Slot(; var_id) => true
            _ => false
        end
        if isleaf
            if _leaf_obligation!(eng, cp, cs)
                k[] += 1
            else
                backtrack = true
            end
        else
            kf = kids[k[]]
            kf === nothing && (
                kids[k[]] = kf = _new_frame(
                    eng.pat.plans[cp], cp, cs, _nchildren(eng.pat.plans[cp])
                )
            )
            if step!(eng, kf) === :produced
                k[] += 1
            else
                kids[k[]] = nothing
                backtrack = true
            end
        end
    end
    return
end

_seq_fail!(eng::MatchEngine, mark::Ref{Int}) = (_unwind!(eng, mark[]); :failed)

function _nchildren(plan::NodePlanT)
    return @match plan begin
        NodePlan.Call(; children) => length(children)
        _ => 0
    end
end

# Head obligation (§4.10): the subject's operation is itself a pattern
# position. Symbolic ops live in the subject IR; non-symbolic ops bind
# through `extras` (slot plans only).
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
    if isempty(eng.frames)
        # leaf root: single-shot obligation, applied inline (§5.4)
        eng.root_done && return false
        eng.root_done = true
        return _leaf_obligation!(eng, eng.pat.root, eng.sroot)
    end
    while !isempty(eng.frames)
        f = eng.frames[end]
        st = step!(eng, f)
        eng.steps += 1
        if st === :produced
            return true
        elseif st === :matched || st === :failed
            pop!(eng.frames)
        end
    end
    return false
end
