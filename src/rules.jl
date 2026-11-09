# REWRITING.md — rule objects, RuleSet/RuleIndex, RuleWorkspace, and the
# native rewrite pass. `RuleSet` is the immutable compiled artifact;
# `RuleWorkspace` is the mutable application context and the rewriter
# callable (`x -> expr′ | nothing`).

using SymbolicUtils: maketerm, metadata, ROArgsT

###
### Rule objects (§2)
###

"""
    RhsT

`FunctionWrapper` signature for callable rule RHSs:
`(view::SubstitutionView) -> Union{expr, nothing}` — `nothing` signals
"matched but produce nothing", and the caller falls through to the next
rule (same convention as `PredT`/`ConstrT` in §3.2).
"""
const RhsT = FunctionWrapper{
    Union{BasicSymbolic{SymReal}, Nothing}, Tuple{SubstitutionView}
}

"""
    RhsPlan

An rhs template compiled against the lhs var ids — evaluation reads
`eng.binds` by index and splices segment captures positionally, never
building a `Sym → value` dict (REWRITING.md §2). `vid_of[i]` is the
pattern var id bound at template-IR node `i` (`0` = not a marker);
`updates` caches exactly the node indices needing rebuild on eval —
everything else keeps `ir[i]`.
"""
struct RhsPlan
    "Template DAG."
    ir::IRStructure{SymReal}
    "Node index of the template root."
    root::Int32
    "template node -> pattern var id (`0` = not a marker node)."
    vid_of::Vector{Int32}
    "template-IR indices whose subtree contains a marker, sorted —
    the only nodes `_rhs_eval` rebuilds."
    updates::Vector{Int32}
end

"""
    $TYPEDSIGNATURES

Compile the rhs template `rhs` against `pat`'s var table. Every marker
term in `rhs` must be a pattern variable — unknown vars throw
`ArgumentError`.
"""
function _compile_rhs(rhs::BasicSymbolic{SymReal}, pat::Matcher)
    ir = IRStructure{SymReal}()
    root = populate_ir!(ir, rhs)
    n = length(ir)
    vid_of = zeros(Int32, n)
    needs = falses(n)
    updates = Int32[]
    g = ir.dependency_graph
    for i in 1:n
        t = ir[i]
        if is_marker_term(t)
            sym = varsym(t)
            vid = get(pat.var_of, sym, zero(Int32))
            vid == 0 && throw(
                ArgumentError(lazy"rhs variable $sym is not a pattern variable")
            )
            vid_of[i] = vid
        end
        # `symbols` is postorder — a node needs work iff it's a marker or
        # any already-visited dependency does.
        needs[i] = vid_of[i] != 0 ||
            any(j -> needs[j], Graphs.outneighbors(g, i))
        needs[i] && push!(updates, Int32(i))
    end
    return RhsPlan(ir, root, vid_of, updates)
end

"""
    CompiledRule

A compiled lhs ([`Matcher`](@ref)) plus its `Constraint`s and rhs —
either an [`RhsPlan`](@ref) template or an [`RhsT`](@ref) callable.
Built by [`mmrule`](@ref).
"""
struct CompiledRule
    pat::Matcher
    constraints::Vector{Constraint}
    rhs::Union{RhsPlan, RhsT}
end

"""
    mmrule(lhs => rhs; vars = Dict(), constraints = Constraint[])

Build a [`CompiledRule`](@ref): `lhs` is compiled via
[`compile_pattern`](@ref); `rhs` is either a symbolic template (compiled
to an [`RhsPlan`](@ref) over the lhs var ids) or a callable
`f(view) -> expr | nothing` (wrapped in [`RhsT`](@ref)). `vars` maps
pattern variables to [`VarSpec`](@ref)s; `constraints` are early-firing
cross-variable checks (§4.9).
"""
function mmrule(
        lhs::Pair{BasicSymbolic{SymReal}, T};
        vars::AbstractDict{BasicSymbolic{SymReal}, VarSpecT} =
            Dict{BasicSymbolic{SymReal}, VarSpecT}(),
        constraints = Constraint[],
    ) where T
    (l, rhs) = lhs
    pat = compile_pattern(l; vars)
    r = rhs isa BasicSymbolic{SymReal} ? _compile_rhs(rhs, pat) : RhsT(rhs)
    return CompiledRule(pat, Constraint[constraints...], r)
end

# The rule application: template evals by var id, callable gets the view.
function _apply_rhs(rule::CompiledRule, eng::MatchEngine)
    rhs = rule.rhs
    rhs isa RhsPlan && return _rhs_eval(rhs, eng)
    return rhs(SubstitutionView(eng, eng.steps))
end

# Evaluate a compiled template against the live engine — `instantiate`'s
# postorder walk with `binds`-indexed marker resolution instead of a dict.
# Only `updates` nodes are rebuilt; subtrees with no markers keep `ir[i]`.
function _rhs_eval(plan::RhsPlan, eng::MatchEngine)
    ir = plan.ir
    g = ir.dependency_graph
    out = copy(ir.symbols)
    vid_of = plan.vid_of
    specs = eng.pat.var_specs
    for i in plan.updates
        vid = vid_of[i]
        if vid != 0
            # segment markers keep the `ir[i]` placeholder — the parent's
            # arg loop splices `b.seq[vid]` directly and only materializes
            # on a head mismatch; a bare root is handled at the return.
            MData.isa_variant(specs[vid], VarSpec.Segment) ||
                (out[i] = _bound_value(eng, vid))
            continue
        end
        t = ir[i]
        nbs = Graphs.outneighbors(g, i)
        op = operation(t)
        argstart = op isa BasicSymbolic{SymReal} ? 2 : 1
        newop = op
        if argstart == 2 && vid_of[nbs[1]] != 0
            # a head bound via extras materializes as Const(op); unwrap
            newop = unwrap_const(out[nbs[1]])
        end
        # +/* get free splicing + identity-Const elision from
        # add_worker/mul_worker; other heads need it explicit (g(g(x))
        # is not g(x)).
        canon = newop === (+) || newop === (*)
        id = canon ? nothing : _identity_el(newop, symtype(t))
        newargs = ArgsT{SymReal}()
        sizehint!(newargs, length(nbs) - argstart + 1)
        for j in argstart:length(nbs)
            c_vid = vid_of[nbs[j]]
            if c_vid != 0 &&
                    MData.isa_variant(specs[c_vid], VarSpec.Segment)
                if eng.binds.seg_op[c_vid] === newop
                    # same head — splice the captured arg list; the term
                    # is never materialized
                    append!(newargs, eng.binds.seq[c_vid])
                    continue
                end
                cexpr = _bound_value(eng, c_vid)
                if !canon && isconst(cexpr) && id !== nothing &&
                        isequal(unwrap_const(cexpr), id)::Bool
                    # Const identity capture under this head: zero args
                    # (§5.6); any other Const is a one-element literal.
                    continue
                end
                push!(newargs, cexpr)
            else
                push!(newargs, out[nbs[j]])
            end
        end
        if newop === (+)
            out[i] = SymbolicUtils.add_worker(SymReal, newargs)
        elseif newop === (*)
            out[i] = SymbolicUtils.mul_worker(SymReal, newargs)
        else
            out[i] = BSImpl.Term{SymReal}(
                newop, newargs; type = symtype(t), shape = SymbolicUtils.shape(t)
            )
        end
    end
    r = plan.root
    rv = vid_of[r]
    if rv != 0 && MData.isa_variant(specs[rv], VarSpec.Segment)
        return _bound_value(eng, rv)
    end
    return out[r]
end

###
### RuleIndex (§5)
###

"""
    RuleIndex

Abstract dispatch seam for many-to-one lookup (REWRITING.md §5):
`lookup!(idx, buf, x)` appends candidate rule ids to `buf`. Phase 1 is
[`BucketIndex`](@ref); a discrimination net (`DiscrimNet`) is Phase 2.
"""
abstract type RuleIndex end

const _NO_RULES = SmallV{Int32}()

"""
    BucketIndex <: RuleIndex

Phase-1 index: rules bucketed by root-obligation signature — a fixed
`op` head, a slot/marked head (`any_head`), or a leaf literal
(`leaf_rules`). `arity[i]` is rule `i`'s `(min, max)` subject-arity
bounds (`optional` counts 0-or-1).
"""
struct BucketIndex <: RuleIndex
    "root op identity -> rule ids."
    by_op::Dict{Any, SmallV{Int32}}
    "rules whose root matches any head (slot roots, slot-headed calls)."
    any_head::SmallV{Int32}
    "rules whose root is ground/literal."
    leaf_rules::SmallV{Int32}
    "rule id -> (min, max) subject-arg bounds at the root."
    arity::Vector{Tuple{Int, Int}}
end

# Saturating upper-bound add — unbounded segment maxes are `typemax(Int)`,
# so `hi + h` overflows; both operands are non-negative so a negative sum
# means saturate.
@inline _sat_add(hi::Int, h::Int) = hi + h < 0 ? typemax(Int) : hi + h

# (min, max) subject args a root plan can consume. Bare slot/segment/literal
# roots are arity-agnostic — bucketing, not this bound, selects them.
function _root_arity(pat::Matcher, plan::NodePlanT)
    return @match plan begin
        NodePlan.Call(; children) => (length(children), length(children))
        NodePlan.SeqCall(; children) => begin
            lo = hi = 0
            for c in children
                (l, h) = _child_take(pat, pat.plans[c])
                lo += l
                hi = _sat_add(hi, h)
            end
            (lo, hi)
        end
        NodePlan.CommCall(; fixed, slots, optionals, segments) =>
            _ac_arity(pat, fixed, slots, optionals, segments)
        NodePlan.ACCall(; fixed, slots, optionals, segments) =>
            _ac_arity(pat, fixed, slots, optionals, segments)
        _ => (0, typemax(Int))
    end
end

# CommCall/ACCall arity: fixed children and slots consume exactly one
# arg each, optionals 0-or-1, segments their spec range.
function _ac_arity(pat::Matcher, fixed, slots, optionals, segments)
    lo = length(fixed) + length(slots)
    hi = lo + length(optionals)
    for s in segments
        (l, h) = _child_take(pat, pat.plans[s])
        lo += l
        hi = _sat_add(hi, h)
    end
    return (lo, hi)
end

# Subject args one pattern child consumes: slots 1 (0..1 when optional),
# segments their spec range, anything else exactly 1.
function _child_take(pat::Matcher, plan::NodePlanT)
    return @match plan begin
        NodePlan.Slot(; optional) => (optional ? 0 : 1, 1)
        NodePlan.Segment(; var_id) => begin
            @match pat.var_specs[var_id] begin
                VarSpec.Segment(; min, max) => (min, max)
                _ => (0, typemax(Int))
            end
        end
        _ => (1, 1)
    end
end

# Root op + head marker for call-ish plans.
_root_op_head(plan::NodePlanT) = @match plan begin
    NodePlan.Call(; op, head) => (op, head)
    NodePlan.SeqCall(; op, head) => (op, head)
    NodePlan.CommCall(; op, head) => (op, head)
    NodePlan.ACCall(; op, head) => (op, head)
    _ => (nothing, zero(Int32))
end

function _build_index(rules::Vector{CompiledRule})
    n = length(rules)
    idx = BucketIndex(
        Dict{Any, SmallV{Int32}}(), SmallV{Int32}(), SmallV{Int32}(),
        Vector{Tuple{Int, Int}}(undef, n)
    )
    for id in Int32(1):Int32(n)
        pat = rules[id].pat
        plan = pat.plans[pat.root]
        idx.arity[id] = _root_arity(pat, plan)
        if MData.isa_variant(plan, NodePlan.Literal)
            push!(idx.leaf_rules, id)
            continue
        end
        if MData.isa_variant(plan, NodePlan.Slot) ||
                MData.isa_variant(plan, NodePlan.Segment)
            # bare var — matches any node
            push!(idx.any_head, id)
            continue
        end
        (op, head) = _root_op_head(plan)
        if head != 0 && is_marker_term(op)
            # slot-headed call — matches any op
            push!(idx.any_head, id)
        else
            push!(get!(() -> SmallV{Int32}(), idx.by_op, op), id)
        end
    end
    return idx
end

###
### DiscrimNet (§5, Phase 2)
###

# (op, arity) key for deterministic call-head edges. `isequal`/`hash`
# make it a `Dict` key; ops are interned so `===` suffices.
struct NetOp
    op::Any
    arity::Int
end

Base.isequal(a::NetOp, b::NetOp) = a.op === b.op && a.arity == b.arity
Base.hash(k::NetOp, h::UInt) = hash(k.arity, hash(k.op, h))

# One deferred-subtree edge: `SeqCall`/`CommCall`/`ACCall` confirm
# `iscall` + `op` (`nothing` = head-marker, any op) + `lo <= arity <=
# hi`, then the engine does the real match under that head.
struct NetDefer
    op::Any
    lo::Int
    hi::Int
    next::Int32
end

"""
    NetState

One trie node of a [`DiscrimNet`](@ref) — the continuation frontier
shared by all patterns whose preorder label prefixes reach it.

- `ops`: `(op, arity)` → next — deterministic call-head transition.
- `opwilds`: `arity` → next — head-marker call (`slot(f)(…)`) — any op.
- `lits`: literal leaf expr → next.
- `defers`: `SeqCall`/`CommCall`/`ACCall` subtree edges — confirm
  `iscall` + `op` (`nothing` = head-marker, any op) + arity bounds,
  then hand the whole subtree to the engine.
- `wild`: slot transition — fires on any subject node (`0` = none).
- `finals`: rule ids whose label sequence ends here.
"""
mutable struct NetState
    ops::Dict{NetOp, Int32}
    opwilds::Dict{Int, Int32}
    lits::Dict{BasicSymbolic{SymReal}, Int32}
    defers::Vector{NetDefer}
    wild::Int32
    finals::SmallV{Int32}
end

NetState() = NetState(
    Dict{NetOp, Int32}(), Dict{Int, Int32}(),
    Dict{BasicSymbolic{SymReal}, Int32}(),
    NetDefer[], Int32(0), SmallV{Int32}()
)

"""
    DiscrimNet <: RuleIndex

Phase-2 index (REWRITING.md §5): a trie over every pattern's *preorder
obligation sequence*. `Call` children descend positionally; slot
obligations are wildcard edges (predicates, `want_type`s and
non-linearity are left to the engine — the net over-approximates
survivors); `SeqCall`/`CommCall`/`ACCall` subtrees only confirm
deterministic structure (op + arity bounds) and defer to the engine —
`optional`/`segment` labels never reach the net.

Evaluation is NFA simulation over `ws.subj`, memoized per
`(state, subj_node)` in `ws.net_cache`: subject-IR interning makes a
DAG-shared subterm evaluate once, and fixpoint iterations re-evaluate
only newly created nodes.
"""
struct DiscrimNet <: RuleIndex
    states::Vector{NetState}
end

DiscrimNet() = DiscrimNet(NetState[NetState()])

# Allocate a state and return its id.
function _net_new!(net::DiscrimNet)
    push!(net.states, NetState())
    return Int32(length(net.states))
end

# Edge `key` out of `d` (a per-state transition map), creating the
# target on demand.
function _net_next!(net::DiscrimNet, d::Dict{K, Int32}, key::K) where {K}
    return get!(() -> _net_new!(net), d, key)
end

# Insert pattern node `i`'s obligations starting at state `σ`; returns
# the state where the node's continuation begins (for `Call`, after all
# children are consumed).
function _net_insert!(net::DiscrimNet, pat::Matcher, i::Int32, σ::Int32)
    plan = pat.plans[i]
    return @match plan begin
        NodePlan.Literal() =>
            _net_next!(net, net.states[σ].lits, pat.ir[i])
        NodePlan.Slot(;) => begin
            st = net.states[σ]
            st.wild == 0 && (st.wild = _net_new!(net))
            st.wild
        end
        NodePlan.Call(; op, head, children) => begin
            σ = head != 0 && is_marker_term(op) ?
                _net_next!(net, net.states[σ].opwilds, length(children)) :
                _net_next!(net, net.states[σ].ops,
                    NetOp(op, length(children)))
            for c in children
                σ = _net_insert!(net, pat, c, σ)
            end
            σ
        end
        NodePlan.SeqCall(; op, head) =>
            _net_defer!(net, σ, pat, plan, op, head)
        NodePlan.CommCall(; op, head) =>
            _net_defer!(net, σ, pat, plan, op, head)
        NodePlan.ACCall(; op, head) =>
            _net_defer!(net, σ, pat, plan, op, head)
        NodePlan.Segment(;) =>
            error("unreachable: segment obligation reached the discrim net")
    end
end

# Defer edge: deterministic confirm = `iscall` + op (head-marker →
# `nothing` = any op) + subject-arity bounds from `_root_arity`.
# Identical edges out of `σ` share the target.
function _net_defer!(
        net::DiscrimNet, σ::Int32, pat::Matcher,
        plan::NodePlanT, @nospecialize(op), head::Int32
    )
    (lo, hi) = _root_arity(pat, plan)
    o = op isa BasicSymbolic{SymReal} && is_marker_term(op) ? nothing : op
    ds = net.states[σ].defers
    for d in ds
        d.op === o && d.lo == lo && d.hi == hi && return d.next
    end
    σ2 = _net_new!(net)
    push!(ds, NetDefer(o, lo, hi, σ2))
    return σ2
end

function _build_net(rules::Vector{CompiledRule})
    net = DiscrimNet()
    for rid in Int32(1):Int32(length(rules))
        pat = rules[rid].pat
        σ = _net_insert!(net, pat, pat.root, Int32(1))
        push!(net.states[σ].finals, rid)
    end
    return net
end

"""
    RuleSet{I <: RuleIndex}

The immutable compiled artifact (REWRITING.md §3): the rules plus the
dispatch index, built once by [`compile_rules`](@ref) and shareable
across tasks and calls — all mutable state lives in
[`RuleWorkspace`](@ref).
"""
struct RuleSet{I <: RuleIndex}
    "Rules in declaration order — application order."
    rules::Vector{CompiledRule}
    "Candidate index — `BucketIndex` today, `DiscrimNet` later."
    index::I
end

"""
    $TYPEDSIGNATURES

Compile a collection of [`CompiledRule`](@ref)s (from [`mmrule`](@ref))
into a [`RuleSet`](@ref) — builds the dispatch index once, shareable
globally. `index` selects the [`RuleIndex`](@ref) implementation:
[`BucketIndex`](@ref) (default, Phase 1) or [`DiscrimNet`](@ref)
(Phase 2).
"""
function compile_rules(
        rules::AbstractVector{CompiledRule};
        index::Type{<:RuleIndex} = BucketIndex,
    )
    rs = collect(CompiledRule, rules)
    return RuleSet(rs, _make_index(index, rs))
end

_make_index(::Type{BucketIndex}, rs) = _build_index(rs)
_make_index(::Type{DiscrimNet}, rs) = _build_net(rs)

###
### RuleWorkspace (§4)
###

"""
    RuleWorkspace

The mutable application context — and the rewriter callable
(REWRITING.md §4). Holds one shared subject `IRStructure`, a lazily
created `MatchEngine` per rule (`reset!` between sites, not
re-allocated), the candidate buffer, and the Phase-2 `net_cache`.

```julia
(ws::RuleWorkspace)(x) -> expr′ | nothing   # first-match rule application
```

Buffers plateau at `max(|pattern|, |subject|)` over sites seen — reuse
does not grow. `ws.maxsteps` is a mutable per-site budget.
"""
mutable struct RuleWorkspace
    "The ruleset this workspace serves."
    set::RuleSet
    "Per-site search budget, mutable between passes."
    maxsteps::Int
    "Shared subject DAG — populated once per site, shared by all engines."
    subj::IRStructure{SymReal}
    "Per-rule engines, lazily created then `reset!` per site."
    engines::Vector{Union{Nothing, MatchEngine}}
    "Candidate buffer for `lookup!`."
    candbuf::SmallV{Int32}
    "Phase-2 memo: (net_state, subj_node) -> next-state set (§7 —
    persists across iterations; unused under `BucketIndex`)."
    net_cache::Dict{Tuple{Int32, Int32}, SmallV{Int32}}
end

function RuleWorkspace(rs::RuleSet; maxsteps::Int = typemax(Int))
    return RuleWorkspace(
        rs, maxsteps, IRStructure{SymReal}(),
        Union{Nothing, MatchEngine}[nothing for _ in rs.rules],
        SmallV{Int32}(), Dict{Tuple{Int32, Int32}, SmallV{Int32}}()
    )
end

# Append candidate rule ids for subject `x` (`sroot` is its node in
# `ws.subj`): root-head bucket ∪ spills, arity-filtered. `buf` is
# caller-owned scratch.
function lookup!(
        idx::BucketIndex, buf::SmallV{Int32}, ws::RuleWorkspace,
        x::BasicSymbolic{SymReal}, sroot::Int32
    )
    empty!(buf)
    n = iscall(x) ? length(arguments(x)) : 0
    if iscall(x)
        ids = get(idx.by_op, operation(x), _NO_RULES)
        for id in ids
            (lo, hi) = idx.arity[id]
            lo <= n <= hi && push!(buf, id)
        end
    else
        append!(buf, idx.leaf_rules)
    end
    for id in idx.any_head
        (lo, hi) = idx.arity[id]
        lo <= n <= hi && push!(buf, id)
    end
    # buckets append by kind — restore declaration order for apply
    sort!(buf)
    return buf
end

###
### Net evaluation — go(σ, s) = NFA states after consuming subject node s
###

# Fold `s`'s call children through `go` starting from `σ`: the Op/
# OpWild head transition consumed `s`; each child subtree advances the
# frontier one label.
function _net_descend!(
        out::SmallV{Int32}, net::DiscrimNet, ws::RuleWorkspace,
        σ::Int32, nbs, argstart::Int
    )
    states = SmallV{Int32}()
    push!(states, σ)
    for j in argstart:length(nbs)
        isempty(states) && return out
        next = SmallV{Int32}()
        for σc in states
            for σn in _net_go(net, ws, σc, nbs[j])
                σn in next || push!(next, σn)
            end
        end
        states = next
    end
    for σn in states
        σn in out || push!(out, σn)
    end
    return out
end

function _net_go(
        net::DiscrimNet, ws::RuleWorkspace, σ::Int32, s::Int32
    )
    key = (σ, s)
    cached = get(ws.net_cache, key, nothing)
    cached !== nothing && return cached
    subj = ws.subj
    t = subj[s]
    st = net.states[σ]
    out = SmallV{Int32}()
    if iscall(t)
        nbs = Graphs.outneighbors(subj.dependency_graph, s)
        op = operation(t)
        argstart = op isa BasicSymbolic{SymReal} ? 2 : 1
        arity = length(nbs) - argstart + 1
        # the subject fixes the exact keys — direct gets, not edge scans
        σ2 = get(st.ops, NetOp(op, arity), Int32(0))
        σ2 != 0 && _net_descend!(out, net, ws, σ2, nbs, argstart)
        σ2 = get(st.opwilds, arity, Int32(0))
        σ2 != 0 && _net_descend!(out, net, ws, σ2, nbs, argstart)
        for d in st.defers
            (d.op === nothing || d.op === op) && d.lo <= arity <= d.hi &&
                push!(out, d.next)
        end
    else
        σ2 = get(st.lits, t, Int32(0))
        σ2 != 0 && push!(out, σ2)
    end
    st.wild != 0 && push!(out, st.wild)
    return ws.net_cache[key] = out
end

function lookup!(
        idx::DiscrimNet, buf::SmallV{Int32}, ws::RuleWorkspace,
        x::BasicSymbolic{SymReal}, sroot::Int32
    )
    empty!(buf)
    for σ in _net_go(idx, ws, Int32(1), sroot)
        append!(buf, idx.states[σ].finals)
    end
    # finals are disjoint across states; declaration order for apply
    sort!(buf)
    return buf
end


# Lazily create / reset the engine for rule `id` at `sroot`.
function _engine_for!(ws::RuleWorkspace, id::Int32, sroot::Int32)
    eng = ws.engines[id]
    if eng === nothing
        rule = ws.set.rules[id]
        eng = MatchEngine(
            rule.pat, ws.subj, sroot, rule.constraints;
            maxsteps = ws.maxsteps
        )
        ws.engines[id] = eng
    else
        reset!(eng, ws.subj, sroot)
        eng.maxsteps = ws.maxsteps
    end
    return eng
end

"""
    (ws::RuleWorkspace)(x) -> Union{expr′, nothing}

The rewriter callable: bucket-lookup the candidates for `x`, `reset!`
each surviving rule's engine to the shared subject IR, first match wins.
A callable rhs returning `nothing` falls through to the next candidate.
"""
function (ws::RuleWorkspace)(x::BasicSymbolic{SymReal})
    return _apply_site!(ws, x, populate_ir!(ws.subj, x))
end

# The ws() body with a precomputed root — IR-driven passes already know
# the node index and skip `populate_ir!` entirely for interned nodes.
function _apply_site!(
        ws::RuleWorkspace, x::BasicSymbolic{SymReal}, sroot::Int32
    )
    rs = ws.set
    ids = lookup!(rs.index, ws.candbuf, ws, x, sroot)
    isempty(ids) && return nothing
    @inbounds for i in eachindex(ids)
        id = ids[i]
        eng = _engine_for!(ws, id, sroot)
        next_match!(eng) || continue
        y = _apply_rhs(rs.rules[id], eng)
        y === nothing || return y
    end
    return nothing
end

###
### Native rewrite pass (§6)
###

# Apply the workspace at one site; `nothing` keeps `x`, a result is
# Const-wrapped (callable rhs's may return non-symbolic values).
@inline function _apply_site(
        ws::RuleWorkspace, x::BasicSymbolic{SymReal}, sroot::Int32
    )
    y = _apply_site!(ws, x, sroot)
    return y === nothing ? x : Const{SymReal}(y)
end
@inline _apply_site(ws::RuleWorkspace, x::BasicSymbolic{SymReal}) =
    _apply_site(ws, x, populate_ir!(ws.subj, x))

"""
    $TYPEDSIGNATURES

The MatchMaker-native rewrite pass (REWRITING.md §6). `order = :post`
(the default) sweeps `ws.subj` postorder — `populate_ir!` interning
dedups shared subterms for free, `maketerm` rebuilds only nodes whose
children changed, and the workspace applies at every node — linear in
IR size, no call-stack, no memo dict. `order = :pre` applies the
workspace before descending into the result (same semantics as
`Rewriters.Prewalk`), driven by an explicit worklist.
"""
function rewrite(
        ws::RuleWorkspace, expr::BasicSymbolic{SymReal};
        order::Symbol = :post
    )
    order === :post && return _rewrite_post(ws, expr)
    order === :pre && return _rewrite_pre(ws, expr)
    throw(ArgumentError(lazy"order must be :pre or :post, got: $order"))
end

# Linear postorder sweep over ws.subj — `symbols` indexes children
# before parents, interning dedups shared subterms, and `ws(x)`
# populating new terms appends beyond `n` (next-iteration nodes).
function _rewrite_post(ws::RuleWorkspace, expr::BasicSymbolic{SymReal})
    subj = ws.subj
    sroot = populate_ir!(subj, expr)
    n = length(subj)
    g = subj.dependency_graph
    out = Vector{BasicSymbolic{SymReal}}(undef, n)
    for i in Int32(1):Int32(n)
        t = subj[i]
        iscall(t) || (out[i] = _apply_site(ws, t); continue)
        nbs = Graphs.outneighbors(g, i)
        op = operation(t)
        argstart = op isa BasicSymbolic{SymReal} ? 2 : 1
        newop = argstart == 2 ? unwrap_const(out[nbs[1]]) : op
        # `outneighbors` are `arguments()` order (IRStructure invariant)
        # and children are interned — compare/rebuild against
        # `subj[nbs[j]]` directly rather than paying `arguments(t)`
        # (on AddMul that rebuilds Mul/^ terms per dict entry).
        newargs = nothing
        for (k, j) in enumerate(argstart:length(nbs))
            na = out[nbs[j]]
            na === subj[nbs[j]] && continue
            if newargs === nothing
                newargs = ArgsT{SymReal}()
                sizehint!(newargs, length(nbs) - argstart + 1)
                for jj in argstart:length(nbs)
                    push!(newargs, subj[nbs[jj]])
                end
            end
            newargs[k] = na
        end
        if newargs === nothing && newop === op
            # unchanged — the node is already interned at index i
            out[i] = _apply_site(ws, t, i)
        else
            if newargs === nothing
                newargs = ArgsT{SymReal}()
                sizehint!(newargs, length(nbs) - argstart + 1)
                for jj in argstart:length(nbs)
                    push!(newargs, subj[nbs[jj]])
                end
            end
            x = maketerm(typeof(t), newop, newargs, metadata(t))
            out[i] = _apply_site(ws, x, populate_ir!(subj, x))
        end
    end
    return out[sroot]
end

# Pre-order: apply ws at a node, then descend into the result — frames
# hold (orig, ws-result, next-child-idx); `out` collects rewritten
# children for the parent's rebuild; `memo` dedups shared subterms.
function _rewrite_pre(ws::RuleWorkspace, x::BasicSymbolic{SymReal})
    out = BasicSymbolic{SymReal}[]
    stk = Tuple{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}, Int}[
        (x, x, 0)]
    memo = IdDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}()
    while !isempty(stk)
        (orig, cur, i) = stk[end]
        if i == 0
            if haskey(memo, orig)
                pop!(stk)
                push!(out, memo[orig])
                continue
            end
            cur = _apply_site(ws, orig)
            if iscall(cur)
                stk[end] = (orig, cur, 1)
            else
                pop!(stk)
                memo[orig] = cur
                push!(out, cur)
            end
            continue
        end
        args = arguments(cur)
        if i <= length(args)
            stk[end] = (orig, cur, i + 1)
            push!(stk, (args[i], args[i], 0))
            continue
        end
        nargs = length(args)
        newargs = nothing
        for k in 1:nargs
            na = out[end - nargs + k]
            na === args[k] && continue
            if newargs === nothing
                newargs = copy(parent(args))::ArgsT{SymReal}
            end
            newargs[k] = na
        end
        resize!(out, length(out) - nargs)
        y = newargs === nothing ? cur : maketerm(
            typeof(cur), operation(cur), newargs, metadata(cur))
        pop!(stk)
        memo[orig] = y
        push!(out, y)
    end
    return out[1]
end

"""
    $TYPEDSIGNATURES

Iterate [`rewrite`](@ref) to a fixed point (REWRITING.md §7): the
workspace `IRStructure` accumulates across iterations — unchanged
subtrees are the same interned nodes, so `populate_ir!` costs only the
new ones. A term seen twice ends the loop (`FixpointNoCycle`
semantics); `maxiterations` bounds it outright.
"""
function fixpoint_rewrite(
        ws::RuleWorkspace, expr::BasicSymbolic{SymReal};
        maxiterations::Int = 10_000, order::Symbol = :post
    )
    seen = IdSet{BasicSymbolic{SymReal}}()
    x = expr
    for _ in 1:maxiterations
        x′ = rewrite(ws, x; order)
        isequal(x′, x) && return x
        x′ in seen && return x′
        push!(seen, x)
        x = x′
    end
    return x
end
