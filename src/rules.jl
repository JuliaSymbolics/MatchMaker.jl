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
`is_seg[i]` marks segment markers, which splice rather than substitute.
"""
struct RhsPlan
    "Template DAG."
    ir::IRStructure{SymReal}
    "Node index of the template root."
    root::Int32
    "template node -> pattern var id (`0` = not a marker node)."
    vid_of::Vector{Int32}
    "template node -> is a segment marker (splices on eval)."
    is_seg::BitVector
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
    n = length(ir.symbols)
    vid_of = zeros(Int32, n)
    is_seg = falses(n)
    for i in 1:n
        t = ir[i]
        is_marker_term(t) || continue
        sym = varsym(t)
        vid = get(pat.var_of, sym, zero(Int32))
        vid == 0 && throw(
            ArgumentError(lazy"rhs variable $sym is not a pattern variable")
        )
        vid_of[i] = vid
        is_seg[i] = _is_segment_term(t)
    end
    return RhsPlan(ir, root, vid_of, is_seg)
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
    name::Symbol
end

"""
    mmrule(lhs => rhs; vars = Dict(), constraints = Constraint[], name)

Build a [`CompiledRule`](@ref): `lhs` is compiled via
[`compile_pattern`](@ref); `rhs` is either a symbolic template (compiled
to an [`RhsPlan`](@ref) over the lhs var ids) or a callable
`f(view) -> expr | nothing` (wrapped in [`RhsT`](@ref)). `vars` maps
pattern variables to [`VarSpec`](@ref)s; `constraints` are early-firing
cross-variable checks (§4.9).
"""
function mmrule(
        lhs::Pair{<:BasicSymbolic{SymReal}};
        vars::AbstractDict{BasicSymbolic{SymReal}, VarSpecT} =
            Dict{BasicSymbolic{SymReal}, VarSpecT}(),
        constraints = Constraint[],
        name::Symbol = Symbol("")
    )
    (l, rhs) = lhs
    pat = compile_pattern(l; vars)
    r = rhs isa BasicSymbolic{SymReal} ? _compile_rhs(rhs, pat) : RhsT(rhs)
    return CompiledRule(pat, Constraint[constraints...], r, name)
end

# The rule application: template evals by var id, callable gets the view.
function _apply_rhs(rule::CompiledRule, eng::MatchEngine)
    rhs = rule.rhs
    rhs isa RhsPlan && return _rhs_eval(rhs, eng)
    return rhs(SubstitutionView(eng, eng.steps))
end

# Evaluate a compiled template against the live engine — `instantiate`'s
# postorder walk with `binds`-indexed marker resolution instead of a dict.
function _rhs_eval(plan::RhsPlan, eng::MatchEngine)
    ir = plan.ir
    g = ir.dependency_graph
    n = length(ir.symbols)
    out = Vector{BasicSymbolic{SymReal}}(undef, n)
    vid_of = plan.vid_of
    is_seg = plan.is_seg
    for i in 1:n
        vid = vid_of[i]
        if vid != 0
            out[i] = _bound_value(eng, vid)
            continue
        end
        t = ir[i]
        if !iscall(t)
            out[i] = t
            continue
        end
        nbs = Graphs.outneighbors(g, i)
        op = operation(t)
        argstart = op isa BasicSymbolic{SymReal} ? 2 : 1
        newop = op
        if argstart == 2 && vid_of[nbs[1]] != 0
            bound = out[nbs[1]]
            # a head bound via extras materializes as Const(op); unwrap
            newop = @match bound begin
                BSImpl.Const(; val) => val
                _ => bound
            end
        end
        newargs = ArgsT{SymReal}()
        sizehint!(newargs, length(nbs) - argstart + 1)
        for j in argstart:length(nbs)
            cexpr = out[nbs[j]]
            if is_seg[nbs[j]]
                if iscall(cexpr) && operation(cexpr) === newop
                    for ca in arguments(cexpr)
                        push!(newargs, ca)
                    end
                elseif isconst(cexpr)
                    # a Const binding equal to the head's identity
                    # contributes zero args (§5.6); any other Const is a
                    # one-element literal capture (canonical +(2) ≡ 2)
                    id = _identity_el(newop, symtype(t))
                    id === nothing || !isequal(unwrap_const(cexpr), id) ||
                        continue
                    push!(newargs, cexpr)
                else
                    push!(newargs, cexpr)
                end
            else
                push!(newargs, cexpr)
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
    return out[plan.root]
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
        NodePlan.CommCall(; fixed, slots, optionals, segments) ||
        NodePlan.ACCall(; fixed, slots, optionals, segments) => begin
            lo = length(fixed) + length(slots)
            hi = lo + length(optionals)
            for s in segments
                (l, h) = _child_take(pat, pat.plans[s])
                lo += l
                hi = _sat_add(hi, h)
            end
            (lo, hi)
        end
        _ => (0, typemax(Int))
    end
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

# Append candidate rule ids for subject `x`: root-head bucket ∪ spills,
# arity-filtered. `buf` is caller-owned scratch.
function lookup!(
        idx::BucketIndex, buf::SmallV{Int32}, x::BasicSymbolic{SymReal}
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
    return buf
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
into a [`RuleSet`](@ref) — builds the `BucketIndex` once, shareable
globally.
"""
function compile_rules(rules::AbstractVector{CompiledRule})
    rs = collect(CompiledRule, rules)
    return RuleSet(rs, _build_index(rs))
end

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
    "Phase-2 memo: (net_state, subj_node) -> surviving rule ids (§7 —
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
    rs = ws.set
    ids = lookup!(rs.index, ws.candbuf, x)
    isempty(ids) && return nothing
    sroot = populate_ir!(ws.subj, x)
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
@inline function _apply_site(ws::RuleWorkspace, x::BasicSymbolic{SymReal})
    y = ws(x)
    return y === nothing ? x : Const{SymReal}(y)
end

"""
    $TYPEDSIGNATURES

The MatchMaker-native bottom-up (default) or top-down rewrite pass over
`expr` (REWRITING.md §6): walks the DAG once with an identity-keyed
memo (hash-consed nodes dedup shared subterms), rebuilds only nodes
whose children changed, and applies the workspace at every node.
"""
function rewrite(
        ws::RuleWorkspace, expr::BasicSymbolic{SymReal};
        order::Symbol = :post
    )
    memo = IdDict{BasicSymbolic{SymReal}, BasicSymbolic{SymReal}}()
    order === :post && return _rewrite_post(ws, expr, memo)
    order === :pre && return _rewrite_pre(ws, expr, memo)
    throw(ArgumentError(lazy"order must be :pre or :post, got: $order"))
end

function _rewrite_post(
        ws::RuleWorkspace, x::BasicSymbolic{SymReal}, memo::IdDict
    )
    return get!(memo, x) do
        if iscall(x)
            args = arguments(x)::ROArgsT{SymReal}
            # copy-on-write: only allocate newargs once a child changes
            for (i, a) in enumerate(args)
                na = _rewrite_post(ws, a, memo)
                na === a && continue
                if args isa ROArgsT{SymReal}
                    args = copy(parent(args))::ArgsT{SymReal}
                end
                args[i] = na
            end
            args isa ArgsT{SymReal} && (
                x = maketerm(typeof(x), operation(x), args, metadata(x))
            )
        end
        _apply_site(ws, x)
    end
end

function _rewrite_pre(
        ws::RuleWorkspace, x::BasicSymbolic{SymReal}, memo::IdDict
    )
    return get!(memo, x) do
        x = _apply_site(ws, x)
        iscall(x) || return x
        args = arguments(x)::ROArgsT{SymReal}
        for (i, a) in enumerate(args)
            na = _rewrite_pre(ws, a, memo)
            na === a && continue
            if args isa ROArgsT{SymReal}
                args = copy(parent(args))::ArgsT{SymReal}
            end
            args[i] = na
        end
        args isa ArgsT{SymReal} ? maketerm(
            typeof(x), operation(x), args, metadata(x)
        ) : x
    end
end

"""
    $TYPEDSIGNATURES

Iterate [`rewrite`](@ref) to a fixed point (REWRITING.md §7): the
workspace `IRStructure` accumulates across iterations — unchanged
subtrees are the same interned nodes, so `populate_ir!` costs only the
new ones. A term seen twice ends the loop (`FixpointNoCycle`
semantics); `maxiterations` bounds it outright.
"""
function fixrewrite(
        ws::RuleWorkspace, expr::BasicSymbolic{SymReal};
        maxiterations::Int = 10_000, order::Symbol = :post
    )
    seen = Set{BasicSymbolic{SymReal}}()
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
