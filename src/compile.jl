# DESIGN.md §5.1–5.2: Matcher, NodePlan ADT, vars-map merge, validation.

###
### NodePlan (§5.2)
###

"""
    NodePlan

Per-node matching plan, indexed by pattern-IR node index (DESIGN.md §5.2). A
Moshi ADT — the variant is the match instruction; the engine dispatches on it
and never re-derives node kind:

- `Literal()` — `Const`/non-variable `Sym`: match iff `isequal`.
- `Slot(var_id, optional)` — a `slot`/`optional` marker occurrence.
- `Segment(var_id)` — a `segment` marker occurrence.
- `Call(op, head, children)` — free head: positional children.
- `AssocCall(op, head, children)` — associative-not-commutative head:
  ordered children, contiguous splits.
- `CommCall(op, head, fixed, slots, optionals, segments)` —
  commutative-not-associative head: children partitioned by kind.
- `ACCall(op, head, fixed, slots, optionals, segments)` — AC head:
  children partitioned by kind.

`op` is `operation(node)` (needed for head-equality, identity coercion, and
segment binding reconstruction); `head` is the node index of a symbolic-head
obligation — nonzero when the operation is itself symbolic (`f(x)` with
symbolic `f`, including head-slots like `slot(f)(x)` per §4.10) and `0`
otherwise.
"""
@data NodePlan begin
    struct Literal end
    struct Slot
        var_id::Int32
        optional::Bool
    end
    struct Segment
        var_id::Int32
    end
    struct Call
        op::Any
        head::Int32
        children::SmallV{Int32}
    end
    struct AssocCall
        op::Any
        head::Int32
        children::SmallV{Int32}
    end
    struct CommCall
        op::Any
        head::Int32
        fixed::SmallV{Int32}
        slots::SmallV{Int32}
        optionals::SmallV{Int32}
        segments::SmallV{Int32}
    end
    struct ACCall
        op::Any
        head::Int32
        fixed::SmallV{Int32}
        slots::SmallV{Int32}
        optionals::SmallV{Int32}
        segments::SmallV{Int32}
    end
end

###
### Matcher (§5.2)
###

"""
    Matcher{T}

A compiled pattern: pattern `IRStructure` + per-node [`NodePlan`](@ref)s +
variable table. Built once by [`compile_pattern`](@ref); shareable across
subjects (the many-to-one hook, §5.2). `var_of` is an `IdDict` — the same
variable is the same interned `Sym` (hashconsing), so `===` identity is both
correct and cheaper than an `isequal`-keyed map.
"""
struct Matcher{T}
    ir::IRStructure{T}                        # pattern DAG
    root::Int32                               # node index of whole pattern
    plans::Vector{NodePlan.Type}                   # indexed by node idx
    var_syms::Vector{BasicSymbolic{T}}        # var_id -> inner Sym
    var_specs::Vector{VarSpec.Type}                # var_id -> spec
    var_of::IdDict{BasicSymbolic{T}, Int32}   # inner sym -> var_id (=== identity)
    is_ground::BitVector                      # subtree contains no variables
    nvars::Int                                # number of distinct variables
end

###
### compile_pattern
###

"""
    compile_pattern(expr::BasicSymbolic{SymReal};
                    vars::AbstractDict{BasicSymbolic{SymReal}, VarSpec.Type} =
                        Dict{BasicSymbolic{SymReal}, VarSpec.Type}())
        -> Matcher{SymReal}

Compile `expr` into a [`Matcher`](@ref) (DESIGN.md §5.2). `vars` maps pattern
variables (inner `Sym`s or marker terms) to `VarSpec` variants
([`slotspec`](@ref)/[`segmentspec`](@ref)); unlisted variables get the
unconstrained spec for their kind.

Loud errors, not silent mismatches (§5.2 validation list): bare occurrences
of marked syms, marker-kind conflicts, `vars`-map variant/kind mismatches,
`optional` occurrences outside AC/A nodes or without a `default`, `segment`/
`optional` markers in head position or at the root, `vars` keys that are not
pattern variables, and segment `min` bounds that provably exceed a
fixed-arity parent's argument count.
"""
function compile_pattern(
        expr::BasicSymbolic{SymReal};
        vars::AbstractDict{BasicSymbolic{SymReal}, VarSpec.Type} =
            Dict{BasicSymbolic{SymReal}, VarSpec.Type}()
    )
    ir = IRStructure{SymReal}()
    root = populate_ir!(ir, expr)
    g = ir.dependency_graph
    n = length(ir)
    plans = Vector{NodePlan.Type}(undef, n)
    is_ground = trues(n)
    var_syms = BasicSymbolic{SymReal}[]
    var_of = IdDict{BasicSymbolic{SymReal}, Int32}()
    var_is_seg = BitVector()    # var_id -> segment-kind
    var_has_opt = BitVector()   # var_id -> has an `optional` occurrence

    # ir.symbols is postorder (populate_ir! pushes children before parents),
    # so 1:n is a bottom-up topological sweep and every marker is seen before
    # its ancestors.
    for i in Int32(1):Int32(n)
        ex = ir[i]
        if is_marker_term(ex)
            inner = _marker_inner(ex)
            is_seg = _is_segment_term(ex)
            is_opt = _is_optional_term(ex)
            vid = get!(var_of, inner) do
                push!(var_syms, inner)
                push!(var_is_seg, is_seg)
                push!(var_has_opt, false)
                return Int32(length(var_syms))
            end
            var_is_seg[vid] == is_seg || throw(
                ArgumentError(
                    lazy"pattern variable $inner occurs as both slot/optional and segment"
                )
            )
            if is_opt
                var_has_opt[vid] = true
            end
            plans[i] = is_seg ? NodePlan.Segment(vid) : NodePlan.Slot(vid, is_opt)
            is_ground[i] = false
        elseif iscall(ex)
            plans[i] = _plan_call!(plans, is_ground, ir, g, ex, i, var_of)
        else
            # Sym/Const (and any other non-call variant): literal match
            plans[i] = NodePlan.Literal()
        end
    end

    @match plans[root] begin
        NodePlan.Slot(_, true) => throw(
            ArgumentError(
                lazy"optional occurrence at the pattern root is not inside an AC/A node"
            )
        )
        NodePlan.Segment(_) => throw(
            ArgumentError(
                lazy"segment occurrence at the pattern root has no argument list to capture"
            )
        )
        _ => nothing
    end

    var_specs = _merge_specs(vars, var_of, var_syms, var_is_seg, var_has_opt)
    _check_fixed_arity!(plans, ir, var_of, var_specs)

    return Matcher{SymReal}(
        ir, root, plans, var_syms, var_specs, var_of, is_ground, length(var_syms)
    )
end

# A marker node must wrap exactly one Sym — validate at compile since
# hand-constructed `Term(slot, ...)`s can bypass the marker ctors.
function _marker_inner(ex::BasicSymbolic{SymReal})
    args = arguments(ex)
    (length(args) == 1 && issym(args[1])) || throw(
        ArgumentError(
            lazy"marker term must wrap exactly one symbolic variable: $ex"
        )
    )
    return args[1]
end

function _plan_call!(
        plans::Vector{NodePlan.Type}, is_ground::BitVector,
        ir::IRStructure{SymReal}, g::SymbolicUtils.OrderedDiGraph{Int32},
        ex::BasicSymbolic{SymReal}, i::Int32,
        var_of::IdDict{BasicSymbolic{SymReal}, Int32}
    )
    op = operation(ex)
    nbs = Graphs.outneighbors(g, i)

    head = zero(Int32)
    if op isa BasicSymbolic{SymReal}
        # symbolic op prefixes outneighbors (IRStructure invariant)
        head = Int32(nbs[1])
        if is_marker_term(op)
            _is_slot_term(op) || throw(
                ArgumentError(
                    lazy"only slot markers may appear in head position, got: $op"
                )
            )
        else
            (issym(op) && haskey(var_of, op)) && throw(
                ArgumentError(
                    lazy"bare occurrence of pattern variable $op in head position"
                )
            )
        end
    end

    ST = symtype(ex)
    ac = _is_ac_head(op, ST)
    assoc = ac || _is_associative_head(op, ST)
    comm = ac || _is_commutative_head(op, ST)

    start = op isa BasicSymbolic{SymReal} ? 2 : 1
    if ac || comm
        fixed = SmallV{Int32}()
        slots = SmallV{Int32}()
        optionals = SmallV{Int32}()
        segments = SmallV{Int32}()
        for k in start:length(nbs)
            c = Int32(nbs[k])
            cex = ir[c]
            if _is_segment_term(cex)
                push!(segments, c)
            elseif _is_optional_term(cex)
                ac || throw(
                    ArgumentError(
                        lazy"optional occurrence $cex outside an AC/associative node"
                    )
                )
                push!(optionals, c)
            elseif _is_slot_term(cex)
                push!(slots, c)
            else
                _check_bare!(cex, var_of)
                push!(fixed, c)
            end
            is_ground[i] &= is_ground[c]
        end
        is_ground[i] &= (iszero(head) || is_ground[head])
        return ac ? NodePlan.ACCall(op, head, fixed, slots, optionals, segments) :
            NodePlan.CommCall(op, head, fixed, slots, optionals, segments)
    else
        children = SmallV{Int32}()
        for k in start:length(nbs)
            c = Int32(nbs[k])
            cex = ir[c]
            if _is_optional_term(cex)
                assoc || throw(
                    ArgumentError(
                        lazy"optional occurrence $cex outside an AC/associative node"
                    )
                )
            elseif !is_marker_term(cex)
                _check_bare!(cex, var_of)
            end
            push!(children, c)
            is_ground[i] &= is_ground[c]
        end
        is_ground[i] &= (iszero(head) || is_ground[head])
        return assoc ? NodePlan.AssocCall(op, head, children) :
            NodePlan.Call(op, head, children)
    end
end

function _check_bare!(
        cex::BasicSymbolic{SymReal},
        var_of::IdDict{BasicSymbolic{SymReal}, Int32}
    )
    (issym(cex) && haskey(var_of, cex)) && throw(
        ArgumentError(
            lazy"bare occurrence of pattern variable $cex — every occurrence must be inside a marker term"
        )
    )
    return nothing
end

# Merge the `vars` map into a per-var_id VarSpec vector (§3.1, §5.2).
function _merge_specs(
        vars::AbstractDict{BasicSymbolic{SymReal}, VarSpec.Type},
        var_of::IdDict{BasicSymbolic{SymReal}, Int32},
        var_syms::Vector{BasicSymbolic{SymReal}},
        var_is_seg::BitVector, var_has_opt::BitVector
    )
    nvars = length(var_syms)
    specs = Vector{VarSpec.Type}(undef, nvars)
    seen = falses(nvars)
    for (k, v) in vars
        ks = unwrap_varspec(k)
        (issym(ks) && haskey(var_of, ks)) || throw(
            ArgumentError(
                lazy"vars key $k is not a pattern variable in this expression"
            )
        )
        vid = var_of[ks]
        seen[vid] && throw(
            ArgumentError(
                lazy"duplicate VarSpec for variable $ks"
            )
        )
        spec_is_seg = MData.isa_variant(v, VarSpec.Segment)
        spec_is_seg == var_is_seg[vid] || throw(
            ArgumentError(
                lazy"VarSpec variant for $ks does not match its marker kind"
            )
        )
        specs[vid] = v
        seen[vid] = true
    end
    for vid in 1:nvars
        seen[vid] || (specs[vid] = var_is_seg[vid] ? segmentspec() : slotspec())
        if var_has_opt[vid]
            dflt = @match specs[vid] begin
                VarSpec.Slot(; default) => default
                _ => nothing
            end
            dflt === nothing && throw(
                ArgumentError(
                    lazy"variable $(var_syms[vid]) has an optional occurrence but no default in its VarSpec"
                )
            )
        end
    end
    return specs
end

# `min` bounds under fixed-arity free heads: the sum of segment mins plus the
# non-segment child count cannot exceed the parent's argument count (§5.2,
# "where provable").
function _check_fixed_arity!(
        plans::Vector{NodePlan.Type}, ir::IRStructure{SymReal},
        var_of::IdDict{BasicSymbolic{SymReal}, Int32},
        specs::Vector{VarSpec.Type}
    )
    for i in Int32(1):Int32(length(plans))
        @match plans[i] begin
            NodePlan.Call(; children) => begin
                min_req = 0
                for c in children
                    cex = ir[c]
                    if _is_segment_term(cex)
                        min_req += @match specs[var_of[varsym(cex)]] begin
                            VarSpec.Segment(; min) => min
                            _ => 0
                        end
                    else
                        min_req += 1
                    end
                end
                min_req > length(children) && throw(
                    ArgumentError(
                        lazy"segment min bounds exceed the fixed arity $(length(children)) of node $i"
                    )
                )
            end
            _ => nothing
        end
    end
    return nothing
end
