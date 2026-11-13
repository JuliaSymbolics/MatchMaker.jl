###
### Pretty-printing
###

# Marker terms print in yellow wherever SymbolicUtils' own display
# machinery renders them — via the `show_call` hook. Non-color IO
# (logs, `sprint`) falls back to plain text automatically.
function SymbolicUtils.show_call(
        io::IO, f::typeof(slot), x::BasicSymbolic{SymReal}
    )
    return printstyled(io, "slot(", arguments(x)[1], ")"; color = :yellow)
end
function SymbolicUtils.show_call(
        io::IO, f::typeof(segment), x::BasicSymbolic{SymReal}
    )
    return printstyled(io, "segment(", arguments(x)[1], ")"; color = :yellow)
end
function SymbolicUtils.show_call(
        io::IO, f::typeof(optional), x::BasicSymbolic{SymReal}
    )
    return printstyled(io, "optional(", arguments(x)[1], ")"; color = :yellow)
end

###
### Patterns
###

Base.show(io::IO, m::Matcher) =
    (print(io, "Matcher("); print(io, m.ir[m.root]); print(io, ")"))

Base.show(io::IO, p::NodePlanT) = MData.show_variant(io, p)
Base.show(io::IO, v::VarSpecT) = MData.show_variant(io, v)

###
### Engine
###

function Base.show(io::IO, e::MatchEngine)
    print(io, "MatchEngine(")
    print(io, e.pat.ir[e.pat.root])
    if 0 < e.sroot <= length(e.subj)
        print(io, " on ")
        print(io, e.subj[e.sroot])
    end
    return print(io, ")")
end

Base.show(io::IO, f::CallFrame) =
    print(io, "CallFrame(", f.pat_node, " on ", f.subj_node, ")")
Base.show(io::IO, f::SeqFrame) =
    print(io, "SeqFrame(", f.pat_node, " on ", f.subj_node, ")")
Base.show(io::IO, f::CommFrame) =
    print(io, "CommFrame(", f.pat_node, " on ", f.subj_node, ")")
Base.show(io::IO, f::ACFrame) =
    print(io, "ACFrame(", f.pat_node, " on ", f.subj_node, ")")

Base.show(io::IO, ::FramePool) = print(io, "FramePool()")

Base.show(io::IO, b::Bindings) = print(io, "Bindings(", count(!iszero, b.node), "/", length(b.node), " bound)")

###
### Results & iterators
###

Base.show(io::IO, it::MatchIterator) =
    (print(io, "matches("); print(io, it.eng.pat.ir[it.eng.pat.root]); print(io, ")"))
Base.show(io::IO, it::BoundMatchIterator) =
    (print(io, "boundmatches("); print(io, it.eng.pat.ir[it.eng.pat.root]); print(io, ")"))
Base.show(io::IO, it::BoundMatchAtIterator) =
    (print(io, "boundmatches_at("); print(io, it.eng.pat.ir[it.eng.pat.root]); print(io, ")"))

###
### Rules
###

function Base.show(io::IO, c::Constraint)
    print(io, "Constraint(<fn>, [")
    join(io, c.vars, ", ")
    return print(io, "])")
end

Base.show(io::IO, c::EngineConstraint) = print(io, "EngineConstraint(<fn>, ", c.var_ids, ")")

Base.show(io::IO, r::RhsPlan) =
    (print(io, "RhsPlan("); print(io, r.ir[r.root]); print(io, ")"))

_show_rhs(io::IO, r::RhsPlan) = print(io, r.ir[r.root])
_show_rhs(io::IO, ::RhsT) = print(io, "<callable>")

function Base.show(io::IO, r::CompiledRule)
    print(io, r.pat.ir[r.pat.root])
    print(io, " => ")
    return _show_rhs(io, r.rhs)
end

###
### Rule indexes
###

Base.show(io::IO, b::BucketIndex) = print(
    io, "BucketIndex(",
    length(b.by_op) + length(b.any_head) + length(b.leaf_rules),
    " rules, ", length(b.by_op), " buckets)",
)

Base.show(io::IO, k::NetOp) = print(io, "NetOp(", something(k.op, "*"), "/", k.arity, ")")

function Base.show(io::IO, d::NetDefer)
    print(io, "NetDefer(", something(d.op, "*"), "/")
    if d.lo == d.hi
        print(io, d.lo)
    elseif d.hi == typemax(Int)
        print(io, d.lo, "..∞")
    else
        print(io, d.lo, "..", d.hi)
    end
    return print(io, " → ", d.next, ")")
end

function Base.show(io::IO, s::NetState)
    parts = String[]
    isempty(s.ops) || push!(parts, "$(length(s.ops)) ops")
    isempty(s.opwilds) || push!(parts, "$(length(s.opwilds)) wilds")
    isempty(s.literals) || push!(parts, "$(length(s.literals)) literals")
    isempty(s.defers) || push!(parts, "$(length(s.defers)) defers")
    iszero(s.wild) || push!(parts, "wild → $(s.wild)")
    isempty(s.finals) || push!(parts, "finals $(Int.(s.finals))")
    print(io, "NetState(")
    join(io, parts, ", ")
    return print(io, ")")
end

Base.show(io::IO, n::DiscrimNet) = print(io, "DiscrimNet(", length(n.states), " states)")

###
### RuleSet & RuleWorkspace
###

Base.show(io::IO, rs::RuleSet) = print(
    io, "RuleSet{", nameof(typeof(rs.index)), "}(", length(rs.rules), " rules)",
)

function Base.show(io::IO, ::MIME"text/plain", rs::RuleSet)
    print(io, "RuleSet{", nameof(typeof(rs.index)), "} with ", length(rs.rules), " rules:")
    for r in rs.rules
        print(io, "\n  ")
        show(io, r)
    end
    return io
end

Base.show(io::IO, ws::RuleWorkspace) =
    print(io, "RuleWorkspace(", length(ws.set.rules), " rules)")

function Base.show(io::IO, ::MIME"text/plain", ws::RuleWorkspace)
    print(io, "RuleWorkspace for a ")
    return show(io, MIME"text/plain"(), ws.set)
end

###
### Traits
###

Base.show(io::IO, ::OperationTraitsCtx) = print(io, "OperationTraitsCtx()")

function Base.show(io::IO, t::OperationTraits)
    print(
        io, "OperationTraits(associative=", t.associative,
        ", commutative=", t.commutative
    )
    t.identity === nothing || print(io, ", identity=", t.identity)
    return print(io, ")")
end
