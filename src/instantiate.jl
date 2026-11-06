# DESIGN.md §5.6: instantiate — rebuild an expression over marker terms.

"""
    $TYPEDSIGNATURES

Rebuild `template`, replacing marker terms with their bound values from
`subst` (a `MarkersMap` or any dict keyed on variable syms/marker terms).
`slot`/`optional` vars substitute their bound expression; `segment` vars
splice `arguments(bound)` into the parent's argument list; a `Const`
segment binding (the identity) contributes zero arguments; a head marker
(`slot(f)(…)`) substitutes the raw bound operation (DESIGN.md §4.10, §5.6).

Iterates the template's `IRStructure` in postorder building `out[i]` — no
recursion: marker nodes resolve to their bound expression, and call nodes
rebuild `f(args…)` splicing segment-bound args (canonical exprs of children
are always available, children before parents).

For templates without segment or head markers, `SymbolicUtils.IRSubstituter`
gives the same result — `instantiate` is required for splicing and head
substitution, which node→expr rules cannot express.
"""
function instantiate(template::BasicSymbolic{SymReal}, subst)
    ir = IRStructure{SymReal}()
    root = populate_ir!(ir, template)
    g = ir.dependency_graph
    n = length(ir.symbols)
    out = Vector{BasicSymbolic{SymReal}}(undef, n)
    is_seg = falses(n)
    for i in 1:n
        t = ir[i]
        if is_marker_term(t)
            is_seg[i] = _is_segment_term(t)
            out[i] = subst[varsym(t)]
            continue
        end
        if !iscall(t)
            out[i] = t
            continue
        end
        nbs = Graphs.outneighbors(g, i)
        op = operation(t)
        argstart = op isa BasicSymbolic{SymReal} ? 2 : 1
        newop = op
        if argstart == 2 && is_marker_term(op)
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
    return out[root]
end
