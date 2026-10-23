# DESIGN.md §5.6: instantiate — rebuild an expression over marker terms.

"""
    $TYPEDSIGNATURES

Rebuild `template`, replacing marker terms with their bound values from
`subst` (a `MarkersMap` or any dict keyed on variable syms/marker terms).
`slot`/`optional` vars substitute their bound expression; `segment` vars
splice `arguments(bound)` into the parent's argument list — a `Const`
binding must equal the parent's `identity_element` (DESIGN.md §5.6).
"""
function instantiate(template::BasicSymbolic{SymReal}, subst)
    return _inst(template, subst, nothing)
end

# `parent_op`/`parent_st` let a segment child verify a `Const` binding is the
# parent's identity element; `nothing` at the root.
function _inst(t::BasicSymbolic{SymReal}, subst, @nospecialize(parent_op))
    if is_marker_term(t)
        _is_segment_term(t) && error(
            lazy"segment $t must appear inside an argument list"
        )
        return subst[varsym(t)]
    end
    iscall(t) || return t
    op = operation(t)
    args = arguments(t)
    newargs = BasicSymbolic{SymReal}[]
    for a in args
        if _is_segment_term(a)
            bound = subst[varsym(a)]
            _splice_segment!(newargs, bound, op)
        else
            push!(newargs, _inst(a, subst, op))
        end
    end
    return term(op, newargs...)
end

# Splice a segment binding into `out`: `f(captured)` contributes its
# arguments; `Const(identity)` contributes nothing (and must equal the
# identity element); `f()` likewise contributes nothing.
function _splice_segment!(
        out::Vector{BasicSymbolic{SymReal}},
        bound::BasicSymbolic{SymReal}, @nospecialize(parent_op)
    )
    if isconst(bound)
        e = _identity_el(parent_op, symtype(bound))
        e !== nothing && isequal(bound, Const{SymReal}(e)) ||
            error(lazy"Const segment binding $bound is not the identity of $parent_op")
        return nothing
    end
    if iscall(bound) && operation(bound) === parent_op
        append!(out, arguments(bound))
        return nothing
    end
    error(lazy"segment binding $bound is not a $parent_op call")
    return nothing
end
