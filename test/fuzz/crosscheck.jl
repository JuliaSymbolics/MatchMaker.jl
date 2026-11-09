# Cross-validate the frame engine against the naive oracle (§5.7):
# every engine result must appear in the oracle's result multiset and
# vice versa. Distinct assignments surface as duplicates in both, so
# comparison is by multiset of normalized binding dicts.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const

include(joinpath(@__DIR__, "..", "shared", "oracle.jl"))

# A result dict in canonical comparable form: values normalized to
# BasicSymbolic (head-slot ops and defaults arrive raw in the oracle,
# Const-wrapped by the engine), sorted by var name.
function _norm_result(d)
    pairs = sort!(
        [
            string(k) => (v isa BasicSymbolic{SymReal} ? v : Const{SymReal}(v))
                for (k, v) in d
        ]; by = first
    )
    return join(
        (string(k, " => ", repr(v)) for (k, v) in pairs), "; "
    )
end

const _NOVARS = Dict{BasicSymbolic{SymReal}, VarSpec.Type}()

function _compare(pat, subj; vars = _NOVARS)
    eng = collect(matchall(compile_pattern(pat; vars), subj))
    ora = oracle_matchall(pat, subj; vars)
    return (
        sort(_norm_result.(eng)),
        sort(_norm_result.(ora)),
    )
end

@syms x y z a b c s t p q r w

let
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = set_operation_traits(g; commutative = true)
    f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f = set_operation_traits(
        f; associative = true, commutative = true, identity = :f0
    )
    fa = Sym{SymReal}(:fa; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    fa = set_operation_traits(fa; associative = true)

    @testset "cross-check vs oracle" begin
        cases = [
            # free head: literals, slots, contiguous segments
            (h(slot(a), slot(b)), h(x, y), _NOVARS),
            (h(x, segment(s), y), h(x, p, q, y), _NOVARS),
            (h(segment(s), segment(t)), h(x, y, z), _NOVARS),
            (h(segment(s), b), h(x, y, b), _NOVARS),
            (h(segment(s), segment(s)), h(x, y, x, y), _NOVARS),
            # commutative-not-associative
            (g(slot(a), slot(b)), g(x, y), _NOVARS),
            (g(x, segment(s)), g(x, p, q), _NOVARS),
            (g(segment(s), segment(t)), g(x, y, z), _NOVARS),
            (g(segment(s), segment(s)), g(x, x, y, y), _NOVARS),
            (g(slot(a), slot(a)), g(x, x), _NOVARS),
            # associative-not-commutative (Seq + coercion)
            (fa(slot(a), segment(s)), fa(x, fa(y, z)), _NOVARS),
            (fa(x, segment(s)), fa(x, y), _NOVARS),
            # AC: slots, segments, non-linear, nested
            (f(slot(a), segment(s)), f(p, q, r), _NOVARS),
            (f(segment(s), segment(t)), f(p, q, r), _NOVARS),
            (x + segment(s), x + p + q, _NOVARS),
            (x + segment(s), x, _NOVARS),
            (f(slot(a), slot(b)), f(p, q), _NOVARS),
            (f(slot(a), slot(a)), f(p, p), _NOVARS),
            (g(slot(a), f(slot(b), segment(s))), g(x, f(p, q)), _NOVARS),
            # specs: min/max, predicates, defaults
            (
                f(segment(s), segment(t)),
                f(p, q, r),
                Dict(s => segmentspec(nothing; min = 1)),
            ),
            (
                h(segment(s)),
                h(x, y, z),
                Dict(s => segmentspec(nothing, seq -> length(seq) == 3)),
            ),
            (
                f(optional(a), segment(s)),
                f(p, q),
                Dict(a => slotspec(nothing; default = 5)),
            ),
            (
                f(x, optional(a)),
                f(x),
                Dict(a => slotspec(nothing; default = 7)),
            ),
            (
                g(x, segment(s)),
                g(x, 1, y),
                Dict(s => segmentspec(SymbolicUtils.issym)),
            ),
        ]
        for (pat, subj, vmap) in cases
            e, o = _compare(pat, subj; vars = vmap)
            @test e == o
            e == o || begin
                @info "mismatch" pat subj
                @info "engine" e
                @info "oracle" o
            end
        end
    end
end
