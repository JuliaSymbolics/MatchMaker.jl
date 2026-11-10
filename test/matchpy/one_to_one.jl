# Ported MatchPy one-to-one oracle cases — source:
# github.com/HPAC/matchpy tests/test_matching.py (TestMatch).
# Each case is (subject, pattern, expected binding multiset); bindings
# are translated to our materialization:
#
#   - MatchPy heads: `f`/`f2` → `h`/`h2` (free), `f_c`/`f2_c` → `g`/`g2`
#     (commutative), `f_a` → `fa` (associative), `f_ac` → `fac` (AC).
#   - `x_` (dot wildcard): `slot(x)` under free/commutative heads; under
#     associative/AC heads MatchPy's dot binds a non-empty run wrapped
#     in the head — translated to `segment(x)` + `min=1`.
#   - `x__` (plus wildcard) → `segment(x)` + `min=1`; `x___` (star) →
#     `segment(x)` + `min=0`. Anonymous `_`/`__`/`___` → fresh syms.
#   - MatchPy list segment values → `op(captured…)` materialization:
#     `h(a,b)`/`fa(a,b)` for ordered heads, `g(a,b)`/`fac(a,b)` for
#     unordered (Multiset). A single-element capture materializes as
#     `op(e)` for generic heads — MatchPy collapses `x ↦ f_a(a)` to
#     `x ↦ a`; ours keeps `fa(a)`.
#   - `s_`/`ss_` (symbol wildcards) → `slot` + `slotspec` predicates;
#     `a_x`/`f(a, variable_name='x')` → `slot` + `isequal` predicate.
#   - `MockConstraint(v)`/`MockConstraint(v, 'x')` → `Constraint(_->v, vars)`.
#
# Skipped (documented divergence or unsupported):
#   - `f_i`/`f_ci` (identity without associativity): our identity
#     coercion exists only under associative/AC heads;
#     test_one_identity_match is unportable.
#   - `oa__`/`oa___` optional *sequence* wildcards — our optional is
#     slot-kind only; `oa_` cases where the subject leaves ≥2 args
#     unconsumed (`o ↦ f_a(b,c)`) are skipped for the same reason.
#   - `optional` under free/commutative heads — ours is A/AC-only by
#     compile-time validation.
#   - The same var as `x_` under an assoc/AC head and as `x_`/`x__` under
#     a free/commutative head — a var may not mix slot and segment
#     kinds here (compile-time error).
#   - Bound-*value* vs bound-*run* recheck divergence: MatchPy rechecks
#     a bound dot's wrapped value against single args under AC; ours
#     rechecks the captured run multiset elementwise.
#   - `x2_` fixed-size wildcards, `match_many`, hypothesis-driven tests.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const, BasicSymbolic

function _mp_norm(d)
    pairs = sort!(
        [
            string(k) => (v isa BasicSymbolic{SymReal} ? v : Const{SymReal}(v))
                for (k, v) in d
        ]; by = first
    )
    return join((string(k, " => ", repr(v)) for (k, v) in pairs), "; ")
end

# deduped match count — MatchPy yields unique substitutions
function mpc(pat, subj; vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(), constraints = Constraint[])
    return length(
        unique(
            _mp_norm.(
                collect(matchall(compile_pattern(pat; vars = _mp_vars(pat, vars)), subj; constraints))
            )
        )
    )
end

# vars keys not present in the pattern must be dropped — the testsets
# share one spec table across cases
function _mp_vars(pat, vars)
    isempty(vars) && return vars
    keep = BasicSymbolic{SymReal}[]
    stack = BasicSymbolic{SymReal}[pat]
    while !isempty(stack)
        e = pop!(stack)
        if iscall(e)
            append!(stack, arguments(e))
        else
            push!(keep, e)
        end
    end
    return Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
        k => v for (k, v) in vars if any(isequal(k), keep)
    )
end

function mp(
        pat, subj, expected;
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(),
        constraints = Constraint[],
        drop = BasicSymbolic{SymReal}[]
    )
    vars = _mp_vars(pat, vars)
    # anonymous wildcards bind too — drop their keys before comparing
    dropn = Set(string.(drop))
    # MatchPy yields each distinct substitution once; the engine yields
    # one result per distinct assignment — dedupe identical maps
    got = unique(
        sort(
            _mp_norm.(
                [
                    Dict(k => v for (k, v) in d if string(k) ∉ dropn)
                        for d in collect(
                            matchall(
                                compile_pattern(pat; vars), subj; constraints
                            )
                        )
                ]
            )
        )
    )
    # expected maps: Dicts, or a Vector{Pair} meaning one map
    maps = expected isa AbstractVector{<:Pair} ? [expected] : expected
    want = sort(_mp_norm.(maps))
    return got == want
end

@syms a b c x y z p q sp xs ys zs u1 u2 u3 u o o2

let
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    h2 = Sym{SymReal}(:h2; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    hu = Sym{SymReal}(:hu; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = set_operation_traits(g; commutative = true)
    g2 = Sym{SymReal}(:g2; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g2 = set_operation_traits(g2; commutative = true)
    fa = Sym{SymReal}(:fa; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    fa = set_operation_traits(fa; associative = true)
    fac = Sym{SymReal}(:fac; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    fac = set_operation_traits(fac; associative = true, commutative = true)

    seg1(vs) = vs => segmentspec(nothing; min = 1)
    seg0(vs) = vs => segmentspec(nothing; min = 0)

    @testset "constant match" begin
        cases = [
            (a, a, 1), (b, a, 0), (h(), h(), 1), (h(a), h(), 0),
            (h(a), h(a), 1), (h(b), h(a), 0), (h(), h(a), 0),
            (h2(a), h(a), 0), (h(a, b), h(a), 0), (h(a, b), h(a, b), 1),
            (h(a), h(a, b), 0), (h(b, a), h(a, b), 0),
            (h(a, b, c), h(a, b), 0), (h(a, h2(b)), h(a, b), 0),
            (h(h2(a), h2(b)), h(a, b), 0), (h(h2(a), b), h(a, b), 0),
            (h(h(a, b)), h(a, b), 0), (h2(a, b), h(a, b), 0),
            (h(a, h2(b)), h(a, h2(b)), 1), (h(h2(a), b), h(h2(a), b), 1),
            (h(h(a, b)), h(h(a, b)), 1),
        ]
        for (subj, pat, n) in cases
            @test mpc(pat, subj) == n
        end
    end

    @testset "commutative literals" begin
        cases = [
            (g(), g(), 1), (g(a), g(), 0), (g(), g(a), 0),
            (g(a, b), g(a, b), 1), (g(b, a), g(a, b), 1),
            (g(b, a, c), g(a, b, c), 1), (g(c, a, b), g(a, b, c), 1),
            (g(b, a, c), g(c, b, a), 1), (g(b, a, a), g(a, a, b), 1),
            (g(a, b, a), g(a, a, b), 1), (g(b, b, a), g(a, a, b), 0),
            (g(c, a, h2(b)), g(a, h2(b), c), 1),
            (g(c, a, h2(b)), g(h2(a), b, c), 0),
            (h2(c, g(a, b)), h2(c, g(b, a)), 1),
            (h2(c, g(a, b)), h2(g(a, b), c), 0),
            (g(c, g(a, b)), g(g(a, b), c), 1),
            (g(c, g(b, a)), g(g(a, b), c), 1),
            (g(c, g(b, b)), g(g(a, b), c), 0),
            (g(a, g(b, a)), g(g(a, b), c), 0),
        ]
        for (subj, pat, n) in cases
            @test mpc(pat, subj) == n
        end
    end

    @testset "commutative slots" begin
        cases = [
            (g(h(a)), g(h(slot(x))), 1),
            (g(h(a), h(b)), g(h(slot(x)), h(slot(y))), 2),
            (g(h(a), h(b)), g(h(slot(x)), h(slot(x))), 0),
            (g(h(a), h(a)), g(h(slot(x)), h(slot(y))), 1),
            (g(h(a), h(b)), g(h(slot(x)), slot(y)), 2),
            (g(h(a), h(a)), g(h(slot(x)), slot(x)), 0),
            (g(h(a), a), g(h(slot(x)), slot(x)), 1),
            (g(h(a), a), g(h(slot(x))), 0),
            (g(h(a), a), g(h(slot(x)), h(slot(y))), 0),
            (g(h(a), h(a)), g(h(slot(x)), h(slot(y)), h(slot(z))), 0),
            (g(h2(a), h2(a)), g(h(slot(x)), h(slot(y))), 0),
            (g2(h(a), h(a)), g(h(slot(x)), h(slot(y))), 0),
        ]
        for (subj, pat, n) in cases
            @test mpc(pat, subj) == n
        end
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 0), y => segmentspec(nothing; min = 0)
        )
        @test mpc(
            g(g(segment(x)), segment(y)), g(g(a, b), c); vars
        ) == 1
    end

    @testset "dot wildcard" begin
        cases = [
            (a, slot(x), [x => a]), (b, slot(x), [x => b]),
            (h(a), h(slot(x)), [x => a]), (h(b), h(slot(x)), [x => b]),
            (h(a), slot(x), [x => h(a)]), (h2(a), h(slot(x)), Dict[]),
            (h(a, b), h(slot(x)), Dict[]),
            (h(a, b), h(slot(x), b), [x => a]),
            (h(a, b), h(slot(x), a), Dict[]),
            (h(a, b), h(a, slot(x)), [x => b]),
            (h(a, b), h(slot(x), slot(x)), Dict[]),
            (h(a, a), h(slot(x), slot(x)), [x => a]),
            (h(a, b), h(slot(x), slot(y)), [x => a, y => b]),
            (h(a), h(slot(x), slot(y)), Dict[]),
            (h(a, b, c), h(slot(x), slot(y)), Dict[]),
            (h(a, h2(b)), h(slot(x), slot(y)), [x => a, y => h2(b)]),
            (h(a, h2(b)), h(slot(x), h2(slot(y))), [x => a, y => b]),
            (h(a, h2(b)), h(slot(x), h2(slot(x))), Dict[]),
            (h(a, h2(a)), h(slot(x), h2(slot(x))), [x => a]),
            (h(h2(a), h2(b)), h(slot(x), slot(x)), Dict[]),
            (h(h2(a), h2(b)), h(slot(x), slot(y)), [x => h2(a), y => h2(b)]),
            (h(h2(a), a), h(slot(x), slot(x)), Dict[]),
            (h(h2(a), a), h(h2(slot(x)), slot(x)), [x => a]),
            (h(h(a, b)), h(slot(x), slot(y)), Dict[]),
            (h(h(a, b)), h(slot(x)), [x => h(a, b)]),
            (h2(a, b), h(slot(x), slot(y)), Dict[]),
            (h(h(a, b)), h(h(slot(x), slot(y))), [x => a, y => b]),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps)
        end
    end

    @testset "star wildcard" begin
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 0), y => segmentspec(nothing; min = 0)
        )
        cases = [
            (a, slot(xs), [xs => a]),
            (h(a), h(segment(x)), [x => h(a)]),
            (h(), h(segment(x)), [x => h()]),
            (h(a), slot(xs), [xs => h(a)]),
            (h2(a), h(segment(x)), Dict[]),
            (h(a, b), h(segment(x)), [x => h(a, b)]),
            (h(a, b), h(segment(x), b), [x => h(a)]),
            (h(a, b), h(segment(x), a), Dict[]),
            (h(a, b), h(a, segment(x)), [x => h(b)]),
            (h(a, b), h(segment(x), segment(x)), Dict[]),
            (h(a, a), h(segment(x), segment(x)), [x => h(a)]),
            (
                h(a, b), h(segment(x), segment(y)),
                [
                    Dict(x => h(), y => h(a, b)),
                    Dict(x => h(a), y => h(b)),
                    Dict(x => h(a, b), y => h()),
                ],
            ),
            (
                h(a), h(segment(x), segment(y)),
                [Dict(x => h(), y => h(a)), Dict(x => h(a), y => h())],
            ),
            (
                h(a, b, c), h(segment(x), segment(y)),
                [
                    Dict(x => h(), y => h(a, b, c)),
                    Dict(x => h(a), y => h(b, c)),
                    Dict(x => h(a, b), y => h(c)),
                    Dict(x => h(a, b, c), y => h()),
                ],
            ),
            (
                h(a, h2(b)), h(segment(x), segment(y)),
                [
                    Dict(x => h(), y => h(a, h2(b))),
                    Dict(x => h(a), y => h(h2(b))),
                    Dict(x => h(a, h2(b)), y => h()),
                ],
            ),
            (h(a, h2(b)), h(segment(x), h2(segment(y))), [x => h(a), y => h2(b)]),
            (h(a, h2(b)), h(segment(x), h2(segment(x))), Dict[]),
            (h(a, h2(a)), h(segment(x), h2(segment(x))), [x => h(a)]),
            (h(h2(a), h2(b)), h(segment(x), segment(x)), Dict[]),
            (
                h(h2(a), h2(b)), h(segment(x), segment(y)),
                [
                    Dict(x => h(h2(a), h2(b)), y => h()),
                    Dict(x => h(h2(a)), y => h(h2(b))),
                    Dict(x => h(), y => h(h2(a), h2(b))),
                ],
            ),
            (h(h2(a), a), h(segment(x), segment(x)), Dict[]),
            (h(h2(a), a), h(h2(segment(x)), segment(x)), [x => h2(a)]),
            (
                h(h(a, b)), h(segment(x), segment(y)),
                [
                    Dict(x => h(h(a, b)), y => h()),
                    Dict(x => h(), y => h(h(a, b))),
                ],
            ),
            (h(h(a, b)), h(segment(x)), [x => h(h(a, b))]),
            (h2(a, b), h(segment(x), segment(y)), Dict[]),
            (h(a, a, a), h(segment(x), b, segment(y)), Dict[]),
            (
                h(a, a, a), h(segment(x), a, segment(y)),
                [
                    Dict(x => h(), y => h(a, a)),
                    Dict(x => h(a), y => h(a)),
                    Dict(x => h(a, a), y => h()),
                ],
            ),
            (h(a), h(segment(x), a, segment(y)), [Dict(x => h(), y => h())]),
            (
                h(a, a), h(segment(x), a, segment(y)),
                [Dict(x => h(a), y => h()), Dict(x => h(), y => h(a))],
            ),
            (
                h(a, b, a), h(segment(x), a, segment(y)),
                [Dict(x => h(), y => h(b, a)), Dict(x => h(a, b), y => h())],
            ),
            (h(a, b, a, b), h(segment(x), segment(x)), [x => h(a, b)]),
            (h(a, b, a, a), h(segment(x), segment(x)), Dict[]),
            (h(a, b, a), h(segment(x), b, segment(x)), [x => h(a)]),
            (h(a, b, a, a), h(segment(x), b, segment(x)), Dict[]),
            (h(a, a, b, a), h(segment(x), b, segment(x)), Dict[]),
            (h(a, b, a, b, a, b, a), h(segment(x), b, segment(x)), [x => h(a, b, a)]),
            (
                h(a, b, a, b), h(segment(x), b, segment(y)),
                [Dict(x => h(a, b, a), y => h()), Dict(x => h(a), y => h(a, b))],
            ),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps; vars)
        end
    end

    @testset "plus wildcard" begin
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1), y => segmentspec(nothing; min = 1)
        )
        cases = [
            (a, slot(xs), [xs => a]),
            (h(a), h(segment(x)), [x => h(a)]),
            (h(), h(segment(x)), Dict[]),
            (h(a), slot(xs), [xs => h(a)]),
            (h2(a), h(segment(x)), Dict[]),
            (h(a, b), h(segment(x)), [x => h(a, b)]),
            (h(a, b), h(segment(x), b), [x => h(a)]),
            (h(a, b), h(segment(x), a), Dict[]),
            (h(a, b), h(a, segment(x)), [x => h(b)]),
            (h(a, b), h(segment(x), segment(x)), Dict[]),
            (h(a, a), h(segment(x), segment(x)), [x => h(a)]),
            (h(a, b), h(segment(x), segment(y)), [Dict(x => h(a), y => h(b))]),
            (h(a), h(segment(x), segment(y)), Dict[]),
            (
                h(a, b, c), h(segment(x), segment(y)),
                [Dict(x => h(a), y => h(b, c)), Dict(x => h(a, b), y => h(c))],
            ),
            (h(a, h2(b)), h(segment(x), segment(y)), [Dict(x => h(a), y => h(h2(b)))]),
            (h(a, h2(b)), h(segment(x), h2(segment(y))), [x => h(a), y => h2(b)]),
            (h(a, h2(b)), h(segment(x), h2(segment(x))), Dict[]),
            (h(a, h2(a)), h(segment(x), h2(segment(x))), [x => h(a)]),
            (h(h2(a), h2(b)), h(segment(x), segment(x)), Dict[]),
            (h(h2(a), h2(b)), h(segment(x), segment(y)), [Dict(x => h(h2(a)), y => h(h2(b)))]),
            (h(h2(a), a), h(segment(x), segment(x)), Dict[]),
            (h(h2(a), a), h(h2(segment(x)), segment(x)), [x => h2(a)]),
            (h(h(a, b)), h(segment(x), segment(y)), Dict[]),
            (h(h(a, b)), h(segment(x)), [x => h(h(a, b))]),
            (h2(a, b), h(segment(x), segment(y)), Dict[]),
            (h(a, a, a), h(segment(x), b, segment(y)), Dict[]),
            (h(a, a, a), h(segment(x), a, segment(y)), [Dict(x => h(a), y => h(a))]),
            (h(a), h(segment(x), a, segment(y)), Dict[]),
            (h(a, a), h(segment(x), a, segment(y)), Dict[]),
            (h(a, b, a), h(segment(x), a, segment(y)), Dict[]),
            (h(a, b, a, b), h(segment(x), segment(x)), [x => h(a, b)]),
            (h(a, b, a, a), h(segment(x), segment(x)), Dict[]),
            (h(a, b, a), h(segment(x), b, segment(x)), [x => h(a)]),
            (h(a, b, a, a), h(segment(x), b, segment(x)), Dict[]),
            (h(a, a, b, a), h(segment(x), b, segment(x)), Dict[]),
            (h(a, b, a, b, a, b, a), h(segment(x), b, segment(x)), [x => h(a, b, a)]),
            (h(a, b, a, b), h(segment(x), b, segment(y)), [Dict(x => h(a), y => h(a, b))]),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps; vars)
        end
    end

    @testset "mixed wildcards" begin
        v1 = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1), y => segmentspec(nothing; min = 0)
        )
        v2 = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 0), y => segmentspec(nothing; min = 1)
        )
        v3 = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 0), y => segmentspec(nothing; min = 0),
            z => segmentspec(nothing; min = 0),
        )
        v4 = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1),
            z => segmentspec(nothing; min = 0),
        )
        v5 = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 0),
            z => segmentspec(nothing; min = 1),
        )
        v6 = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1),
            z => segmentspec(nothing; min = 1),
        )
        cases = [
            # f(a,b)  f(x__, y___)   MatchPy: [x:[a,b],y:[]; x:[a],y:[b]]
            (
                h(a, b), h(segment(x), segment(y)), v1,
                [Dict(x => h(a, b), y => h()), Dict(x => h(a), y => h(b))],
            ),
            # f(a,b)  f(x___, y__)   MatchPy: [x:[a],y:[b]; x:[],y:[a,b]]
            (
                h(a, b), h(segment(x), segment(y)), v2,
                [Dict(x => h(a), y => h(b)), Dict(x => h(), y => h(a, b))],
            ),
            # f(a,b,c) f(x_, y__)    [x:a, y:[b,c]]
            (
                h(a, b, c), h(slot(xs), segment(y)), v1,
                [Dict(xs => a, y => h(b, c))],
            ),
            # f(a,b,c) f(x__, y_)    [x:[a,b], y:c]
            (
                h(a, b, c), h(segment(x), slot(ys)), v1,
                [Dict(x => h(a, b), ys => c)],
            ),
            # f(a,b,c) f(x_, y___)   [x:a, y:[b,c]]
            (
                h(a, b, c), h(slot(xs), segment(y)), v2,
                [Dict(xs => a, y => h(b, c))],
            ),
            # f(a,b,c) f(x___, y_)   [x:[a,b], y:c]
            (
                h(a, b, c), h(segment(x), slot(ys)), v2,
                [Dict(x => h(a, b), ys => c)],
            ),
            # f(a,b,c) f(x___, y_, z___)
            #   [x:[a,b],y:c,z:[]; x:[a],y:b,z:[c]; x:[],y:a,z:[b,c]]
            (
                h(a, b, c), h(segment(x), slot(ys), segment(z)), v3,
                [
                    Dict(x => h(a, b), ys => c, z => h()),
                    Dict(x => h(a), ys => b, z => h(c)),
                    Dict(x => h(), ys => a, z => h(b, c)),
                ],
            ),
            # f(a,b,c) f(x__, y_, z___)
            #   [x:[a,b],y:c,z:[]; x:[a],y:b,z:[c]]
            (
                h(a, b, c), h(segment(x), slot(ys), segment(z)), v4,
                [
                    Dict(x => h(a, b), ys => c, z => h()),
                    Dict(x => h(a), ys => b, z => h(c)),
                ],
            ),
            # f(a,b,c) f(x___, y_, z__)
            #   [x:[a],y:b,z:[c]; x:[],y:a,z:[b,c]]
            (
                h(a, b, c), h(segment(x), slot(ys), segment(z)), v5,
                [
                    Dict(x => h(a), ys => b, z => h(c)),
                    Dict(x => h(), ys => a, z => h(b, c)),
                ],
            ),
            # f(a,b,c) f(x__, y_, z__)   [x:[a],y:b,z:[c]]
            (
                h(a, b, c), h(segment(x), slot(ys), segment(z)), v6,
                [Dict(x => h(a), ys => b, z => h(c))],
            ),
            # f(a,a) f(x_, x__) / f(x__, x_) — skipped: same var 'x' as
            # both dot and sequence would be a slot/segment kind mix
        ]
        for (subj, pat, v, maps) in cases
            @test mp(pat, subj, maps; vars = v)
        end
        # f(x__, f_c(x__)) vs f(f(a,b), f_c(reorder)) — bound run under f,
        # multiset recheck under g (all four orders match)
        vm = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1)
        )
        cases2 = [
            (h(h(slot(xs)), g(slot(xs))), h(h(a), g(a)), true),
            (h(h(segment(x)), g(segment(x))), h(h(a, b), g(a, b)), true),
            (h(h(segment(x)), g(segment(x))), h(h(a, b), g(b, a)), true),
            (h(h(segment(x)), g(segment(x))), h(h(b, a), g(b, a)), true),
            (h(h(segment(x)), g(segment(x))), h(h(b, a), g(a, b)), true),
            (h(g(segment(x)), h(segment(x))), h(g(a, b), h(a, b)), true),
            (h(g(segment(x)), h(segment(x))), h(g(b, a), h(a, b)), true),
            (h(g(segment(x)), h(segment(x))), h(g(b, a), h(b, a)), true),
            (h(g(segment(x)), h(segment(x))), h(g(a, b), h(b, a)), true),
            (h(g(segment(x)), g(segment(x))), h(g(a, b), g(a, b)), true),
        ]
        for (pat, subj, ok) in cases2
            @test !isempty(matchall(compile_pattern(pat; vars = _mp_vars(pat, vm)), subj)) == ok
        end
    end

    @testset "commutative multiple fixed vars" begin
        cases = [
            (
                g(a, b, a, a, b), g(slot(x), slot(x), slot(x), slot(y), slot(y)),
                [Dict(x => a, y => b)],
            ),
            (
                g(a, b, a, b), g(slot(x), slot(x), slot(y), slot(y)),
                [Dict(x => a, y => b), Dict(x => b, y => a)],
            ),
            (
                g(a, b, a, b), g(slot(x), slot(x), slot(x), slot(y), slot(y)),
                Dict[],
            ),
            (g(a, b, a, b), g(slot(x), slot(y), slot(y)), Dict[]),
            (
                g(a, b, a, b), g(slot(x), a, slot(y), slot(y)),
                [Dict(x => a, y => b)],
            ),
            (
                g(a, b, b, b), g(slot(x), b, slot(y), slot(y)),
                [Dict(x => a, y => b)],
            ),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps)
        end
        # anonymous dots: f_c(a,b,a,a,b)  f_c(_,_,_,y_,y_) -> y:{a},{b}
        drop = BasicSymbolic{SymReal}[u1, u2, u3]
        @test mp(
            g(slot(u1), slot(u2), slot(u3), slot(y), slot(y)),
            g(a, b, a, a, b), [Dict(y => a), Dict(y => b)]; drop = drop
        )
        @test mp(
            g(slot(u1), slot(u2), slot(y), slot(y)),
            g(a, b, a, b), [Dict(y => b), Dict(y => a)]; drop = drop
        )
        @test mp(
            g(slot(u1), slot(u2), slot(u3), slot(y), slot(y)),
            g(a, b, a, b), Dict[]; drop = drop
        )
        @test mp(
            g(slot(u1), slot(y), slot(y)),
            g(a, b, a, b), Dict[]; drop = drop
        )
        @test mp(
            g(slot(u1), slot(u2), slot(y), slot(y)),
            g(a, b, b, b), [Dict(y => b)]; drop = drop
        )
        @test mp(
            g(slot(u1), a, slot(y), slot(y)),
            g(a, b, a, b), [Dict(y => b)]; drop = drop
        )
        @test mp(
            g(slot(u1), b, slot(y), slot(y)),
            g(a, b, a, b), [Dict(y => a)]; drop = drop
        )
        @test mp(
            g(slot(u1), b, slot(y), slot(y)),
            g(a, b, b, b), [Dict(y => b)]; drop = drop
        )
    end

    @testset "commutative multiple sequence vars" begin
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 0), y => segmentspec(nothing; min = 0),
            u1 => segmentspec(nothing; min = 1), u2 => segmentspec(nothing; min = 1),
        )
        # f_c(a,b)  f_c(x___, y___) — all 4 splits
        @test mp(
            g(segment(x), segment(y)), g(a, b),
            [
                Dict(x => g(a), y => g(b)), Dict(x => g(b), y => g(a)),
                Dict(x => g(a, b), y => g()), Dict(x => g(), y => g(a, b)),
            ]; vars
        )
        # f_c(a,b)  f_c(x___, x___)  -> []
        @test mp(g(segment(x), segment(x)), g(a, b), Dict[]; vars)
        # f_c(a,a)  f_c(x___, x___)  -> [{x: Multiset([a])}]
        @test mp(g(segment(x), segment(x)), g(a, a), [x => g(a)]; vars)
        # f_c(a,a)  f_c(x___, x___, y___) -> [{x:{a},y:{}}; {x:{},y:{a,a}}]
        @test mp(
            g(segment(x), segment(x), segment(y)), g(a, a),
            [Dict(x => g(a), y => g()), Dict(x => g(), y => g(a, a))]; vars
        )
        # h(a, b, g(a,b)) vs h(x___, g(x___)) -> [x: (a,b)]
        @test mp(
            h(segment(x), g(segment(x))), h(a, b, g(a, b)), [x => h(a, b)]; vars
        )
        @test mp(
            h(segment(x), g(segment(x))), h(b, a, g(a, b)), [x => h(b, a)]; vars
        )
        @test mp(
            h(segment(x), g(segment(x))), h(a, a, g(a, b)), Dict[]; vars
        )
        @test mp(
            h(segment(x), g(segment(x))), h(a, b, g(a, a)), Dict[]; vars
        )
        # f_c(a)   f_c(__, __)   -> []
        @test mp(
            g(segment(u1), segment(u2)), g(a), Dict[]; vars
        )
        # f_c(a,a) f_c(__, __)   -> [{}]
        @test mp(
            g(segment(u1), segment(u2)), g(a, a), [Dict()]; vars,
            drop = BasicSymbolic{SymReal}[u1, u2]
        )
        # f_c(a,b) f_c(__, __)   -> [{}]
        @test mp(
            g(segment(u1), segment(u2)), g(a, b), [Dict()]; vars,
            drop = BasicSymbolic{SymReal}[u1, u2]
        )
    end

    @testset "mixed commutative vars" begin
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1)
        )
        cases = [
            (h(h(slot(xs)), g(slot(xs))), h(h(a), g(a)), true),
            (h(h(segment(x)), g(segment(x))), h(h(a, b), g(a, b)), true),
            (h(h(segment(x)), g(segment(x))), h(h(a, b), g(b, a)), true),
            (h(h(segment(x)), g(segment(x))), h(h(b, a), g(b, a)), true),
            (h(h(segment(x)), g(segment(x))), h(h(b, a), g(a, b)), true),
            (h(g(segment(x)), h(segment(x))), h(g(a, b), h(a, b)), true),
            (h(g(segment(x)), h(segment(x))), h(g(b, a), h(a, b)), true),
            (h(g(segment(x)), h(segment(x))), h(g(b, a), h(b, a)), true),
            (h(g(segment(x)), h(segment(x))), h(g(a, b), h(b, a)), true),
            (h(g(segment(x)), g(segment(x))), h(g(a, b), g(a, b)), true),
        ]
        for (pat, subj, ok) in cases
            @test !isempty(matchall(compile_pattern(pat; vars = _mp_vars(pat, vars)), subj)) == ok
        end
    end

    @testset "mixed assoc/comm vars" begin
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1)
        )
        cases = [
            # same-var segments under different heads — rechecks
            (h(fa(segment(x)), fac(segment(x))), h(fa(a), fac(a)), true),
            (h(fac(segment(x)), fa(segment(x))), h(fac(a), fa(a)), true),
            (h(fac(segment(x)), g(segment(x))), h(fac(a), g(a)), true),
            (
                h(fac(segment(x)), fac(segment(x), segment(x))),
                h(fac(a, b), fac(a, a, b, b)), true,
            ),
            # bound under ordered head, multiset recheck under unordered
            (h(fa(segment(x)), g(segment(x))), h(fa(a, b), g(b, a)), true),
            (h(fa(segment(x)), g(segment(x))), h(fa(a, b), g(a, b)), true),
            (h(fa(segment(x)), g(segment(x))), h(fa(a), g(a)), true),
            (h(fa(segment(x)), g(segment(x))), h(fa(a, b), g(a, a)), false),
            (h(fa(segment(x)), g(segment(x))), h(fa(a, b), g(b)), false),
        ]
        for (pat, subj, ok) in cases
            @test !isempty(matchall(compile_pattern(pat; vars = _mp_vars(pat, vars)), subj)) == ok
        end
    end

    @testset "symbol wildcards" begin
        # s_ = any-symbol wildcard (slotspec issym); ss_ = SpecialSymbol
        # (slotspec isequal(_, sp))
        iss = slotspec(SymbolicUtils.issym)
        spc = slotspec(e -> isequal(e, sp))
        v = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => iss, sp => spc, y => segmentspec(nothing; min = 0)
        )
        cases = [
            (a, slot(x), [x => a]),
            (sp, slot(x), [x => sp]),
            (h(a), slot(x), Dict[]),
            (a, slot(sp), Dict[]),
            (h(a), slot(sp), Dict[]),
            (sp, slot(sp), [sp => sp]),
            (fa(a), fa(slot(x)), [x => a]),
            (fa(h(a)), fa(slot(x)), Dict[]),
            (g(a), g(slot(sp)), Dict[]),
            (g(sp), g(slot(sp)), [sp => sp]),
            (g(a, sp), g(slot(sp), segment(y)), [sp => sp]),
            (
                g(a, sp), g(slot(x), segment(y)),
                [Dict(x => sp), Dict(x => a)],
            ),
            (fac(a), fac(slot(sp)), Dict[]),
            (fac(sp), fac(slot(sp)), [sp => sp]),
            (fac(a, sp), fac(slot(sp), segment(y)), [sp => sp]),
            (
                fac(a, sp), fac(slot(x), segment(y)),
                [Dict(x => sp), Dict(x => a)],
            ),
            (fac(a, sp), fac(slot(x)), Dict[]),
        ]
        drop = BasicSymbolic{SymReal}[y]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps; vars = v, drop = drop)
        end
    end

    @testset "variable_name" begin
        # a_x / f(a, variable_name='x') — a slot constrained to a literal
        lit_a = slotspec(e -> isequal(e, a))
        lit_fa = slotspec(e -> isequal(e, h(a)))
        lit_fab = slotspec(e -> isequal(e, h(a, b)))
        lit_f2a = slotspec(e -> isequal(e, h2(a)))
        cases = [
            (a, slot(x), lit_a, [x => a]),
            (h(a), h(slot(x)), lit_a, [x => a]),
            (h(b), h(slot(x)), lit_a, Dict[]),
            (h(a, b), h(slot(x), b), lit_a, [x => a]),
            (h(a), slot(x), lit_fa, [x => h(a)]),
            (h2(a), slot(x), lit_fa, Dict[]),
            (h(a, b), slot(x), lit_fab, [x => h(a, b)]),
            (h2(h(a)), h2(slot(x)), lit_fa, [x => h(a)]),
            (h2(h(a, b)), h2(slot(x)), lit_fab, [x => h(a, b)]),
        ]
        for (subj, pat, spec, maps) in cases
            @test mp(
                pat, subj, maps;
                vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(x => spec)
            )
        end
    end

    @testset "associative dot" begin
        # dot under an associative head binds a non-empty contiguous run
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1), y => segmentspec(nothing; min = 1)
        )
        cases = [
            (fa(a), fa(segment(x)), [x => fa(a)]),
            (fa(a, b), fa(segment(x)), [x => fa(a, b)]),
            (fa(a, b), fa(a, segment(x)), [x => fa(b)]),
            (fa(a, b, c), fa(a, segment(x)), [x => fa(b, c)]),
            (fa(a, b, c), fa(segment(x), c), [x => fa(a, b)]),
            (fa(a, b, c), fa(segment(x)), [x => fa(a, b, c)]),
            (fa(a, b, a, b), fa(segment(x), segment(x)), [x => fa(a, b)]),
            (fa(a, b, a), fa(segment(x), b, segment(x)), [x => fa(a)]),
            (fa(a, a, b, a, a), fa(segment(x), b, segment(x)), [x => fa(a, a)]),
            (
                fa(a, b, c), fa(segment(x), segment(y)),
                [Dict(x => fa(a), y => fa(b, c)), Dict(x => fa(a, b), y => fa(c))],
            ),
            (fa(a), fa(segment(x)), [x => fa(a)]),
            (fa(a, b), fa(segment(x)), [x => fa(a, b)]),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps; vars)
        end
        @test mp(
            fa(segment(u)), fa(a), [Dict()];
            vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
                u => segmentspec(nothing; min = 1)
            ), drop = BasicSymbolic{SymReal}[u]
        )
        @test mp(
            fa(segment(u)), fa(a, b), [Dict()];
            vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
                u => segmentspec(nothing; min = 1)
            ), drop = BasicSymbolic{SymReal}[u]
        )
    end

    @testset "AC dot" begin
        vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            x => segmentspec(nothing; min = 1)
        )
        cases = [
            (fac(a), fac(segment(u)), [Dict()]),
            (fac(a), fac(segment(x)), [x => fac(a)]),
            (fac(a, b), fac(segment(u)), [Dict()]),
            (fac(a, b), fac(segment(x)), [x => fac(a, b)]),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps; vars, drop = BasicSymbolic{SymReal}[u])
        end
    end

    @testset "optional wildcard" begin
        # only the portable cases: optional dot under fa/fac (A/AC) with
        # ≤1 leftover arg — plus the two-optional variants MatchPy lists
        # under f_i (identity-free heads don't port, but these read the
        # same under fa). oa_ = optional(o) default a, o2b_ = optional(o2)
        # default b.
        vo = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            o => slotspec(nothing; default = a),
            o2 => slotspec(nothing; default = b),
        )
        cases = [
            (fa(a), fa(a, optional(o)), [o => a]),
            (fa(a, b), fa(a, optional(o)), [o => b]),
            (fac(a), fac(a, optional(o)), [o => a]),
            (fac(a, b), fac(a, optional(o)), [o => b]),
            (fac(a, b, c), fac(a, optional(o)), Dict[]),
            (fa(a), fa(a, optional(o), optional(o)), [o => a]),
            (fa(a), fa(a, optional(o), optional(o2)), [Dict(o => a, o2 => b)]),
            (fa(a, a), fa(a, optional(o), optional(o)), [o => a]),
            # nested-fa cases (f(f(oa_), oa_) under a free head in
            # MatchPy): under `fa` the subject flattens — not portable
            (fac(a), fac(optional(o)), [o => a]),
        ]
        for (subj, pat, maps) in cases
            @test mp(pat, subj, maps; vars = vo)
        end
    end

    @testset "constraints" begin
        # global MockConstraint(v) — ports as a Constraint over the
        # pattern's vars
        cases = [
            (a, slot(u1), [_u -> false], 0),
            (a, slot(u1), [_u -> true], 1),
            (h(a, b), h(slot(u1), slot(u2)), [_u -> false, _u -> true], 0),
            (h(a, b), h(slot(u1), slot(u2)), [_u -> false, _u -> false], 0),
            (h(a, b), h(slot(u1), slot(u2)), [_u -> true, _u -> false], 0),
            (h(a, b), h(slot(u1), slot(u2)), [_u -> true, _u -> true], 1),
            (a, slot(x), [_u -> true], 1),
            (a, slot(x), [_u -> false], 0),
            (h(a, a), h(slot(x), slot(x)), [_u -> false, _u -> false], 0),
            (h(a, a), h(slot(x), slot(x)), [_u -> true, _u -> false], 0),
            (h(a, a), h(slot(x), slot(x)), [_u -> false, _u -> true], 0),
            (h(a, a), h(slot(x), slot(x)), [_u -> true, _u -> true], 1),
            (h(a), h(a), [_u -> false], 0),
            (h(a), h(a), [_u -> true], 1),
            (g(a, a), g(slot(x), slot(x)), [_u -> false, _u -> false], 0),
            (g(a, a), g(slot(x), slot(x)), [_u -> true, _u -> false], 0),
            (g(a, a), g(slot(x), slot(x)), [_u -> false, _u -> true], 0),
            (g(a, a), g(slot(x), slot(x)), [_u -> true, _u -> true], 1),
            (h(a, g(a)), h(slot(x), g(slot(x))), [_u -> false, _u -> false], 0),
            (h(a, g(a)), h(slot(x), g(slot(x))), [_u -> true, _u -> false], 0),
            (h(a, g(a)), h(slot(x), g(slot(x))), [_u -> false, _u -> true], 0),
            (h(a, g(a)), h(slot(x), g(slot(x))), [_u -> true, _u -> true], 1),
            (g(a, h(a)), g(slot(x), h(slot(x))), [_u -> false, _u -> false], 0),
            (g(a, h(a)), g(slot(x), h(slot(x))), [_u -> true, _u -> false], 0),
            (g(a, h(a)), g(slot(x), h(slot(x))), [_u -> false, _u -> true], 0),
            (g(a, h(a)), g(slot(x), h(slot(x))), [_u -> true, _u -> true], 1),
        ]
        for (subj, pat, cns, n) in cases
            cs = [Constraint(fn, BasicSymbolic{SymReal}[]) for fn in cns]
            @test mpc(pat, subj; constraints = cs) == n
        end
        # segment-position constraints: h(___ , ___) with global values
        vv = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            u1 => segmentspec(nothing; min = 0), u2 => segmentspec(nothing; min = 0),
            x => segmentspec(nothing; min = 0),
        )
        @test mpc(
            h(segment(u1), segment(u2)), h(a, b); vars = vv,
            constraints = [
                Constraint(_ -> false, BasicSymbolic{SymReal}[]),
                Constraint(_ -> false, BasicSymbolic{SymReal}[]),
            ]
        ) == 0
        @test mpc(
            h(segment(u1), segment(u2)), h(a, b); vars = vv,
            constraints = [
                Constraint(_ -> true, BasicSymbolic{SymReal}[]),
                Constraint(_ -> true, BasicSymbolic{SymReal}[]),
            ]
        ) == 3
        # local MockConstraint(v, 'x') — constraint over [x]
        @test mpc(
            g(slot(x), slot(x)), g(a, a);
            constraints = [Constraint(_ -> true, [x])]
        ) == 1
        @test mpc(
            g(segment(x)), g(a, a); vars = vv,
            constraints = [Constraint(_ -> false, [x])]
        ) == 0
        @test mpc(
            g(segment(x)), g(a, a); vars = vv,
            constraints = [Constraint(_ -> true, [x])]
        ) == 1
        # selective constraint: f(___, x_, ___) on f(a,aa,b,bb)
        @syms aa bb
        vx = Dict{BasicSymbolic{SymReal}, VarSpec.Type}(
            u1 => segmentspec(nothing; min = 0), u2 => segmentspec(nothing; min = 0)
        )
        res = collect(
            matchall(
                compile_pattern(h(segment(u1), slot(x), segment(u2)); vars = vx),
                h(a, aa, b, bb);
                constraints = [Constraint(v -> length(string(v[1])) > 1, [x])]
            )
        )
        @test length(res) == 2
        @test any(r -> isequal(r[x], aa), res)
        @test any(r -> isequal(r[x], bb), res)
    end

    @testset "syntactic net" begin
        # test_syntactic.py::test_generate_net_and_match — the
        # DiscriminationNet is a different algorithm, but the one-to-one
        # match/no-match semantics are comparable. f→h, f2→h2, f_u→hu.
        # Anonymous _/__/___ are each a distinct variable: _ → slot(w1),
        # __/___ → segment(w2)/segment(w3) (__ needs min=1 via vars, ___
        # is the default min=0); _s (Wildcard.symbol) → slot(sw) +
        # issym spec. Skipped: `(__, a)` — a bare segment at the
        # pattern root has no argument list to capture here.
        @syms w1 w2 w3 sw
        D = Dict{BasicSymbolic{SymReal}, VarSpec.Type}
        p1(v) = v => segmentspec(nothing; min = 1)
        iss = slotspec(SymbolicUtils.issym)
        cases = [
            # (subject, pattern, is_match[, vars])
            (a, a, true),
            (a, slot(w1), true),
            (h2(a), slot(w1), true),
            (h2(hu(a)), slot(w1), true),
            (h2(a, b), slot(w1), true),
            (h(a), h(slot(w1)), true),
            (h(h2(a)), h(slot(w1)), true),
            (h(h2(hu(a))), h(slot(w1)), true),
            (h(h2(a, b)), h(slot(w1)), true),
            (h(a), h(a, a), false),
            (h(a, a), h(a, a), true),
            (h(a, b), h(a, a), false),
            (h(b, a), h(a, a), false),
            (h(a), h(segment(w2), a), false, D(p1(w2))),
            (h(a, a), h(segment(w2), a), true, D(p1(w2))),
            (h(a, b, a), h(segment(w2), a), true, D(p1(w2))),
            (h(a, b, a, a), h(segment(w2), a, a), true, D(p1(w2))),
            (h(a, a, a), h(segment(w2), a, a), true, D(p1(w2))),
            (h(a), h(segment(w2), a, a), false, D(p1(w2))),
            (h(a, a), h(segment(w2), a, a), false, D(p1(w2))),
            (h(a), h(segment(w2), a), true),
            (h(a, a), h(segment(w2), a), true),
            (h(a, b, a), h(segment(w2), a), true),
            (h(a, b, a, a), h(segment(w2), a, a), true),
            (h(a, a, a), h(segment(w2), a, a), true),
            (h(a), h(segment(w2), a, a), false),
            (h(a, a), h(segment(w2), a, a), true),
            (h(a, b, a, a), h(segment(w2), a, b), false),
            (h(a, b, a, b), h(segment(w2), a, b), true),
            (h(a, a, b), h(segment(w2), a, b), true),
            (h(a, b, b), h(segment(w2), a, b), false),
            (h(a, b), h(segment(w2), a, b), true),
            (h(a, a), h(segment(w2), a, b), false),
            (h(b, b), h(segment(w2), a, b), false),
            (h(a), h(segment(w2), a, slot(w1)), false),
            (h(), h(segment(w2), a, slot(w1)), false),
            (h(b), h(segment(w2), a, slot(w1)), false),
            (h(a, a), h(segment(w2), a, slot(w1)), true),
            (h(a, b), h(segment(w2), a, slot(w1)), true),
            (h(b, a), h(segment(w2), a, slot(w1)), false),
            (h(a, a, a), h(segment(w2), a, slot(w1)), true),
            (h(a, b, a), h(segment(w2), a, slot(w1)), false),
            (h(b, a, a), h(segment(w2), a, slot(w1)), true),
            (h(a, a, b), h(segment(w2), a, slot(w1)), true),
            (h(a, b, a, b), h(segment(w2), a, slot(w1)), true),
            (h(a, a, a, b, a, b), h(segment(w2), a, slot(w1)), true),
            (h(a, b, a), h(segment(w2), a, segment(w3), a), true, D(p1(w3))),
            (h(a, a, a), h(segment(w2), a, segment(w3), a), true, D(p1(w3))),
            (h(a, b, a, b), h(segment(w2), a, segment(w3), a), false, D(p1(w3))),
            (h(b, b, a, a), h(segment(w2), a, segment(w3), a), false, D(p1(w3))),
            (h(b, a, a, a), h(segment(w2), a, segment(w3), a), true, D(p1(w3))),
            (h(a, b, b, a), h(segment(w2), a, segment(w3), a), true, D(p1(w3))),
            (h(h2(a)), h(segment(w2), h2(a)), true),
            (h(a, h2(a)), h(segment(w2), h2(a)), true),
            (h(h2(a), h2(a)), h(segment(w2), h2(a)), true),
            (h(h2(a), h2(b)), h(segment(w2), h2(a)), false),
            (h(h2(b), h2(a)), h(segment(w2), h2(a)), true),
            (h(h2(a), h2(b)), h(segment(w2), h2(slot(w1))), true),
            (h(h2(b), h2(a)), h(segment(w2), h2(slot(w1))), true),
            (h(h2(b), h2(hu(a))), h(segment(w2), h2(slot(w1))), true),
            (h(h2(b), h2(h2(a, b))), h(segment(w2), h2(slot(w1))), true),
            (h(h2(b), h2(hu(a), a)), h(segment(w2), h2(slot(w1))), false),
            (h(h2(a), h2(b)), h(segment(w2), h2(segment(w3))), true),
            (h(h2(b), h2(a, b)), h(segment(w2), h2(segment(w3))), true),
            (h(h2(a), h2(b)), h(segment(w2), h2(segment(w3), a)), false),
            (h(h2(b), h2(a, b)), h(segment(w2), h2(segment(w3), a)), false),
            (h(h2(b), h2(a, a)), h(segment(w2), h2(segment(w3), a)), true),
            (h(h2(a, b), h2(a, a)), h(segment(w2), h2(segment(w3), a)), true),
            (h(h2(b, b), h2(b, a)), h(segment(w2), h2(segment(w3), a)), true),
            (h(h2(b, a), b, h2(b, a)), h(segment(w2), h2(segment(w3), a), b), false),
            (h(h2(b, a), b, h2(b, a), b), h(segment(w2), h2(segment(w3), a), b), true),
            (h(h2(a)), h(segment(w2), h2(hu(a))), false),
            (h(h2(hu(b))), h(segment(w2), h2(hu(a))), false),
            (h(h2(hu(a), b)), h(segment(w2), h2(hu(a))), false),
            (h(h2(hu(a))), h(segment(w2), h2(hu(a))), true),
            (h(a, a, a, b), h(segment(w2), a, a, b, segment(w3)), true),
            (h(a, a, a, b), h(segment(w2), a, a, b), true),
            (h(a, a, a, b), h(segment(w2), a, b), true),
            (h(h2(b), h2(a), h2(a), h2(b)), h(segment(w2), h2(a), segment(w3), h2(b)), true),
            (h(h2(a), h2(a), h2(b), h2(b)), h(segment(w2), h2(a), segment(w3), h2(b)), true),
            (h(a, a), h(segment(w2), a, slot(sw)), true, D(sw => iss)),
            (h(a, a, a), h(segment(w2), a, slot(sw)), true, D(sw => iss)),
        ]
        for case in cases
            (subj, pat, want) = case[1:3]
            vars = length(case) > 3 ? case[4] : D()
            @test (mpc(pat, subj; vars) >= 1) == want
        end
    end
end
