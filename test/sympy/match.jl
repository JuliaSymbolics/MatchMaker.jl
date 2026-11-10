# Ported SymPy `Basic.match` cases — source:
# github.com/sympy/sympy sympy/core/tests/test_match.py.
# SymPy's matcher is algebraic, not purely structural: it splits
# coefficients (`3x + p` vs `4x+5` → {p: x+5}), inserts implicit
# identities (`a*f(x) + b` vs `sin(x)` → {a: 0}), recognizes powers on
# rationals (`x/3` vs `y/w` → {w: 3}), and sometimes *solves*
# (`x**r` vs `y**2` → {y: x^(r/2)}). None of that is portable — this
# file covers the cases whose expected results coincide with
# structural AC matching.
#
# Translations:
#   - `Wild('p')` → `slot(p)`; a Wild that is a direct argument of an
#     `Add`/`Mul` absorbs the leftover args → `segment(p)` + min=1
#     (the same translation as MatchPy's dot under assoc/AC).
#   - `f(x)`/`Derivative`/`Sum`/noncommutative product/tuple →
#     declared free heads (`fn`, `der`, `sm`, `nc`, `tup`); `exp`/`log`/
#     `sin`/`cos` are used directly as function heads.
#   - `Wild(exclude=[...])` → `slotspec` predicate: the bound value may
#     not contain any excluded subexpression or operation.
#   - `x.match(p)` returns one substitution or None; we compare the
#     deduped `matchall` binding multiset (our engine may yield the
#     same substitution from distinct assignments).
#
# Skipped (needs the algebraic semantics above): coefficient splitting
# (`3*x + p`, `2*p` vs `6`, `p*x` vs `3x²`), implicit 0/1/identity
# bindings (`x` vs `p*x` → {p:1}, `x+1` vs `x+1+p` → {p:0},
# `a*f(x)**c` vs `x` → {c:0}), negative-power/rational coercions
# (`w/y` vs `x/3`, `6/x²` vs `a/x`), equation solving (`y**2` vs
# `x**r`, `p*x²+p*x+2p` vs `3x+3+6/x`), noncommutative-symbol Mul
# semantics, `find()`/`xreplace`/`_combine_inverse`, and bound-symbol
# wildcards (reverted upstream anyway).

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const, BasicSymbolic

const VS = Dict{BasicSymbolic{SymReal}, VarSpec.Type}

function _sn_norm(d)
    pairs = sort!(
        [
            string(k) => (v isa BasicSymbolic{SymReal} ? v : Const{SymReal}(v))
                for (k, v) in d
        ]; by = first
    )
    return join((string(k, " => ", repr(v)) for (k, v) in pairs), "; ")
end

# sm(pat, subj, expected): expected is a Dict or Vector{Pair} (one
# substitution), a Vector of those, or `nothing` for no match.
function sm(pat, subj, expected; vars = VS())
    got = unique(
        sort(
            _sn_norm.(
                collect(
                    matchall(
                        compile_pattern(pat; vars), subj
                    )
                )
            )
        )
    )
    maps = if expected === nothing
        Dict[]
    elseif expected isa AbstractVector{<:Pair} || expected isa AbstractDict
        [Dict(expected)]
    else
        [Dict(m) for m in expected]
    end
    want = sort(_sn_norm.(maps))
    return got == want
end

# every subexpression of v plus the operation of each call —
# SymPy's `exclude` rejects candidates containing them
function _subexprs(v)
    out = Any[v]
    if iscall(v)
        op = operation(v)
        op isa BasicSymbolic && push!(out, op)
        for a in arguments(v)
            append!(out, _subexprs(a))
        end
    end
    return out
end
_has(v, x) = x isa Function ?
    any(e -> iscall(e) && operation(e) === x, _subexprs(v)) :
    any(e -> isequal(e, x isa BasicSymbolic ? x : Const{SymReal}(x)), _subexprs(v))
excl(xs...) = slotspec(v -> !any(x -> _has(v, x), xs))

@syms a b c x y z im P Q R V W X Y

let
    fn = Sym{SymReal}(:fn; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    der = Sym{SymReal}(:der; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    sm_ = Sym{SymReal}(:sm; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    tup = Sym{SymReal}(:tup; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    nc = Sym{SymReal}(:nc; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    seg1(v) = v => segmentspec(nothing; min = 1)

    @testset "symbol" begin
        # test_symbol
        @test sm(x, x, Dict())
        @test sm(slot(P), x, [P => x])
        @test sm(slot(P), Const{SymReal}(5), [P => 5])
        @test sm(x + 1, Const{SymReal}(5), nothing)
    end

    @testset "add" begin
        # test_add — Wild leftovers under + are segments (min=1)
        vars = VS(seg1(P))
        @test sm(b + segment(P), a + b, [P => a]; vars)
        @test sm(a + segment(P), a + b, [P => b]; vars)
        @test sm(b + segment(P), 1 + b, [P => 1]; vars)
        @test sm(a + segment(P) + c, a + b + c, [P => b]; vars)
        @test sm(b + segment(P) + c, a + b + c, [P => a]; vars)
        @test sm(a + segment(P) + x + c, a + b + c + x, [P => b]; vars)
        @test sm(b + segment(P) + c + x, a + b + c + x, [P => a]; vars)
        @test sm(b, a + b + c + x, nothing)
        # Wild absorbing a multi-arg leftover sub-sum
        @test sm(b + segment(P), a + b + c + x, [P => a + c + x]; vars)
        @test sm(a + segment(P) + c, a + b + c + x, [P => b + x]; vars)
        @test sm(b + segment(P) + c, a + b + c + x, [P => a + x]; vars)
        # skipped: 3x + p vs 4x+5 → {p: x+5} (coefficient splitting)
        @test sm(slot(P) * x + 5, 4x + 5, [P => 4])
    end

    @testset "power" begin
        # test_power — `^` is a free head
        @test sm(slot(P)^slot(Q), (x + y)^a, Dict(P => x + y, Q => a))
        @test sm(slot(P)^slot(P), (x + y)^a, nothing)
        @test sm(slot(P)^slot(P), (x + y)^(x + y), [P => x + y])
        @test sm(slot(P)^slot(Q), (x + y)^(x + y), Dict(P => x + y, Q => x + y))
        # (2x)^2 canonicalizes to 4*x^2
        @test sm(slot(P) * slot(Q)^slot(R), (2x)^2, Dict(P => 4, Q => x, R => 2))
        # skipped: 1 vs x**p → {p: 0} (base**0 coercion)
    end

    @testset "mul" begin
        # test_mul/test_interface
        @test sm(slot(P) * x, 4x, [P => 4])
        @test sm(slot(P) * y, 4x, nothing)
        vars = VS(seg1(P))
        # Wild absorbing a multi-arg leftover sub-product
        @test sm(segment(P) * x, a * x * b * c, [P => a * b * c]; vars)
        @test sm(c * segment(P) * x, a * x * b * c, [P => a * b]; vars)
        # non-linear Wild across two nested Add args
        @test sm(
            (slot(P) + b) * (slot(P) + c), (a + b) * (a + c), [P => a]
        )
        # skipped: x vs p*x → {p: 1} (implicit coefficient);
        #          exp(x) vs x^p*exp(x*q) → {p: 0, q: 1}
        @test sm(slot(P) * slot(Q), x * y, [Dict(P => x, Q => y), Dict(P => y, Q => x)])
        @test sm(slot(P) + slot(Q), x + y, [Dict(P => x, Q => y), Dict(P => y, Q => x)])
        @test sm(slot(P) + 1, x + 1, [P => x])
        @test sm(slot(P) * 3, x * 3, [P => x])
        @test sm(slot(P)^3, x^3, [P => x])
        @test sm(slot(P) * cos(slot(Q)), x * cos(y), Dict(P => x, Q => y))
    end

    @testset "division" begin
        # test_match_exclude/test_issue_4559 — `/` is a 2-arg free head
        @test sm(3 / (slot(P) * x + slot(Q)), 3 / (4x + 5), Dict(P => 4, Q => 5))
        @test sm(slot(P) / (slot(Q) * x + slot(R)), 3 / (4x + 5), Dict(P => 3, Q => 4, R => 5))
        # skipped: 2/(x+1), 1/(x+1) vs p/(q*x+r) — {q: 1} coefficient
        @test sm(slot(V) / slot(W), 3 / x, Dict(V => 3, W => x))
        @test sm(slot(V) * slot(W), 3 * x, [Dict(V => 3, W => x), Dict(V => x, W => 3)])
        @test sm(slot(V) / slot(W), x / 3, Dict(V => x, W => 3))
        # skipped: 3x vs y/w → {w: 1/3} (rational-as-Pow)
    end

    @testset "complex" begin
        # test_complex — `im` stands in for I
        @test sm(slot(X) + im, 1 + im, [X => 1])
        @test sm(slot(X) + im, a + im, [X => a])
        @test sm(slot(X) * im, a * im, [X => a])
        @test sm(slot(X) * slot(Y), a * im, [Dict(X => a, Y => im), Dict(X => im, Y => a)])
        @test sm(slot(X) + slot(Y) * im, a + b * im, Dict(X => a, Y => b))
    end

    @testset "functions" begin
        # test_functions — WildFunction('g') binds only applied calls:
        # a slot with an iscall predicate
        g = slot(P)
        vars = VS(P => slotspec(iscall))
        @test sm(g, x, nothing; vars)
        @test sm(g, cos(5x), [P => cos(5x)]; vars)
        # skipped: p*g, p*g(q*x) (implicit coefficient 1); the g(q*x)
        # head-capture case is XFAIL upstream
    end

    @testset "derivative" begin
        # test_derivative1/test_derivative2 — `der` is a free head
        fx = fn(x)
        fd = der(fx, x)
        fdd = der(fx, x, x)
        @test sm(slot(P), fd, [P => fd])
        @test sm(slot(P) + 1, fd + 1, [P => fd])
        @test sm(fd, fd, Dict())
        @test sm(slot(P) * fd, 3 * fd, [P => 3])
        @test sm(slot(P) * fd + slot(Q), 3 * fd - 1, Dict(P => 3, Q => -1))
        @test sm(der(fx, x), fd, Dict())
        @test sm(der(fx, x, x), fd, nothing)
        @test sm(der(fx, x), fdd, nothing)
        @test sm(der(fx, x, x), fdd, Dict())
    end

    @testset "match bugs" begin
        # test_match_bug3 — leftover arg must be consumed
        @test sm(x * exp(slot(P) * x), b * x * exp(a * x), nothing)
        # test_issue_4883 — the one pairing that doesn't rely on
        # coefficient splitting (-P vs -2 can't match structurally)
        @test sm((slot(P) - x)^2, (2 - x)^2, [P => 2])
        # test_issue_3539 — no structural match
        @test sm(slot(P) - x, x - 2, nothing)
        @test sm(slot(P) * x, 6 / x, nothing)
        # test_match_issue_21942 — literal exponent shared, base binds
        ex = (1 - a)^-1
        @test sm(
            slot(P)^ex, (b * x^ex + y^ex * (1 - b))^ex,
            [P => b * x^ex + y^ex * (1 - b)]
        )
        @test sm(
            -slot(P)^ex, -(b * x^ex + y^ex * (1 - b))^ex,
            [P => b * x^ex + y^ex * (1 - b)]
        )
    end

    @testset "match terms" begin
        # test_match_terms — literal -1 factors inside Mul args
        @test sm(5 * slot(X) - slot(Y), 5y - x, Dict(X => y, Y => x))
        @test sm(x + slot(X) * z, x + (y - 1) * z, [X => y - 1])
        @test sm(
            x - log(slot(X) / y) * (1 - exp(x / y)),
            x - log(x / y) * (1 - exp(x / y)),
            [X => x]
        )
    end

    @testset "match bound" begin
        # test_match_bound — `sm`/`tup` free heads; V is non-linear
        # across a nested tuple arg
        @test sm(
            sm_(slot(V), tup(slot(V), 1, slot(W))),
            sm_(x, tup(x, 1, 2)), Dict(V => x, W => 2)
        )
        @test sm(
            sm_(slot(V), tup(slot(V), 1, 2)),
            sm_(x, tup(x, 1, 2)), Dict(V => x)
        )
        @test sm(sm_(y, tup(y, 1, slot(W))), sm_(x, tup(x, 1, 2)), nothing)
    end

    @testset "noncomm pow" begin
        # test_mul_noncommutative_pow — modeled with the free head `nc`;
        # Wild exponents match the base, not the exponent count
        @test sm(nc(slot(W)^2, b, slot(W)^3), nc(a^2, b, a^3), [W => a])
        @test sm(nc(slot(W)^2, b, slot(W)^4), nc(a^2, b, a^2), nothing)
        @test sm(nc(slot(W), b, slot(W)), nc(a, b, a), [W => a])
        @test sm(nc(slot(W), b, slot(W)), nc(a, b, c), nothing)
    end

    @testset "polynomial" begin
        # test_match_polynomial — coefficient-position slots
        pa = slot(P); qa = slot(Q); ra = slot(R)
        @test sm(
            pa * x^3 + qa * x^2 + ra * x + slot(V),
            4x^3 + 3x^2 + 2x + 1,
            Dict(P => 4, Q => 3, R => 2, V => 1)
        )
        # skipped: missing-term/zero-coefficient variants ({b: 0},
        # {c: 0}, {b: 1}) need implicit identity bindings
    end

    @testset "exclude" begin
        # test_exclude — Wild(exclude) → slotspec predicate over
        # subexpressions/operations
        p = slot(P); vars = VS(P => excl(1, x))
        @test sm(x + p, x + 1, nothing; vars)          # p ↦ 1 excluded
        @test sm(p + 1, x + 1, nothing; vars)          # p ↦ x excluded
        r = slot(R); rvars = VS(R => excl(sin, y))
        @test sm(r, cos(x) + 5 * sin(y), nothing; vars = rvars)  # contains sin/y
        @test sm(cos(y) + r, cos(x) + 5 * sin(y), nothing; vars = rvars)
        # r ↦ cos(x) contains neither sin nor y; p*sin(q) ↔ 5sin(y)
        vars2 = VS(P => excl(1, x), R => excl(sin, y))
        @test sm(
            r + p * sin(slot(Q)), cos(x) + 5 * sin(y),
            Dict(R => cos(x), P => 5, Q => y); vars = vars2
        )
        # skipped: Wild-vs-Wild cases (p.match(q+r)) — subjects are
        # concrete here, not patterns
    end
end
