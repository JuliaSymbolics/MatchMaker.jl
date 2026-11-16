# Port of SymbolicUtils.TRIG_REDUCE_RULES (80 rules) to MatchMaker, rule for rule, in the same order. The
# right-hand-side helpers (_trig_power_reduce, _half_pi_shift_sign, predicates, ...) are SymbolicUtils' own.
#  * `@acrule(f(~x)*g(~y) => ..)` leaves unmatched factors alone in SymbolicUtils. Here an explicit `segment(r)`
#    collects the leftover factors and the right-hand side multiplies them back.
#  * `~~a + ~y + ~~b` (two segments) becomes `segment(a) + slot(y)`: `+` is AC, so one segment captures the rest.
module TrigReduceRules

using MatchMaker, SymbolicUtils
using SymbolicUtils: SymReal, BasicSymbolic, Const

export trig_reduce_rules

const SU = SymbolicUtils
const VT = MatchMaker.VarSpecT

@syms x y n a r s     # pattern variables; the markers are built with slot/segment
const sx, sy, sn = slot(x), slot(y), slot(n)
const sr = segment(r)

C(v) = Const{SymReal}(v)
mkvars(pairs...) = Dict{BasicSymbolic{SymReal}, VT}(pairs...)
spec(f) = slotspec(e -> f(SU.unwrap_const(e)))        # SU predicates take raw values
rest_seg() = segmentspec(nothing; min = 1)

function trig_reduce_rules()
    R = CompiledRule[]

    # ── Cleanup ─────────────────────────────────────────────────────────
    for (f, val) in ((sin, 0), (cos, 1), (tan, 0), (sinh, 0), (cosh, 1), (tanh, 0))
        push!(R, mmrule(f(C(0)) => C(val)))
    end
    parity = (
        (cos, :even), (sin, :odd), (tan, :odd), (cot, :odd), (sec, :even), (csc, :odd),
        (cosh, :even), (sinh, :odd), (tanh, :odd), (coth, :odd), (sech, :even), (csch, :odd),
    )
    for (f, p) in parity
        rhs = p === :even ? (v -> f(-1 * v[x])) : (v -> -1 * f(-1 * v[x]))
        push!(R, mmrule(f(sx) => rhs; vars = mkvars(x => spec(SU._has_neg_leading))))
    end

    # ── Period reduction ────────────────────────────────────────────────
    ev, od = SU._is_nonzero_even_multiple_of_pi, SU._is_odd_multiple_of_pi
    per = vars -> mkvars(y => spec(vars), a => rest_seg())
    pat(f) = f(segment(a) + sy)
    # (f, odd_multiple_rhs_sign, even_multiple_present?) in SU declaration order
    push!(R, mmrule(pat(sin) => (v -> sin(v[a])); vars = per(ev)))
    push!(R, mmrule(pat(sin) => (v -> -sin(v[a])); vars = per(od)))
    push!(R, mmrule(pat(cos) => (v -> cos(v[a])); vars = per(ev)))
    push!(R, mmrule(pat(cos) => (v -> -cos(v[a])); vars = per(od)))
    push!(R, mmrule(pat(tan) => (v -> tan(v[a])); vars = per(od)))
    push!(R, mmrule(pat(tan) => (v -> tan(v[a])); vars = per(ev)))
    push!(R, mmrule(pat(cot) => (v -> cot(v[a])); vars = per(od)))
    push!(R, mmrule(pat(cot) => (v -> cot(v[a])); vars = per(ev)))
    push!(R, mmrule(pat(sec) => (v -> -sec(v[a])); vars = per(od)))
    push!(R, mmrule(pat(sec) => (v -> sec(v[a])); vars = per(ev)))
    push!(R, mmrule(pat(csc) => (v -> -csc(v[a])); vars = per(od)))
    push!(R, mmrule(pat(csc) => (v -> csc(v[a])); vars = per(ev)))

    # ── Quarter-period (odd multiples of π/2) ───────────────────────────
    hp = per(SU._is_odd_half_pi)
    sg(v) = SU._half_pi_shift_sign(SU.unwrap_const(v[y]))
    push!(R, mmrule(pat(sin) => (v -> sg(v) * cos(v[a])); vars = hp))
    push!(R, mmrule(pat(cos) => (v -> -sg(v) * sin(v[a])); vars = hp))
    push!(R, mmrule(pat(tan) => (v -> -cot(v[a])); vars = hp))
    push!(R, mmrule(pat(cot) => (v -> -tan(v[a])); vars = hp))
    push!(R, mmrule(pat(sec) => (v -> -sg(v) * csc(v[a])); vars = hp))
    push!(R, mmrule(pat(csc) => (v -> sg(v) * sec(v[a])); vars = hp))

    # ── Power reduction f(x)^n, n ≥ 2 ───────────────────────────────────
    nv = mkvars(n => spec(SU._isinteger_ge2))
    power(f) = v -> SU._trig_power_reduce(f, v[x], SU.unwrap_const(v[n]))
    inv_power(f) = v -> 1 / SU._trig_power_reduce(f, v[x], SU.unwrap_const(v[n]))
    for (f, rhs) in (
            (cos, power(cos)), (sin, power(sin)), (tan, power(tan)), (cot, power(cot)),
            (sec, inv_power(cos)), (csc, inv_power(sin)),
            (cosh, power(cosh)), (sinh, power(sinh)), (tanh, power(tanh)), (coth, power(coth)),
            (sech, inv_power(cosh)), (csch, inv_power(sinh)),
        )
        push!(R, mmrule(f(sx)^sn => rhs; vars = nv))
    end

    # ── Same-argument cancellations (leftover factors kept via sr) ──────
    cancel(l, rr, rhs) = push!(R, mmrule(l(sx) * rr(sx) * sr => (v -> rhs(v[x]) * v[r])))
    cancel(tan, cos, x_ -> sin(x_))
    cancel(cot, sin, x_ -> cos(x_))
    cancel(sec, cos, x_ -> C(1))
    cancel(csc, sin, x_ -> C(1))
    cancel(tan, cot, x_ -> C(1))
    cancel(sec, sin, x_ -> tan(x_))
    cancel(csc, cos, x_ -> cot(x_))
    cancel(tan, csc, x_ -> sec(x_))
    cancel(cot, sec, x_ -> csc(x_))

    # ── Dual conversion ─────────────────────────────────────────────────
    dual(l, rr, rhs) = push!(R, mmrule(l(sx) * rr(sy) * sr => (v -> rhs(v[x], v[y]) * v[r])))
    dual(tan, sec, (p, q) -> sin(p) / (cos(p) * cos(q)))
    dual(tan, csc, (p, q) -> sin(p) / (cos(p) * sin(q)))
    dual(cot, sec, (p, q) -> cos(p) / (sin(p) * cos(q)))
    dual(cot, csc, (p, q) -> cos(p) / (sin(p) * sin(q)))
    dual(sec, csc, (p, q) -> 1 / (cos(p) * sin(q)))
    dual(sec, sec, (p, q) -> 1 / (cos(p) * cos(q)))
    dual(csc, csc, (p, q) -> 1 / (sin(p) * sin(q)))

    # ── Product-to-sum ──────────────────────────────────────────────────
    dual(cos, cos, (p, q) -> (cos(p - q) + cos(p + q)) / 2)
    dual(sin, sin, (p, q) -> (cos(p - q) - cos(p + q)) / 2)
    dual(sin, cos, (p, q) -> (sin(p + q) + sin(p - q)) / 2)
    dual(cosh, cosh, (p, q) -> (cosh(p - q) + cosh(p + q)) / 2)
    dual(sinh, sinh, (p, q) -> (cosh(p + q) - cosh(p - q)) / 2)
    dual(sinh, cosh, (p, q) -> (sinh(p + q) + sinh(p - q)) / 2)

    # ── Exponential ─────────────────────────────────────────────────────
    push!(
        R, mmrule(
            exp(sx) * exp(sy) * sr =>
                (v -> (SU._iszero(v[x] + v[y]) ? C(1) : exp(v[x] + v[y])) * v[r])
        )
    )
    push!(R, mmrule(exp(sx)^sy => (v -> exp(v[x] * v[y]))))

    # ── Conditional fallback: only when the other factors contain a trig fn ──
    fb = mkvars(s => rest_seg())
    function fallback(f, rhs)
        return push!(
            R, mmrule(
                f(sx) * segment(s) =>
                    (v -> SU._any_trig(v[s]) ? rhs(v[x]) * v[s] : nothing); vars = fb
            )
        )
    end
    fallback(tan, p -> sin(p) / cos(p))
    fallback(cot, p -> cos(p) / sin(p))
    fallback(sec, p -> 1 / cos(p))
    fallback(csc, p -> 1 / sin(p))
    fallback(tanh, p -> sinh(p) / cosh(p))
    fallback(coth, p -> cosh(p) / sinh(p))
    fallback(sech, p -> 1 / cosh(p))
    fallback(csch, p -> 1 / sinh(p))
    return R
end

end # module
