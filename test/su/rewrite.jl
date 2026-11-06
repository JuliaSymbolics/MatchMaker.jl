# Ported SymbolicUtils @rule match cases — source: SymbolicUtils.jl
# test/rewrite.jl. SU's ~x / ~~x / ~!x map to slot / segment /
# optional; ~!x defaults to the *head identity* (0 under +, 1 under
# *), so `vars` supplies `default` explicitly. ~x::pred maps to
# slotspec predicates — including on the default (see the defslots
# predicate testset).
#
# Expected bindings differ in shape: SU returns ~~x as a vector of
# captures, we materialize the head applied to the capture
# (a+b not [a,b]; 0/1 for empty). `sm` compares the deduped
# matchall multiset — SU's first-match may pick any of them.
#
# Skipped (not matcher semantics): rule/Rewriters plumbing (@acrule
# application sites, where/conditional rules, timing/budget tests);
# "frankenstein"/opposite-sign Div-to-Pow negative-exponent matching
# (1/a^b is a^(-b) there — our / is a real head); exp/sqrt special-
# function pow views; ~! under ^ (base**1 coercion — optional is
# A/AC-only here); non-canonical `term` subjects holding raw numbers
# (our subjects are BasicSymbolic).

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const, BasicSymbolic, term

const VS = Dict{BasicSymbolic{SymReal}, VarSpec.Type}

function _su_norm(d)
    pairs = sort!(
        [
            string(k) => (v isa BasicSymbolic{SymReal} ? v : Const{SymReal}(v))
            for (k, v) in d
        ]; by = first
    )
    return join((string(k, " => ", repr(v)) for (k, v) in pairs), "; ")
end

function sm(pat, subj, expected; vars = VS())
    got = unique(sort(_su_norm.(collect(matchall(
        compile_pattern(pat; vars), subj
    )))))
    maps = if expected === nothing
        Dict[]
    elseif expected isa AbstractVector{<:Pair} || expected isa AbstractDict
        [Dict(expected)]
    else
        [Dict(m) for m in expected]
    end
    want = sort(_su_norm.(maps))
    return got == want
end

@syms a b c d x y z
@syms wx wy wz wm wa wb wc wf

let
    F = Sym{SymReal}(:F; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    G = Sym{SymReal}(:G; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})

    @testset "literal and slot" begin
        @test sm(Const{SymReal}(1), Const{SymReal}(1), Dict())
        @test sm(Const{SymReal}(1), Const{SymReal}(2), nothing)
        @test sm(slot(wx), Const{SymReal}(2), [wx => 2])
        @test sm(slot(wx), a, [wx => a])
    end

    @testset "term" begin
        @test sm(sin(slot(wx)), sin(a), [wx => a])
        @test sm(sin(slot(wx)), sin(a^2), [wx => a^2])
        @test sm(sin(slot(wx)), sin(a)^2, nothing)
        @test sm(sin(sin(slot(wx))), sin(a^2), nothing)
        @test sm(sin(sin(slot(wx))), sin(sin(a)), [wx => a])
        @test sm(sin(slot(wx))^2, sin(a)^2, [wx => a])
    end

    @testset "equality / non-linear" begin
        @test sm(slot(wx)^slot(wx), a^a, [wx => a])
        @test sm(slot(wx)^slot(wx), b^a, nothing)
        @test sm(slot(wx)^slot(wx), a + a, nothing)
        @test sm(slot(wx)^slot(wx), sin(a)^sin(a), [wx => sin(a)])
        # shared factor across both products — x must bind consistently
        # either product may supply x — two consistent maps each
        @test sm(slot(wx) * slot(wy) + slot(wz) * slot(wx), a * b + a * c,
            [Dict(wx => a, wy => b, wz => c), Dict(wx => a, wy => c, wz => b)])
        @test sm(slot(wx) * slot(wy) + slot(wx) * slot(wz), a * b + b * c,
            [Dict(wx => b, wy => a, wz => c), Dict(wx => b, wy => c, wz => a)])
        @test sm(slot(wy) * slot(wx) + slot(wz) * slot(wx), a * c + b * c,
            [Dict(wx => c, wy => a, wz => b), Dict(wx => c, wy => b, wz => a)])
    end

    @testset "segments" begin
        # +(~~x): term() keeps the one-arg Add head (+(seg) folds to the
        # bare marker, which is illegal at the pattern root)
        @test sm(term(+, segment(wx)), a + b, [wx => a + b])
        @test sm(term(+, segment(wx)), term(+, a, b, c), [wx => a + b + c])
        # non-linear segment under AC: second ~~x rechecks the bound
        # multiset (subjects are non-canonical `term` calls to keep
        # duplicate args distinct)
        @test sm(term(+, segment(wx), slot(wy), segment(wx)),
            term(+, a, b, a), Dict(wx => a, wy => b))
        @test sm(term(+, segment(wx), slot(wy), segment(wx)),
            term(+, a, b, a, a, b), Dict(wx => a + b, wy => a))
        # empty capture under + materializes the identity
        @test sm(term(+, segment(wx), slot(wy), segment(wx)),
            term(+, a), Dict(wx => 0, wy => a))
        # AC backtrack preserves nested segment order: ~~y's ordered run
        # is rechecked order-sensitively at the other head. Which
        # occurrence binds first depends on canonical arg order — the
        # materialization head is dispatch-order trivia (TODO), so the
        # same run [a,b] may arrive as F(a,b) or G(a,b)
        let got = unique(sort(_su_norm.(collect(matchall(
                compile_pattern(F(segment(wy)) * F(segment(wz)) + G(segment(wy))),
                F(a, b) * F(b, a) + G(a, b)))))),
            want = sort([
                _su_norm(Dict(wy => F(a, b), wz => F(b, a))),
                _su_norm(Dict(wy => G(a, b), wz => F(b, a))),
            ])
            @test length(got) == 1 && got[1] in want
        end
    end

    @testset "commutative + and *" begin
        @test sm(
            exp(sin(slot(wx)) + cos(slot(wx))),
            exp(sin(a) + cos(a)),
            [wx => a]
        )
        # two unordered slot pairs — all four assignments
        @test sm(
            (slot(wx) + slot(wy)) * (slot(wz) + slot(wa))^slot(wm),
            (a + b) * (x + c)^b,
            [
                Dict(wx => a, wy => b, wz => x, wa => c, wm => b),
                Dict(wx => a, wy => b, wz => c, wa => x, wm => b),
                Dict(wx => b, wy => a, wz => x, wa => c, wm => b),
                Dict(wx => b, wy => a, wz => c, wa => x, wm => b),
            ]
        )
        vars = VS(wx => slotspec(SymbolicUtils.isconst))
        @test sm(slot(wx) + slot(wy), 2 + x, Dict(wx => 2, wy => x); vars)
        @test sm(slot(wy) + slot(wx), 2 + x, Dict(wx => 2, wy => x); vars)
        @test sm(
            slot(wy) * (slot(wz) + slot(wa)) + slot(wx),
            c * (a + b) + d,
            [
                Dict(wx => d, wy => c, wz => a, wa => b),
                Dict(wx => d, wy => c, wz => b, wa => a),
            ]
        )
        @test sm(
            slot(wx) + (slot(wz) + slot(wa)) * slot(wy),
            d + c * (a + b),
            [
                Dict(wx => d, wy => c, wz => a, wa => b),
                Dict(wx => d, wy => c, wz => b, wa => a),
            ]
        )
    end

    @testset "defslots" begin
        # (~x + ~!y)^2 — ~!y defaults to the + identity
        vars = VS(wy => slotspec(default = 0))
        @test sm((slot(wx) + optional(wy))^2, b^2, Dict(wx => b, wy => 0); vars)
        @test sm((slot(wx) + optional(wy))^2, (a + b)^2,
            [Dict(wx => a, wy => b), Dict(wx => b, wy => a)]; vars)
        # ~x * ~!y — ~!y defaults to the * identity
        vars1 = VS(wy => slotspec(default = 1))
        @test sm(slot(wx) * optional(wy), a * b,
            [Dict(wx => a, wy => b), Dict(wx => b, wy => a)]; vars = vars1)
        @test sm(slot(wx) * optional(wy), a, Dict(wx => a, wy => 1); vars = vars1)
        # ~x*~!y + ~z vs c + a*b: y ∈ {1, a, b}
        @test sm(slot(wx) * optional(wy) + slot(wz), c + a * b,
            [
                Dict(wx => c, wy => 1, wz => a * b),
                Dict(wx => a, wy => b, wz => c),
                Dict(wx => b, wy => a, wz => c),
            ]; vars = vars1)
        @test sm(slot(wx) * optional(wy) + slot(wz), c + b,
            [
                Dict(wx => c, wy => 1, wz => b),
                Dict(wx => b, wy => 1, wz => c),
            ]; vars = vars1)
        # (~!x)*(~y + ~z) — optional factor vs a bare Add
        varsx = VS(wx => slotspec(default = 1))
        @test sm(optional(wx) * (slot(wy) + slot(wz)), a * (c + 2),
            [
                Dict(wx => a, wy => c, wz => 2),
                Dict(wx => a, wy => 2, wz => c),
            ]; vars = varsx)
        @test sm(optional(wx) * (slot(wy) + slot(wz)), 2 * (c + 2),
            [
                Dict(wx => 2, wy => c, wz => 2),
                Dict(wx => 2, wy => 2, wz => c),
            ]; vars = varsx)
        @test sm(optional(wx) * (slot(wy) + slot(wz)), c + 2,
            [
                Dict(wx => 1, wy => c, wz => 2),
                Dict(wx => 1, wy => 2, wz => c),
            ]; vars = varsx)
        # (~!a)*exp(~x)*sin(~x) — non-linear x across free heads under *
        varsa = VS(wa => slotspec(default = 1))
        @test sm(optional(wa) * exp(slot(wx)) * sin(slot(wx)),
            sin(x) * exp(x), Dict(wa => 1, wx => x); vars = varsa)
        @test sm(optional(wa) * exp(slot(wx)) * sin(slot(wx)),
            sin(x) * exp(x) * a, Dict(wa => a, wx => x); vars = varsa)
        # (~!a)*exp(~x)*sin(~!b + ~x^2 + ~x)
        varsab = VS(wa => slotspec(default = 1), wb => slotspec(default = 0))
        @test sm(
            optional(wa) * exp(slot(wx)) * sin(optional(wb) + slot(wx)^2 + slot(wx)),
            exp(x) * sin(1 + x + x^2) * 2,
            Dict(wa => 2, wb => 1, wx => x); vars = varsab)
        @test sm(
            optional(wa) * exp(slot(wx)) * sin(optional(wb) + slot(wx)^2 + slot(wx)),
            exp(x) * sin(x + x^2) * 2,
            Dict(wa => 2, wb => 0, wx => x); vars = varsab)
        @test sm(
            optional(wa) * exp(slot(wx)) * sin(optional(wb) + slot(wx)^2 + slot(wx)),
            exp(x) * sin(x + x^2),
            Dict(wa => 1, wb => 0, wx => x); vars = varsab)
        # predicate in the consume path
        varsp1 = VS(wm => slotspec(v -> SymbolicUtils.isconst(v) && v.val isa Int; default = 0))
        @test sm(x + optional(wm), x + 2, Dict(wm => 2); vars = varsp1)
        @test sm(x + optional(wm), x + 2.1, nothing; vars = varsp1)
        # predicate checked against the default too
        varsp2 = VS(wm => slotspec(v -> !(SymbolicUtils.isconst(v) && v.val === 0); default = 0))
        @test sm(x + optional(wm), x + 1, Dict(wm => 1); vars = varsp2)
        @test sm(x + optional(wm), x, nothing; vars = varsp2)
        # non-linear optional: ~!f binds in sin and rechecks in cos
        varsf = VS(wf => slotspec(default = 1))
        # both factor assignments are consistent — SU's first-match
        # returns wf => 2
        @test sm(
            sin(optional(wf) * slot(wx)) + cos(optional(wf) * slot(wx)),
            sin(2x) + cos(2x),
            [Dict(wf => 2, wx => x), Dict(wf => x, wx => 2)]; vars = varsf)
        @test sm(
            sin(optional(wf) * slot(wx)) + cos(optional(wf) * slot(wx)),
            sin(2x) + cos(x), nothing; vars = varsf)
    end
end
