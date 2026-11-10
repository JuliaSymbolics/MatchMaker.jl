# Ported Metatheory.jl classical-matcher cases — source:
# Metatheory.jl test/classic/reductions.jl ("Pattern variable segment",
# "Multiple PatSegments", "Multiple Repeated PatSegments"). Metatheory
# works on Julia Exprs with :f heads and Int literals; here `f`/`g`/`h`
# are declared free heads and literals are Const args. `~x` → `slot`,
# `~~x` → `segment`. A bound segment materializes as the head applied
# to the capture (f(1,2); f() for empty), where Metatheory returns the
# raw view — the substitution sets are equivalent.
#
# Metatheory's matcher enumerates segment splits longest-first and a
# @rule returns the first match; `sm` compares the full matchall set,
# which is the same multiset either way.
#
# Skipped: e-graph side tests (ematch/segment_ematch — equational
# matching through saturation is a different paradigm), the e-matcher's
# ≤1-segment restriction, Expr-specific heads (`-a - b`, `@capture`).

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const, BasicSymbolic

const VS = Dict{BasicSymbolic{SymReal}, VarSpec.Type}

function _mt_norm(d)
    pairs = sort!(
        [
            string(k) => (v isa BasicSymbolic{SymReal} ? v : Const{SymReal}(v))
                for (k, v) in d
        ]; by = first
    )
    return join((string(k, " => ", repr(v)) for (k, v) in pairs), "; ")
end

function sm(pat, subj, expected; vars = VS())
    got = unique(
        sort(
            _mt_norm.(
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
    want = sort(_mt_norm.(maps))
    return got == want
end

@syms wx wy wz

let
    f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})

    @testset "segment as tail" begin
        @test sm(
            f(slot(wx), segment(wy)), f(1, 2, 3, 4),
            Dict(wx => 1, wy => f(2, 3, 4))
        )
        @test sm(
            f(slot(wx), 2, segment(wy)), f(1, 2, 3, 4),
            Dict(wx => 1, wy => f(3, 4))
        )
        @test sm(
            f(slot(wx), 2, segment(wy)), f(1, 2, 3),
            Dict(wx => 1, wy => f(3))
        )
        # empty tail capture
        @test sm(
            f(slot(wx), 2, 3, 4, segment(wy)), f(1, 2, 3, 4),
            Dict(wx => 1, wy => f())
        )
        # the whole arg list
        @test sm(f(segment(wx)), f(1, 2, 3, 4), [wx => f(1, 2, 3, 4)])
        # nested inside another call
        @test sm(
            g(1, f(slot(wx), 2, segment(wy)), 3),
            g(1, f(1, 2, 3, 4), 3),
            Dict(wx => 1, wy => f(3, 4))
        )
        @test sm(
            g(1, f(slot(wx), 2, segment(wy)), 3),
            g(1, f(1, 2, 3), 3),
            Dict(wx => 1, wy => f(3))
        )
        @test sm(
            g(1, f(slot(wx), 2, segment(wy)), 3),
            g(1, f(1, 2, 3, h(4, 5), 6), 3),
            Dict(wx => 1, wy => f(3, h(4, 5), 6))
        )
    end

    @testset "segment as head" begin
        @test sm(
            f(segment(wx), slot(wy)), f(1, 2, 3, 4),
            Dict(wx => f(1, 2, 3), wy => 4)
        )
        @test sm(f(segment(wx), 3, 4), f(1, 2, 3, 4), [wx => f(1, 2)])
        @test sm(
            f(slot(wx), 2, 3, segment(wy)), f(1, 2, 3, 4),
            Dict(wx => 1, wy => f(4))
        )
    end

    @testset "multiple segments" begin
        # every split of the arg list
        @test sm(
            f(segment(wx), segment(wy)), f(1, 2, 3, 4),
            [
                Dict(wx => f(), wy => f(1, 2, 3, 4)),
                Dict(wx => f(1), wy => f(2, 3, 4)),
                Dict(wx => f(1, 2), wy => f(3, 4)),
                Dict(wx => f(1, 2, 3), wy => f(4)),
                Dict(wx => f(1, 2, 3, 4), wy => f()),
            ]
        )
        @test sm(
            f(segment(wx), 3, segment(wy)), f(1, 2, 3, 4, 5),
            Dict(wx => f(1, 2), wy => f(4, 5))
        )
        @test sm(
            f(segment(wx), 3, segment(wy), 5, segment(wz)),
            f(1, 2, 3, 4, 5, 6),
            Dict(wx => f(1, 2), wy => f(4), wz => f(6))
        )
        @test sm(
            f(segment(wx), 3, segment(wy), 5, segment(wz), 7),
            f(1, 2, 2, 3, 4, 4, 5, 6, 7, 7),
            Dict(wx => f(1, 2, 2), wy => f(4, 4), wz => f(6, 7))
        )
    end

    @testset "repeated segments" begin
        # non-linear ~~x: the second capture must repeat the first run
        @test sm(
            f(segment(wx), segment(wx), 4), f(1, 2, 1, 2, 4),
            [wx => f(1, 2)]
        )
        @test sm(f(segment(wx), segment(wx), 4), f(1, 2, 3, 4), nothing)
        @test sm(f(segment(wx), segment(wx), 4), f(4), [wx => f()])
        @test sm(f(segment(wx), segment(wx)), f(1, 2, 1, 2), [wx => f(1, 2)])
        @test sm(f(segment(wx), segment(wx)), f(1, 2, 3, 4), nothing)
        @test sm(
            f(segment(wx), 3, segment(wx)), f(1, 2, 3, 1, 2),
            [wx => f(1, 2)]
        )
        @test sm(f(segment(wx), 3, segment(wx)), f(3), [wx => f()])
        @test sm(f(segment(wx), 3, segment(wx)), f(1, 2, 3, 4, 5), nothing)
        # three occurrences of the same segment var
        @test sm(
            f(segment(wx), 3, segment(wx), 5, segment(wx)),
            f(1, 2, 3, 1, 2, 5, 1, 2), [wx => f(1, 2)]
        )
        @test sm(
            f(segment(wx), 3, segment(wx), 5, segment(wx)),
            f(1, 2, 3, 3, 1, 2, 5, 1, 2), nothing
        )
        # interleaved non-linear segments — z must backtrack from
        # [6] to [6,7] so the y recheck can succeed
        @test sm(
            f(
                segment(wx), 3, segment(wy), 5, segment(wx), segment(wz),
                7, segment(wy)
            ),
            f(1, 2, 2, 3, 4, 4, 5, 1, 2, 2, 6, 7, 7, 4, 4),
            Dict(wx => f(1, 2, 2), wy => f(4, 4), wz => f(6, 7))
        )
    end
end
