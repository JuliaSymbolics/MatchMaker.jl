using Test
using MatchMaker
using MatchMaker: MatchEngine, Constraint, next_match!
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

@testset "segments under free heads" begin
    @syms x y z
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f2 = Sym{SymReal}(:f2; type = FnType{Tuple{Number, Number}, Number, Nothing})
    @syms a b s t

    # single segment: must capture the whole remaining run
    @test isequal(
        only(matchall(h(slot(a), segment(s)), h(x, y, z))),
        MarkersMap(a => x, s => h(y, z))
    )
    @test isequal(
        only(matchall(h(segment(s), slot(a)), h(x, y, z))),
        MarkersMap(a => z, s => h(x, y))
    )

    # empty capture when nothing is left
    @test isequal(
        only(matchall(h(x, segment(s)), h(x))),
        MarkersMap(s => h())
    )

    # no whole match when the subject has the wrong head or too few args
    @test isempty(matchall(h(x, segment(s)), g(x, y)))
    @test isempty(matchall(h(x, y, segment(s)), h(x)))

    # split enumeration: increasing captured length, left segment first
    # (DESIGN.md §4.8) — every subject arg must be consumed (§4.1)
    ms = matchall(h(segment(s), segment(t)), h(x, y, z))
    @test length(ms) == 4
    @test isequal(ms[1], MarkersMap(s => h(), t => h(x, y, z)))
    @test isequal(ms[2], MarkersMap(s => h(x), t => h(y, z)))
    @test isequal(ms[3], MarkersMap(s => h(x, y), t => h(z)))
    @test isequal(ms[4], MarkersMap(s => h(x, y, z), t => h()))

    # non-linear segment: recheck must equal the earlier capture
    @test isequal(
        only(matchall(h(segment(s), g(segment(s))), h(x, y, g(x, y)))),
        MarkersMap(s => h(x, y))
    )
    @test isempty(matchall(h(segment(s), g(segment(s))), h(x, y, g(y, x))))
    @test isequal(
        only(matchall(h(segment(s), segment(s)), h(x, y, x, y))),
        MarkersMap(s => h(x, y))
    )
    @test isequal(
        only(matchall(h(segment(s), segment(s)), h(x, x))),
        MarkersMap(s => h(x))
    )

    # min / max bounds
    m_min = compile_pattern(
        h(x, segment(s)); vars = Dict(s => segmentspec(nothing, nothing; min = 2))
    )
    @test isempty(collect(matches(m_min, h(x, y))))
    @test isequal(
        only(collect(matches(m_min, h(x, y, z)))),
        MarkersMap(s => h(y, z))
    )
    m_max = compile_pattern(
        h(x, segment(s)); vars = Dict(s => segmentspec(nothing, nothing; max = 1))
    )
    @test isempty(collect(matches(m_max, h(x, y, z))))

    # element predicate / sequence predicate
    m_pred = compile_pattern(
        h(segment(s)); vars = Dict(s => segmentspec(SymbolicUtils.issym))
    )
    @test isequal(
        only(collect(matches(m_pred, h(x, y)))),
        MarkersMap(s => h(x, y))
    )
    m_seqpred = compile_pattern(
        h(segment(s));
        vars = Dict(s => segmentspec(nothing, seq -> length(seq) == 2))
    )
    @test isempty(collect(matches(m_seqpred, h(x, y, z))))

    # instantiate splices the captured run (§5.6)
    @test isequal(
        instantiate(
            h(segment(s), y),
            matchall(h(segment(s), y), h(x, z, y))[1]
        ),
        h(x, z, y)
    )

    # fixed-domain head: segment min > domain arity is a compile error
    @test_throws ArgumentError compile_pattern(
        f2(segment(s), y);
        vars = Dict(s => segmentspec(nothing, nothing; min = 3))
    )
end
