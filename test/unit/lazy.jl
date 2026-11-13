using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, BasicSymbolic

@testset "lazy BoundMatch results" begin
    @syms x y z a b s t v p q r

    subj = p + q + r + x + y
    pat = compile_pattern(segment(s) + segment(v))

    eager = matchall(pat, subj)
    lazy = boundmatchall(pat, subj)
    @test lazy isa Vector{BoundMatch}
    @test eager isa Vector{MarkersMap}
    @test collect(boundmatches_at(compile_pattern(sin(slot(a))), sin(sin(x)))) isa
        Vector{Tuple{BoundMatch, BasicSymbolic{SymReal}}}
    @test collect(matches_at(compile_pattern(sin(slot(a))), sin(sin(x)))) isa
        Vector{Tuple{MarkersMap, BasicSymbolic{SymReal}}}
    @test length(lazy) == length(eager)

    # values agree with eager results, elementwise and as a multiset
    mats = [materialize(m) for m in lazy]
    @test Set(mats) == Set(eager)

    # dict interface on the frozen snapshot
    m1 = lazy[1]
    @test m1[s] isa SymbolicUtils.BasicSymbolic
    @test haskey(m1, s) && haskey(m1, segment(s)) && haskey(m1, slot(v))
    @test !haskey(m1, x)
    @test length(m1) == 2
    @test_throws KeyError m1[x]
    @test Set(k for k in keys(m1)) == Set([s, v])

    # empty segment under + materializes to the identity — one of the
    # two partitions has the empty capture on either side
    empty_cap = boundmatchall(pat, p)
    @test length(empty_cap) == 2
    @test any(m -> isequal(m[v], SymbolicUtils.Const{SymReal}(0)), empty_cap)
    @test any(m -> isequal(m[s], SymbolicUtils.Const{SymReal}(0)), empty_cap)

    # snapshots persist across later matching (no engine aliasing)
    s_before = m1[s]
    v_before = m1[v]
    boundmatchall(compile_pattern(segment(s) + segment(v)), a + b)
    @test isequal(m1[s], s_before) && isequal(m1[v], v_before)
    @test isequal(materialize(m1), mats[1])

    # boundmatches() yields BoundMatch snapshots
    its = collect(boundmatches(pat, p + q))
    @test all(m -> m isa BoundMatch, its) && length(its) == 4

    # free-head segments: empty capture reconstructs h()
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    hl = boundmatchall(compile_pattern(h(segment(s), segment(v))), h(p, q))
    @test length(hl) == 3
    @test isequal(hl[1][s], h())

    # match()/matchall stay eager MarkersMap
    @test match(pat, p + q) isa MarkersMap
end
