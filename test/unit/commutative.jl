# Comm frame (§5.5d): commutative-not-associative heads. C-only heads
# have no identity coercion — a non-g() subject can't match g(...) at
# all. Segments capture a sub-multiset of the remaining args; all args
# must be consumed.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

@syms x y z a b s t

let
    g = Sym{SymReal}(:g; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    g = set_operation_traits(g; commutative = true)
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    @testset "commutativity" begin
        # commuted arguments match in any order
        @test isequal(only(matchall(g(x, y), g(y, x))), MarkersMap())
        # no coercion: non-g() subject can't match g(...)
        @test isempty(matchall(g(x, y), x + y))
        @test isempty(matchall(g(x, y), x))
        # arity must fit exactly without segments
        @test isempty(matchall(g(x, y), g(x)))
        @test isempty(matchall(g(x), g(x, y)))
        # literal heads still checked
        @test isempty(matchall(g(x, y), h(x, y)))
        # slot takes whichever arg is left over
        @test isequal(only(matchall(g(slot(a), x), g(x, y))), MarkersMap(a => y))
        # both assignments enumerate
        @test isequal(
            collect(matchall(g(slot(a), slot(b)), g(y, x))),
            MarkersMap[MarkersMap(a => y, b => x), MarkersMap(a => x, b => y)]
        )
    end
    @testset "non-linear" begin
        # a slot bound elsewhere rechecks against remaining args
        @test isempty(matchall(g(slot(a), slot(a)), g(x, y)))
        # duplicate subject args give distinct assignments with equal binds
        @test length(matchall(g(slot(a), slot(a)), g(x, x))) == 2
    end
    @testset "segments (sub-multisets)" begin
        # a segment consumes whatever the fixed children don't
        @test isequal(
            only(matchall(g(x, segment(s)), g(x, y, z))),
            MarkersMap(s => g(y, z))
        )
        # empty capture materializes through the head
        @test isequal(
            only(matchall(g(x, segment(s)), g(x))), MarkersMap(s => g())
        )
        # a segment consumes whatever the fixed children don't
        @test isequal(
            only(matchall(g(x, segment(s)), g(x, y))),
            MarkersMap(s => g(y))
        )
        # two same-var segments need equal multisets left over
        @test length(matchall(g(segment(s), segment(s)), g(x, y, x, y))) == 4
        @test isempty(matchall(g(segment(s), segment(s)), g(x, y, x, z)))
        # grown selections aren't skipped: every sub-size fails the
        # sequence predicate, so the only viable capture needs growth
        m_len2 = compile_pattern(
            g(segment(s));
            vars = Dict(s => segmentspec(nothing, seq -> length(seq) == 2))
        )
        @test isequal(
            only(collect(matches(m_len2, g(x, y)))),
            MarkersMap(s => g(x, y))
        )
        # element-predicate failure is non-killing under a C head:
        # combinations containing the failing element are rejected, but
        # s can still take any sym-only sub-multiset while t absorbs
        # the rest (contrast the contiguous-run kill in segments.jl)
        m_pred = compile_pattern(
            g(segment(s), segment(t));
            vars = Dict(s => segmentspec(SymbolicUtils.issym))
        )
        @test isequal(
            collect(matches(m_pred, g(x, 1, y))),
            MarkersMap[
                MarkersMap(s => g(), t => g(x, 1, y)),
                MarkersMap(s => g(x), t => g(1, y)),
                MarkersMap(s => g(y), t => g(x, 1)),
                MarkersMap(s => g(x, y), t => g(1)),
            ]
        )
        # ...but the failing element still has to be consumed somewhere
        m_pred2 = compile_pattern(
            g(x, segment(s)); vars = Dict(s => segmentspec(SymbolicUtils.issym))
        )
        @test isempty(matches(m_pred2, g(x, 1, y)))
        # a bound-elsewhere position must free its `used` marks when the
        # seek passes it — regression: four distinct {x,y}-pairing
        # assignments collapsed to two by stale marks
        res = collect(matchall(g(segment(s), segment(s)), g(x, x, y, y)))
        @test length(res) == 4
        @test all(isequal(MarkersMap(s => g(x, y))), res)
        # a run bound under an ordered head is a multiset when
        # rechecked under an unordered head — pool order must not
        # matter
        vars = Dict(x => segmentspec(nothing; min = 1))
        res = collect(
            matchall(
                compile_pattern(h(h(segment(x)), g(segment(x))); vars),
                h(h(x, y), g(y, x))
            )
        )
        @test isequal(only(res), MarkersMap(x => h(x, y)))
        @test isempty(
            matchall(
                compile_pattern(h(h(segment(x)), g(segment(x))); vars),
                h(h(x, y), g(x, x))
            )
        )
    end
    @testset "nested frame failure" begin
        # a nested frame failing its head check must not clobber
        # already-bound vars — regression: _seq_args ran before the
        # frame's trail mark, so _call_fail! unwound the entire trail.
        # The ha(...) position's first candidate (h(y)) fails the head
        # check after slot(a) bound a ↦ x in the outer frame.
        ha = Sym{SymReal}(:ha; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
        ha = set_operation_traits(ha; associative = true)
        g2 = Sym{SymReal}(:g2; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
        @syms c
        @test isequal(
            only(matchall(
                g2(slot(a), g(ha(slot(b), segment(s)), slot(c))),
                g2(x, g(h(y), ha(y)))
            )),
            MarkersMap(a => x, b => y, c => h(y), s => ha())
        )
    end
end
