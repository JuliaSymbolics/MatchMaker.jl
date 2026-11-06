# Generated fuzz (§7): random patterns and subjects, cross-validated
# against the naive oracle. Deterministic seed — a failure prints the
# seed so the case can be replayed and minimized.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType, Const
using Random: Xoshiro, seed!

include(joinpath(@__DIR__, "..", "oracle.jl"))

# Reuse the normalizer from crosscheck (copied to keep the fuzz file
# self-contained — the include graph here is one file deep).
function _fz_norm(d)
    pairs = sort!(
        [
            string(k) => (v isa BasicSymbolic{SymReal} ? v : Const{SymReal}(v))
            for (k, v) in d
        ]; by = first
    )
    return join((string(k, " => ", repr(v)) for (k, v) in pairs), "; ")
end

@syms x y z a b s t p q
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

    HEADS = (h, g, f, fa, (+), (*))
    ATOMS = (x, y, z, p, q, Const{SymReal}(1), Const{SymReal}(2))
    SLOTS = (a, b)
    SEGS = (s, t)

    function rand_subject(rng::Xoshiro, depth::Int)
        depth <= 0 && return rand(rng, ATOMS)
    rand(rng) < 0.25 && return rand(rng, ATOMS)
        op = rand(rng, HEADS)
        nargs = rand(rng, 0:3)
        args = BasicSymbolic{SymReal}[rand_subject(rng, depth - 1) for _ in 1:nargs]
        return op === (+) ? SymbolicUtils.add_worker(SymReal, args) :
            op === (*) ? SymbolicUtils.mul_worker(SymReal, args) :
            op(args...)
    end

    function rand_pattern(rng::Xoshiro, depth::Int, vars::Dict)
        r = rand(rng)
        if depth <= 0 || r < 0.3
            return rand(rng, ATOMS)
        elseif r < 0.55
            vs = rand(rng, SLOTS)
            vars[vs] = get!(vars, vs, VarSpec.Slot(nothing, nothing))
            return slot(vs)
        elseif r < 0.7
            vs = rand(rng, SEGS)
            vars[vs] = get!(vars, vs, VarSpec.Segment(nothing, nothing, 0, typemax(Int)))
            return segment(vs)
        elseif r < 0.8
            vs = rand(rng, SLOTS)
            vars[vs] = get!(vars, vs, VarSpec.Slot(nothing, Const{SymReal}(rand(rng, 3:9))))
            return optional(vs)
        else
            op = rand(rng, HEADS)
            nargs = rand(rng, 1:3)
            args = BasicSymbolic{SymReal}[rand_pattern(rng, depth - 1, vars) for _ in 1:nargs]
            return op === (+) ? +(args...) :
                op === (*) ? *(args...) : op(args...)
        end
    end

    # A pattern is valid iff every `optional` sits under an A/AC head —
    # the generator's other invariants (disjoint slot/segment var
    # pools, defaults on every optional) hold by construction.
    function pattern_valid(pat)
        iscall(pat) || return !_is_optional_term(pat)
        op = operation(pat)
        ST = SymReal
        ac_or_a = _is_associative_head(op, ST)
        for c in arguments(pat)
            if _is_optional_term(c) && !ac_or_a
                return false
            end
            iscall(c) && !is_marker_term(c) && !pattern_valid(c) && return false
        end
        return true
    end

    @testset "generated fuzz" begin
        N = 300
        fails = NamedTuple[]
        for seed in 1:N
            rng = Xoshiro(seed)
            vars = Dict{BasicSymbolic{SymReal}, VarSpec.Type}()
            pat = rand_pattern(rng, 3, vars)
            pattern_valid(pat) || continue
            subj = rand_subject(rng, 3)
            local eng, ora
            try
                eng = collect(matchall(compile_pattern(pat; vars), subj))
            catch err
                err isa ArgumentError && continue
                rethrow()
            end
            ora = oracle_matchall(pat, subj; vars)
            e = sort(_fz_norm.(eng))
            o = sort(_fz_norm.(ora))
            if e != o
                push!(fails, (seed = seed, pat = pat, subj = subj, e = e, o = o))
            end
        end
        for f in fails
            @info "mismatch" f.seed f.pat f.subj
            @info "engine" f.e
            @info "oracle" f.o
        end
        @test isempty(fails)
    end
end
