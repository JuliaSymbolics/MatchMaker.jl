using SafeTestsets

@safetestset "QA (Aqua)" begin
    include("qa.jl")
end

@safetestset "pattern variables" begin
    include("unit/patternvars.jl")
end

@safetestset "operation traits" begin
    include("unit/traits.jl")
end

@safetestset "pattern compiler" begin
    include("unit/compile.jl")
end

@safetestset "match engine" begin
    include("unit/engine.jl")
end

@safetestset "segments" begin
    include("unit/segments.jl")
end

@safetestset "commutative" begin
    include("unit/commutative.jl")
end

@safetestset "associative" begin
    include("unit/associative.jl")
end

@safetestset "AC" begin
    include("unit/ac.jl")
end

@safetestset "instantiate" begin
    include("unit/instantiate.jl")
end

@safetestset "constraints" begin
    include("unit/constraints.jl")
end

@safetestset "MatchPy port" begin
    include("matchpy/one_to_one.jl")
end

@safetestset "SymPy port" begin
    include("sympy/match.jl")
end

@safetestset "SymbolicUtils port" begin
    include("su/rewrite.jl")
end

@safetestset "Metatheory port" begin
    include("metatheory/reductions.jl")
end

@safetestset "oracle cross-check" begin
    include("fuzz/crosscheck.jl")
end

@safetestset "generated fuzz" begin
    include("fuzz/generator.jl")
end

@safetestset "lazy results" begin
    include("unit/lazy.jl")
end

@safetestset "JET smoke" begin
    include("jet.jl")
end
