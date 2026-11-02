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

@safetestset "JET smoke" begin
    include("jet.jl")
end
