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

@safetestset "JET smoke" begin
    include("jet.jl")
end
