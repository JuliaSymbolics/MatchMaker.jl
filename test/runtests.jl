using SafeTestsets

@safetestset "QA (Aqua)" begin
    include("qa.jl")
end

@safetestset "JET smoke" begin
    include("jet.jl")
end
