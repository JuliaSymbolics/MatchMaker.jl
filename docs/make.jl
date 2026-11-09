using Documenter
using MatchMaker
using SymbolicUtils

DocMeta.setdocmeta!(MatchMaker, :DocTestSetup, :(using MatchMaker); recursive = true)

makedocs(
    sitename = "MatchMaker.jl",
    modules = [MatchMaker],
    remotes = nothing,
    pages = [
        "Home" => "index.md",
        "Tutorial" => "tutorial.md",
        "User guide" => "guide.md",
        "API reference" => [
            "Patterns" => "api/patterns.md",
            "Traits" => "api/traits.md",
            "Matching" => "api/matching.md",
            "Results" => "api/results.md",
            "Engine" => "api/engine.md",
            "Rewriting" => "api/rewriting.md",
            "Internals" => "api/internals.md",
        ],
        "Design notes" => "optional-segments.md",
    ],
    checkdocs = :none,
)
