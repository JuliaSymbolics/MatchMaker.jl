using JET
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic
using Test

# Smoke test: JET reports filtered to MatchMaker frames only — inference
# noise inside SymbolicUtils is SymbolicUtils' business, not ours. Hot-path
# checks on the engine land in `perf/hardening` (DESIGN.md §12).
@syms x

const _BS = BasicSymbolic{SymReal}
d = Substitution(x => x)

@testset "JET" begin
    for (f, tt) in (
            (slot, Tuple{_BS}),
            (segment, Tuple{_BS}),
            (optional, Tuple{_BS}),
            (slot, Tuple{Symbol}),
            (is_marker_term, Tuple{_BS}),
            (unwrap_varspec, Tuple{_BS}),
            (varsym, Tuple{_BS}),
            (slotspec, Tuple{}),
            (segmentspec, Tuple{}),
            (Base.getindex, Tuple{Substitution, _BS}),
            (Base.haskey, Tuple{Substitution, _BS}),
        )
        reports = JET.get_reports(JET.report_call(f, tt; target_modules = (MatchMaker,)))
        @test isempty(reports)
    end
end
