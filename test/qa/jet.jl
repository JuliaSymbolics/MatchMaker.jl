using JET
using MatchMaker
using MatchMaker: RuleSet
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic
using Test

# Smoke test: JET reports filtered to MatchMaker frames only — inference
# noise inside SymbolicUtils is SymbolicUtils' business, not ours. Hot-path
# checks on the engine land in `perf/hardening` (DESIGN.md §12).
@syms x

const _BS = BasicSymbolic{SymReal}
d = MarkersMap(x => x)

_rw = mmrule(slot(x) + slot(x) => slot(x) * slot(x))
_rw_ws = RuleWorkspace(RuleSet(CompiledRule[_rw]))

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
            (Base.getindex, Tuple{MarkersMap, _BS}),
            (Base.haskey, Tuple{MarkersMap, _BS}),
            (set_operation_traits, Tuple{_BS}),
            (compile_pattern, Tuple{_BS}),
            (match, Tuple{_BS, _BS}),
            (matchall, Tuple{_BS, _BS}),
            (matches, Tuple{Matcher, _BS}),
            (boundmatches_at, Tuple{Matcher, _BS}),
            (matches_at, Tuple{Matcher, _BS}),
            (MatchMaker._next_hit_site!, Tuple{MatchEngine, Int32}),
            (Base.iterate, Tuple{BoundMatchAtIterator}),
            (instantiate, Tuple{_BS, MarkersMap}),
            (MatchMaker._seg_value, Tuple{MatchMaker.MatchEngine, Int32}),
            # rules.jl — rule objects, index, workspace, rewrite pass
            (mmrule, Tuple{Pair{_BS, _BS}}),
            (MatchMaker._compile_rhs, Tuple{_BS, Matcher}),
            (MatchMaker._rhs_eval, Tuple{RhsPlan, MatchEngine}),
            (MatchMaker._apply_rhs, Tuple{CompiledRule, MatchEngine}),
            (RuleSet, Tuple{Vector{CompiledRule}}),
            (
                RuleSet,
                Tuple{Vector{CompiledRule}, Type{DiscrimNet}},
            ),
            (MatchMaker._build_index, Tuple{Vector{CompiledRule}}),
            (
                MatchMaker._make_index,
                Tuple{Type{BucketIndex}, Vector{CompiledRule}},
            ),
            (
                MatchMaker._make_index,
                Tuple{Type{DiscrimNet}, Vector{CompiledRule}},
            ),
            # DiscrimNet construction + evaluation internals
            (MatchMaker.NetState, Tuple{}),
            (DiscrimNet, Tuple{}),
            (MatchMaker.NetOp, Tuple{Any, Int}),
            (isequal, Tuple{MatchMaker.NetOp, MatchMaker.NetOp}),
            (hash, Tuple{MatchMaker.NetOp, UInt}),
            (MatchMaker.NetDefer, Tuple{Any, Int, Int, Int32}),
            (MatchMaker._build_net, Tuple{Vector{CompiledRule}}),
            (
                MatchMaker._net_insert!,
                Tuple{DiscrimNet, Matcher, Int32, Int32},
            ),
            (
                MatchMaker._net_next!,
                Tuple{
                    DiscrimNet, Dict{MatchMaker.NetOp, Int32},
                    MatchMaker.NetOp,
                },
            ),
            (MatchMaker._net_new!, Tuple{DiscrimNet}),
            (
                MatchMaker._net_defer!,
                Tuple{
                    DiscrimNet, Int32, Matcher,
                    MatchMaker.NodePlanT, Function, Int32,
                },
            ),
            (
                MatchMaker._net_descend!,
                Tuple{
                    MatchMaker.SmallV{Int32}, DiscrimNet,
                    RuleWorkspace, Int32,
                    SymbolicUtils.AdjView{Int32}, Int,
                },
            ),
            (
                MatchMaker.lookup!,
                Tuple{
                    BucketIndex, MatchMaker.SmallV{Int32},
                    RuleWorkspace, _BS, Int32,
                },
            ),
            (
                MatchMaker.lookup!,
                Tuple{
                    DiscrimNet, MatchMaker.SmallV{Int32},
                    RuleWorkspace, _BS, Int32,
                },
            ),
            (
                MatchMaker._net_go,
                Tuple{DiscrimNet, RuleWorkspace, Int32, Int32},
            ),
            (RuleWorkspace, Tuple{MatchMaker.RuleSet{BucketIndex}}),
            (_rw_ws, Tuple{_BS}),
            (
                MatchMaker._apply_site!,
                Tuple{RuleWorkspace, _BS, Int32},
            ),
            (rewrite, Tuple{RuleWorkspace, _BS}),
            (fixpoint_rewrite, Tuple{RuleWorkspace, _BS}),
        )
        reports = JET.get_reports(JET.report_call(f, tt; target_modules = (MatchMaker,)))
        @test isempty(reports)
    end
end
