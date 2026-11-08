"""
    MatchMaker

Symbolic pattern matching on top of SymbolicUtils.jl.

The governing design document is `DESIGN.md` (section references throughout
source comments point at it); `DEVELOPING.md` documents codebase navigation
and the implicit contracts between components. This module file only declares
dependencies and wires includes together; the file layout is DESIGN.md §6.
"""
module MatchMaker

using SymbolicUtils
using SymbolicUtils: BasicSymbolic, Sym, Term, Const, SymReal,
    issym, isconst, symtype, shape, BSImpl, ArgsT,
    hasmetadata, getmetadata, setmetadata, is_function_symbolic, SmallV,
    replace_node!, get_canonical_expr!, promote_symtype, FnType
using Moshi.Data: @data
import Moshi.Data as MData
using Moshi.Match: @match
using DocStringExtensions
using FunctionWrappers: FunctionWrapper
using Graphs
using ReadOnlyArrays
using EnumX: @enumx
using Preferences: @load_preference
import Base: match, materialize, eachmatch

include("patternvars.jl")
include("traits.jl")
include("compile.jl")
include("bindings.jl")
include("engine.jl")
include("matchers/primitives.jl")
include("matchers/seq.jl")
include("matchers/commutative.jl")
include("matchers/ac.jl")
include("instantiate.jl")
include("api.jl")

export slot, segment, optional,
    is_marker_term, is_marker_op,
    is_slot_marker, is_segment_marker, unwrap_varspec, varsym,
    VarSpec, slotspec, segmentspec,
    MarkersMap, materialize,
    is_associative, is_commutative, identity_element,
    OperationTraitsCtx, OperationTraits, set_operation_traits,
    Matcher, NodePlan, compile_pattern,
    Constraint, MatchEngine, MatchFrame, next_match!,
    SubstitutionView, MatchIterator, BoundMatchIterator, BoundMatch,
    matches, matchall, boundmatches, boundmatchall, eachmatch,
    instantiate,
    FrameStatus,
    @slots, @segments

end # module MatchMaker
