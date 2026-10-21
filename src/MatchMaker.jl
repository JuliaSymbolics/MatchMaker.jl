"""
    MatchMaker

MatchPy-style symbolic pattern matching on top of SymbolicUtils.jl.

The governing design document is `DESIGN.md` (section references throughout
source comments point at it); `DEVELOPING.md` documents codebase navigation
and the implicit contracts between components. This module file only declares
dependencies and wires includes together; the file layout is DESIGN.md §6.
"""
module MatchMaker

using SymbolicUtils
# @public SymbolicUtils names used across the package (not bare-`using`
# exported): the variant type, term constructors, and node predicates.
using SymbolicUtils: BasicSymbolic, Sym, Term, Const, SymReal,
                    issym, isconst, symtype, shape
using Moshi.Data: @data
import Moshi.Data as MData
using Moshi.Match: @match
using DocStringExtensions
using FunctionWrappers: FunctionWrapper
using Graphs
using ReadOnlyArrays

include("patternvars.jl")
include("traits.jl")
include("compile.jl")
include("bindings.jl")
include("engine.jl")
include("matchers/primitives.jl")
include("matchers/seq.jl")
include("matchers/commutative.jl")
include("matchers/associative.jl")
include("matchers/ac.jl")
include("instantiate.jl")
include("api.jl")

end # module MatchMaker
