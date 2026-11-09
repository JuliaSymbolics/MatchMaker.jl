using MatchMaker
using Aqua
using JET
using SciMLTesting
import SymbolicUtils

# `BasicSymbolic` is the package's domain type — methods on it (e.g.
# `match(::BasicSymbolic, ::BasicSymbolic)`) are treated as own, not piracy.
const OWN_DOMAIN_TYPES = [
    SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)",
]

# Moshi's `@data` expands to a submodule whose source ExplicitImports
# cannot walk — SciMLTesting already allows the equivalent EnumX
# `@enumx` modules automatically.
const GENERATED_ADT_MODULES = (MatchMaker.VarSpec, MatchMaker.NodePlan)

# Externally-owned names MatchMaker imports for which the owning package
# offers no public spelling: `FunctionWrapper` has none in FunctionWrappers,
# `SmallV` none in SymbolicUtils, `materialize`/`maketerm`/`metadata` none
# in Base/TermInterface.
const NONPUBLIC_EXPLICIT_IMPORTS = (
    :FunctionWrapper, :SmallV, :materialize, :maketerm, :metadata,
)

# Externally-owned names reached by qualified access for which the owning
# package offers no public spelling.
const NONPUBLIC_QUALIFIED_ACCESSES = (
    # SymbolicUtils
    :OrderedDiGraph,
    # Base
    :RefValue, :SizeUnknown, :materialize,
)

# Externally-owned bindings MatchMaker deliberately exposes as part of its
# public API: `materialize` and `eachmatch` are `Base` generics extended
# with matcher methods, `RhsT` is a `FunctionWrapper` type alias owned by
# MatchMaker.
const REEXPORTED_API = (:materialize, :eachmatch, :RhsT)

run_qa(
    MatchMaker;
    Aqua = Aqua,
    JET = JET,
    jet = true,
    aqua_kwargs = (; piracies = (; treat_as_own = OWN_DOMAIN_TYPES)),
    ei_kwargs = (;
        no_implicit_imports = (; allow_unanalyzable = GENERATED_ADT_MODULES),
        no_stale_explicit_imports = (;
            allow_unanalyzable = GENERATED_ADT_MODULES,
        ),
        all_explicit_imports_are_public = (; ignore = NONPUBLIC_EXPLICIT_IMPORTS),
        all_qualified_accesses_are_public = (; ignore = NONPUBLIC_QUALIFIED_ACCESSES),
    ),
    reexports_allow = REEXPORTED_API,
)
