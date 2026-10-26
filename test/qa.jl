using Aqua
using MatchMaker
import SymbolicUtils
using SymbolicUtils: BasicSymbolic
using Test

# `BasicSymbolic` is the package's domain type — methods on it (e.g.
# `match(::BasicSymbolic, ::BasicSymbolic)`) are treated as own, not piracy.
Aqua.test_all(
    MatchMaker;
    piracies = (;
        treat_as_own = [
            SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)",
        ],
    )
)
