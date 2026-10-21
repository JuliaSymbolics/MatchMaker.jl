using JET
using MatchMaker
using Test

# Smoke test only. Real JET checks of the hot paths
# (`compile_pattern`, `next_match!`, `instantiate`) land with
# `perf/hardening` (DESIGN.md §12).
JET.test_package(MatchMaker)
