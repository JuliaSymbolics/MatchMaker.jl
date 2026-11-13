using MatchMaker, SymbolicUtils, Test

@testset "printing" begin
    @syms x a b s
    plain(x) = sprint(show, x)
    function colored(x)
        io = IOBuffer()
        show(IOContext(io, :color => true), x)
        return String(take!(io))
    end

    m = compile_pattern(sin(slot(a)) + segment(s))
    @test plain(m) == "Matcher(segment(s) + sin(slot(a)))"
    @test contains(colored(m), "\x1b[33msegment(s)\x1b[39m")
    @test contains(colored(m), "\x1b[33mslot(a)\x1b[39m")

    r = mmrule(slot(a) + slot(b) => a * b)
    @test plain(r) == "slot(a) + slot(b) => a*b"
    @test plain(mmrule(exp(slot(a)) => 0)) == "exp(slot(a)) => 0"
    @test plain(mmrule(slot(a) => (v -> v[a]))) == "slot(a) => <callable>"

    rs = compile_rules(CompiledRule[r, mmrule(exp(slot(a)) => 0)])
    @test plain(rs) == "RuleSet{BucketIndex}(2 rules)"
    @test sprint(show, MIME"text/plain"(), rs) ==
        "RuleSet{BucketIndex} with 2 rules:\n" *
        "  slot(a) + slot(b) => a*b\n" *
        "  exp(slot(a)) => 0"
    @test plain(RuleWorkspace(rs)) == "RuleWorkspace(2 rules)"

    @test plain(matches(m, sin(x) + x)) ==
        "matches(segment(s) + sin(slot(a)))"
    @test plain(boundmatches(m, sin(x) + x)) ==
        "boundmatches(segment(s) + sin(slot(a)))"
    @test plain(boundmatches_at(m, sin(x) + x)) ==
        "boundmatches_at(segment(s) + sin(slot(a)))"

    net = compile_rules(CompiledRule[r], DiscrimNet)
    @test plain(net) == "RuleSet{DiscrimNet}(1 rules)"
    @test contains(plain(net.index), "DiscrimNet(")
    @test contains(plain(net.index.states[1]), "NetState(")

    # compiled-plan internals stay terse
    @test contains(plain(m.plans[m.root]), "NodePlan.")
    @test contains(plain(first(m.var_specs)), "VarSpec.")

    eng = MatchMaker.matches(m, sin(x) + x).eng
    @test plain(eng) == "MatchEngine(segment(s) + sin(slot(a)) on sin(x) + x)"
end
