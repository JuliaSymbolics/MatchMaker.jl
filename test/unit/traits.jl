using MatchMaker
using MatchMaker: _is_ac_head, _is_associative_head, _is_commutative_head,
    _is_number_st, _identity_el
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, BasicSymbolic, FnType
using Test

@syms x

@testset "public traits — defaults" begin
    @test is_associative(+, Number) && is_commutative(+, Number)
    @test is_associative(*, Int) && is_commutative(*, Float64)
    @test identity_element(+, Number) === 0
    @test identity_element(*, Real) === 1

    @test !is_associative(-, Number) && !is_commutative(-, Number)
    @test !is_associative(sin, Real) && !is_commutative(sin, Real)
    @test identity_element(-, Number) === nothing

    # `*` on matrices is not commutative — no numeric default applies
    @test !is_associative(*, Matrix{Float64})
    @test !is_commutative(*, Matrix{Float64})
    @test !is_associative(+, String)
end

@testset "OperationTraitsCtx metadata channel" begin
    g = Sym{SymReal}(:g; type = FnType{Tuple{Number}, Number, Nothing})
    @test !is_commutative(g, Number)          # no metadata → all false
    @test !is_associative(g, Number)
    @test identity_element(g, Number) === nothing

    g2 = set_operation_traits(g; commutative = true)
    @test is_commutative(g2, Number)
    @test !is_associative(g2, Number)
    @test identity_element(g2, Number) === nothing

    g3 = set_operation_traits(
        g; associative = true, commutative = true,
        identity = 0
    )
    @test is_associative(g3, Number) && is_commutative(g3, Number)
    @test identity_element(g3, Number) === 0

    @test_throws ArgumentError set_operation_traits(sin(x))
    @test_throws ArgumentError set_operation_traits(x + 1)
end

@testset "fast-path wrappers" begin
    @test _is_ac_head(+, Number)
    @test _is_ac_head(*, Real)
    @test _is_ac_head(*, Int64)
    @test !_is_ac_head(*, Matrix{Float64})     # matrix mult → not AC
    @test !_is_ac_head(-, Number)
    @test !_is_ac_head(sin, Number)

    @test _is_number_st(Number) && _is_number_st(Real) && _is_number_st(Int)
    @test _is_number_st(Float64) && _is_number_st(Rational{Int})
    @test !_is_number_st(Matrix{Float64}) && !_is_number_st(String)

    # metadata heads flow through the same wrappers
    g3 = set_operation_traits(
        Sym{SymReal}(:h; type = FnType{Tuple{Number}, Number, Nothing});
        associative = true, commutative = true, identity = 0
    )
    @test _is_ac_head(g3, Number)
    @test _is_associative_head(g3, Number) && _is_commutative_head(g3, Number)
    @test _identity_el(g3, Number) === 0

    @test _identity_el(+, Number) === 0
    @test _identity_el(*, Int) === 1
    @test _identity_el(-, Number) === nothing
end
