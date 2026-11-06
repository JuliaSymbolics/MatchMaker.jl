# instantiate (§5.6): substitute slot/optional/head-marker vars and
# splice segment bindings into the parent's argument list.

using Test
using MatchMaker
using SymbolicUtils
using SymbolicUtils: Sym, SymReal, FnType

@syms x y z a b s t p q hd(x)

let
    h = Sym{SymReal}(:h; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    hd2 = Sym{SymReal}(:hd2; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f = Sym{SymReal}(:f; type = FnType{Tuple{Vararg{Number}}, Number, Nothing})
    f = set_operation_traits(
        f; associative = true, commutative = true, identity = :f0
    )

    @testset "splice correctness" begin
        # a multi-arg capture splices its args in place
        m = matchall(h(a, segment(s), b), h(a, x, y, b))[1]
        @test isequal(instantiate(h(a, segment(s), b), m), h(a, x, y, b))
        # a one-arg capture under the same head splices to the element
        m = matchall(f(x, segment(s)), f(x, y))[1]
        @test isequal(instantiate(f(z, segment(s)), m), f(z, y))
        # ...but under a different head it is one argument
        @test isequal(instantiate(h(z, segment(s)), m), h(z, f(y)))
        # identity element → zero args (empty capture, §4.6/§5.6)
        m = match(x + segment(s), x)
        @test isequal(instantiate(y + segment(s), m), y)
        m = match(x * segment(s), x)
        @test isequal(instantiate(z * segment(s), m), z)
        # a non-identity Const binding is a one-element literal
        # capture (canonical +(2) ≡ 2 / *(3) ≡ 3) — it must splice, not skip
        m = match(x + segment(s), x + 2)
        @test isequal(instantiate(x + segment(s), m), x + 2)
        m = match(x * segment(s), x * 3)
        @test isequal(instantiate(y * segment(s), m), 3y)
        # identity Const under a *different* head is just a value
        m = match(x + segment(s), x)
        @test isequal(instantiate(h(x, segment(s)), m), h(x, 0))
        # empty capture under a generic head is f() — splices to zero args
        m = matchall(f(x, segment(s)), f(x))[1]
        @test isequal(instantiate(f(x, segment(s)), m), f(x))
        # segment bound inside a nested term
        m = matchall(h(f(segment(s)), slot(a)), h(f(x, y), b))[1]
        @test isequal(instantiate(h(f(segment(s)), slot(a)), m), h(f(x, y), b))
    end
    @testset "head markers (§4.10)" begin
        # a slot bound to an operation materializes as the head
        m = match(slot(hd)(slot(a)), sin(y))
        @test isequal(instantiate(slot(hd)(x), m), sin(x))
        m = match(slot(hd2)(slot(a), slot(b)), p + q)
        @test isequal(instantiate(slot(hd2)(x, y), m), x + y)
    end
    @testset "end-to-end rewrite" begin
        # a + 0 → a
        m = match(slot(a) + 0, p + 0)
        @test isequal(instantiate(slot(a), m), p)
        # 1 * a → a
        m = match(1 * slot(a), 1 * q)
        @test isequal(instantiate(slot(a), m), q)
        # f(a, b) → f(b, a)
        m = match(h(slot(a), slot(b)), h(p, q))
        @test isequal(instantiate(h(slot(b), slot(a)), m), h(q, p))
        # u + rest → rest + u (rotate the head arg to the back)
        m = match(x + segment(s), x + p + q)
        @test isequal(instantiate(segment(s) + x, m), p + q + x)
    end
end
