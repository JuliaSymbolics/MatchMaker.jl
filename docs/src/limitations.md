# Limitations and common pitfalls

MatchMaker matches **structurally**, over the canonicalized symbolic DAG
that SymbolicUtils produces. Most surprises come from the fact that the
tree you write is not always the tree that gets matched — SymbolicUtils
may fold, reorder, or reshape a term before the matcher ever sees it.
This page collects the cases users most often trip over.

## Canonicalization happens before matching

Both pattern and subject pass through SymbolicUtils construction first,
so they are canonicalized identically. Consequences:

- `x + y` may print and store as `+(y, x)` — argument order inside `+`
  and `*` is canonical, not written order.
- `x + x` is `2x` — an `*(2, x)` term, not a `+` term. A pattern like
  `slot(a) + slot(a)` (nonlinear `a`) matches it via the `*` coercion
  path, but `slot(a) + slot(b)` treats it as a two-argument product.
- `exp(0)`, `sin(0)`, `x * 1` etc. **evaluate to Julia values** when all
  arguments are concrete numbers — see the next section.

## Folded literals never reach the matcher

`exp(0)` written in Julia is an ordinary `Base.exp(::Int)` call — it
returns `1` before SymbolicUtils is involved. There is no `exp(0)` term
left to match, so `mmrule(exp(0) => 1)` cannot observe it
([#7](https://github.com/JuliaSymbolics/MatchMaker.jl/issues/7)).

The workaround is a slot with a value-checking predicate — the predicate
receives the bound term, and plain Julia values are compared with
`isequal`:

```julia
@syms x u
zero_lit = mmrule(exp(slot(u)) => 0;
                  vars = Dict(u => slotspec(t -> isequal(t, Const{SymReal}(0)))))
ws = RuleWorkspace(compile_rules(CompiledRule[zero_lit]))
ws(exp(Const{SymReal}(0)))   # Const{SymReal}(0) — the symbolic exp(0) term
ws(exp(x))                   # nothing — predicate rejected the binding
```

Two details make this work:

- the subject `exp(0)` must be *built symbolically* — `exp(Const{SymReal}(0))` —
  so it survives as an `exp` call term;
- `mmrule(lhs => 0)` treats a non-symbolic, non-callable RHS as a literal —
  it is wrapped in `Const` rather than called.

## `-x` and `-x*y` have different shapes

`-slot(v)` matches `cos(-a)` but not `cos(-a*b)`
([#8](https://github.com/JuliaSymbolics/MatchMaker.jl/issues/8)). Unary
minus on a symbol is a `*(-1, a)` term; `-a*b` canonicalizes to the flat
product `*(-1, a, b)` — there is no unary `-` node wrapping a product.
A pattern `-slot(v)` therefore only sees subjects whose shape is a
negation of a single factor.

If you want "a product containing a `-1` factor", match the flat form
with a segment:

```julia
@syms a b v s
m = compile_pattern(cos(-1 * slot(v) * segment(s)))
matchall(m, cos(-a))      # v => a, s => 1  (empty product = identity)
matchall(m, cos(-a * b))  # v => a, s => b  and  v => b, s => a
```

Note that the segment binds the multiplicative identity `1` when it
captures zero arguments.

## Untyped vs. typed variables

`slot(x)` is untyped (`symtype` `Number`-agnostic); `slot(x; type = Real)`
or a `Sym{Real}` variable is typed. Type filtering happens at binding
time, but it also affects the reconstructed result: instantiated RHS
terms derive their `symtype` from the *bound* argument, so an untyped
slot still produces terms equal to subjects built from typed symbols —
this is what makes `cos(-α) - cos(α)` cancel under `fixpoint_rewrite`
([#6](https://github.com/JuliaSymbolics/MatchMaker.jl/issues/6)). If you
nevertheless see structurally-identical terms failing `isequal`, check
`symtype` on both sides — a term rebuilt with a different declared type
is a different term.

## `optional` under non-associative heads

Optional slots are supported under associative and
associative-commutative heads (`+`, `*`, and user operations via
[`set_operation_traits`](@ref)). Under free (plain `Call`) and
commutative-only heads they are rejected at compile time — see the
[design notes](optional-segments.md) for the rationale.

## Matching is structural, not semantic

`0 * x`, `x - x`, `sin(x)^2 + cos(x)^2` — the matcher sees the terms as
written, not their mathematical value. Rules are the mechanism for
simplification; matching itself does no algebraic reasoning. If you need
value equality, put it in a `slotspec` predicate or a
[`Constraint`](@ref) rather than in the tree shape.
