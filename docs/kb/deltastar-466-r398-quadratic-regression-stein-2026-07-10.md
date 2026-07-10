# Issue #466 R398: quadratic-regression Stein interface

R348 proves the exact period-square recursion

```text
X_b^2 = n + sum_{v in H, v != 1} X_{b(v-1)}.
```

After grouping nonzero frequencies into multiplicative cosets and normalizing the multiplicities,
this defines a Markov kernel `K` with

```text
(n-1) KX = X^2-n.
```

The step multiset is reversible: replacing `v` by `v^{-1}` changes `v-1` by multiplication by a
member of `H` and by `-1`, which is also in the dyadic subgroup. Thus the induced coset walk is
symmetric.

`_R398QuadraticRegressionSteinIdentity.lean` proves abstractly that every symmetric stochastic
kernel with this regression satisfies

```text
sum_i (n-X_i)(X_i+1) f(X_i)
  = (n-1)/2 sum_{i,j} K(i,j)(X_i-X_j)(f(X_i)-f(X_j)).
```

This is an exact exchangeable-pairs/Stein identity. For increasing exponential test functions the
left side is a restoring drift and the right side is a jump-energy form. A prize-strength use would
need a saddle-tilted jump-energy estimate at scale `O(n)`.

## Quantitative verdict: the hoped-for jump bound is refuted

Let

```text
D(b) = average_v (X_{b(v-1)}-X_b)^2
```

and tilt cosets by `exp(theta X_b)` at `theta=sqrt(2 log(m)/n)`. Exact-subgroup/FFT probes at the
quartic diagonal give

```text
 n     p near n^4       E_theta[D]/n
16       65537              0.984
32     1048609              2.274
64    16777601              4.818
```

The normalized constant approximately doubles when `n` doubles: the tilted jump energy trends as
`Theta(n^2)`, not `O(n)`. The unconditional mean remains `E[D]/n=2`, but exponential tilting exposes
the high-energy states that matter for the maximum. Consequently the direct Stein-MGF closure
reproduces the quartic-scale wall rather than the prize scale. R398 survives as an exact structural
identity; the proposed uniform jump-energy bypass is retired.
