# R380: half-radius syndrome-line audit (2026-07-09)

## Question

At error count `e` with `2e<n` and `e+k+1<=n`, can a non-joint affine line in the
Reed--Solomon syndrome space meet the weight-`e` syndrome ball in at most `2e+1`
scalars?  At the predecessor of radius `1/2`, this would give at most `n-1` bad
scalars and close the good side of the tight-budget prize-shaped examples.

## Exhaustive result

`scripts/probes/probe_r380_half_radius_syndrome_lines.py` exhausts affine lines in
small Vandermonde syndrome spaces, quotiented by translation along the direction.
It found a counterexample for `[n,k,e,p]=[6,2,2,7]`:

```text
base      = (0,1,0,0)
direction = (0,0,1,0)
bad gamma = 1,2,3,4,5,6
```

No two-coordinate syndrome subspace contains the whole line, but six scalars lie in
the weight-two ball.  Hence `6>2e+1=5`.  The six decompositions are certified in
`_R380HalfRadiusTwoEPlusOneRefuted.lean` without `sorry`.

## Exact mechanism

For Vandermonde column `v(x)=(1,x,x^2,x^3)`, solve

```text
a v(x) + b v(y) = (0,1,gamma,0).
```

The first two coordinates give `b=-a` and `a=(x-y)^-1`.  The last two become

```text
x+y = gamma,
x^2+xy+y^2 = 0.
```

Thus `x/y` is a nontrivial cube root of unity.  In `F_7^*`, which has order six,
this gives a representation for every nonzero `gamma`; explicitly the locations are
the scalar multiples of one fixed cubic-resonant pair.

## Consequences

1. The field-uniform `2e+1` conjecture is refuted.
2. The example reaches exactly `n` bad scalars, so it does not refute the weaker
   `#bad<=n` bound needed at budget `floor(p/2^128)=n`.
3. More importantly, its mechanism requires `3 | n`.  The prize evaluation group has
   order `2^30` and contains no nontrivial cube root of unity.  A corrected conjecture
   should exploit the dyadic subgroup, not merely the MDS property.  The axiom-clean
   theorem `R381DyadicCubicResonanceExcluded.no_dyadic_cubic_resonance` formally proves
   that `u^(2^mu)=1` and `u^2+u+1=0` are incompatible in characteristic other than `3`.
4. The ordinary secant-variety degree argument cannot prove the desired bound in the
   production range: for `D=n-k` and `e=n/2-1`, the `e`-secant variety of the rational
   normal curve fills the ambient projective syndrome space whenever `2e>=D`.
   Any useful bound must retain the finite evaluation set and its multiplicative
   torsion restrictions.

## Next conjecture

For a multiplicative evaluation subgroup `H` of two-power order, `e<n/2`, and
`e+k+1<=n`, every non-joint syndrome line has at most `n` points in the weight-`e`
syndrome ball.  The first proof target is to classify equality: the R380 construction
suggests that an `n`-point line should force odd torsion in `H`, which would sharpen
the prize case to `n-1`.
