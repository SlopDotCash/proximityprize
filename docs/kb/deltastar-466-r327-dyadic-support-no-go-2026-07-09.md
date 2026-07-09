# R327: Dyadic support separation is not the half-CS saving

## Question

Could the open `MixedMainResHalfCS(1/2)` estimate follow just from the
2-adic separation between the coarse character subfamily and its complement?
Squaring a valuation shell sends its Fourier support into a coarser subgroup,
so there is a tempting Littlewood--Paley-style triangularity.

## Exact countermodel

On `Z/4Z`, take

```
A = (1,-1,1,-1),   B = (1,1,-1,-1).
```

`A` is the real frequency-two character.  `B` is real, mean zero, and has only
odd Fourier frequencies.  Thus their Fourier supports are disjoint in exactly
the coarse/odd pattern.  But pointwise

```
A^2 = B^2 = (1,1,1,1).
```

Consequently

```
sum A^2 B^2 = 4,
sum A^4 = sum B^4 = 4,
```

and the mixed Cauchy--Schwarz ratio is `1`, not `1/2`.

The identities and strict failure of half-CS are formalized axiom-clean in
`_R327DyadicSupportNoGo.lean`.

## Consequence

Reality, zero mean, disjoint coarse/fine Fourier support, and the nesting of
shell self-sumsets are insufficient.  The empirical half-CS saving seen in
the actual child cosets must use arithmetic restrictions on the Fourier
coefficients, in particular the coupled Gauss/Jacobi phases.  The next viable
target is therefore a fourth-order Jacobi correlation identity or inequality,
not an abstract dyadic square-function theorem.
