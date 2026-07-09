# R289: constrained sextic average is the cubic subconvexity target

Date: 2026-07-09.

## Claim

The R37/R38 sextic exact-sum route should not be consumed through the current
all-lag uniform `SexticCorrelationBound` interface.  The exact triple
convolution energy lives on a four-dimensional constraint surface inside the
five-dimensional lag box.

For

```text
E3 = sum_d |sum_{x+y+z=d, x,y,z != 0} J_x J_y J_z|^2,
```

expand the square and set

```text
x' = j,     y' = j + a',     z' = j + b',
x  = j + t, y  = j + t + a, z  = j + t + b.
```

The equality of additive convolution indices is

```text
x + y + z = x' + y' + z'
```

which becomes the lag hyperplane

```text
3t + a + b = a' + b'.
```

So the cubic energy is governed by a constrained sextic average

```text
sum_{a,b,a',b',t : 3t+a+b=a'+b'}
  sum_j J_{j+t} J_{j+t+a} J_{j+t+b}
        conj(J_j J_{j+a'} J_{j+b'}).
```

R37 gives an exact complete-character-sum formula for each summand, but the
existing R37/R38 consumer takes a supremum over all five lag variables and then
sums the whole lag box.  That discards both the hyperplane constraint and the
final phase.

## Scale consequence

The uniform all-lag route sees roughly

```text
m^5 * (m * B)^2
```

for a five-lag box and an R37 pointwise six-`J` bound `m * B`.

But the cubic convolution target is

```text
E3 <= C * m^3 * q^3.
```

The probes show `E3/(m^3 q^3)` is constant-scale, while the quadratic lag route
and the all-lag sextic route both spend dimensions too early.  This is the same
phenomenon in two coordinates: pair/lag control loses the zero-lag quadratic
profile; all-lag sextic control loses the codimension-one convolution surface.

## New target

Replace pointwise/five-lag sextic control by:

```text
ConstrainedSexticAverageSubconvex:
  |sum_{3t+a+b=a'+b'} Corr6(a,b,a',b',t)| <= C * m^3 * q^3.
```

Here `Corr6` is the balanced six-`J` correlation from R37.  This is not merely
a prettier restatement: it keeps the exact linear constraint that defines
`tripleConv`, and therefore preserves cancellation between different lag data.

## Relation to R37/R38

R37 remains the right local normal form:

```text
Corr6(a,b,a',b',t)
 = m * sum_{u in G} sum_w A_{a,b}(u*w) conj(A_{a',b'}(w)) lam_t(w).
```

But R38's `SexticVarietyInput` is a per-`u`, per-lag pointwise statement.  The
new conjectural input should be a constrained vertical equidistribution theorem
for the entire family over

```text
(a,b,a',b',t,u,w) with 3t+a+b=a'+b',
```

after separating the Wick diagonal classes.  In words: prove square-root
cancellation for the connected six-point family after summing over the
convolution hyperplane, not before.

## Sanity check

A direct brute-force check at the first small R23 cell verified that the
hyperplane parameterization matches the triple-convolution energy:

```text
p=193 n=8 m=24
E3     = 3.000331e+11
direct = 3.000331e+11
lag    = 3.000331e+11
ratio  = E3/(m^3 q^3) = 3.0190
```

The residual `~1` absolute error is floating-point summation error against a
`3e11` total.  A second cell at `m=72` was interrupted because the brute-force
six-loop check is too slow; the next probe should be FFT/vectorized on the
constraint surface.

## Next proof attack

1. Formalize the exact lag-hyperplane expansion of `TripleConvEnergyBound`.
2. Split the hyperplane sum into Wick diagonal classes and connected classes.
3. Test whether the connected aggregate has stable sign/cancellation in the
   existing Jacobi probes.
4. Replace `SexticCorrelationBound` consumers by a direct
   `ConstrainedSexticAverageSubconvex -> TripleConvEnergyBound` consumer.

This is currently the sharpest subconvexity lens: the prize asks for a cubic
average theorem, not a uniform theorem on every sextic slice.
