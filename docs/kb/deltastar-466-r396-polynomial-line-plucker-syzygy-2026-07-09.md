# R396: polynomial-line Plucker syzygy (2026-07-09)

Status: Plucker compatibility brick axiom-clean; it does not exclude the
realized sunflower, and global rate-quarter closure remains open.

## Discovery

The cardinal-only four-core sunflower in the rate-quarter dossier treats decoded lines as
independent labels.  Actual decoded polynomial lines `L_i=(a_i,r_i)` lie in a two-dimensional
module over `F[X]`.  Writing

```text
Delta_0ij = det(L_i-L_0,L_j-L_0),
```

they obey the componentwise syzygy

```text
Delta_012 (L_3-L_0)
- Delta_013 (L_2-L_0)
+ Delta_023 (L_1-L_0) = 0.
```

They also obey the affine determinant cocycle

```text
Delta_012 - Delta_013 + Delta_023 - Delta_123 = 0.
```

Both identities are exact polynomial identities, proved by `ring` in
`Frontier/_R396PolynomialLinePluckerSyzygy.lean`.

## Local propagation

At an evaluation coordinate `x`, if `Delta_012(x)=Delta_013(x)=0` and either component of
`L_1(x)-L_0(x)` is nonzero, then `Delta_023(x)=0`.  Thus two overlap-induced determinant
zeros propagate to a third determinant except on the common zero set of the reference-line
difference.

Combining this identity with separate degree and root-cardinality theorems would bound the
exceptional coordinate set by `k-1` for distinct degree-`<k` decoded lines.  That global bound is
not exported by this file: the module itself has no degree hypotheses, injected evaluation
domain, `jointCore`, petal, or multiplicity theorem.

## Red team

The identity alone does not close the saturated rate-quarter case.  The exact `F29,n=28,k=7`
RS sunflower in the main rate-quarter dossier realizes the limiting case.  Its lines are
`L_i=(a_i H,r_i H)` for one degree-six kernel locator `H`, so every nonzero triple determinant is
`c_ijk H^2`.  At the six roots of `H`, both reference components vanish and the propagation
hypothesis fails; away from the kernel, the determinant-zero hypotheses fail.  Each determinant
therefore saturates the full `2(k-1)` root budget while obeying every syzygy in this module.

A useful global successor needs additional off-line population or strict-surplus hypotheses.
Merely concentrating failures in a degree-`k-1` exceptional divisor is not contradictory: the
realized `H^2` configuration witnesses equality.

No prize claim is made from R396 alone.
