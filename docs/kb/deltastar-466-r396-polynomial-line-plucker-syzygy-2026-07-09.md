# R396: polynomial-line Plucker syzygy (2026-07-09)

Status: algebraic anti-sunflower brick axiom-clean; global rate-quarter closure remains open.

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

For distinct degree-`<k` decoded lines, at least one component difference is a nonzero
degree-`<k` polynomial.  The exceptional coordinate set therefore has size at most `k-1`.
This is structure absent from the abstract `k=7,n=28` sunflower countermodel: simultaneous
petal-overlap saturation must route every failed propagation through one low-degree exceptional
set.

## Red team

The identity alone does not close the saturated rate-quarter case.  At coordinates where the
reference difference vanishes, the propagation conclusion is vacuous, and a sunflower could in
principle concentrate its compatibility defects there.  The next required theorem is a
multiplicity-aware global form: sum the propagated roots across several determinant pencils and
show that concentrating all failures in a degree-`k-1` exceptional divisor either forces one
determinant to vanish identically or exceeds the available `2(k-1)` determinant degree.

No prize claim is made from R396 alone.
