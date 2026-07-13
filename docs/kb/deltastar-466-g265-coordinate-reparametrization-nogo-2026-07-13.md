# G265: quotient coordinate reparametrization is diagonal, not a physical one-sided move

Date: 2026-07-13
Issue: #466
Branch: `research/proximity-prize` only (#499)

## Question

Fable's G264 admissibility audit exposed the gap between the relaxed nonnegative cone and actual
weighted relation profiles. The highest-ranked survivor was to characterize the realizable move set
of the characteristic-p profile

```text
W_G(t) = #{(y,z) in G^2 : 2y-z=t}
```

before using G264's four-quadrant Cramer witnesses. G258 supplied the only proved structured family
on the board: quotient-unit relabelings of `W`. Does that family give a physical deformation of the
fixed sponsor data, or only a coordinate change?

## Exact answer

It is a coordinate change. If `g` is a primitive root and quotient classes are labelled by
`g^j G`, replacing `g` by `g^a` changes label `j` to `a*j`. Every field-derived quotient profile is
therefore relabelled by the same unit:

```text
w_a(j) = w(a*j),     R_{r,a}(j) = R_r(a*j).
```

For any quotient unit `u`, G265 proves

```text
sum_x (u.W)(x) (u.R)(x) = sum_x W(x)R(x),
C_m(u.W,u.R) = C_m(W,R),
C_m(u.W,R) = C_m(W,u^-1.R).
```

The first identity is finite change of variables, the second also uses preservation of the two
masses, and the third states the real geometry: a one-sided relabeling changes only the relative
placement of `W` against the fixed row. Thus primitive-root/unit freedom is a diagonal gauge action
on `(W,R)`, and its physical covariance orbit is a singleton.

## Exact characteristic-p certificate

The self-contained integer probe recomputes `W_G` and the adjacent-rank rows directly over `F_p`.
At G258's flagship `(n,p,m)=(16,1297,81)`, primitive-root exponent `53` produces exactly G258's
moved support. The distinction is:

```text
one-sided W relabel, fixed R:       (C5,C6)=(-346283,-1161769)
physical coordinate change W,R:    (C5,C6)=(+1261081,+3691265)=base.
```

All 432 primitive exponents modulo 1296 were checked and preserve both simultaneous covariances.
Four further cells pass the same exact test. No FFT enters any covariance.

## Physical affine stabilizer

The probe also checks the sponsor-independent affine classification. For `n>1`, the subgroup sum is
zero. If an affine map stabilizes the subgroup, `aG+b=G`, summing gives `n*b=0`; because `p` does
not divide `n`, `b=0`. Then `aG=G` iff `a in G`. Hence the affine stabilizer has exactly `n`
elements and acts trivially on `F_p^*/G`. There is no nontrivial affine subgroup symmetry that can
supply G264's missing quadrant.

At sponsor scale this corrects the asymptotic interpretation of G258. The `phi(m1)>2^126` and
`phi(m2)>2^127` unit families are enormous coordinate-choice families, but diagonal invariance makes
their physical sign freedom exactly zero. Their size is evidence that label-free summaries forget
the row alignment, not evidence for many alternative subgroup relation profiles.

## Scope and consequence

This does not invalidate G258's theorem: one-sided unit relabeling remains a decisive countermodel to
any input that knows only the unlabelled Fourier multiset, positivity, integrality, and support size.
It corrects the word “physical.” Nor does it invalidate G264's algebra: its Cramer construction is a
sharp no-go on the relaxed nonnegative cone. But neither family is an admissible deformation of the
fixed sponsor pair.

FS15-FS18 remain fully consumed: their almost-all-prime/resultant ladder does not select the sponsor
and rank six is forced exceptional by G262. G265 is orthogonal. It pins the admissible-set boundary:
coordinate gauges preserve CORE exactly, while arbitrary one-sided placements are black-box
countermodels only. The sole live prize face remains the direct row-labelled sponsor
Jacobi/cyclotomic covariance at each rank. CORE OPEN / ON-BGK.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G265CoordinateReparametrizationNoGo.lean`
- `scripts/probes/g265_coordinate_reparametrization_nogo.py`
- DISPROOF entry `[466-G265-coordinate-reparametrization-nogo]`
