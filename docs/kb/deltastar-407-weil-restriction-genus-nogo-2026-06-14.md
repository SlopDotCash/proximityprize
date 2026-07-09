# #407 — Weil-restriction / superelliptic-genus / dyadic-CM route: PRECISE NO-GO (2026-06-14)

**Vector.** weil-restriction-genus. View `η_b = Σ_{y^n=1} ψ(by)` as a point-count deviation on
the Artin-Schreier-Kummer cover `w^p − w = b·x^m` (`m=(q−1)/n`), with the sup-norm
`M = max_b|η_b|` governed by the genus and the Frobenius eigenvalues on the Jacobian. The hope
(user's angle): for dyadic `n=2^μ` the relevant Jacobian has CM by `Z[ζ_{2^μ}]`, and the CM
structure + specific genus give a Weil bound `2g√q/m` that beats `√(n log m)`.

**Verdict: PARTIAL — reconfirms the wall, with a NEW precise structural reason the tool fails.**

## The genus arithmetic (derived + numerically confirmed)

Completing the multiplicative sum: `m·η_b = −1 + Σ_{x∈F_q} ψ(b x^m) = Σ_{χ:χ^m=1,χ≠1} χ̄(b)·g(χ)`.
The carrier curve `w^p−w = b x^m` (gcd(m,p)=1) has Artin-Schreier genus `g_A = (p−1)(m−1)/2`;
per nontrivial additive character `ψ^a` the relevant eigenvalues are the **m−1 Gauss sums `g(χ)`
of the order-`m` characters χ**, each of modulus exactly `√q` (Weil/Hasse-Davenport, verified
on the nose: `|g(χ)|=√q` to 1e-3 for p=97,113,193,257). The Weil bound is the triangle sum over
these m−1 unit-modulus eigenvalues:
  `|η_b| ≤ (m−1)√q/m ≈ √q`.
At prize scale (`n=2^32`, `m=2^128`, `q=2^160`): Weil gives `2^80`, target `√(n ln m)=2^19.24` —
a **60.76-bit (exact half-power) gap**. The genus provides NO cancellation; it merely COUNTS the
m−1 eigenvalues.

## Why the dyadic CM does NOT act (the new structural reason — the crux)

In the prize regime `n` takes the **full 2-part** of `p−1` (`prizeIndex_odd` in-tree), so
`m=(p−1)/n` is **ODD** and **gcd(n,m)=1** (verified on every sampled prime where n is the 2-part).
Consequently:

- η_b's Frobenius eigenvalues are Gauss sums of **order-m (ODD)** characters; they carry CM by
  `Z[ζ_m]` (odd cyclotomic), **NOT** `Z[ζ_{2^μ}]`.
- The dyadic-CM Jacobian the user invokes is the **Fermat curve `F_n: X^n+Y^n=1`** (genus
  `(n−1)(n−2)/2`, CM by `Z[ζ_n]`). Its Frobenius eigenvalues are **order-n Jacobi sums**
  `J(χ^a,χ^b) = g(χ^a)g(χ^b)/g(χ^{a+b})`, products of n-side Gauss sums.
- **The order-`n` and order-`m` character systems are on COPRIME orders** (`gcd(2^μ, odd)=1`),
  hence arithmetically disjoint: no algebraic identity (Hasse-Davenport, Stickelberger) connects
  η_b (= order-m Gauss sums) to `F_n`'s Jacobian (= order-n Jacobi sums). **The dyadic-CM Jacobian
  does not compute η_b**, and the curve that does compute η_b has its CM on the wrong (odd) side.

`m≈2^128` is a single huge fixed cofactor with no exploitable internal structure, so `Q(ζ_m)`
has degree `φ(m)~2^128` and gives no eigenvalue collapse / no low-degree characteristic polynomial.

## Numerical kill of the residual CM-collapse hope

A CM/Legendre-flat eigenphase sequence `a_j = g(χ_j)/√q` would have `max_c|DFT_c(a)| ~ √m`
(perfectly flat). Measured (n=8, m up to 201): `max|DFT|/√m` **GROWS** (2.3→2.6+) while
`max|DFT|/√(m log m)` is **STABLE at ≈1.13–1.25**. So the Gauss-phase sequence is **pseudorandom,
not CM-flat**: the √(m log m) max-of-Gaussians law holds (matching the in-tree house constant
≈1.33), and no CM relation forces the √m flatness a genus bound would need. (Cross-checks
TangentSumJacobiAverage: η-flatness is carried by the Jacobi-sum/tangent average, an
equidistribution statement, not an algebraic-genus one.)

## Honest bottom line

The genus/Weil/CM tool is the WRONG instrument for η_b, for a precise reason now mapped: the
prize's dyadic structure lives on the order-`n` side (the subgroup elements / the Fermat Jacobian),
while η_b's Frobenius eigenvalues live on the coprime order-`m` side (odd Gauss sums). Weil counts
m−1 flat eigenvalues and triangle-sums to `√q` — exactly the half-power-too-big bound the campaign
already records from BGK/di-Benedetto. **No closure; no partial bound below √q.** This is the
char-sum analogue of the in-tree `weil_recovers_root_count_not_better` no-go: Weil recovers the
trivial count, not the sub-√q cancellation.

**Cross-path lever.** The split it sharpens — dyadic CM on the n-side (Fermat/Jacobi, where it IS
structured) vs pseudorandom odd-Gauss-sum flatness on the m-side (where η_b lives) — says any
working tool must act on the **m-side equidistribution** (Jacobi-sum average per
TangentSumJacobiAverage), where there is no algebraic CM to exploit; the dyadic 2-power structure
is a red herring for the η_b sup-norm. This re-points the search at effective Jacobi/Kloosterman
equidistribution of the ODD-order family, off the (futile) algebraic-CM lane.
