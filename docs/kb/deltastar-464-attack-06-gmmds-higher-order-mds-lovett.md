# Attack #06 — GM-MDS / higher-order-MDS list-decoding-capacity (R3 / AGL24) vs. δ*

Issue #464/#444/#407. Angle: does the AGL24 result "higher-order-MDS codes achieve
list-decoding capacity" pin δ* for explicit smooth-domain Reed–Solomon codes, bypassing the
generalized-Paley / BCHKS-1.12 wall? It is an algebraic-geometry generic-position statement, not
a character sum — so on its face it looks Paley-free. This essay tries to close the prize from
that angle end-to-end, then adversarially refutes the attempt and pins the exact reduction.

## 1. Target theorem this angle would prove

To close the prize via R3 we would need:

> **(R3-Prize.)** For the explicit smooth 2-power Reed–Solomon code `RS[F_q, μ_n, k]`
> (`n = 2^30`, `ε* = 2^-128`, `q ≈ n·2^128`), the higher-order-MDS / GM-MDS list-decoding
> capacity theorem pins `δ*` (the **mutual correlated agreement** threshold) exactly inside the
> window interior `(1−√ρ, 1−ρ−Θ(1/log n))`.

Two independent obligations have to hold for this to even be the right object:

- **(O1, the algebra).** The order-`ℓ` higher-minor non-vanishing for the *specific* eval points
  `μ_n` — i.e. `RIMKernelTrivialFromLovett` / the codim-≥2 generalized-Vandermonde higher minor.
- **(O2, the object).** GM-MDS list-decoding capacity must actually deliver *mutual correlated
  agreement* (the `ε_mca` the prize needs), not merely ordinary list-decodability.

## 2. State of the in-tree R3 chain (what is proven)

The GM-MDS cone (#346/#389/#354) is large and mostly **proven**:

- `lovettThm17_unconditional` (`GMMDS/LovettMergeIndepProof.lean`) — Lovett's Theorem 1.7,
  proven unconditionally, axiom-clean. The symbolic independence of the dual-variable family
  `pFamUnion V k` over `MvPolynomial (Fin n) F` is **done**.
- `symbolicFullRank_of_classical_imports` (`AGL24GrandAssembly.lean`) — the campaign capstone:
  Frank orientation + `GMMDSResidual` ⟹ symbolic Theorem 2.11. Every other layer is proven.
- `isGenericInter_of_normalDet` (`HigherOrderMDSOrderKNormal.lean`) — the **codim-1** order-`k`
  certificate is fully proven (the honest generalization of the order-2/3 single-normal method).
- `symbolicMinorFromLovett_of_ringChange` (`GMMDS/LovettSymbolicMinorDischarge.lean`) — the
  discharge of the connector from the ring-change transfer, axiom-clean.

The chain is gated at **one** named open `Prop`:

```
RIMKernelTrivialFromLovett ι F k :=
  (∀ m, LovettThm17 F m) → ∀ e δ, GZPCondition e δ k →
    ∀ v : Fin t × Fin k → MvPolynomial ι F, (RIM F e).mulVec v = 0 → v = 0
```

the **ring-change transfer**: transport Lovett's independence over the dual-variable ring
`MvPolynomial (Fin n) F` to triviality of the RIM kernel over the **edge-variable** ring
`MvPolynomial ι F`. (`GMMDSDualZeroPatternTheorem` unpinned is *False* at `δ ≡ 0` — the 13th
machine-checked false-residual catch — repaired only by pinning `∑ⱼ δⱼ = card ι − k`.)

## 3. Proof attempt for (O1): can the codim-≥2 higher minor be discharged at smooth μ_n points?

Lever (a) of the prompt: is the codim-≥2 higher-minor non-vanishing for the **specific** smooth
2-power eval points provable via a Schur / Lindström–Gessel–Viennot argument?

The single-normal method (`isGenericInter_of_normalDet`) is square only at `card = k − 1`
(`codim_frameSpan_eq_one_iff`). The GM-MDS worst case keeps **fixed small card** (pairs) while
`k → ∞`, so each set is codim `k − 2 ≥ 2` and order-`ℓ` generic position is governed by a
**non-square stacked-normal / generalized-Vandermonde higher minor**, not a scalar det. The
Schur route is exactly the right idea: `SchurLagrangeBridge.lean` proves the top-coefficient /
divided-difference identity

```
[s] x^b = Σ_{i∈s} (v i)^b / ∏_{j∈s\{i}} (v i − v j) = h_{b−k}(v_s)   (complete homogeneous Schur)
```

so the bad-pencil criterion at the smooth points becomes the **vanishing of a Schur polynomial**
`h_{b−k}(v_S) = 0` with `v_S ⊂ μ_n`. An LGV / Jacobi–Trudi argument *would* close (O1) **iff**
these Schur minors are non-vanishing at the specific points `μ_n`.

## 4. Adversarial refutation

The hope dies at the **specific points**. For the prize domain `μ_n` with `n` a power of two:

1. **Antipodal vanishing is in-tree, for the exact prize domain.**
   `reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs`
   (`HigherOrderMDSOrderThreeFail.lean`, axiom-clean) shows that antipodal pairs `{x, −x}`
   (`a + b = 0`) make the three interpolation normals coplanar, so the pair-spans share an
   unexpected common vector and **order-3 higher-MDS fails**. Since `−1 = ζ^{n/2} ∈ μ_n` for
   even `n`, the smooth 2-power domain is **negation-closed**, so it fails order-3 higher MDS
   *even in the Sidon regime* (`SidonModNeg` does not forbid `a + b = 0`). The concrete witness
   `{±1,±2,±3}` is `antipodal_example_not_isHigherMDS_three`. So the generalized-Vandermonde
   higher minor **does vanish** at `μ_n` — the order-`ℓ` generic-position certificate that R3
   needs is *false at the very points the prize fixes*.

2. **The vanishing locus is Galois/rotation-stable (cyclotomic, not generic-position).**
   `scripts/probes/probe_schur_vanishing_rotation_invariant.py` (re-run: 12000 checks, 1797
   actual vanishings, all rotation-invariant): `[R']x^b = 0 ⟺ [ζR']x^b = 0` on `μ_n`. The
   Schur-vanishing locus is closed under multiplication by `ζ ∈ μ_n`, i.e. it is a union of
   Galois orbits — a genuine **cyclotomic vanishing**, not a measure-zero generic-position
   accident a Dirichlet-prime / large-field argument can dodge. This is exactly the in-tree
   finding `issue334-algebraic-floor-reduces-cyclotomic-wall`: gapped-Vandermonde RIM minors
   vanish at `μ_n` at distinct roots via `1 + ζ^{n/2} = 0` (Lam–Leung).

3. **So (O1) reduces to the wall.** `RIMKernelTrivialFromLovett` for `μ_n` is *not* a soft
   generic-position statement: at the smooth 2-power points the higher minor is governed by
   whether short `±1`-combinations of `2^μ`-th roots of unity vanish — the Schur factor
   `h_{b−k}(ζ^T)` is the same elementary/complete-symmetric-vanishing object the unified core
   `K` counts (the count side of the generalized-Paley spectrum; `VandermondeInterpolationSafe`:
   "every char-`p` excess lives in the Schur factor"). It is the same cyclotomic-vanishing wall
   as Paley face 3↔4, attacked from the algebra side. R3 at `μ_n` does **not** avoid the Paley
   object; it *is* the Paley object in Schur disguise.

4. **(O2) is independently fatal — wrong object.** Even granting (O1), GM-MDS / AGL24 deliver
   ordinary **list-decoding capacity**. The prize needs **mutual correlated agreement**
   (`ε_mca`). `MCAUpToCapacityFalse.lean` (`rs_mca_uptoCapacity_false_of_smallField`,
   axiom-clean) proves that for `|F| < (n−k)·2^128` the MCA error at the near-capacity radius
   `δ = 1 − (k+1)/n` **exceeds** `ε* = 2^-128`: the up-to-capacity MCA bound is *FALSE*. The
   prize field `q ≈ n·2^128` is squarely in this small-field regime. So even a perfect R3
   higher-order-MDS-achieves-capacity theorem cannot place `δ*` near capacity — list-decoding
   capacity and MCA threshold are *different thresholds*, and the prize one is the strictly
   smaller MCA one, which capacity arguments overshoot.

## 5. Lever analysis

- The **crack that would work** but does not exist: a Schur/LGV non-vanishing of
  `h_{b−k}(ζ^T)` over `μ_n` that survives the *antipodal* relation `1 + ζ^{n/2} = 0`. It fails
  because the prize domain is negation-closed: the relation is cyclotomic and Galois-stable, not
  generic. Any field-enlargement / Dirichlet-prime trick (which fixes ceiling existence
  problems) is silent here because the vanishing is char-0 cyclotomic.
- The **exact reduction step:** `RIMKernelTrivialFromLovett ι F k` at `ι = μ_n` ⟹ Schur minor
  `h_{b−k}(ζ^T) ≠ 0` ⟹ (refuted) by antipodal coplanarity / Lam–Leung. The algebraic route
  meets the analytic route at one cyclotomic-vanishing wall.
- **Second, independent wall:** the object mismatch (O2). MCA up-to-capacity is provably false
  in the prize field regime, so even unconditional R3 capacity cannot pin the MCA δ* in the
  window interior.

## 6. Honest verdict

**Reduces to Paley (and additionally hits the MCA-≠-capacity wall).** R3 is *not* a Paley-free
route to the prize. Its single open algebraic core `RIMKernelTrivialFromLovett`, specialized to
the prize's smooth 2-power domain `μ_n`, is the cyclotomic-Schur-vanishing object — the same wall
as the generalized-Paley spectrum, reached from the algebraic-geometry side (confirming
`issue334-algebraic-floor-reduces-cyclotomic-wall`). And even if discharged, GM-MDS delivers
ordinary list-decoding capacity, whereas the prize δ* is the *mutual correlated agreement*
threshold, which `rs_mca_uptoCapacity_false_of_smallField` proves cannot reach capacity in the
prize field regime. No closure; no new axiom-clean brick required — the two decisive facts
(antipodal order-3 failure at `μ_n`; MCA-up-to-capacity false) are **already in-tree and
axiom-clean**. This is the ~61st-plus independent confirmation of the one wall, now triangulated
from the GM-MDS / higher-order-MDS direction.

### Named remaining open input
`ArkLib.GMMDS.RIMKernelTrivialFromLovett ι F k` (the ring-change transfer), which at `ι = μ_n`
reduces to the cyclotomic Schur-minor non-vanishing = the Paley wall.

### Key in-tree bricks (axiom-clean, already landed — not re-derived here)
- `HigherOrderMDSOrderThreeFail.reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs`,
  `antipodal_example_not_isHigherMDS_three` — order-3 higher-MDS fails on negation-closed `μ_n`.
- `ProximityGap.MCANearCapacityGK.rs_mca_uptoCapacity_false_of_smallField` — MCA up-to-capacity
  is false in the prize field regime.
- `ProximityGap.SchurLagrange.interpolate_coeff_top` / `dividedDifferencePow` — the Schur bridge
  that identifies the bad-pencil criterion with Schur-polynomial vanishing on `μ_n`.
- `ArkLib.HigherOrderMDS.codim_frameSpan_eq_one_iff` — pins the codim-1 boundary of the
  single-normal method (why GM-MDS difficulty is genuinely codim-≥2).
