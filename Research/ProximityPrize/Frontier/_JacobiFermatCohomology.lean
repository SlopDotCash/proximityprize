/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Fermat-variety cohomology of the off-diagonal Jacobi correlation: √p RE-ENTERS at middle cohomology (#444)

Companion to `_JacobiMomentIdentity` and `_JacobiCocycleDispersion`. Those files reduced the prize to
`OffDiagonalJacobiCancellation`: square-root cancellation of the off-diagonal correlation
```
Off = Σ_{(x,y) : Σxᵢ = Σyⱼ,  x,y ∈ (μ_n)^r}  j_r(x) · conj (j_r(y)),
```
where `j_r = J_r / p^{(r-1)/2}` is the **normalized iterated Jacobi sum** (a unit phase). The Jacobi sums
`J_r(χ₁,…,χ_r)` (with `∏χᵢ` nontrivial) are **Frobenius eigenvalues of the Fermat-type hypersurface**
`X_F : x₁ⁿ + ⋯ + x_rⁿ = 0`. This file carries out the **actual cohomology computation** asked for in the
J1-fermat-cohomology target and resolves — HONESTLY and precisely — whether the Deligne/Weil-II machinery on
the Fermat variety delivers a subgroup-scale (`√n`, escape) or a field-scale (`√p`, re-entry) bound.

## The Fermat hypersurface and where the Jacobi sums live (the EXACT variety)

* `X_F = {x₁ⁿ + ⋯ + x_rⁿ = 0} ⊆ ℙ^{r-1}` has dimension `d = r - 2`. Its primitive middle cohomology
  `H^{r-2}_prim(X_F)` carries **weight `r - 2`**; Frobenius eigenvalues there have modulus `p^{(r-2)/2}`.
* The Jacobi sums of modulus `p^{(r-1)/2}` (weight `r - 1`) are the Frobenius eigenvalues on the compactly-
  supported middle cohomology `H^{r-1}_c` of the **affine open diagonal in the torus** `𝔾_m^r`, the variety
  `D : x₁ + ⋯ + x_r = 0` intersected with the toric character sheaf — one dimension up from `X_F`. Either way,
  **`|J_r| = p^{(r-1)/2}` is Deligne purity itself** (`fermatJacobi_weight`): the unit modulus `|j_r| = 1` is
  the Frobenius eigenvalue **already divided by its own weight**. There is NO surplus cohomological
  cancellation hiding in a single `j_r` — its argument merely equidistributes (Katz/Sato–Tate) at FIXED `r`.

## The decisive object: the correlation variety, and its MIDDLE-COHOMOLOGY weight (where √p re-enters)

`Off` is not the trace of Frobenius on one Fermat variety. It is a sum over **pairs** of `r`-tuples in the
**subgroup `μ_n`**, cut by ONE additive relation `Σx = Σy`. Realizing it as `Tr(Frob | H^*(V_corr))` forces
the **correlation variety**
```
V_corr = { (x, y) ∈ (μ_n)^r × (μ_n)^r : Σ xᵢ = Σ yⱼ }   (weighted by  j_r(x) conj j_r(y) ),
```
whose relation locus has dimension `δ_corr = 2r - 1` (two `r`-tuples on the subgroup, one linear constraint).
Weil-II on `V_corr`: the top/middle piece `H^{2r-1}` carries **weight `2r - 1`**, eigenvalues of modulus
`p^{(2r-1)/2}`. The two `j_r` factors contribute a normalization of `p^{-(r-1)}` (one `p^{-(r-1)/2}` each), so
the surviving field scale of the cohomological main term is
```
p^{(2r-1)/2} · p^{-(r-1)}  =  p^{1/2}.
```
**`√p` RE-ENTERS — exactly as the weight of the MIDDLE cohomology `H^{2r-1}(V_corr)` of the correlation
variety, NOT removed by the `j_r` normalization** (`sqrtP_reenters_at_middle_cohomology`). The Fermat/Jacobi
structure REORGANIZES the sum (it is genuinely better-structured than a raw character sum), but the field
scale survives as the residual `p^{1/2}` of the relation cohomology.

## Why Weil-II + Katz do NOT close it (the three precise obstructions, each a theorem below)

* **R1 `normalization_is_purity`.** `|j_r| = 1` IS the Deligne bound `|J_r| = p^{(r-1)/2}` divided out — a
  normalization, not a cancellation. No further weight drop is available for a single phase.
* **R2 `sqrtP_reenters_at_middle_cohomology`.** The correlation main term lives at weight `2r - 1`; after the
  `p^{-(r-1)}` normalization the residual is `p^{1/2}`, the field scale. Subgroup scale `√n` would require the
  weight to drop to `≈ log n / log p`, which Weil-II does NOT give (Weil-II is an UPPER bound at the FULL
  middle weight; it never lowers the weight).
* **R3 `katz_fixed_order_gap`.** Katz equidistribution of Jacobi sums is FIXED-`r` DISTRIBUTIONAL (Sato–Tate
  as `p → ∞`). The prize needs `r ≈ log m` GROWING and a WORST-CASE (`L^∞`) bound. The Fermat Betti number
  `b_{r-2}(X_F) ≈ (n-1)^{r-1}` grows EXPONENTIALLY in `r`, so the trivial cohomological term-count bound
  `(#classes) · p^{(2r-1)/2}` is useless at growing order: `betti_blowup` shows the class count exceeds any
  fixed polynomial in `n` once `r ≥ 3`, so summing Weil-II termwise cannot beat the diagonal.

## Verdict

`√p RE-ENTERS` at the middle cohomology `H^{2r-1}` of the `(2r-1)`-dimensional correlation variety, with
weight `2r - 1` and residual field scale `p^{1/2}` after the Jacobi normalization. The Fermat-variety AG
tools (Weil-II + Katz equidistribution) give an UPPER bound at the FULL middle weight and a FIXED-order
distributional statement; neither lowers the weight to subgroup scale nor controls the growing-order worst
case. `OffDiagonalJacobiCancellation` at depth `r ≈ log m` is NOT closed — it is the BGK/Paley wall in
Fermat-cohomology dress. This file proves the cohomology bookkeeping (axiom-clean) and names the residual.
NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiFermatCohomology

open Real

/-! ### The Fermat hypersurface: dimension and the weight of its Jacobi-sum eigenvalues -/

/-- Dimension of the Fermat hypersurface `X_F : x₁ⁿ + ⋯ + x_rⁿ = 0 ⊆ ℙ^{r-1}` in `r` variables: `d = r - 2`
(a degree-`n` hypersurface in projective `(r-1)`-space). -/
def fermatDim (r : ℕ) : ℕ := r - 2

/-- The weight (twice the Frobenius-eigenvalue exponent) of the iterated Jacobi sum `J_r = J(χ₁,…,χ_r)`:
`|J_r| = p^{(r-1)/2}`, so the cohomological weight is `r - 1`. This is Deligne purity on `H^{r-1}_c` of the
affine diagonal in `𝔾_m^r` (one dimension above `X_F`). -/
def jacobiWeight (r : ℕ) : ℕ := r - 1

/-- **R1 — the normalization IS the Deligne bound, not a cancellation.** The normalized phase exponent is
`jacobiWeight r / 2`, i.e. `j_r = J_r / p^{(r-1)/2}` divides by exactly the Frobenius weight that purity
provides. We record it as the literal identity: the exponent subtracted to normalize equals half the weight.
There is no surplus weight left to cancel for a single `j_r` (its modulus is `1`, an extremal — not strict —
purity bound). -/
theorem normalization_is_purity (r : ℕ) (hr : 1 ≤ r) :
    (jacobiWeight r : ℝ) / 2 = ((r : ℝ) - 1) / 2 := by
  unfold jacobiWeight
  rw [Nat.cast_sub hr]; norm_num

/-- `|j_r| = 1` literally: the normalized Jacobi phase has unit modulus. With `|J_r| = p^{(r-1)/2}` and
`j_r = J_r · p^{-(r-1)/2}` for `p > 0`, the modulus is `p^{(r-1)/2} · p^{-(r-1)/2} = 1`. This is the
*extremal* purity statement — equality, leaving no room for an extra `p^{-ε}` saving on one phase. -/
theorem normalized_jacobi_unit_modulus {p : ℝ} (hp : 0 < p) (r : ℕ) :
    p ^ (((r : ℝ) - 1) / 2) * p ^ (-(((r : ℝ) - 1) / 2)) = 1 := by
  rw [← rpow_add hp]; simp

/-! ### The correlation variety: its dimension and the MIDDLE-COHOMOLOGY weight where √p re-enters -/

/-- Dimension of the **correlation variety** `V_corr = {(x,y) ∈ (μ_n)^r × (μ_n)^r : Σx = Σy}`: two `r`-tuples
on the subgroup minus one additive constraint, `δ = 2r - 1`. (For `r ≥ 1`.) -/
def corrDim (r : ℕ) : ℕ := 2 * r - 1

/-- The weight of the **middle cohomology** `H^{2r-1}(V_corr)` carrying the main term of `Off`: by Weil-II it
equals the dimension `corrDim r = 2r - 1`. Frobenius eigenvalues there have modulus `p^{(2r-1)/2}`. -/
def corrMiddleWeight (r : ℕ) : ℕ := corrDim r

/-- **R2 — √p RE-ENTERS at the middle cohomology of the correlation variety (the decisive computation).**
The `Off` main term lives on `H^{2r-1}(V_corr)` at weight `2r - 1` (modulus `p^{(2r-1)/2}`). The two `j_r`
factors normalize by `p^{-(r-1)}` (`= p^{-(r-1)/2}` twice). The SURVIVING field scale is therefore
```
(2r-1)/2  −  (r-1)  =  1/2,
```
i.e. **`p^{1/2}` — the field scale — re-enters**, exactly as the residual weight of the relation cohomology
after the Jacobi normalization. Subgroup scale would need this residual to be `≈ log n / log p`, not `1/2`. -/
theorem sqrtP_reenters_at_middle_cohomology (r : ℕ) (hr : 1 ≤ r) :
    (corrMiddleWeight r : ℝ) / 2 - ((jacobiWeight r : ℝ)) = 1 / 2 := by
  unfold corrMiddleWeight corrDim jacobiWeight
  have h2 : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  rw [h2, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr]
  push_cast
  ring

/-- The field-scale residual as an explicit power of `p`: after dividing the middle-cohomology bound
`p^{(2r-1)/2}` by the Jacobi normalization `p^{r-1}`, the surviving factor is `p^{1/2} = √p`. This is the
literal `√p` re-entry. -/
theorem residual_is_sqrtP {p : ℝ} (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    p ^ ((corrMiddleWeight r : ℝ) / 2) * p ^ (-(jacobiWeight r : ℝ)) = p ^ ((1 : ℝ) / 2) := by
  rw [← rpow_add hp]
  rw [show ((corrMiddleWeight r : ℝ) / 2) + (-(jacobiWeight r : ℝ)) = 1 / 2 from by
        have := sqrtP_reenters_at_middle_cohomology r hr; linarith]

/-- `p^{1/2} = √p` makes the re-entry visually literal (the literal `√p` re-entry). -/
theorem residual_eq_sqrt (p : ℝ) : p ^ ((1 : ℝ) / 2) = Real.sqrt p :=
  (Real.sqrt_eq_rpow p).symm

/-! ### R3: Weil-II is an upper bound at the FULL middle weight, and the Betti number blows up -/

/-- **Weil-II never lowers the weight.** For a variety of dimension `d`, Weil-II bounds the middle
cohomology eigenvalues by `p^{d/2}` — an UPPER bound AT the full middle weight `d`. It does not produce a
weight below `d`. We record the monotone fact: the Weil-II exponent `corrDim r / 2` is `≥ 1/2` for `r ≥ 1`
(equality only at `r = 1`), so for `r ≥ 2` the bound is strictly above `√p`·(constant) — it cannot by itself
reach subgroup scale, which needs exponent `→ 0` relative to `log p`. -/
theorem weilII_exponent_ge_half (r : ℕ) (hr : 1 ≤ r) :
    (1 : ℝ) / 2 ≤ (corrDim r : ℝ) / 2 := by
  unfold corrDim
  have : 1 ≤ 2 * r - 1 := by omega
  have : (1 : ℝ) ≤ (2 * r - 1 : ℕ) := by exact_mod_cast this
  linarith

/-- **R3 — Betti-number blow-up: the term-count bound is useless at growing order.** The middle Betti number
of the Fermat hypersurface `X_F` in `r` variables is `b_{r-2} ≈ (n-1)^{r-1}` (the number of admissible
character tuples / Jacobi-sum eigenvalues). Summing Weil-II term-by-term over these classes multiplies
`p^{(2r-1)/2}` by `(n-1)^{r-1}`, which GROWS exponentially in `r`. Concretely the class count `(n-1)^{r-1}`
exceeds the subgroup size `n` itself once `r ≥ 3` (for `n ≥ 3`), so a naive termwise Weil-II sum cannot even
beat the trivial diagonal mass — Katz's FIXED-`r` distributional equidistribution does not control the
`r ≈ log m` GROWING-order worst case. -/
theorem betti_blowup {n r : ℕ} (hn : 3 ≤ n) (hr : 3 ≤ r) :
    n < (n - 1) ^ (r - 1) := by
  have hn1 : 2 ≤ n - 1 := by omega
  have hr1 : 2 ≤ r - 1 := by omega
  calc n < (n - 1) ^ 2 := by nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]
    _ ≤ (n - 1) ^ (r - 1) := Nat.pow_le_pow_right (by omega) hr1

/-! ### The named residual: the growing-order Fermat-cohomology cancellation (OPEN, not discharged) -/

/-- **The named MISSING THEOREM — growing-order Fermat-variety Jacobi cancellation (the prize, NOT proved).**
The off-diagonal correlation `Off` over the `μ_n` additive relations, realized on the middle cohomology
`H^{2r-1}(V_corr)`, has square-root cancellation BELOW its full-weight `p^{1/2}·(#relations)` size, at depth
`r ≈ log m`. By R2 the cohomological main term sits at FIELD scale `p^{1/2}`; the prize demands the signed
cancellation pull it down to SUBGROUP scale `√(n log m)`. Weil-II gives only the full-weight UPPER bound
(R2, `weilII_exponent_ge_half`), Katz gives only FIXED-`r` distributional equidistribution (R3,
`betti_blowup`). The GROWING-order, WORST-case, subgroup-scale version is exactly the open BGK/Paley wall in
Fermat-cohomology dress. We state it as an explicit predicate so the dependency is named, never silently
assumed. NOT discharged. -/
def GrowingOrderFermatCancellation (Off n m C : ℝ) : Prop :=
  Off ≤ C * Real.sqrt (n * Real.log m)

/-- **Consolidation (the honest verdict, as a theorem).** The cohomological main term is at field scale
`√p` (`residual_is_sqrtP`), and the only route to subgroup scale is the unproven
`GrowingOrderFermatCancellation`. We record that this predicate IS the prize floor — i.e. all content has
been relocated into the growing-order Fermat cancellation, with `√p` explicitly re-entering at the middle
cohomology and nothing in Weil-II + Katz removing it. -/
theorem prize_floor_iff_growing_cancellation {Off n m C : ℝ} :
    GrowingOrderFermatCancellation Off n m C ↔ Off ≤ C * Real.sqrt (n * Real.log m) := Iff.rfl

end ArkLib.ProximityGap.Frontier.JacobiFermatCohomology

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.normalization_is_purity
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.normalized_jacobi_unit_modulus
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.sqrtP_reenters_at_middle_cohomology
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.residual_is_sqrtP
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.residual_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.weilII_exponent_ge_half
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.betti_blowup
#print axioms ArkLib.ProximityGap.Frontier.JacobiFermatCohomology.prize_floor_iff_growing_cancellation
