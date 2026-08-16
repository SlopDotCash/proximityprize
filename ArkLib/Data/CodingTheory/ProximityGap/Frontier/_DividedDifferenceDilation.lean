/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Dilation homogeneity of the monomial divided difference (#444 / #407)

The far-line bad-`γ` is the Schur ratio `γ = −dividedDifferencePow R v a / dividedDifferencePow
R v b`, and the orbit law `#bad = 1 + (n/2)·O` is a DIRECT consequence of this ratio being a
**dilation eigenvector** (lalalune, #444 08:46 comment): `γ(g·T) = g^{a-b} γ(T)`.

The algebraic core of that eigenvector property is the dilation HOMOGENEITY of the in-tree
`dividedDifferencePow` itself. Under the node dilation `v ↦ g·v` (`g ≠ 0`):

  numerator `(g v_i)^b = g^b (v_i)^b`;
  denominator `∏_{j∈R.erase i} (g v_i − g v_j) = g^{#R−1} ∏ (v_i − v_j)`;

so every summand scales by `g^b · (g^{#R−1})⁻¹`, giving the headline:

  `dividedDifferencePow R (g·v) b = g^b · (g^{#R−1})⁻¹ · dividedDifferencePow R v b`.

The Schur-ratio eigenvector `γ(g·v) = g^{a−b} γ(v)` then drops out: the `(g^{#R−1})⁻¹` factor
cancels between numerator (`a`) and denominator (`b`).

Probe `scripts/probes/probe_ddval_dilation.py` (exact `ℚ`, 2000 random node sets `|R|=2..6`,
random dilations `g`, monomial degrees `b=0..8`) reproduces BOTH the homogeneity and the
`g^{a−b}` ratio law with a clean PASS. This is NOT a moment/energy/Wick object, NOT a census or
orbit re-derivation: it is a pure scaling identity for the in-tree `dividedDifferencePow`, the
algebraic mechanism BENEATH the orbit law.

All theorems reference the REAL in-tree `dividedDifferencePow` (from `SchurLagrangeBridge`).
-/

open Finset

namespace ProximityGap.DDDilation

open ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- **The dilated difference product collapses by `g^{#s−1}`.** For a fixed node `i ∈ s`,
`∏_{j ∈ s.erase i} (g·v i − g·v j) = g^{#s−1} · ∏_{j ∈ s.erase i} (v i − v j)`. The factor is
`g` raised to the size of `s.erase i = #s − 1`. -/
theorem prod_dilate_diff (s : Finset ι) (v : ι → F) (g : F) {i : ι} (hi : i ∈ s) :
    ∏ j ∈ s.erase i, (g * v i - g * v j) = g ^ (#s - 1) * ∏ j ∈ s.erase i, (v i - v j) := by
  have hcard : #(s.erase i) = #s - 1 := Finset.card_erase_of_mem hi
  calc
    ∏ j ∈ s.erase i, (g * v i - g * v j)
        = ∏ j ∈ s.erase i, g * (v i - v j) := by
          refine Finset.prod_congr rfl ?_
          intro j _; ring
    _ = (∏ _j ∈ s.erase i, g) * ∏ j ∈ s.erase i, (v i - v j) := by
          rw [Finset.prod_mul_distrib]
    _ = g ^ (#s - 1) * ∏ j ∈ s.erase i, (v i - v j) := by
          rw [Finset.prod_const, hcard]

/-- **Dilation homogeneity of the monomial divided difference (HEADLINE).** For `g ≠ 0`,
dilating the nodes by `g` scales `dividedDifferencePow` by `g^b · (g^{#s−1})⁻¹`:

  `dividedDifferencePow s (g·v) b = g^b · (g^{#s−1})⁻¹ · dividedDifferencePow s v b`.

This is the algebraic eigenvector mechanism beneath the far-line orbit law (the numerator
contributes `g^b`, the denominator `g^{#s−1}`). Proven termwise off `prod_dilate_diff`. -/
theorem dividedDifferencePow_dilate (s : Finset ι) (v : ι → F) {g : F} (hg : g ≠ 0) (b : ℕ) :
    dividedDifferencePow s (fun i => g * v i) b
      = g ^ b * (g ^ (#s - 1))⁻¹ * dividedDifferencePow s v b := by
  unfold dividedDifferencePow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hgpow : (g ^ (#s - 1) : F) ≠ 0 := pow_ne_zero _ hg
  rw [prod_dilate_diff s v g hi, mul_inv, mul_pow]
  field_simp

/-- **The Schur ratio is a dilation eigenvector (`g^{a−b}`).** With `γ(v) = −[a-ratio]`, dilating
the nodes by `g ≠ 0` scales the bad-`γ` by `g^{a−b}`:

  `dividedDifferencePow s (g·v) a / dividedDifferencePow s (g·v) b
     = g^{a−b} · (dividedDifferencePow s v a / dividedDifferencePow s v b)`,

provided `g^b` is invertible and the `b`-difference is nonzero (so the ratio is defined). This
is lalalune's `γ(g·T) = g^{a−b} γ(T)`, the orbit-law mechanism, with the `(g^{#s−1})⁻¹` factor
cancelling between numerator and denominator. Stated over `ℤ`-exponents via `zpow`. -/
theorem schurRatio_dilate_eigen (s : Finset ι) (v : ι → F) {g : F} (hg : g ≠ 0) (a b : ℕ) :
    dividedDifferencePow s (fun i => g * v i) a * (dividedDifferencePow s (fun i => g * v i) b)⁻¹
      = g ^ (a : ℤ) * (g ^ (b : ℤ))⁻¹
        * (dividedDifferencePow s v a * (dividedDifferencePow s v b)⁻¹) := by
  rw [dividedDifferencePow_dilate s v hg a, dividedDifferencePow_dilate s v hg b]
  have hga : (g ^ a : F) ≠ 0 := pow_ne_zero _ hg
  have hgb : (g ^ b : F) ≠ 0 := pow_ne_zero _ hg
  have hgs : (g ^ (#s - 1) : F) ≠ 0 := pow_ne_zero _ hg
  rw [mul_inv, mul_inv, inv_inv]
  rw [zpow_natCast, zpow_natCast]
  field_simp

end ProximityGap.DDDilation
