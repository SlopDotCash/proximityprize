/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyBalancedLimit
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftFactorization
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftMultiplicityBudget
import ArkLib.Research.ProximityGap.Frontier.PaleySignedHankelDegree
import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import Mathlib.Tactic.NormNum.Prime

/-!
# Signed Paley row estimates, central factorization, and balanced square-root bounds

Builds on `PaleySignedHankelDegree` to formalize the local contact order, finite signed row
estimate (`∑_t (W_w(t)^2 - (a - z_t - 2x)^2)_+ ≤ 4 D_x`), exact arbitrary-sign central
factorization (`det J = C lc * ∏_t (X - C t)^⌊W_w(t)^2 / 4⌋`), finite prescribed signed rectangle
bounds (`p = 65537, |A| = |B| = 256 ⇒ |S| ≤ 56,829`), and the asymptotic arbitrary-sign balanced
bound `< √3 / 2 + ε` as `|A|, |B| ~ √p`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace ProximityGap.PaleySignedSquareRoot

open Finset Filter Matrix Polynomial
open PaleyDefectMinor PaleyInterpolationContact PaleyShiftMultiplicityBudget
open PaleyShiftFactorization PaleySignedHankelDegree
open scoped Polynomial Topology

/-! ## 3. Local contact, finite signed row estimate, and exact central factorization -/

section RowEstimateAndFactorization

variable {p : ℕ} [Fact p.Prime]

private theorem signed_minority_contact (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (ha : 2 ≤ A.card) (b : ZMod p)
    {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    let D := p / 2 + (A.card - 2)
    let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
    (X - C b) ^ (if -b ∈ A then A.card - 2 else A.card - 1) ∣
      signedPowerSum A A w D - C 2 * signedPowerSum A E w D := by
  classical
  dsimp only
  let d := p / 2
  let k := A.card - 2
  let D := d + k
  let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
  have hodd : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hshift : ∀ (U : Finset (ZMod p)) (j : ℕ),
      ((signedPowerSum A U w D).comp (X + C b)).coeff j =
        (∑ u ∈ U, Lagrange.nodalWeight A id u * (w u : ZMod p) * (b + u) ^ (D - j)) *
          (D.choose j : ZMod p) := fun U j => by
    simp only [signedPowerSum, Polynomial.sum_comp, mul_comp, C_comp, pow_comp, add_comp, X_comp,
      add_assoc, ← C_add, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow, sum_mul, mul_assoc]
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro j hj
  have hjk : j ≤ k := by dsimp [k]; split_ifs at hj <;> omega
  have hpow : ∀ u ∈ A,
      (if u ∈ E then (-1 : ZMod p) else 1) * (w u : ZMod p) * (b + u) ^ (D - j) =
        (τ : ZMod p) * (b + u) ^ (k - j) := by
    intro u hu
    rw [show D - j = d + (k - j) by dsimp [D]; omega, pow_add]
    by_cases hz : b + u = 0
    · have hu' : -b ∈ A := by simpa [show -b = u by linear_combination -hz] using hu
      have hj' : j < k := by dsimp [k]; simpa [hu'] using hj
      simp [hz, zero_pow (show k - j ≠ 0 by omega)]
    · have hc := quadraticChar_eq_pow_of_char_ne_two' hodd (b + u)
      rw [ZMod.card] at hc
      change (quadraticChar (ZMod p) (b + u) : ZMod p) = (b + u) ^ d at hc
      rw [← hc]
      have hsign : ((if u ∈ E then (-1 : ℤ) else 1) * w u) * quadraticChar (ZMod p) (b + u) = τ := by
        have hq := quadraticChar_dichotomy hz
        dsimp [E]
        simp only [mem_filter, hu, true_and]
        rcases hw u hu with h1 | h1 <;> rcases hq with h2 | h2 <;> rcases hτ with rfl | rfl <;>
          simp [h1, h2]
      have hcast : (if u ∈ E then (-1 : ZMod p) else 1) * (w u : ZMod p) *
          (quadraticChar (ZMod p) (b + u) : ZMod p) = (τ : ZMod p) := by
        have h := congrArg (Int.cast (R := ZMod p)) hsign
        simpa only [Int.cast_mul, apply_ite (Int.cast (R := ZMod p)), Int.cast_neg, Int.cast_one]
          using h
      calc (if u ∈ E then (-1 : ZMod p) else 1) * (w u : ZMod p) *
              ((quadraticChar (ZMod p) (b + u) : ZMod p) * (b + u) ^ (k - j))
          = ((if u ∈ E then (-1 : ZMod p) else 1) * (w u : ZMod p) *
              (quadraticChar (ZMod p) (b + u) : ZMod p)) * (b + u) ^ (k - j) := by ring
        _ = (τ : ZMod p) * (b + u) ^ (k - j) := by rw [hcast]
  have hsum : (∑ u ∈ A, Lagrange.nodalWeight A id u * (w u : ZMod p) * (b + u) ^ (D - j)) -
      2 * (∑ u ∈ E, Lagrange.nodalWeight A id u * (w u : ZMod p) * (b + u) ^ (D - j)) = 0 := by
    have hmom := nodalWeight_shift_moment A b (show k - j < A.card by dsimp [k]; omega)
    simp only [show k - j ≠ A.card - 1 by dsimp [k]; omega, ↓reduceIte] at hmom
    calc _ = ∑ u ∈ A, Lagrange.nodalWeight A id u *
              ((if u ∈ E then (-1 : ZMod p) else 1) * (w u : ZMod p) * (b + u) ^ (D - j)) := by
            rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun u hu => ?_
            dsimp [E]
            simp only [mem_filter, hu, true_and]
            split_ifs <;> ring
      _ = ∑ u ∈ A, Lagrange.nodalWeight A id u * ((τ : ZMod p) * (b + u) ^ (k - j)) :=
            Finset.sum_congr rfl fun u hu => by rw [hpow u hu]
      _ = (τ : ZMod p) * ∑ u ∈ A, Lagrange.nodalWeight A id u * (b + u) ^ (k - j) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [hmom, mul_zero]
  simp only [sub_comp, mul_comp, C_comp, coeff_sub, coeff_C_mul]
  change ((signedPowerSum A A w D).comp (X + C b)).coeff j -
      2 * ((signedPowerSum A E w D).comp (X + C b)).coeff j = 0
  rw [hshift A j, hshift E j]
  have hfac : ∀ l r t : ZMod p, l * t - 2 * (r * t) = (l - 2 * r) * t := fun _ _ _ => by ring
  rw [hfac, hsum, zero_mul]

/-- Local multiplicity lower bound at shift `b` for the arbitrary-sign Hankel determinant. -/
theorem signed_local_dvd (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) {h : ℕ} (hh : 2 * (h + 1) ≤ A.card)
    (b : ZMod p) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
    let ν := if -b ∈ A then A.card - 2 else A.card - 1
    let r := h + 1 - E.card
    (X - C b) ^ (r * (ν - 2 * h) + r * (r - 1)) ∣ signedDet A w h := by
  classical
  dsimp only
  let D := p / 2 + (A.card - 2)
  let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
  let ν := if -b ∈ A then A.card - 2 else A.card - 1
  obtain ⟨v, hv⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hD_lt : D < p := by dsimp [D]; omega
  have h2h_le : 2 * h ≤ D := by dsimp [D]; omega
  have h2h_nu : 2 * h ≤ ν := by dsimp [ν]; split_ifs <;> omega
  have hunit : ∀ k ≤ 2 * h, (D.descFactorial k : ZMod p) ≠ 0 := fun k hk =>
    descFactorial_ne_zero_zmod hD_lt (hk.trans h2h_le)
  let site (i : Fin E.card) : ZMod p := (E.equivFin.symm i).1
  let coef (i : Fin E.card) : ZMod p :=
    2 * (Lagrange.nodalWeight A id (site i) * (w (site i) : ZMod p))
  have hsum : (∑ i : Fin E.card, C (coef i) * (X + C (site i)) ^ D) =
      C 2 * signedPowerSum A E w D := by
    let g (u : ZMod p) : (ZMod p)[X] :=
      C (2 * (Lagrange.nodalWeight A id u * (w u : ZMod p))) * (X + C u) ^ D
    change (∑ i, g (E.equivFin.symm i).1) = _
    rw [E.equivFin.symm.sum_comp (fun u : E => g u.1), Finset.sum_coe_sort E g]
    simp only [g, map_mul, map_ofNat, signedPowerSum, Finset.mul_sum, mul_assoc]
  apply PaleyDefectMinor.pow_dvd_normalizedHankel_of_contact
    (signedPowerSum A A w D) (X - C b) site coef D h (ν - 2 * h) h2h_le hunit
  rw [hsum, Nat.sub_add_cancel h2h_nu]
  exact signed_minority_contact hp A w hw ha b hτ

private theorem signed_row_excess (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (b : ZMod p) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
    let z : ℕ := if -b ∈ A then 1 else 0
    τ * signedShiftSum A w b = (A.card : ℤ) - z - 2 * E.card := by
  classical
  dsimp only
  let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
  unfold signedShiftSum
  rw [Finset.mul_sum]
  have hpt : ∀ u ∈ A, τ * (w u * quadraticChar (ZMod p) (b + u)) =
      (1 : ℤ) - (if u = -b then 1 else 0) - 2 * (if u ∈ E then 1 else 0) := by
    intro u hu
    by_cases hz : b + u = 0
    · have hub : u = -b := by linear_combination hz
      have hnotE : u ∉ E := by
        simp only [E, mem_filter, hz, MulChar.map_zero, mul_zero]
        rcases hτ with rfl | rfl <;> omega
      rw [hz, MulChar.map_zero, mul_zero, mul_zero]
      simp only [hub, ↓reduceIte, sub_self]
      simp only [← hub, hnotE, ↓reduceIte, mul_zero, sub_zero]
    · have hub : u ≠ -b := fun h => hz (by rw [h, add_neg_cancel])
      have hq := quadraticChar_dichotomy hz
      simp only [E, mem_filter, hu, true_and, hub, ↓reduceIte]
      rcases hw u hu with h1 | h1 <;> rcases hq with h2 | h2 <;> rcases hτ with rfl | rfl <;>
        simp [h1, h2]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  have hz_eq : ∑ u ∈ A, (if u = -b then (1 : ℤ) else 0) = if -b ∈ A then 1 else 0 := by
    rw [Finset.sum_ite_eq']
  have hE_eq : ∑ u ∈ A, (if u ∈ E then (1 : ℤ) else 0) = (E.card : ℤ) := by
    rw [← Finset.sum_filter, show A.filter (fun u => u ∈ E) = E by
      ext u; simp only [E, mem_filter]; tauto, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hz_eq, hE_eq]
  change (A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * (E.card : ℤ) =
    (A.card : ℤ) - ((if -b ∈ A then (1 : ℕ) else 0 : ℕ) : ℤ) - 2 * (E.card : ℤ)
  split_ifs <;> simp

/-- **Finite signed row estimate (Equation (1) of `paley-signed-square-root.md`)**:
For every odd prime `p`, every `A ⊆ ZMod p` with `2 ≤ |A| ≤ (p - 1)/2 + 1`, every individual sign
assignment `w u ∈ {±1}` on `A`, and every `1 ≤ x ≤ ⌊|A| / 2⌋`,
`∑ t : ZMod p, max 0 (W_w(t)^2 - (|A| - z_t - 2x)^2) ≤ 4 * D_x`. -/
theorem signed_row_estimate (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) {x : ℕ} (hx : 1 ≤ x) (hx' : 2 * x ≤ A.card) :
    ∑ b : ZMod p,
        max (0 : ℤ) ((signedShiftSum A w b) ^ 2 -
          ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2) ≤
      4 * (degreeBudget (p / 2) A.card x (minorityCount A w) : ℤ) := by
  classical
  let h := x - 1
  have hx_eq : h + 1 = x := by dsimp [h]; omega
  obtain ⟨hdet_ne, hdet_deg⟩ :=
    signedDet_ne_zero_and_natDegree_le hp A w hw ha ha' (h := h) (by omega)
  rw [hx_eq] at hdet_deg
  have hpt : ∀ b : ZMod p,
      max (0 : ℤ) ((signedShiftSum A w b) ^ 2 -
        ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2) ≤
      4 * ((signedDet A w h).rootMultiplicity b : ℤ) := by
    intro b
    let W := signedShiftSum A w b
    let τ : ℤ := if 0 ≤ W then 1 else -1
    have hτ : τ = 1 ∨ τ = -1 := by dsimp [τ]; split_ifs <;> simp
    have hτW_nn : 0 ≤ τ * W := by dsimp [τ]; split_ifs <;> nlinarith
    have hτW_sq : (τ * W) ^ 2 = W ^ 2 := by rcases hτ with h1 | h1 <;> rw [h1] <;> ring
    let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
    let z : ℕ := if -b ∈ A then 1 else 0
    have hrow := signed_row_excess A w hw b hτ
    change τ * W = (A.card : ℤ) - (z : ℤ) - 2 * E.card at hrow
    let ν := if -b ∈ A then A.card - 2 else A.card - 1
    let r := x - E.card
    have hdvd := signed_local_dvd hp A w hw ha ha' (h := h) (by omega) b hτ
    have hord : r * (ν - 2 * h) + r * (r - 1) ≤ (signedDet A w h).rootMultiplicity b :=
      (le_rootMultiplicity_iff hdet_ne).mpr (by simpa [r, ν, E, hx_eq] using hdvd)
    have hordZ : (4 : ℤ) * ((r * (ν - 2 * h) + r * (r - 1) : ℕ) : ℤ) ≤
        4 * ((signedDet A w h).rootMultiplicity b : ℤ) := by exact_mod_cast Nat.mul_le_mul_left 4 hord
    refine le_trans ?_ hordZ
    have hz_eq : (z : ℤ) = if -b ∈ A then 1 else 0 := by dsimp [z]; split_ifs <;> simp
    rw [← hz_eq]
    by_cases he : E.card < x
    · have h2h_nu : 2 * h ≤ ν := by dsimp [ν, h]; split_ifs <;> omega
      have hr_pos : 1 ≤ r := by dsimp [r]; omega
      have hnu_eq : (ν : ℤ) = (A.card : ℤ) - 1 - (z : ℤ) := by
        dsimp [ν, z]; split_ifs <;> omega
      have hident : (4 : ℤ) * ((r * (ν - 2 * h) + r * (r - 1) : ℕ) : ℤ) =
          W ^ 2 - ((A.card : ℤ) - (z : ℤ) - 2 * x) ^ 2 := by
        rw [← hτW_sq, hrow]
        zify [h2h_nu, hr_pos, show E.card ≤ x by omega, show 1 ≤ x by omega]
        rw [hnu_eq]
        have hhZ : (h : ℤ) = (x : ℤ) - 1 := by dsimp [h]; omega
        have hrZ : (r : ℤ) = (x : ℤ) - (E.card : ℤ) := by dsimp [r]; omega
        rw [hhZ, hrZ]; ring
      rw [hident]
      have hnn : 0 ≤ (4 : ℤ) * ((r * (ν - 2 * h) + r * (r - 1) : ℕ) : ℤ) := by positivity
      rw [hident] at hnn
      exact max_le hnn le_rfl
    · have hge : x ≤ E.card := not_lt.mp he
      have hsq_le : W ^ 2 ≤ ((A.card : ℤ) - (z : ℤ) - 2 * x) ^ 2 := by
        rw [← hτW_sq, hrow]
        have hle1 : (A.card : ℤ) - (z : ℤ) - 2 * (E.card : ℤ) ≤
            (A.card : ℤ) - (z : ℤ) - 2 * (x : ℤ) := by omega
        have hnn1 : 0 ≤ (A.card : ℤ) - (z : ℤ) - 2 * (E.card : ℤ) := hrow ▸ hτW_nn
        exact pow_le_pow_left₀ hnn1 hle1 2
      have hmax0 : max (0 : ℤ) (W ^ 2 - ((A.card : ℤ) - (z : ℤ) - 2 * x) ^ 2) = 0 :=
        max_eq_left (by linarith)
      rw [hmax0]
      positivity
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ (univ : Finset (ZMod p))) => hpt b
  rw [← Finset.mul_sum, ← Nat.cast_sum] at hsum
  have hcap := (Polynomial.sum_rootMultiplicity_le_natDegree (W := signedDet A w h) univ).trans hdet_deg
  exact hsum.trans (by exact_mod_cast Nat.mul_le_mul_left 4 hcap)

private theorem sum_quadraticChar_mul_shift (hp : p ≠ 2) {u v : ZMod p} (huv : u ≠ v) :
    ∑ b : ZMod p, quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v) = -1 := by
  classical
  have hodd : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  set δ : ZMod p := v - u
  have hδ : δ ≠ 0 := sub_ne_zero.mpr huv.symm
  -- Substitute `y = b + u`:
  have h1 : ∑ b : ZMod p, quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v) =
      ∑ y : ZMod p, quadraticChar (ZMod p) y * quadraticChar (ZMod p) (y + δ) := by
    refine Fintype.sum_equiv (Equiv.addRight u) _ _ fun b => ?_
    simp [δ, add_assoc]
  rw [h1, ← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)), MulChar.map_zero, zero_mul, zero_add]
  -- On `y ≠ 0`, `χ(y) * χ(y + δ) = χ(1 + δ * y⁻¹)`:
  have h2 : ∑ y ∈ univ.erase (0 : ZMod p),
        quadraticChar (ZMod p) y * quadraticChar (ZMod p) (y + δ) =
      ∑ z ∈ univ.erase (1 : ZMod p), quadraticChar (ZMod p) z := by
    refine Finset.sum_nbij' (fun y => 1 + δ * y⁻¹) (fun z => δ * (z - 1)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_erase] at hy ⊢
      refine ⟨fun h => mul_ne_zero hδ (inv_ne_zero hy.1) (by linear_combination h), mem_univ _⟩
    · intro z hz
      rw [mem_erase] at hz ⊢
      exact ⟨mul_ne_zero hδ (inv_ne_zero (sub_ne_zero.mpr hz.1)), mem_univ _⟩
    · intro y hy
      have hy0 : y ≠ 0 := (mem_erase.mp hy).1
      field_simp [hδ, hy0]; ring
    · intro z hz
      have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (mem_erase.mp hz).1
      field_simp [hδ, hz1]; ring
    · intro y hy
      have hy0 : y ≠ 0 := (mem_erase.mp hy).1
      have harg : y * (y + δ) = y ^ 2 * (1 + δ * y⁻¹) := by field_simp [hy0]
      rw [← map_mul, harg, map_mul, quadraticChar_sq_one' hy0, one_mul]
  rw [h2]
  have htot := quadraticChar_sum_zero hodd
  rw [← Finset.add_sum_erase _ _ (mem_univ (1 : ZMod p)), map_one] at htot
  omega

/-- Exact shift-orthogonality second moment for arbitrary site signs `w u ∈ {±1}`:
`∑ b : ZMod p, W_w(b)^2 = p * |A| - (∑ u ∈ A, w u)^2`. -/
theorem sum_sq_signedShiftSum (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) :
    ∑ b : ZMod p, (signedShiftSum A w b) ^ 2 = (p : ℤ) * A.card - (∑ u ∈ A, w u) ^ 2 := by
  classical
  have hsq : ∀ b : ZMod p, (signedShiftSum A w b) ^ 2 =
      ∑ u ∈ A, ∑ v ∈ A, (w u * w v) *
        (quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v)) := fun b => by
    unfold signedShiftSum
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hswap : ∑ u ∈ A, ∑ b : ZMod p, ∑ v ∈ A,
        (w u * w v) * (quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v)) =
      ∑ u ∈ A, ∑ v ∈ A, (w u * w v) *
        ∑ b : ZMod p, quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => (Finset.mul_sum ..).symm
  rw [hswap]
  have hinner : ∀ u ∈ A, ∀ v ∈ A,
      (w u * w v) * (∑ b : ZMod p, quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v)) =
        if u = v then (p : ℤ) - 1 else -(w u * w v) := by
    intro u hu v _
    by_cases huv : u = v
    · subst huv
      simp only [↓reduceIte]
      have hwsq : w u * w u = 1 := by rcases hw u hu with h | h <;> rw [h] <;> ring
      rw [hwsq, one_mul]
      have hdiag : ∑ b : ZMod p, quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + u) =
          (p : ℤ) - 1 := by
        rw [← Finset.add_sum_erase _ _ (mem_univ (-u)), neg_add_cancel, MulChar.map_zero,
          mul_zero, zero_add]
        have hones : ∑ b ∈ univ.erase (-u),
            quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + u) =
            ∑ _b ∈ univ.erase (-u), (1 : ℤ) := by
          refine Finset.sum_congr rfl fun b hb => ?_
          have hne : b + u ≠ 0 := fun h => (mem_erase.mp hb).1 (by linear_combination h)
          simpa [pow_two] using quadraticChar_sq_one hne
        rw [hones, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_erase_of_mem (mem_univ (-u)), Finset.card_univ, ZMod.card]
        have := (Fact.out : p.Prime).pos
        omega
      exact hdiag
    · simp only [huv, ↓reduceIte, sum_quadraticChar_mul_shift hp huv]; ring
  have hsplit : ∑ u ∈ A, ∑ v ∈ A,
        (w u * w v) * (∑ b : ZMod p, quadraticChar (ZMod p) (b + u) * quadraticChar (ZMod p) (b + v)) =
      ∑ u ∈ A, ∑ v ∈ A, ((if u = v then (p : ℤ) else 0) - w u * w v) := by
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [hinner u hu v hv]
    by_cases huv : u = v
    · subst huv
      have hwsq : w u * w u = 1 := by rcases hw u hu with h | h <;> rw [h] <;> ring
      simp [hwsq]
    · simp [huv]
  rw [hsplit]
  simp_rw [Finset.sum_sub_distrib]
  have h1 : ∑ u ∈ A, ∑ v ∈ A, (if u = v then (p : ℤ) else 0) = (p : ℤ) * A.card := by
    have hper : ∀ u ∈ A, ∑ v ∈ A, (if u = v then (p : ℤ) else 0) = (p : ℤ) := fun u hu => by
      simp [Finset.sum_ite_eq, hu]
    rw [Finset.sum_congr rfl hper, Finset.sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ u ∈ A, ∑ v ∈ A, w u * w v = (∑ u ∈ A, w u) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [h1, h2]

/-- Exact sum of central multiplicities `∑ b : ZMod p, ⌊W_w(b)^2 / 4⌋ = D_{⌊|A|/2⌋}`. -/
theorem sum_signed_central_multiplicity (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) :
    ∑ b : ZMod p, ((signedShiftSum A w b) ^ 2 / 4).toNat =
      degreeBudget (p / 2) A.card (A.card / 2) (minorityCount A w) := by
  classical
  let z (b : ZMod p) : ℤ := if -b ∈ A then 1 else 0
  have hz : ∑ b : ZMod p, z b = (A.card : ℤ) := by
    change (∑ b : ZMod p, (fun u : ZMod p => if u ∈ A then (1 : ℤ) else 0) ((Equiv.neg _) b)) = _
    refine ((Equiv.neg (ZMod p)).bijective.sum_comp
      (fun u => if u ∈ A then (1 : ℤ) else 0)).trans ?_
    rw [Finset.sum_boole]
    have h : univ.filter (fun i => i ∈ A) = A := by ext; simp
    rw [h]
  have hpar : ∀ b : ZMod p,
      signedShiftSum A w b % 2 = if A.card % 2 = 0 then z b else 1 - z b := fun b => by
    have h := signed_row_excess A w hw b (τ := 1) (Or.inl rfl)
    dsimp only [z] at h ⊢
    rw [one_mul] at h
    split_ifs at h ⊢ <;> omega
  have hpoint : ∀ b : ZMod p,
      4 * (((signedShiftSum A w b) ^ 2 / 4).toNat : ℤ) =
        (signedShiftSum A w b) ^ 2 - (if A.card % 2 = 0 then z b else 1 - z b) := fun b => by
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg (sq_nonneg _) (by decide)), four_mul_floor, hpar]
  have hsum := Finset.sum_congr (s₁ := (univ : Finset (ZMod p))) rfl fun b _ => hpoint b
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_sq_signedShiftSum hp A w hw] at hsum
  -- Relate `(∑ u ∈ A, w u)^2` to `(A.card - 2 * s)^2`:
  let s := minorityCount A w
  have hsum_w_sq : (∑ u ∈ A, w u) ^ 2 = ((A.card : ℤ) - 2 * (s : ℤ)) ^ 2 := by
    let P := A.filter fun u => w u = 1
    let N := A.filter fun u => w u = -1
    have hdisj : Disjoint P N := by rw [Finset.disjoint_filter]; intro u _ h1 h2; omega
    have hunion : P ∪ N = A := by
      ext u; simp only [P, N, mem_union, mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun hu => (hw u hu).imp (And.intro hu) (And.intro hu)⟩
    have hcard : P.card + N.card = A.card := by rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hsw : ∑ u ∈ A, w u = (P.card : ℤ) - (N.card : ℤ) := by
      rw [← hunion, Finset.sum_union hdisj]
      have hP : ∑ u ∈ P, w u = (P.card : ℤ) := by
        rw [Finset.sum_congr rfl fun u hu => (mem_filter.mp hu).2, Finset.sum_const, nsmul_eq_mul,
          mul_one]
      have hN : ∑ u ∈ N, w u = -(N.card : ℤ) := by
        rw [Finset.sum_congr rfl fun u hu => (mem_filter.mp hu).2, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [hP, hN]; ring
    rw [hsw]
    have hs_eq : s = min P.card N.card := rfl
    rcases le_total P.card N.card with hle | hle
    · have hs : s = P.card := by rw [hs_eq, min_eq_left hle]
      rw [hs]; have : (P.card : ℤ) + N.card = A.card := by exact_mod_cast hcard
      nlinarith
    · have hs : s = N.card := by rw [hs_eq, min_eq_right hle]
      rw [hs]; have : (P.card : ℤ) + N.card = A.card := by exact_mod_cast hcard
      nlinarith
  rw [hsum_w_sq] at hsum
  obtain ⟨d, hd⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hd_eq : p / 2 = d := by omega
  let x := A.card / 2
  have hs_le_x : s ≤ x := by
    let P := A.filter fun u => w u = 1
    let N := A.filter fun u => w u = -1
    have hdisj : Disjoint P N := by rw [Finset.disjoint_filter]; intro u _ h1 h2; omega
    have hunion : P ∪ N = A := by
      ext u; simp only [P, N, mem_union, mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun hu => (hw u hu).imp (And.intro hu) (And.intro hu)⟩
    have hcard : P.card + N.card = A.card := by rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have : 2 * min P.card N.card ≤ P.card + N.card := by omega
    change min P.card N.card ≤ A.card / 2
    omega
  have hbudget_le : (x - s) * (A.card - x - s) ≤ x * (d + A.card - 2 * x) := by
    have h1 : x - s ≤ x := Nat.sub_le _ _
    have h2 : A.card - x - s ≤ d + A.card - 2 * x := by omega
    exact Nat.mul_le_mul h1 h2
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sum, hd_eq]
  unfold degreeBudget
  rw [Nat.cast_sub hbudget_le, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (show 2 * x ≤ d + A.card by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub hs_le_x, Nat.cast_sub (show s ≤ A.card - x by omega),
    Nat.cast_sub (show x ≤ A.card by omega)]
  have hpZ : (p : ℤ) = 2 * d + 1 := by exact_mod_cast hd
  by_cases ha_par : A.card % 2 = 0
  · simp only [ha_par, ↓reduceIte, hz] at hsum
    have haZ : (A.card : ℤ) = 2 * x := by exact_mod_cast (show A.card = 2 * x by dsimp [x]; omega)
    rw [hpZ] at hsum
    rw [haZ] at hsum ⊢
    nlinarith only [hsum]
  · simp only [ha_par, ↓reduceIte, Finset.sum_sub_distrib, hz, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one] at hsum
    have haZ : (A.card : ℤ) = 2 * x + 1 := by
      exact_mod_cast (show A.card = 2 * x + 1 by dsimp [x]; omega)
    rw [hpZ] at hsum
    rw [haZ] at hsum ⊢
    nlinarith only [hsum]

/-- **Complete arbitrary-sign central factorization**:
At width `x = ⌊|A|/2⌋`, `signedDet A w (|A|/2 - 1)` factors completely over `ZMod p` with exact
root multiplicity `⌊W_w(b)^2 / 4⌋` at every `b ∈ ZMod p`. -/
theorem signed_central_factorization (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) :
    let P := signedDet A w (A.card / 2 - 1)
    P = C P.leadingCoeff * ∏ b : ZMod p, (X - C b) ^ ((signedShiftSum A w b) ^ 2 / 4).toNat := by
  classical
  let h := A.card / 2 - 1
  let P := signedDet A w h
  have hx : h + 1 = A.card / 2 := by dsimp [h]; omega
  obtain ⟨hP_ne, hP_deg_le⟩ :=
    signedDet_ne_zero_and_natDegree_le hp A w hw ha ha' (h := h) (by omega)
  rw [hx] at hP_deg_le
  have hlocal : ∀ b : ZMod p, (X - C b) ^ ((signedShiftSum A w b) ^ 2 / 4).toNat ∣ P := by
    intro b
    let W := signedShiftSum A w b
    let τ : ℤ := if 0 ≤ W then 1 else -1
    have hτ : τ = 1 ∨ τ = -1 := by dsimp [τ]; split_ifs <;> simp
    have hτW_nn : 0 ≤ τ * W := by dsimp [τ]; split_ifs <;> nlinarith
    have hτW_sq : (τ * W) ^ 2 = W ^ 2 := by rcases hτ with h1 | h1 <;> rw [h1] <;> ring
    let E := A.filter fun u => w u * quadraticChar (ZMod p) (b + u) = -τ
    let z : ℕ := if -b ∈ A then 1 else 0
    have hrow := signed_row_excess A w hw b hτ
    have hz_le : z ≤ 1 := by dsimp [z]; split_ifs <;> decide
    have hquota := quota_of_minority ha hz_le hrow hτW_nn
    rw [hτW_sq] at hquota
    have hnu : A.card - 1 - z = if -b ∈ A then A.card - 2 else A.card - 1 := by
      dsimp [z]; split_ifs <;> omega
    rw [hnu] at hquota
    rw [hquota]
    exact signed_local_dvd hp A w hw ha ha' (h := h) (by omega) b hτ
  have hsum_ord : ∑ b : ZMod p, ((signedShiftSum A w b) ^ 2 / 4).toNat ≤ P.natDegree := by
    refine (Finset.sum_le_sum fun b _ => (le_rootMultiplicity_iff hP_ne).mpr (hlocal b)).trans ?_
    exact Polynomial.sum_rootMultiplicity_le_natDegree (W := P) univ
  rw [sum_signed_central_multiplicity hp A w hw ha ha'] at hsum_ord
  have hdeg_eq : P.natDegree = ∑ b : ZMod p, ((signedShiftSum A w b) ^ 2 / 4).toNat := by
    rw [sum_signed_central_multiplicity hp A w hw ha ha']
    exact le_antisymm hP_deg_le hsum_ord
  exact eq_leadingCoeff_mul_prod_of_local_dvd P univ _ hdeg_eq fun b _ => hlocal b

/-- Exact root multiplicity of the arbitrary-sign central determinant at every `b ∈ ZMod p`. -/
theorem signed_central_rootMultiplicity (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) (b : ZMod p) :
    (signedDet A w (A.card / 2 - 1)).rootMultiplicity b = ((signedShiftSum A w b) ^ 2 / 4).toNat := by
  classical
  let h := A.card / 2 - 1
  let P := signedDet A w h
  have hx : h + 1 = A.card / 2 := by dsimp [h]; omega
  obtain ⟨hP_ne, hP_deg_le⟩ :=
    signedDet_ne_zero_and_natDegree_le hp A w hw ha ha' (h := h) (by omega)
  rw [hx] at hP_deg_le
  have hfac := signed_central_factorization hp A w hw ha ha'
  have hle : ∀ c : ZMod p, ((signedShiftSum A w c) ^ 2 / 4).toNat ≤ P.rootMultiplicity c := fun c =>
    (le_rootMultiplicity_iff hP_ne).mpr (by
      dsimp only at hfac
      rw [hfac]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (mem_univ c)) _)
  apply le_antisymm _ (hle b)
  by_contra hlt
  have hstrict := Finset.sum_lt_sum (s := (univ : Finset (ZMod p))) (fun c _ => hle c)
    ⟨b, mem_univ b, lt_of_not_ge hlt⟩
  have hcap : ∑ c : ZMod p, P.rootMultiplicity c ≤ P.natDegree :=
    Polynomial.sum_rootMultiplicity_le_natDegree (W := P) univ
  have hdeg_le : P.natDegree ≤ degreeBudget (p / 2) A.card (A.card / 2) (minorityCount A w) :=
    hP_deg_le
  rw [sum_signed_central_multiplicity hp A w hw ha ha'] at hstrict
  omega

end RowEstimateAndFactorization

/-! ## 4. Prescribed signed rectangle bounds (`p = 65537` and asymptotic `√3 / 2`) -/

section SignedRectangle

variable {p : ℕ} [Fact p.Prime]

/-- Finite row-square ceiling on any prescribed target set `B` with arbitrary source signs `w`. -/
theorem signed_row_sum_sq_le (hp : p ≠ 2) (A B : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) {x : ℕ} (hx : 1 ≤ x) (hx' : 2 * x ≤ A.card) :
    ∑ b ∈ B, (signedShiftSum A w b) ^ 2 ≤
      ∑ b ∈ B, ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 +
        4 * (degreeBudget (p / 2) A.card x (minorityCount A w) : ℤ) := by
  have h1 : ∑ b ∈ B, (signedShiftSum A w b) ^ 2 ≤
      ∑ b ∈ B, (((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 +
        max (0 : ℤ) ((signedShiftSum A w b) ^ 2 -
          ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2)) :=
    Finset.sum_le_sum fun b _ => by
      have hle := le_max_right (0 : ℤ) ((signedShiftSum A w b) ^ 2 -
        ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2)
      linarith
  rw [Finset.sum_add_distrib] at h1
  have hsub : ∑ b ∈ B, max (0 : ℤ) ((signedShiftSum A w b) ^ 2 -
        ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2) ≤
      ∑ b : ZMod p, max (0 : ℤ) ((signedShiftSum A w b) ^ 2 -
        ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ B) fun _ _ _ => le_max_left _ _
  linarith [h1, hsub, signed_row_estimate hp A w hw ha ha' hx hx']

/-- **Exact prescribed signed rectangle inequality (difference convention `χ(u - t)`)**:
retains both the overlap indicator `z_t = 1_{t ∈ A}` and the minority correction `D_x`. -/
theorem signed_rectangle_sq_le_exact (hp : p ≠ 2) (A B : Finset (ZMod p)) (w v : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (hv : ∀ t ∈ B, |v t| ≤ 1)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) {x : ℕ} (hx : 1 ≤ x) (hx' : 2 * x ≤ A.card) :
    (∑ u ∈ A, ∑ t ∈ B, w u * v t * quadraticChar (ZMod p) (u - t)) ^ 2 ≤
      (B.card : ℤ) * (∑ t ∈ B, ((A.card : ℤ) - (if t ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 +
        4 * (degreeBudget (p / 2) A.card x (minorityCount A w) : ℤ)) := by
  classical
  let B' := B.image Neg.neg
  have hB'_card : B'.card = B.card := Finset.card_image_of_injective B neg_injective
  have hsum_eq : ∑ u ∈ A, ∑ t ∈ B, w u * v t * quadraticChar (ZMod p) (u - t) =
      ∑ b ∈ B', v (-b) * signedShiftSum A w b := by
    rw [Finset.sum_comm, Finset.sum_image (fun _ _ _ _ h => neg_inj.mp h)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [neg_neg, signedShiftSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show -t + u = u - t by ring]; ring
  rw [hsum_eq]
  have hcs : (∑ b ∈ B', v (-b) * signedShiftSum A w b) ^ 2 ≤
      (B'.card : ℤ) * ∑ b ∈ B', (v (-b) * signedShiftSum A w b) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hv_sq : ∑ b ∈ B', (v (-b) * signedShiftSum A w b) ^ 2 ≤
      ∑ b ∈ B', (signedShiftSum A w b) ^ 2 := by
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hb
    rw [neg_neg, mul_pow]
    have hv1 : (v t) ^ 2 ≤ 1 := by
      have h1 := hv t ht
      rw [← sq_abs]
      nlinarith [abs_nonneg (v t)]
    nlinarith [sq_nonneg (signedShiftSum A w (-t))]
  have hrow := signed_row_sum_sq_le hp A B' w hw ha ha' hx hx'
  have hbase_eq : ∑ b ∈ B', ((A.card : ℤ) - (if -b ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 =
      ∑ t ∈ B, ((A.card : ℤ) - (if t ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 := by
    rw [Finset.sum_image (fun _ _ _ _ h => neg_inj.mp h)]
    refine Finset.sum_congr rfl fun t _ => by rw [neg_neg]
  rw [hbase_eq] at hrow
  rw [hB'_card] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left (hv_sq.trans hrow) (Int.natCast_nonneg _))

/-- **Simplified prescribed signed rectangle inequality** for `2 * x < A.card`:
`(∑ u ∈ A, ∑ t ∈ B, w u * v t * χ(u - t))^2 ≤ |B|^2 * (|A| - 2x)^2 + 4 * |B| * x * (p/2 + |A| - 2x)`. -/
theorem signed_rectangle_sq_le (hp : p ≠ 2) (A B : Finset (ZMod p)) (w v : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (hv : ∀ t ∈ B, |v t| ≤ 1)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) {x : ℕ} (hx : 1 ≤ x) (hx' : 2 * x < A.card) :
    (∑ u ∈ A, ∑ t ∈ B, w u * v t * quadraticChar (ZMod p) (u - t)) ^ 2 ≤
      (B.card : ℤ) ^ 2 * ((A.card : ℤ) - 2 * x) ^ 2 +
        4 * (B.card : ℤ) * ((x * (p / 2 + A.card - 2 * x) : ℕ) : ℤ) := by
  have hex := signed_rectangle_sq_le_exact hp A B w v hw hv ha ha' hx hx'.le
  have hbase : ∑ t ∈ B, ((A.card : ℤ) - (if t ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 ≤
      (B.card : ℤ) * ((A.card : ℤ) - 2 * x) ^ 2 := by
    calc _ ≤ ∑ _t ∈ B, ((A.card : ℤ) - 2 * x) ^ 2 := by
            refine Finset.sum_le_sum fun t _ => ?_
            split_ifs
            · exact pow_le_pow_left₀ (by omega) (by omega) 2
            · simp
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hbud : (degreeBudget (p / 2) A.card x (minorityCount A w) : ℤ) ≤
      ((x * (p / 2 + A.card - 2 * x) : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le (x * (p / 2 + A.card - 2 * x)) _
  have hBnn : (0 : ℤ) ≤ B.card := Int.natCast_nonneg _
  have hstep : (B.card : ℤ) * (∑ t ∈ B, ((A.card : ℤ) - (if t ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 +
        4 * (degreeBudget (p / 2) A.card x (minorityCount A w) : ℤ)) ≤
      (B.card : ℤ) * ((B.card : ℤ) * ((A.card : ℤ) - 2 * x) ^ 2 +
        4 * ((x * (p / 2 + A.card - 2 * x) : ℕ) : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hBnn
  calc _ ≤ _ := hex.trans hstep
    _ = _ := by ring

local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- Concrete signed finite bound at `p = 65537`: for EVERY two 256-site sets `A, B ⊆ ZMod 65537`
and EVERY vertex signs `w, v ∈ {±1}`, `|∑ u ∈ A, ∑ t ∈ B, w u * v t * χ(u - t)| ≤ 56,829`. -/
theorem signed_discrepancy_65537 (A B : Finset (ZMod 65537)) (w v : ZMod 65537 → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) (hv : ∀ t ∈ B, |v t| ≤ 1)
    (ha : A.card = 256) (hb : B.card = 256) :
    |∑ u ∈ A, ∑ t ∈ B, w u * v t * quadraticChar (ZMod 65537) (u - t)| ≤ 56829 := by
  have h := signed_rectangle_sq_le (p := 65537) (by decide) A B w v hw hv
    (by omega) (by omega) (x := 64) (by decide) (by omega)
  rw [ha, hb] at h
  set s := |∑ u ∈ A, ∑ t ∈ B, w u * v t * quadraticChar (ZMod 65537) (u - t)|
  have hs_sq : s ^ 2 ≤ 3229614080 := by
    have hsq : s ^ 2 = (∑ u ∈ A, ∑ t ∈ B, w u * v t * quadraticChar (ZMod 65537) (u - t)) ^ 2 :=
      sq_abs _
    rw [hsq]
    exact h
  by_contra! hgt
  have hbig : (56830 : ℤ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by decide) (by omega) 2
  omega

/-- Envelope for arbitrary-sign balanced rectangles, tending to `3 / 4` as `a, b ~ √p`. -/
noncomputable def signedEnvelope (p a b : ℝ) : ℝ :=
  (1 / 2 + 2 / a) ^ 2 + (p / 2 + a / 2 + 2) / (a * b)

theorem signed_quarter_bound {a b p : ℕ} {s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (H : s ^ 2 ≤ (b : ℝ) ^ 2 * ((a : ℝ) - 2 * ((a / 4 : ℕ) : ℝ)) ^ 2 +
      4 * (b : ℝ) * (((a / 4 * (p / 2 + a - 2 * (a / 4)) : ℕ) : ℝ))) :
    (s / ((a : ℝ) * b)) ^ 2 ≤ signedEnvelope p a b := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have h₁ : 4 * ((a / 4 : ℕ) : ℝ) ≤ a := by exact_mod_cast (show 4 * (a / 4) ≤ a by omega)
  have h₂ : (a : ℝ) ≤ 4 * ((a / 4 : ℕ) : ℝ) + 3 := by
    exact_mod_cast (show a ≤ 4 * (a / 4) + 3 by omega)
  have h₃ : ((p / 2 + a - 2 * (a / 4) : ℕ) : ℝ) ≤ (p : ℝ) / 2 + (a : ℝ) / 2 + 2 := by
    have hnat : 2 * (p / 2 + a - 2 * (a / 4)) ≤ p + a + 4 := by omega
    have hR : (2 : ℝ) * ((p / 2 + a - 2 * (a / 4) : ℕ) : ℝ) ≤ (p : ℝ) + (a : ℝ) + 4 := by
      exact_mod_cast hnat
    linarith
  have h₄ : ((a : ℝ) - 2 * ((a / 4 : ℕ) : ℝ)) ^ 2 ≤ ((a : ℝ) / 2 + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h₅ : 4 * ((a / 4 : ℕ) : ℝ) * ((p / 2 + a - 2 * (a / 4) : ℕ) : ℝ) ≤
      (a : ℝ) * ((p : ℝ) / 2 + (a : ℝ) / 2 + 2) :=
    mul_le_mul h₁ h₃ (by positivity) ha'.le
  have hmajor : s ^ 2 ≤ (b : ℝ) ^ 2 * ((a : ℝ) / 2 + 2) ^ 2 +
      (b : ℝ) * (a : ℝ) * ((p : ℝ) / 2 + (a : ℝ) / 2 + 2) := by
    rw [Nat.cast_mul] at H
    nlinarith only [H, mul_le_mul_of_nonneg_left h₄ (sq_nonneg (b : ℝ)),
      mul_le_mul_of_nonneg_left h₅ hb'.le]
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos (mul_pos ha' hb'))]
  convert hmajor using 1
  unfold signedEnvelope
  field_simp

theorem tendsto_signedEnvelope {p a b : ℕ → ℝ} (hp : Tendsto p atTop atTop)
    (ha : Tendsto (fun n => a n / Real.sqrt (p n)) atTop (𝓝 1))
    (hb : Tendsto (fun n => b n / Real.sqrt (p n)) atTop (𝓝 1)) :
    Tendsto (fun n => signedEnvelope (p n) (a n) (b n)) atTop (𝓝 (3 / 4)) := by
  have hp' := hp.eventually_gt_atTop 0
  have hr := Real.tendsto_sqrt_atTop.comp hp
  have ha' : Tendsto a atTop atTop :=
    (ha.pos_mul_atTop (by norm_num) hr).congr' (by
      filter_upwards [hp'] with n hn
      exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hn).ne')
  have hb' : Tendsto b atTop atTop :=
    (hb.pos_mul_atTop (by norm_num) hr).congr' (by
      filter_upwards [hp'] with n hn
      exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hn).ne')
  have hden := ha.mul hb
  have hfirst := ((tendsto_const_nhds (x := (1 / 2 : ℝ))).add
    ((tendsto_inv_atTop_zero.comp ha').const_mul 2)).pow 2
  have hterm1 : Tendsto (fun n => (1 / 2 : ℝ) / ((a n / Real.sqrt (p n)) * (b n / Real.sqrt (p n))))
      atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun n => (1 / 2 : ℝ) / ((a n / Real.sqrt (p n)) * (b n / Real.sqrt (p n))))
        atTop (𝓝 ((1 / 2 : ℝ) / (1 * 1))) :=
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).div hden (by norm_num)
    simpa only [mul_one, div_one] using h1
  have hterm2 : Tendsto (fun n => (1 / 2 : ℝ) * (b n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hb').const_mul (1 / 2 : ℝ)
  have hterm3 : Tendsto (fun n => (2 : ℝ) * (a n * b n)⁻¹) atTop (𝓝 0) := by
    have hab : Tendsto (fun n => a n * b n) atTop atTop := ha'.atTop_mul_atTop₀ hb'
    simpa using (tendsto_inv_atTop_zero.comp hab).const_mul (2 : ℝ)
  have hlim : Tendsto (fun n =>
      (1 / 2 + 2 * (a n)⁻¹) ^ 2 +
        ((1 / 2 : ℝ) / ((a n / Real.sqrt (p n)) * (b n / Real.sqrt (p n))) +
          ((1 / 2 : ℝ) * (b n)⁻¹ + 2 * (a n * b n)⁻¹))) atTop (𝓝 (3 / 4)) := by
    have hsum := hfirst.add (hterm1.add (hterm2.add hterm3))
    have hval : (1 / 2 + 2 * (0 : ℝ)) ^ 2 + ((1 / 2 : ℝ) + (0 + 0)) = 3 / 4 := by norm_num
    rw [hval] at hsum
    exact hsum
  refine hlim.congr' ?_
  filter_upwards [hp', ha.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hb.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn han hbn
  have ha0 : a n ≠ 0 := by intro h; simp [h] at han
  have hb0 : b n ≠ 0 := by intro h; simp [h] at hbn
  have hrp := Real.sq_sqrt hn.le
  have hrn := (Real.sqrt_pos.mpr hn).ne'
  dsimp [signedEnvelope]
  field_simp [ha0, hb0, hn.ne', hrn]
  rw [hrp]
  ring

/-- **Asymptotic arbitrary-sign balanced square-root bound**:
along any sequence of primes `p n → ∞` with `|A n|, |B n| ~ √(p n)` and ARBITRARY vertex signs
`w n u ∈ {±1}`, `|v n t| ≤ 1`, the relative signed discrepancy is eventually `< √3 / 2 + ε`. -/
theorem eventually_signed_balanced_discrepancy (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (A B : (n : ℕ) → Finset (ZMod (p n)))
    (w v : (n : ℕ) → ZMod (p n) → ℤ)
    (hw : ∀ n, ∀ u ∈ A n, w n u = 1 ∨ w n u = -1)
    (hv : ∀ n, ∀ t ∈ B n, |v n t| ≤ 1)
    (hp : Tendsto p atTop atTop)
    (ha : Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt (p n)) atTop (𝓝 1))
    (hb : Tendsto (fun n => ((B n).card : ℝ) / Real.sqrt (p n)) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (|∑ u ∈ A n, ∑ t ∈ B n, w n u * v n t * quadraticChar (ZMod (p n)) (u - t)| : ℝ) /
        ((A n).card * (B n).card : ℝ) < Real.sqrt 3 / 2 + ε := by
  have hpR : Tendsto (fun n => (p n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hp
  have hr := Real.tendsto_sqrt_atTop.comp hpR
  have hlim := (Real.continuous_sqrt.tendsto (3 / 4)).comp (tendsto_signedEnvelope hpR ha hb)
  have heq : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε)),
    hr.eventually_ge_atTop 8, ha.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    ha.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    hb.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), hp.eventually_gt_atTop 2]
    with n hlimn hrn hla hua hlb hpn
  dsimp at hrn hla hua hlb hlimn
  let a := (A n).card
  let b := (B n).card
  let s := ∑ u ∈ A n, ∑ t ∈ B n, w n u * v n t * quadraticChar (ZMod (p n)) (u - t)
  have hrpos : 0 < Real.sqrt (p n) := by linarith
  have hla' := (lt_div_iff₀ hrpos).mp hla
  have hua' := (div_lt_iff₀ hrpos).mp hua
  have hlb' := (lt_div_iff₀ hrpos).mp hlb
  have ha4 : 4 ≤ a := by
    have : (4 : ℝ) ≤ (A n).card := by linarith
    exact_mod_cast this
  have hb1 : 0 < b := by
    have : (0 : ℝ) < (B n).card := by linarith
    exact_mod_cast this
  have ha2 : 2 * a ≤ p n := by
    have sqr := Real.sq_sqrt (show 0 ≤ (p n : ℝ) by positivity)
    have : 2 * ((A n).card : ℝ) ≤ p n := by
      nlinarith [mul_nonneg hrpos.le (show 0 ≤ Real.sqrt (p n) - 4 by linarith)]
    exact_mod_cast this
  have H := signed_rectangle_sq_le (p := p n) (by omega) (A n) (B n) (w n) (v n)
    (hw n) (hv n) (by change 2 ≤ a; omega) (by change a ≤ p n / 2 + 1; omega)
    (x := a / 4) (by omega) (by change 2 * (a / 4) < a; omega)
  have H' := signed_quarter_bound (s := (|s| : ℝ)) (p := p n) (by omega : 0 < a) hb1 (by
    have hsq : |s| ^ 2 ≤ (b : ℤ) ^ 2 * ((a : ℤ) - 2 * (a / 4 : ℕ)) ^ 2 +
        4 * (b : ℤ) * ((a / 4 * (p n / 2 + a - 2 * (a / 4)) : ℕ) : ℤ) := by
      rw [sq_abs]; exact H
    have hh := (Int.cast_le (R := ℝ)).mpr hsq
    simpa only [Int.cast_pow, Int.cast_abs, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
      Int.cast_sub, Int.cast_add] using hh)
  have hgoal : (|s| : ℝ) / ((a : ℝ) * b) ≤ Real.sqrt (signedEnvelope (p n) a b) :=
    Real.le_sqrt_of_sq_le H'
  simpa only [a, b, s, Int.cast_abs, Int.cast_sum, Int.cast_mul] using hgoal.trans_lt hlimn

end SignedRectangle

end ProximityGap.PaleySignedSquareRoot

#print axioms ProximityGap.PaleySignedSquareRoot.signed_local_dvd
#print axioms ProximityGap.PaleySignedSquareRoot.signed_row_estimate
#print axioms ProximityGap.PaleySignedSquareRoot.sum_sq_signedShiftSum
#print axioms ProximityGap.PaleySignedSquareRoot.sum_signed_central_multiplicity
#print axioms ProximityGap.PaleySignedSquareRoot.signed_central_factorization
#print axioms ProximityGap.PaleySignedSquareRoot.signed_central_rootMultiplicity
#print axioms ProximityGap.PaleySignedSquareRoot.signed_rectangle_sq_le_exact
#print axioms ProximityGap.PaleySignedSquareRoot.signed_rectangle_sq_le
#print axioms ProximityGap.PaleySignedSquareRoot.signed_discrepancy_65537
#print axioms ProximityGap.PaleySignedSquareRoot.eventually_signed_balanced_discrepancy
