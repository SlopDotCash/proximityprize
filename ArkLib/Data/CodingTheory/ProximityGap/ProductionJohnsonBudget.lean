/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProductionRegimeBracket

/-!
# The production Johnson budget, discharged (#357)

`ProductionRegimeBracket.production_good_johnson_of_packageSupply` consumes one
numeric hypothesis: `johnsonBoundReal ≤ ε*`.  This file discharges it at production
shape.  The [Hab25]/T4.12 bound is

  `johnsonBoundReal = ((2(m+½)⁵ + 3(m+½)·δ·ρ₊)/(3·ρ₊^{3/2})·n + (m+½)/ρ₊^{1/2}) / q`

with `m = max(⌈√ρ₊/(2η)⌉, 3)`.  For rates `1/2 ≤ ρ₊` (with `k ≤ n`), `δ ≤ 1`, and
any cap `m ≤ M`:

* `johnsonBoundReal_le_production` — the whole bound is at most
  `(4(M+1)⁵ + 2(M+1))·n / q`;
* `ofReal_johnsonBoundReal_le_production` — hence at `ε* ≥ ofReal` of that ratio
  the budget hypothesis of the bracket holds.  At `M = 64`, `n ≤ 2^{30}` the ratio
  is `≤ 2^{63}/q`, so `q ≥ 2^{192}` suffices for `ε* = 2^{−128}` — comfortably
  inside the `2^{256}` production field.

With this, the Johnson reach of the production bracket is conditional on exactly
ONE object: `CellPackageSupply`.  No numeric residue remains.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.ProductionRegime

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- `(1/2)^{3/2} ≥ 1/4`. -/
private lemma half_rpow_three_half : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ ((3 : ℝ) / 2) := by
  have h1 : (1 / 2 : ℝ) ^ ((2 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
    _ ≤ _ := h1

/-- `(1/2)^{1/2} ≥ 1/2`. -/
private lemma half_rpow_half : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ ((1 : ℝ) / 2) := by
  have h1 : (1 / 2 : ℝ) ^ ((1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  calc (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ ((1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
    _ ≤ _ := h1

/-- **The production Johnson budget.**  For `k ≤ n`, rate `ρ₊ ≥ 1/2`, radius
`δ ≤ 1`, and `m`-quantity capped by `M ≥ 3`, the [Hab25] numeric bound is at most
`(4(M+1)⁵ + 2(M+1))·n / q`. -/
theorem johnsonBoundReal_le_production (domain : Fin n ↪ F) (η δ : ℝ≥0) {k M : ℕ}
    (hM3 : 3 ≤ M) (hkn : k ≤ n)
    (hm : (max (⌈((((k : ℝ) / Fintype.card (Fin n)
        + 1 / Fintype.card (Fin n))) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 ≤ M))
    (hρ : (1 / 2 : ℝ) ≤ (k : ℝ) / Fintype.card (Fin n) + 1 / Fintype.card (Fin n))
    (hδ1 : δ ≤ 1) :
    johnsonBoundReal domain k η δ
      ≤ (((4 * (M + 1) ^ 5 + 2 * (M + 1)) * n : ℕ) : ℝ) / (Fintype.card F : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by
    have := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F)
    exact_mod_cast this
  unfold johnsonBoundReal CodingTheory.rs_epsMCA_johnson_range_boundReal
  simp only [Fintype.card_fin]
  set ρp : ℝ := (k : ℝ) / n + 1 / n with hρp
  set m : ℝ := max (⌈(ρp ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 with hmdef
  rw [Fintype.card_fin] at hm hρ
  have hm3 : (3 : ℝ) ≤ m := le_max_right _ _
  have hmM : m ≤ M := hm
  have hM1 : m + 1 / 2 ≤ (M : ℝ) + 1 := by linarith
  have hm0 : (0 : ℝ) < m + 1 / 2 := by linarith
  have hρ2 : (1 / 2 : ℝ) ≤ ρp := hρ
  have hρ0 : (0 : ℝ) < ρp := by linarith
  have hρtop : ρp ≤ 2 := by
    rw [hρp]
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have h1 : (k : ℝ) / n ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hkn'
    have h2 : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hn1
    linarith
  have hM1R : (4 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    linarith
  -- rpow lower bounds
  have h32 : (1 / 4 : ℝ) ≤ ρp ^ ((3 : ℝ) / 2) :=
    le_trans half_rpow_three_half
      (Real.rpow_le_rpow (by norm_num) hρ2 (by norm_num))
  have h12 : (1 / 2 : ℝ) ≤ ρp ^ ((1 : ℝ) / 2) :=
    le_trans half_rpow_half
      (Real.rpow_le_rpow (by norm_num) hρ2 (by norm_num))
  -- the numerator of piece 1
  have hδR : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := (δ : ℝ≥0).coe_nonneg
  have hpow5 : (m + 1 / 2) ^ 5 ≤ ((M : ℝ) + 1) ^ 5 :=
    pow_le_pow_left₀ (by linarith) hM1 5
  have hterm2 : 3 * (m + 1 / 2) * (δ : ℝ) * ρp ≤ 6 * ((M : ℝ) + 1) := by
    have h1 : 3 * (m + 1 / 2) * (δ : ℝ) * ρp ≤ 3 * ((M : ℝ) + 1) * 1 * 2 := by
      have hb1 : (0:ℝ) ≤ 3 * (m + 1/2) := by linarith
      have hb2 : 3 * (m + 1/2) ≤ 3 * ((M : ℝ) + 1) := by linarith
      have step1 : 3 * (m + 1 / 2) * (δ : ℝ) ≤ 3 * ((M : ℝ) + 1) * 1 :=
        mul_le_mul hb2 hδR hδ0 (by linarith)
      exact mul_le_mul step1 hρtop (by linarith) (by positivity)
    linarith
  have hnum : 2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * (δ : ℝ) * ρp
      ≤ 3 * ((M : ℝ) + 1) ^ 5 := by
    have h4 : (4 : ℝ) ^ 4 ≤ ((M : ℝ) + 1) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hM1R 4
    have h6 : 6 * ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ 5 := by
      nlinarith [h4, hM1R]
    nlinarith [hpow5, hterm2]
  have hnum0 : (0 : ℝ) ≤ 2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * (δ : ℝ) * ρp := by
    positivity
  -- piece 1 bound: numerator/(3ρ^{3/2}) ≤ 4(M+1)⁵
  have hpiece1 : (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * (δ : ℝ) * ρp)
      / (3 * ρp ^ ((3 : ℝ) / 2)) ≤ 4 * ((M : ℝ) + 1) ^ 5 := by
    have hden : (3 / 4 : ℝ) ≤ 3 * ρp ^ ((3 : ℝ) / 2) := by linarith
    calc (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * (δ : ℝ) * ρp)
          / (3 * ρp ^ ((3 : ℝ) / 2))
        ≤ (3 * ((M : ℝ) + 1) ^ 5) / (3 / 4) :=
          div_le_div₀ (by positivity) hnum (by norm_num) hden
      _ = 4 * ((M : ℝ) + 1) ^ 5 := by ring
  -- piece 2 bound: (m+½)/ρ^{1/2} ≤ 2(M+1)
  have hpiece2 : (m + 1 / 2) / ρp ^ ((1 : ℝ) / 2) ≤ 2 * ((M : ℝ) + 1) := by
    calc (m + 1 / 2) / ρp ^ ((1 : ℝ) / 2)
        ≤ ((M : ℝ) + 1) / (1 / 2) :=
          div_le_div₀ (by positivity) hM1 (by norm_num) h12
      _ = 2 * ((M : ℝ) + 1) := by ring
  -- assemble
  refine div_le_div_of_nonneg_right ?_ hq0.le
  push_cast
  have hN0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  calc (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * (δ : ℝ) * ρp)
        / (3 * ρp ^ ((3 : ℝ) / 2)) * (n : ℝ) + (m + 1 / 2) / ρp ^ ((1 : ℝ) / 2)
      ≤ 4 * ((M : ℝ) + 1) ^ 5 * (n : ℝ) + 2 * ((M : ℝ) + 1) := by
        have := mul_le_mul_of_nonneg_right hpiece1 hN0
        linarith [hpiece2]
    _ ≤ (4 * ((M : ℝ) + 1) ^ 5 + 2 * ((M : ℝ) + 1)) * (n : ℝ) := by
        nlinarith [hM1R]

/-- **The budget hypothesis of the production bracket, discharged.**  At any
`ε* ≥ ofReal ((4(M+1)⁵ + 2(M+1))·n/q)` — in particular at `ε* = 2^{−128}` whenever
`(4(M+1)⁵ + 2(M+1))·n·2^{128} ≤ q` — the Johnson budget holds. -/
theorem ofReal_johnsonBoundReal_le_production (domain : Fin n ↪ F) (η δ : ℝ≥0)
    {k M : ℕ} (hM3 : 3 ≤ M) (hkn : k ≤ n)
    (hm : (max (⌈((((k : ℝ) / Fintype.card (Fin n)
        + 1 / Fintype.card (Fin n))) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 ≤ M))
    (hρ : (1 / 2 : ℝ) ≤ (k : ℝ) / Fintype.card (Fin n) + 1 / Fintype.card (Fin n))
    (hδ1 : δ ≤ 1) {εstar : ℝ≥0∞}
    (hq : (((4 * (M + 1) ^ 5 + 2 * (M + 1)) * n : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    ENNReal.ofReal (johnsonBoundReal domain k η δ) ≤ εstar := by
  refine le_trans ?_ hq
  have hb := johnsonBoundReal_le_production domain η δ hM3 hkn hm hρ hδ1
  calc ENNReal.ofReal (johnsonBoundReal domain k η δ)
      ≤ ENNReal.ofReal ((((4 * (M + 1) ^ 5 + 2 * (M + 1)) * n : ℕ) : ℝ)
          / (Fintype.card F : ℝ)) := ENNReal.ofReal_le_ofReal hb
    _ = (((4 * (M + 1) ^ 5 + 2 * (M + 1)) * n : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos (α := F))]
        congr 1
        · rw [ENNReal.ofReal_natCast]
        · rw [ENNReal.ofReal_natCast]

open BCIKS20.CellPencilJohnson CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
/-- **THE PRODUCTION JOHNSON REACH, END TO END.**  Conditional on exactly the named
`CellPackageSupply` residual: for every production-shaped instance (rate `≥ 1/2`,
`m`-quantity capped by `M`, field large enough that `(4(M+1)⁵ + 2(M+1))·n/q ≤ ε*` —
at `ε* = 2^{−128}`, `M = 64`, `n ≤ 2^{30}`: every `q ≥ 2^{192}`), every Johnson-range
radius is below the threshold:  `δ ≤ mcaDeltaStar(RS, ε*)`. -/
theorem production_johnson_reach
    (hsupply : ∀ (n k m : ℕ) (_ : NeZero n) (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀)
      (_ : DecidableEq F₀) (domain : Fin n ↪ F₀) (δ : ℝ≥0),
      2 ≤ k → k + 1 ≤ n → 12 ≤ m → δ ≤ 1 →
      CellPackageSupply domain k δ
        (max (n * (GuruswamiSudan.constraintIndices m).card
          * (gs_degree_bound k n m / (k - 1))) n))
    {n k m M : ℕ} [NeZero n] {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
    (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm12 : 12 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < _root_.gs_johnson k n m)
    (hM3 : 3 ≤ M)
    (hmle : (m : ℝ) ≤
      max (⌈((((k : ℝ) / n + 1 / n)) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3)
    (hmM : (max (⌈((((k : ℝ) / Fintype.card (Fin n)
        + 1 / Fintype.card (Fin n))) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 ≤ M))
    (hρ : (1 / 2 : ℝ) ≤ (k : ℝ) / Fintype.card (Fin n) + 1 / Fintype.card (Fin n))
    {εstar : ℝ≥0∞}
    (hq : (((4 * (M + 1) ^ 5 + 2 * (M + 1)) * n : ℕ) : ℝ≥0∞)
      / (Fintype.card F₀ : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F₀) (A := F₀)
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) εstar :=
  production_good_johnson_of_packageSupply hsupply domain η δ hk2 hkn hm12 hδ1 hδJ
    hmle (ofReal_johnsonBoundReal_le_production domain η δ hM3 (by omega) hmM hρ hδ1 hq)

end ProximityGap.ProductionRegime

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.ProductionRegime.johnsonBoundReal_le_production
#print axioms ProximityGap.ProductionRegime.ofReal_johnsonBoundReal_le_production
#print axioms ProximityGap.ProductionRegime.production_johnson_reach
