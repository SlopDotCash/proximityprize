/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CollinearityMatchingFrame
import ArkLib.Data.CodingTheory.ProximityGap.MCAVerticalStratumCharZero
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The wide-circuit stratum trichotomy: partial collapses are impossible

Campaign #357, exactness-converse lane, increment 1. The census programme stratifies
wide circuits of `Γ_n` (collinear triples of pair-points) into horizontal (all products
equal), vertical (all pairs antipodal) and slanted. This file proves the stratification
is a genuine **trichotomy with no partial collapse**: for a collinear `Distinct6` triple,

* the product multiplicity is `1` or `3` — two equal products force all three equal
  (`horizontal_of_products_eq₁₂`, with the `₁₃`/`₂₃` labelings collapsing to the
  `(1,2)`-equality);
* the sum-value multiplicity is `1` or `3` — two equal pair-sums force all three pairs
  antipodal (`vertical_of_sums_eq₁₂` and labelings);
* `wideCircuit_trichotomy` — every collinear `Distinct6` triple is horizontal, vertical,
  or **generic** (products pairwise distinct AND sums pairwise distinct);
* `balanced_trichotomy` — the same statement on the pure-ℕ `Balanced` matching side of
  the frame (via the ℂ instantiation), with horizontal/vertical/at-most-one-antipodal
  in congruence form.

Probe verification (`probe_matching_converse_patterns.py`): zero partial-collapse
configurations among all balanced `Distinct6` triples at `n = 16` (1328 circuits) and
`n = 32` (23520 circuits).

Mechanism: the determinant factors over the field once two products (resp. two sums)
coincide, and the surviving factor is killed by pair-sum rigidity
(`pair_sum_rigidity`) plus antipodal product-injectivity (`antipodal_products_ne`,
the doubling-kernel argument), each contradiction landing on a `Distinct6` inequality.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the matching-pattern census comments; the exactness-converse lane claim);
  `CollinearityMatchingFrame.lean` (the balance frame), `MCAVerticalStratumCharZero.lean`
  (pair-sum rigidity), `PairSumRigidityModP.lean` (`pow_half_eq_neg_one_field`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.WideCircuitTrichotomy

open ProximityGap.MCAVerticalStratumCharZero
open ArkLib.ProximityGap.PairSumRigidityModP
open ArkLib.ProximityGap.CollinearityMatchingFrame

variable {L : Type*} [Field L] [CharZero L] {m : ℕ} {ζ : L}

/-- The pencil collinearity equation of three pair-points of `Γ_n`, in the exact shape
of `collinear_iff_balanced` (the matching frame). -/
abbrev collinearEq (ζ : L) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) : Prop :=
  (ζ ^ a₂ + ζ ^ b₂ - (ζ ^ a₁ + ζ ^ b₁)) * (ζ ^ (a₃ + b₃) - ζ ^ (a₁ + b₁))
    = (ζ ^ (a₂ + b₂) - ζ ^ (a₁ + b₁)) * (ζ ^ a₃ + ζ ^ b₃ - (ζ ^ a₁ + ζ ^ b₁))

/-- Pairwise distinctness of the six exponents (three disjoint genuine pairs). -/
def Distinct6 (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) : Prop :=
  (a₁ ≠ b₁ ∧ a₂ ≠ b₂ ∧ a₃ ≠ b₃) ∧
  (a₁ ≠ a₂ ∧ a₁ ≠ b₂ ∧ b₁ ≠ a₂ ∧ b₁ ≠ b₂) ∧
  (a₁ ≠ a₃ ∧ a₁ ≠ b₃ ∧ b₁ ≠ a₃ ∧ b₁ ≠ b₃) ∧
  (a₂ ≠ a₃ ∧ a₂ ≠ b₃ ∧ b₂ ≠ a₃ ∧ b₂ ≠ b₃)

/-! ## The abstract factorizations of the determinant -/

section Abstract

variable {E₁ E₂ E₃ M₁ M₂ M₃ : L}

private lemma det_prod₁₂ (hdet : (E₂ - E₁) * (M₃ - M₁) = (M₂ - M₁) * (E₃ - E₁))
    (h : M₁ = M₂) : M₃ = M₁ ∨ E₂ = E₁ := by
  have hfac : (M₃ - M₁) * (E₂ - E₁) = 0 := by linear_combination hdet + (E₁ - E₃) * h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (sub_eq_zero.mp h')

private lemma det_prod₁₃ (hdet : (E₂ - E₁) * (M₃ - M₁) = (M₂ - M₁) * (E₃ - E₁))
    (h : M₁ = M₃) : M₁ = M₂ ∨ E₃ = E₁ := by
  have hfac : (M₁ - M₂) * (E₃ - E₁) = 0 := by linear_combination hdet + (E₂ - E₁) * h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (sub_eq_zero.mp h')

private lemma det_prod₂₃ (hdet : (E₂ - E₁) * (M₃ - M₁) = (M₂ - M₁) * (E₃ - E₁))
    (h : M₂ = M₃) : M₁ = M₂ ∨ E₃ = E₂ := by
  have hfac : (M₁ - M₂) * (E₃ - E₂) = 0 := by linear_combination hdet + (E₂ - E₁) * h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (sub_eq_zero.mp h')

private lemma det_sum₁₂ (hdet : (E₂ - E₁) * (M₃ - M₁) = (M₂ - M₁) * (E₃ - E₁))
    (h₁ : E₁ = 0) (h₂ : E₂ = 0) : E₃ = 0 ∨ M₁ = M₂ := by
  have hfac : E₃ * (M₁ - M₂) = 0 := by
    linear_combination hdet + (M₃ - M₂) * h₁ + (M₁ - M₃) * h₂
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.mp h')

private lemma det_sum₁₃ (hdet : (E₂ - E₁) * (M₃ - M₁) = (M₂ - M₁) * (E₃ - E₁))
    (h₁ : E₁ = 0) (h₃ : E₃ = 0) : E₂ = 0 ∨ M₃ = M₁ := by
  have hfac : E₂ * (M₃ - M₁) = 0 := by
    linear_combination hdet + (M₃ - M₂) * h₁ + (M₂ - M₁) * h₃
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.mp h')

private lemma det_sum₂₃ (hdet : (E₂ - E₁) * (M₃ - M₁) = (M₂ - M₁) * (E₃ - E₁))
    (h₂ : E₂ = 0) (h₃ : E₃ = 0) : E₁ = 0 ∨ M₂ = M₃ := by
  have hfac : E₁ * (M₂ - M₃) = 0 := by
    linear_combination hdet + (M₁ - M₃) * h₂ + (M₂ - M₁) * h₃
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.mp h')

end Abstract

/-! ## The arithmetic kills -/

/-- Power equality at a primitive `2^m`-th root is residue equality. -/
theorem pow_eq_pow_iff (hζ : IsPrimitiveRoot ζ (2 ^ m)) {x y : ℕ} :
    ζ ^ x = ζ ^ y ↔ x % 2 ^ m = y % 2 ^ m := by
  classical
  have hn : (0 : ℕ) < 2 ^ m := by positivity
  constructor
  · intro h
    refine hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ?_
    rw [← pow_mod_reduce hζ.pow_eq_one x, ← pow_mod_reduce hζ.pow_eq_one y, h]
  · intro h
    rw [pow_mod_reduce hζ.pow_eq_one x, pow_mod_reduce hζ.pow_eq_one y, h]

/-- A pair of `2^m`-th roots sums to zero **iff** the pair is antipodal. -/
theorem pair_sum_eq_zero_iff (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m)) {a b : ℕ}
    (hb : b < 2 ^ m) :
    ζ ^ a + ζ ^ b = 0 ↔ b = (a + 2 ^ (m - 1)) % 2 ^ m := by
  have hn : (0 : ℕ) < 2 ^ m := by positivity
  have hneg : ζ ^ (2 ^ (m - 1)) = -1 := pow_half_eq_neg_one_field hm hζ
  constructor
  · intro h
    have hb' : ζ ^ b = ζ ^ (a + 2 ^ (m - 1)) := by
      rw [pow_add, hneg]
      linear_combination h
    have hmod : b % 2 ^ m = (a + 2 ^ (m - 1)) % 2 ^ m := (pow_eq_pow_iff hζ).mp hb'
    rwa [Nat.mod_eq_of_lt hb] at hmod
  · intro h
    have hpow : ζ ^ b = ζ ^ (a + 2 ^ (m - 1)) := by
      refine (pow_eq_pow_iff hζ).mpr ?_
      rw [h, Nat.mod_eq_of_lt (Nat.mod_lt _ hn)]
    rw [hpow, pow_add, hneg]
    ring

/-- **The sum-collision dichotomy**: two genuine pairs with equal sums are equal as
pairs, or both antipodal. -/
theorem sum_eq_dichotomy (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m)
    (hb₂ : b₂ < 2 ^ m) (h11 : a₁ ≠ b₁) (h22 : a₂ ≠ b₂)
    (hsum : ζ ^ a₁ + ζ ^ b₁ = ζ ^ a₂ + ζ ^ b₂) :
    ((a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ b₁ = a₂))
      ∨ (b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m) := by
  classical
  by_cases hna : b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m
  · refine Or.inr ⟨hna, ?_⟩
    have h0 : ζ ^ a₁ + ζ ^ b₁ = 0 := (pair_sum_eq_zero_iff hm hζ hb₁).mpr hna
    exact (pair_sum_eq_zero_iff hm hζ hb₂).mp (hsum ▸ h0)
  · exact Or.inl (pair_sum_rigidity hm hζ ha₁ hb₁ ha₂ hb₂ h11 h22 hna hsum)

private lemma two_half (hm : 1 ≤ m) : 2 * 2 ^ (m - 1) = 2 ^ m := by
  have h := pow_succ 2 (m - 1)
  rw [Nat.sub_add_cancel hm] at h
  omega

/-- Residues below `2H` congruent mod `H` differ by `0` or `H`. -/
private lemma cases_of_modEq_half {H a₁ a₂ : ℕ} (hH : 0 < H) (h1 : a₁ < 2 * H)
    (h2 : a₂ < 2 * H) (hmod : a₁ ≡ a₂ [MOD H]) :
    a₂ = a₁ ∨ a₂ = a₁ + H ∨ a₁ = a₂ + H := by
  obtain ⟨c, hc⟩ : (H : ℤ) ∣ (a₂ : ℤ) - (a₁ : ℤ) := hmod.dvd
  have hHz : (0 : ℤ) < H := by exact_mod_cast hH
  have hub : c < 2 := by
    by_contra hcon
    have h2c : (2 : ℤ) ≤ c := by omega
    have hmul : (H : ℤ) * 2 ≤ H * c := mul_le_mul_of_nonneg_left h2c hHz.le
    omega
  have hlb : -2 < c := by
    by_contra hcon
    have h2c : c ≤ (-2 : ℤ) := by omega
    have hmul : (H : ℤ) * c ≤ H * (-2) := mul_le_mul_of_nonneg_left h2c hHz.le
    omega
  interval_cases c <;> omega

/-- **Antipodal product injectivity**: two antipodal pairs on distinct base points have
distinct products (the doubling-kernel argument: equal products force the base points to
agree modulo the half-period). -/
theorem antipodal_products_ne (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m)
    (hb₁ : b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m) (hb₂ : b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m)
    (h21 : a₂ ≠ a₁) (h2b1 : a₂ ≠ b₁) (h1b2 : a₁ ≠ b₂) :
    ζ ^ (a₁ + b₁) ≠ ζ ^ (a₂ + b₂) := by
  intro heq
  have hHpos : 0 < 2 ^ (m - 1) := by positivity
  have h2H : 2 * 2 ^ (m - 1) = 2 ^ m := two_half hm
  have hmod : a₁ + b₁ ≡ a₂ + b₂ [MOD 2 ^ m] := (pow_eq_pow_iff hζ).mp heq
  have hb₁' : b₁ ≡ a₁ + 2 ^ (m - 1) [MOD 2 ^ m] := by
    rw [hb₁]; exact Nat.mod_modEq _ _
  have hb₂' : b₂ ≡ a₂ + 2 ^ (m - 1) [MOD 2 ^ m] := by
    rw [hb₂]; exact Nat.mod_modEq _ _
  have hsum : 2 * a₁ + 2 ^ (m - 1) ≡ 2 * a₂ + 2 ^ (m - 1) [MOD 2 ^ m] := by
    calc 2 * a₁ + 2 ^ (m - 1) = a₁ + (a₁ + 2 ^ (m - 1)) := by ring
    _ ≡ a₁ + b₁ [MOD 2 ^ m] := (Nat.ModEq.refl a₁).add hb₁'.symm
    _ ≡ a₂ + b₂ [MOD 2 ^ m] := hmod
    _ ≡ a₂ + (a₂ + 2 ^ (m - 1)) [MOD 2 ^ m] := (Nat.ModEq.refl a₂).add hb₂'
    _ = 2 * a₂ + 2 ^ (m - 1) := by ring
  have hcancel : 2 * a₁ ≡ 2 * a₂ [MOD 2 ^ m] := hsum.add_right_cancel' _
  rw [← h2H] at hcancel
  have hhalf : a₁ ≡ a₂ [MOD 2 ^ (m - 1)] :=
    Nat.ModEq.mul_left_cancel' (by norm_num) hcancel
  rcases cases_of_modEq_half hHpos (by omega) (by omega) hhalf with h | h | h
  · exact h21 h
  · -- `a₂ = a₁ + H`, so `b₁ = a₂`
    apply h2b1
    rw [hb₁, ← h, Nat.mod_eq_of_lt ha₂]
  · -- `a₁ = a₂ + H`, so `b₂ = a₁`
    apply h1b2
    rw [hb₂, ← h, Nat.mod_eq_of_lt ha₁]

/-! ## The partial-collapse kills -/

/-- **Two equal products force the third (the `m`-multiplicity is `1` or `3`).**
A collinear `Distinct6` triple with `m₁ = m₂` is horizontal. -/
theorem horizontal_of_products_eq₁₂ (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m)
    (hb₂ : b₂ < 2 ^ m) (h11 : a₁ ≠ b₁) (h22 : a₂ ≠ b₂) (h12 : a₁ ≠ a₂) (h1b2 : a₁ ≠ b₂)
    (h2b1 : a₂ ≠ b₁) (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃)
    (hM : ζ ^ (a₁ + b₁) = ζ ^ (a₂ + b₂)) :
    ζ ^ (a₃ + b₃) = ζ ^ (a₁ + b₁) := by
  rcases det_prod₁₂ hdet hM with h | h
  · exact h
  · rcases sum_eq_dichotomy hm hζ ha₁ hb₁ ha₂ hb₂ h11 h22 h.symm with hp | ⟨hh₁, hh₂⟩
    · rcases hp with ⟨h', _⟩ | ⟨h', _⟩
      · exact absurd h' h12
      · exact absurd h' h1b2
    · exact absurd hM
        (antipodal_products_ne hm hζ ha₁ ha₂ hh₁ hh₂ (Ne.symm h12) h2b1 h1b2)

/-- The `(1,3)` labeling: `m₁ = m₃` forces `m₁ = m₂`. -/
theorem products_eq₁₂_of_eq₁₃ (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₃ : a₃ < 2 ^ m)
    (hb₃ : b₃ < 2 ^ m) (h11 : a₁ ≠ b₁) (h33 : a₃ ≠ b₃) (h13 : a₁ ≠ a₃) (h1b3 : a₁ ≠ b₃)
    (h3b1 : a₃ ≠ b₁) (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃)
    (hM : ζ ^ (a₁ + b₁) = ζ ^ (a₃ + b₃)) :
    ζ ^ (a₁ + b₁) = ζ ^ (a₂ + b₂) := by
  rcases det_prod₁₃ hdet hM with h | h
  · exact h
  · rcases sum_eq_dichotomy hm hζ ha₁ hb₁ ha₃ hb₃ h11 h33 h.symm with hp | ⟨hh₁, hh₃⟩
    · rcases hp with ⟨h', _⟩ | ⟨h', _⟩
      · exact absurd h' h13
      · exact absurd h' h1b3
    · exact absurd hM
        (antipodal_products_ne hm hζ ha₁ ha₃ hh₁ hh₃ (Ne.symm h13) h3b1 h1b3)

/-- The `(2,3)` labeling: `m₂ = m₃` forces `m₁ = m₂`. -/
theorem products_eq₁₂_of_eq₂₃ (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m) (ha₃ : a₃ < 2 ^ m)
    (hb₃ : b₃ < 2 ^ m) (h22 : a₂ ≠ b₂) (h33 : a₃ ≠ b₃) (h23 : a₂ ≠ a₃) (h2b3 : a₂ ≠ b₃)
    (h3b2 : a₃ ≠ b₂) (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃)
    (hM : ζ ^ (a₂ + b₂) = ζ ^ (a₃ + b₃)) :
    ζ ^ (a₁ + b₁) = ζ ^ (a₂ + b₂) := by
  rcases det_prod₂₃ hdet hM with h | h
  · exact h
  · rcases sum_eq_dichotomy hm hζ ha₂ hb₂ ha₃ hb₃ h22 h33 h.symm with hp | ⟨hh₂, hh₃⟩
    · rcases hp with ⟨h', _⟩ | ⟨h', _⟩
      · exact absurd h' h23
      · exact absurd h' h2b3
    · exact absurd hM
        (antipodal_products_ne hm hζ ha₂ ha₃ hh₂ hh₃ (Ne.symm h23) h3b2 h2b3)

/-- **Two equal sums force the vertical stratum (the `e`-multiplicity is `1` or `3`).**
A collinear `Distinct6` triple with `e₁ = e₂` has all three pairs antipodal. -/
theorem vertical_of_sums_eq₁₂ (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m)
    (hb₂ : b₂ < 2 ^ m) (hb₃ : b₃ < 2 ^ m) (h11 : a₁ ≠ b₁) (h22 : a₂ ≠ b₂)
    (h12 : a₁ ≠ a₂) (h1b2 : a₁ ≠ b₂) (h2b1 : a₂ ≠ b₁)
    (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃)
    (hE : ζ ^ a₁ + ζ ^ b₁ = ζ ^ a₂ + ζ ^ b₂) :
    b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
      ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m := by
  rcases sum_eq_dichotomy hm hζ ha₁ hb₁ ha₂ hb₂ h11 h22 hE with hp | ⟨hh₁, hh₂⟩
  · rcases hp with ⟨h', _⟩ | ⟨h', _⟩
    · exact absurd h' h12
    · exact absurd h' h1b2
  · have hz₁ : ζ ^ a₁ + ζ ^ b₁ = 0 := (pair_sum_eq_zero_iff hm hζ hb₁).mpr hh₁
    have hz₂ : ζ ^ a₂ + ζ ^ b₂ = 0 := (pair_sum_eq_zero_iff hm hζ hb₂).mpr hh₂
    rcases det_sum₁₂ hdet hz₁ hz₂ with h3 | hM
    · exact ⟨hh₁, hh₂, (pair_sum_eq_zero_iff hm hζ hb₃).mp h3⟩
    · exact absurd hM
        (antipodal_products_ne hm hζ ha₁ ha₂ hh₁ hh₂ (Ne.symm h12) h2b1 h1b2)

/-- The `(1,3)` labeling of the vertical kill. -/
theorem vertical_of_sums_eq₁₃ (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m) (h11 : a₁ ≠ b₁) (h33 : a₃ ≠ b₃)
    (h13 : a₁ ≠ a₃) (h1b3 : a₁ ≠ b₃) (h3b1 : a₃ ≠ b₁)
    (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃)
    (hE : ζ ^ a₁ + ζ ^ b₁ = ζ ^ a₃ + ζ ^ b₃) :
    b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
      ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m := by
  rcases sum_eq_dichotomy hm hζ ha₁ hb₁ ha₃ hb₃ h11 h33 hE with hp | ⟨hh₁, hh₃⟩
  · rcases hp with ⟨h', _⟩ | ⟨h', _⟩
    · exact absurd h' h13
    · exact absurd h' h1b3
  · have hz₁ : ζ ^ a₁ + ζ ^ b₁ = 0 := (pair_sum_eq_zero_iff hm hζ hb₁).mpr hh₁
    have hz₃ : ζ ^ a₃ + ζ ^ b₃ = 0 := (pair_sum_eq_zero_iff hm hζ hb₃).mpr hh₃
    rcases det_sum₁₃ hdet hz₁ hz₃ with h2 | hM
    · exact ⟨hh₁, (pair_sum_eq_zero_iff hm hζ hb₂).mp h2, hh₃⟩
    · exact absurd hM.symm
        (antipodal_products_ne hm hζ ha₁ ha₃ hh₁ hh₃ (Ne.symm h13) h3b1 h1b3)

/-- The `(2,3)` labeling of the vertical kill. -/
theorem vertical_of_sums_eq₂₃ (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m) (h22 : a₂ ≠ b₂) (h33 : a₃ ≠ b₃)
    (h23 : a₂ ≠ a₃) (h2b3 : a₂ ≠ b₃) (h3b2 : a₃ ≠ b₂)
    (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃)
    (hE : ζ ^ a₂ + ζ ^ b₂ = ζ ^ a₃ + ζ ^ b₃) :
    b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
      ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m := by
  rcases sum_eq_dichotomy hm hζ ha₂ hb₂ ha₃ hb₃ h22 h33 hE with hp | ⟨hh₂, hh₃⟩
  · rcases hp with ⟨h', _⟩ | ⟨h', _⟩
    · exact absurd h' h23
    · exact absurd h' h2b3
  · have hz₂ : ζ ^ a₂ + ζ ^ b₂ = 0 := (pair_sum_eq_zero_iff hm hζ hb₂).mpr hh₂
    have hz₃ : ζ ^ a₃ + ζ ^ b₃ = 0 := (pair_sum_eq_zero_iff hm hζ hb₃).mpr hh₃
    rcases det_sum₂₃ hdet hz₂ hz₃ with h1 | hM
    · exact ⟨(pair_sum_eq_zero_iff hm hζ hb₁).mp h1, hh₂, hh₃⟩
    · exact absurd hM
        (antipodal_products_ne hm hζ ha₂ ha₃ hh₂ hh₃ (Ne.symm h23) h3b2 h2b3)

/-! ## The trichotomy -/

/-- **THE WIDE-CIRCUIT TRICHOTOMY.** Every collinear `Distinct6` triple of pair-points
of `Γ_n` is horizontal (all products equal), vertical (all pairs antipodal), or
**generic**: products pairwise distinct AND sums pairwise distinct. Partial collapses
are impossible. -/
theorem wideCircuit_trichotomy (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ} (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m)
    (hb₂ : b₂ < 2 ^ m) (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m)
    (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃) :
    (ζ ^ (a₁ + b₁) = ζ ^ (a₂ + b₂) ∧ ζ ^ (a₂ + b₂) = ζ ^ (a₃ + b₃))
    ∨ (b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
        ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m)
    ∨ ((ζ ^ (a₁ + b₁) ≠ ζ ^ (a₂ + b₂) ∧ ζ ^ (a₁ + b₁) ≠ ζ ^ (a₃ + b₃)
          ∧ ζ ^ (a₂ + b₂) ≠ ζ ^ (a₃ + b₃))
        ∧ (ζ ^ a₁ + ζ ^ b₁ ≠ ζ ^ a₂ + ζ ^ b₂ ∧ ζ ^ a₁ + ζ ^ b₁ ≠ ζ ^ a₃ + ζ ^ b₃
          ∧ ζ ^ a₂ + ζ ^ b₂ ≠ ζ ^ a₃ + ζ ^ b₃)) := by
  obtain ⟨⟨h11, h22, h33⟩, ⟨h12, h1b2, hb12, hb1b2⟩, ⟨h13, h1b3, hb13, hb1b3⟩,
    ⟨h23, h2b3, hb23, hb2b3⟩⟩ := hD6
  by_cases hM12 : ζ ^ (a₁ + b₁) = ζ ^ (a₂ + b₂)
  · have h3 := horizontal_of_products_eq₁₂ hm hζ ha₁ hb₁ ha₂ hb₂ h11 h22 h12 h1b2
      (Ne.symm hb12) hdet hM12
    exact Or.inl ⟨hM12, hM12.symm.trans h3.symm⟩
  by_cases hM13 : ζ ^ (a₁ + b₁) = ζ ^ (a₃ + b₃)
  · exact absurd (products_eq₁₂_of_eq₁₃ hm hζ ha₁ hb₁ ha₃ hb₃ h11 h33 h13 h1b3
      (Ne.symm hb13) hdet hM13) hM12
  by_cases hM23 : ζ ^ (a₂ + b₂) = ζ ^ (a₃ + b₃)
  · exact absurd (products_eq₁₂_of_eq₂₃ hm hζ ha₂ hb₂ ha₃ hb₃ h22 h33 h23 h2b3
      (Ne.symm hb23) hdet hM23) hM12
  by_cases hE12 : ζ ^ a₁ + ζ ^ b₁ = ζ ^ a₂ + ζ ^ b₂
  · exact Or.inr (Or.inl (vertical_of_sums_eq₁₂ hm hζ ha₁ hb₁ ha₂ hb₂ hb₃ h11 h22 h12
      h1b2 (Ne.symm hb12) hdet hE12))
  by_cases hE13 : ζ ^ a₁ + ζ ^ b₁ = ζ ^ a₃ + ζ ^ b₃
  · exact Or.inr (Or.inl (vertical_of_sums_eq₁₃ hm hζ ha₁ hb₁ hb₂ ha₃ hb₃ h11 h33 h13
      h1b3 (Ne.symm hb13) hdet hE13))
  by_cases hE23 : ζ ^ a₂ + ζ ^ b₂ = ζ ^ a₃ + ζ ^ b₃
  · exact Or.inr (Or.inl (vertical_of_sums_eq₂₃ hm hζ hb₁ ha₂ hb₂ ha₃ hb₃ h22 h33 h23
      h2b3 (Ne.symm hb23) hdet hE23))
  · exact Or.inr (Or.inr ⟨⟨hM12, hM13, hM23⟩, ⟨hE12, hE13, hE23⟩⟩)

/-! ## The matching-side form -/

/-- **The trichotomy on the `Balanced` matching side** (via the ℂ instantiation of the
frame): every balanced `Distinct6` exponent-triple is horizontal (equal products mod
`n`), vertical (all pairs antipodal), or generic (products pairwise distinct mod `n`,
and no two pairs simultaneously antipodal). -/
theorem balanced_trichotomy (hm : 1 ≤ m) {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m) (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hbal : Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃)) :
    ((a₁ + b₁) % 2 ^ m = (a₂ + b₂) % 2 ^ m ∧ (a₂ + b₂) % 2 ^ m = (a₃ + b₃) % 2 ^ m)
    ∨ (b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
        ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m)
    ∨ (((a₁ + b₁) % 2 ^ m ≠ (a₂ + b₂) % 2 ^ m ∧ (a₁ + b₁) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m
          ∧ (a₂ + b₂) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
        ∧ (¬(b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m)
          ∧ ¬(b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m)
          ∧ ¬(b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m))) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (2 ^ m : ℕ)))
      (2 ^ m) := Complex.isPrimitiveRoot_exp _ (by positivity)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ m : ℕ)) with hζdef
  have hdet : collinearEq ζ a₁ b₁ a₂ b₂ a₃ b₃ :=
    (collinear_iff_balanced hm hζ a₁ b₁ a₂ b₂ a₃ b₃).mpr hbal
  rcases wideCircuit_trichotomy hm hζ ha₁ hb₁ ha₂ hb₂ ha₃ hb₃ hD6 hdet with
    ⟨h1, h2⟩ | hv | ⟨⟨hM12, hM13, hM23⟩, ⟨hE12, hE13, hE23⟩⟩
  · exact Or.inl ⟨(pow_eq_pow_iff hζ).mp h1, (pow_eq_pow_iff hζ).mp h2⟩
  · exact Or.inr (Or.inl hv)
  · refine Or.inr (Or.inr ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩)
    · exact fun h => hM12 ((pow_eq_pow_iff hζ).mpr h)
    · exact fun h => hM13 ((pow_eq_pow_iff hζ).mpr h)
    · exact fun h => hM23 ((pow_eq_pow_iff hζ).mpr h)
    · rintro ⟨hh₁, hh₂⟩
      exact hE12 (((pair_sum_eq_zero_iff hm hζ hb₁).mpr hh₁).trans
        ((pair_sum_eq_zero_iff hm hζ hb₂).mpr hh₂).symm)
    · rintro ⟨hh₁, hh₃⟩
      exact hE13 (((pair_sum_eq_zero_iff hm hζ hb₁).mpr hh₁).trans
        ((pair_sum_eq_zero_iff hm hζ hb₃).mpr hh₃).symm)
    · rintro ⟨hh₂, hh₃⟩
      exact hE23 (((pair_sum_eq_zero_iff hm hζ hb₂).mpr hh₂).trans
        ((pair_sum_eq_zero_iff hm hζ hb₃).mpr hh₃).symm)

/-! ## Source audit -/

#print axioms pair_sum_eq_zero_iff
#print axioms sum_eq_dichotomy
#print axioms antipodal_products_ne
#print axioms horizontal_of_products_eq₁₂
#print axioms vertical_of_sums_eq₁₂
#print axioms wideCircuit_trichotomy
#print axioms balanced_trichotomy

end ArkLib.ProximityGap.WideCircuitTrichotomy
