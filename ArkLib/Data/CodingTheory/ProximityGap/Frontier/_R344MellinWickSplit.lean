/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R343MellinFourthMoment

/-!
# R344: the Wick split of the Mellin fourth moment

Sixth brick of the Gauss-phase PAPR arc. r343 gave the exact fourth moment as a
congruence-class Gauss-phase energy. This file splits it into the **exactly
computable Wick/diagonal part** and the **wraparound remainder**:

  `∑_{b≠0} (S_b·conj S_b)² = (q−1)·( (t−1)·(2(t−1)−1)·q² + W )`,

where `W` (`wraparound`) is the sum over congruence tuples `j₁+j₃ ≡ k₁+k₃ (mod t)`
that are NOT a permutation match `{k₁,k₃} = {j₁,j₃}`. The diagonal count
`(t−1)(2t−3)` with value `q²` per tuple is the exact Gaussian/Wick prediction at
depth 2 (random phases have the same diagonal and `W = O(√·)`-fluctuation).

Scope honesty: `W = 0`-style cancellation at depth 2 does NOT reach the prize
regime (`t ≫ n`: the depth-4 Markov sup bound `~q^{3/4}√t` only beats the trivial
`t·n` when `t < n`); the prize wall remains the `r ≈ ln q` tower. The value of this
brick is that the wraparound object `W` — the EXACT depth-2 shadow of the
DC-subtracted energy face — now has a machine-checked closed form to attack and to
transfer against the in-tree r304 cyclotomic difference-class computations.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.R344MellinWickSplit

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.R342MellinLevelSet
open ArkLib.ProximityGap.R343MellinFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The permutation-diagonal (Wick) tuples: `(k₁,k₃)` is `(j₁,j₃)` or `(j₃,j₁)`. -/
def IsWickPair (j₁ j₃ k₁ k₃ : ℕ) : Prop :=
  (k₁ = j₁ ∧ k₃ = j₃) ∨ (k₁ = j₃ ∧ k₃ = j₁)

instance (j₁ j₃ k₁ k₃ : ℕ) : Decidable (IsWickPair j₁ j₃ k₁ k₃) := by
  unfold IsWickPair
  infer_instance

theorem IsWickPair.modEq {j₁ j₃ k₁ k₃ t : ℕ} (h : IsWickPair j₁ j₃ k₁ k₃) :
    (j₁ + j₃) ≡ (k₁ + k₃) [MOD t] := by
  rcases h with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · rw [h1, h3]
  · rw [h1, h3, Nat.add_comm]

open Classical in
/-- The wraparound remainder: congruence tuples that are not Wick pairs. -/
noncomputable def wraparound (d : ℕ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  ∑ j₁ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
  ∑ j₃ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
  ∑ k₁ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
  ∑ k₃ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
    if (j₁ + j₃) ≡ (k₁ + k₃) [MOD (Fintype.card F - 1) / d]
        ∧ ¬ IsWickPair j₁ j₃ k₁ k₃
    then gaussSum (χ ^ (d * j₁)) ψ * gaussSum (χ ^ (d * j₃)) ψ
        * (starRingEnd ℂ) (gaussSum (χ ^ (d * k₁)) ψ)
        * (starRingEnd ℂ) (gaussSum (χ ^ (d * k₃)) ψ)
    else 0

/-- `τ_j · conj(τ_j) = q` for nontrivial `χ^{dj}` and primitive `ψ`. -/
theorem gaussSum_mul_conj_self {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {j : ℕ} (hj : j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0) :
    gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) ψ)
      = (Fintype.card F : ℂ) := by
  have hj0 : 0 < j := Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hj)
  have hjt : j < (Fintype.card F - 1) / d :=
    Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  have htd : ((Fintype.card F - 1) / d) * d = Fintype.card F - 1 :=
    Nat.div_mul_cancel hd
  have hne : (χ ^ (d * j)) ≠ 1 := by
    refine chi_pow_ne_one hord (Nat.mul_pos hd0 hj0) ?_
    calc d * j < d * ((Fintype.card F - 1) / d) :=
          (Nat.mul_lt_mul_left hd0).mpr hjt
      _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast congrArg Complex.ofReal (norm_gaussSum_sq hne hψ)

/-- Double-sum pair-indicator collapse: summing an indicator pinned to `(a, b)`
over `J × J` extracts the single value. -/
theorem sum_pair_indicator {J : Finset ℕ} {a b : ℕ} (ha : a ∈ J) (hb : b ∈ J)
    (f : ℕ → ℕ → ℂ) :
    ∑ k₁ ∈ J, ∑ k₃ ∈ J, (if k₁ = a ∧ k₃ = b then f k₁ k₃ else 0) = f a b := by
  rw [Finset.sum_eq_single_of_mem a ha (fun k₁ _ hk₁ =>
    Finset.sum_eq_zero fun k₃ _ => if_neg (fun h => hk₁ h.1))]
  rw [Finset.sum_eq_single_of_mem b hb (fun k₃ _ hk₃ =>
    if_neg (fun h => hk₃ h.2))]
  exact if_pos ⟨rfl, rfl⟩

open Classical in
/-- **The Wick split**: the fourth moment decomposes as the exactly-computed
diagonal plus the wraparound remainder,

  `∑_{b≠0} (S_b·conj S_b)² = (q−1)·((t−1)·(2·(t−1)−1)·q² + W)`. -/
theorem mellin_fourth_moment_wick_split {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ∑ b ∈ Finset.univ.erase (0 : F),
        (mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)) ^ 2
      = ((Fintype.card F - 1 : ℕ) : ℂ)
          * ((((Fintype.card F - 1) / d - 1 : ℕ) : ℂ)
              * (2 * (((Fintype.card F - 1) / d - 1 : ℕ) : ℂ) - 1)
              * (Fintype.card F : ℂ) ^ 2
            + wraparound d χ ψ) := by
  classical
  set t := (Fintype.card F - 1) / d with ht
  set J : Finset ℕ := (Finset.range t).erase 0 with hJ
  set τ : ℕ → ℂ := fun j => gaussSum (χ ^ (d * j)) ψ with hτ
  set q : ℂ := (Fintype.card F : ℂ) with hq
  have hττ : ∀ j ∈ J, τ j * (starRingEnd ℂ) (τ j) = q :=
    fun j hj => gaussSum_mul_conj_self hd hd0 hord hψ hj
  rw [mellin_fourth_moment hd hd0 hord ψ]
  congr 1
  -- split each congruence indicator into Wick + wraparound
  have hsplit : ∀ j₁ ∈ J, ∀ j₃ ∈ J, ∀ k₁ ∈ J, ∀ k₃ ∈ J,
      (if (j₁ + j₃) ≡ (k₁ + k₃) [MOD t]
       then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
      = (if IsWickPair j₁ j₃ k₁ k₃
         then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
        + (if (j₁ + j₃) ≡ (k₁ + k₃) [MOD t] ∧ ¬ IsWickPair j₁ j₃ k₁ k₃
           then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
           else 0) := by
    intro j₁ _ j₃ _ k₁ _ k₃ _
    by_cases hw : IsWickPair j₁ j₃ k₁ k₃
    · rw [if_pos hw, if_pos hw.modEq, if_neg (fun h => h.2 hw), add_zero]
    · rw [if_neg hw]
      by_cases hc : (j₁ + j₃) ≡ (k₁ + k₃) [MOD t]
      · rw [if_pos hc, if_pos ⟨hc, hw⟩, zero_add]
      · rw [if_neg hc, if_neg (fun h => hc h.1), add_zero]
  have hsum_split : ∑ j₁ ∈ J, ∑ j₃ ∈ J, ∑ k₁ ∈ J, ∑ k₃ ∈ J,
      (if (j₁ + j₃) ≡ (k₁ + k₃) [MOD t]
       then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
      = (∑ j₁ ∈ J, ∑ j₃ ∈ J, ∑ k₁ ∈ J, ∑ k₃ ∈ J,
          if IsWickPair j₁ j₃ k₁ k₃
          then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
        + wraparound d χ ψ := by
    unfold wraparound
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j₃ hj₃ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k₃ hk₃ =>
      hsplit j₁ hj₁ j₃ hj₃ k₁ hk₁ k₃ hk₃
  rw [hsum_split]
  congr 1
  -- evaluate the Wick diagonal
  have hinner : ∀ j₁ ∈ J, ∀ j₃ ∈ J,
      ∑ k₁ ∈ J, ∑ k₃ ∈ J,
        (if IsWickPair j₁ j₃ k₁ k₃
         then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
      = if j₁ = j₃ then q ^ 2 else 2 * q ^ 2 := by
    intro j₁ hj₁ j₃ hj₃
    have hval : τ j₁ * τ j₃ * (starRingEnd ℂ) (τ j₁) * (starRingEnd ℂ) (τ j₃)
        = q ^ 2 := by
      have h1 := hττ j₁ hj₁
      have h3 := hττ j₃ hj₃
      calc τ j₁ * τ j₃ * (starRingEnd ℂ) (τ j₁) * (starRingEnd ℂ) (τ j₃)
          = (τ j₁ * (starRingEnd ℂ) (τ j₁)) * (τ j₃ * (starRingEnd ℂ) (τ j₃)) := by
            ring
        _ = q * q := by rw [h1, h3]
        _ = q ^ 2 := by ring
    by_cases hj : j₁ = j₃
    · subst hj
      rw [if_pos rfl]
      have hcond : ∀ k₁ k₃ : ℕ, IsWickPair j₁ j₁ k₁ k₃ ↔ (k₁ = j₁ ∧ k₃ = j₁) := by
        intro k₁ k₃
        unfold IsWickPair
        tauto
      calc ∑ k₁ ∈ J, ∑ k₃ ∈ J,
            (if IsWickPair j₁ j₁ k₁ k₃
             then τ j₁ * τ j₁ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
             else 0)
          = ∑ k₁ ∈ J, ∑ k₃ ∈ J,
            (if k₁ = j₁ ∧ k₃ = j₁
             then τ j₁ * τ j₁ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
             else 0) := by
            refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₃ _ => ?_
            rw [if_congr (hcond k₁ k₃) rfl rfl]
        _ = τ j₁ * τ j₁ * (starRingEnd ℂ) (τ j₁) * (starRingEnd ℂ) (τ j₁) :=
            sum_pair_indicator hj₁ hj₁ _
        _ = q ^ 2 := hval
    · rw [if_neg hj]
      -- two disjoint matches: (j₁,j₃) and (j₃,j₁)
      have hdisj : ∀ k₁ k₃ : ℕ,
          (if IsWickPair j₁ j₃ k₁ k₃
           then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
          = (if k₁ = j₁ ∧ k₃ = j₃
             then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃) else 0)
            + (if k₁ = j₃ ∧ k₃ = j₁
               then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
               else 0) := by
        intro k₁ k₃
        unfold IsWickPair
        by_cases h1 : k₁ = j₁ ∧ k₃ = j₃
        · rw [if_pos (Or.inl h1), if_pos h1,
            if_neg (fun h2 => hj (h1.1.symm.trans h2.1)), add_zero]
        · by_cases h2 : k₁ = j₃ ∧ k₃ = j₁
          · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
          · rw [if_neg (fun h => h.elim h1 h2), if_neg h1, if_neg h2, add_zero]
      calc ∑ k₁ ∈ J, ∑ k₃ ∈ J,
            (if IsWickPair j₁ j₃ k₁ k₃
             then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
             else 0)
          = (∑ k₁ ∈ J, ∑ k₃ ∈ J,
              (if k₁ = j₁ ∧ k₃ = j₃
               then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
               else 0))
            + ∑ k₁ ∈ J, ∑ k₃ ∈ J,
              (if k₁ = j₃ ∧ k₃ = j₁
               then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
               else 0) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k₁ _ => ?_
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k₃ _ => hdisj k₁ k₃
        _ = τ j₁ * τ j₃ * (starRingEnd ℂ) (τ j₁) * (starRingEnd ℂ) (τ j₃)
            + τ j₁ * τ j₃ * (starRingEnd ℂ) (τ j₃) * (starRingEnd ℂ) (τ j₁) := by
            rw [sum_pair_indicator hj₁ hj₃ _, sum_pair_indicator hj₃ hj₁ _]
        _ = 2 * q ^ 2 := by
            have := hval
            rw [show τ j₁ * τ j₃ * (starRingEnd ℂ) (τ j₃) * (starRingEnd ℂ) (τ j₁)
              = τ j₁ * τ j₃ * (starRingEnd ℂ) (τ j₁) * (starRingEnd ℂ) (τ j₃) by ring,
              hval]
            ring
  rw [Finset.sum_congr rfl fun j₁ hj₁ => Finset.sum_congr rfl fun j₃ hj₃ =>
    hinner j₁ hj₁ j₃ hj₃]
  -- count: ∑_{j₁,j₃∈J} (if j₁=j₃ then q² else 2q²) = (t−1)(2(t−1)−1)q²
  have hcardJ : J.card = t - 1 := by
    rw [hJ, Finset.card_erase_of_mem, Finset.card_range]
    have hq1 : 0 < Fintype.card F - 1 := by
      have := Fintype.one_lt_card (α := F)
      omega
    have ht0 : 0 < t := by
      have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, zero_mul] at htd; omega
      · exact h
    exact Finset.mem_range.mpr ht0
  have hterm : ∀ j₁ ∈ J, ∀ j₃ ∈ J,
      (if j₁ = j₃ then q ^ 2 else 2 * q ^ 2)
      = 2 * q ^ 2 + (if j₃ = j₁ then -(q ^ 2) else 0) := by
    intro j₁ _ j₃ _
    by_cases h : j₁ = j₃
    · rw [if_pos h, if_pos h.symm]
      ring
    · rw [if_neg h, if_neg (fun h' => h h'.symm), add_zero]
  calc ∑ j₁ ∈ J, ∑ j₃ ∈ J, (if j₁ = j₃ then q ^ 2 else 2 * q ^ 2)
      = ∑ j₁ ∈ J, ∑ j₃ ∈ J, (2 * q ^ 2 + (if j₃ = j₁ then -(q ^ 2) else 0)) := by
        refine Finset.sum_congr rfl fun j₁ hj₁ => Finset.sum_congr rfl fun j₃ hj₃ => ?_
        exact hterm j₁ hj₁ j₃ hj₃
    _ = ∑ j₁ ∈ J, ((J.card : ℂ) * (2 * q ^ 2) + -(q ^ 2)) := by
        refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_ite_eq' J j₁ (fun _ => -(q ^ 2)), if_pos hj₁]
    _ = (J.card : ℂ) * ((J.card : ℂ) * (2 * q ^ 2) + -(q ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((t - 1 : ℕ) : ℂ) * (2 * ((t - 1 : ℕ) : ℂ) - 1) * q ^ 2 := by
        rw [hcardJ]
        ring

#print axioms gaussSum_mul_conj_self
#print axioms sum_pair_indicator
#print axioms mellin_fourth_moment_wick_split

end ArkLib.ProximityGap.R344MellinWickSplit
