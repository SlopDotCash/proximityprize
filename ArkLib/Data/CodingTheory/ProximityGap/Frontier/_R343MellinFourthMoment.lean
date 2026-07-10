/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R342MellinLevelSet

/-!
# R343: the exact fourth moment of the Mellin sum (depth-2 rung of the tower)

Fifth brick of the Gauss-phase PAPR arc (_R339 identity, _R340 autocorrelation,
_R341/_R342 Parseval + level set). The fourth moment over frequencies collapses by
character orthogonality to the congruence-constrained Gauss-phase energy:

  `∑_{b≠0} (S_b·conj S_b)² = (q−1) · ∑_{j₁,j₃,k₁,k₃ ∈ J, j₁+j₃ ≡ k₁+k₃ (mod t)}
        τ_{j₁} τ_{j₃} conj(τ_{k₁}) conj(τ_{k₃})`.

This is the EXACT depth-2 rung of the moment tower: the additive-energy structure of
the Mellin frequencies (solutions of `j₁+j₃ ≡ k₁+k₃ mod t`) weighted by Gauss phases.
The diagonal solutions (`{j₁,j₃} = {k₁,k₃}`) contribute `≈ 2·((t−1)q)²/(q−1)·(q−1)`
(the Wick/Gaussian prediction); everything the open core asks at depth 2 is whether
the `t`-wraparound off-diagonal classes cancel — the same wraparound-window question
as the DC-subtracted energy face, now in exact Mellin coordinates.

* `char_orthogonality` — `∑_{b≠0} λ₁⁻¹(b)·λ₂(b) = (q−1)·[λ₁ = λ₂]` for any two
  multiplicative characters (generalizes r341's frequency orthogonality).
* `chi_pow_eq_iff_modEq` — `χ^{da} = χ^{db} ↔ a ≡ b (mod t)` for full-order `χ`.
* `mellin_fourth_moment` — the boxed identity.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.R343MellinFourthMoment

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.R342MellinLevelSet

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Generalized character orthogonality**: for any two multiplicative characters,
`∑_{b≠0} λ₁⁻¹(b)·λ₂(b)` is `q−1` when `λ₁ = λ₂` and `0` otherwise. -/
theorem char_orthogonality (lam₁ lam₂ : MulChar F ℂ) :
    ∑ b ∈ Finset.univ.erase (0 : F), (lam₁⁻¹) b * lam₂ b
      = if lam₁ = lam₂ then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
  classical
  by_cases hl : lam₁ = lam₂
  · subst hl
    rw [if_pos rfl]
    have hone : ∀ b ∈ Finset.univ.erase (0 : F), (lam₁⁻¹) b * lam₁ b = 1 := by
      intro b hb
      have hbne : b ≠ 0 := Finset.ne_of_mem_erase hb
      have hne : lam₁ b ≠ 0 := by
        intro h0
        have hn := norm_mulChar_apply_unit lam₁ hbne
        rw [h0, norm_zero] at hn
        norm_num at hn
      rw [MulChar.inv_apply_eq_inv' lam₁ b, inv_mul_cancel₀ hne]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  · rw [if_neg hl]
    set μ : MulChar F ℂ := lam₂ * lam₁⁻¹ with hμ
    have hμapply : ∀ b : F, (lam₁⁻¹) b * lam₂ b = μ b := by
      intro b
      rw [hμ, MulChar.mul_apply]
      ring
    have hμne : μ ≠ 1 := by
      intro hcontra
      exact hl (mul_inv_eq_one.mp hcontra).symm
    have hzero : ∑ b : F, μ b = 0 := MulChar.sum_eq_zero_of_ne_one hμne
    have hsplit0 : ∑ b : F, μ b = μ 0 + ∑ b ∈ Finset.univ.erase (0 : F), μ b := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
    rw [Finset.sum_congr rfl fun b _ => hμapply b]
    have hμ0 : μ 0 = 0 := MulChar.map_nonunit μ (by simp)
    rw [hsplit0, hμ0, zero_add] at hzero
    exact hzero

/-- For full-order `χ` and `t·d = q−1`: `χ^{da} = χ^{db} ↔ a ≡ b (mod t)`. -/
theorem chi_pow_eq_iff_modEq {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1) (a b : ℕ) :
    χ ^ (d * a) = χ ^ (d * b) ↔ a ≡ b [MOD (Fintype.card F - 1) / d] := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hfin : IsOfFinOrder χ := by
    rw [← orderOf_pos_iff, hord]
    have := Fintype.one_lt_card (α := F)
    omega
  rw [hfin.pow_eq_pow_iff_modEq, hord, ← htd, mul_comm t d]
  exact Nat.ModEq.mul_left_cancel_iff' hd0.ne'

/-- **The exact fourth moment**: over the `q−1` nonzero frequencies,

  `∑_{b≠0} (S_b·conj S_b)² = (q−1)·∑_{j₁,j₃,k₁,k₃ ∈ J}
      [j₁+j₃ ≡ k₁+k₃ (mod t)]·τ_{j₁}τ_{j₃}·conj(τ_{k₁})·conj(τ_{k₃})`.

The depth-2 moment rung in exact form: additive-energy classes of Mellin
frequencies mod `t`, weighted by Gauss phases. -/
theorem mellin_fourth_moment {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) :
    ∑ b ∈ Finset.univ.erase (0 : F),
        (mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)) ^ 2
      = ((Fintype.card F - 1 : ℕ) : ℂ)
          * ∑ j₁ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
            ∑ j₃ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
            ∑ k₁ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
            ∑ k₃ ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
              if (j₁ + j₃) ≡ (k₁ + k₃) [MOD (Fintype.card F - 1) / d]
              then gaussSum (χ ^ (d * j₁)) ψ * gaussSum (χ ^ (d * j₃)) ψ
                  * (starRingEnd ℂ) (gaussSum (χ ^ (d * k₁)) ψ)
                  * (starRingEnd ℂ) (gaussSum (χ ^ (d * k₃)) ψ)
              else 0 := by
  classical
  set t := (Fintype.card F - 1) / d with ht
  set J : Finset ℕ := (Finset.range t).erase 0 with hJ
  set τ : ℕ → ℂ := fun j => gaussSum (χ ^ (d * j)) ψ with hτ
  -- the merged per-tuple character factor
  set Ch : ℕ → ℕ → ℕ → ℕ → F → ℂ := fun j₁ j₃ k₁ k₃ b =>
    ((χ ^ (d * (j₁ + j₃)))⁻¹) b * (χ ^ (d * (k₁ + k₃))) b with hCh
  -- Step 1: expand the square of |S|² into the four-fold sum
  have hdouble : ∀ b : F,
      mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)
      = ∑ j ∈ J, ∑ k ∈ J,
          (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
            * (τ j * (starRingEnd ℂ) (τ k)) := by
    intro b
    unfold mellinSum
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    have hconj : (starRingEnd ℂ) (((χ ^ (d * k))⁻¹) b) = (χ ^ (d * k)) b := by
      rw [conj_mulChar_apply, inv_inv]
    rw [hconj, hτ]
    ring
  have hexpand : ∀ b : F,
      (mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)) ^ 2
      = ∑ j₁ ∈ J, ∑ j₃ ∈ J, ∑ k₁ ∈ J, ∑ k₃ ∈ J,
          Ch j₁ j₃ k₁ k₃ b
            * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)) := by
    intro b
    rw [sq, hdouble b, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_mul_sum]
    -- now: ∑ k₁ ∑ j₃ (T j₁ k₁ * T j₃ k₃-sum) — reorder to ∑ j₃ ∑ k₁ ∑ k₃
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₃ _ => ?_
    refine Finset.sum_congr rfl fun k₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₃ _ => ?_
    -- merge the character factors
    have hsplitInv : ((χ ^ (d * (j₁ + j₃)))⁻¹ : MulChar F ℂ)
        = (χ ^ (d * j₁))⁻¹ * (χ ^ (d * j₃))⁻¹ := by
      rw [Nat.mul_add, pow_add, mul_inv]
    have hsplitPos : (χ ^ (d * (k₁ + k₃)) : MulChar F ℂ)
        = (χ ^ (d * k₁)) * (χ ^ (d * k₃)) := by
      rw [Nat.mul_add, pow_add]
    rw [hCh]
    simp only [hsplitInv, hsplitPos, MulChar.mul_apply]
    ring
  rw [Finset.sum_congr rfl fun b _ => hexpand b]
  -- Step 2: move the b-sum inside the four index sums
  rw [Finset.sum_comm]
  have hs1 : ∀ j₁ : ℕ, ∑ b ∈ Finset.univ.erase (0 : F), ∑ j₃ ∈ J, ∑ k₁ ∈ J, ∑ k₃ ∈ J,
      Ch j₁ j₃ k₁ k₃ b * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃))
      = ∑ j₃ ∈ J, ∑ b ∈ Finset.univ.erase (0 : F), ∑ k₁ ∈ J, ∑ k₃ ∈ J,
      Ch j₁ j₃ k₁ k₃ b * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)) :=
    fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun j₁ _ => hs1 j₁]
  have hs2 : ∀ j₁ j₃ : ℕ, ∑ b ∈ Finset.univ.erase (0 : F), ∑ k₁ ∈ J, ∑ k₃ ∈ J,
      Ch j₁ j₃ k₁ k₃ b * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃))
      = ∑ k₁ ∈ J, ∑ b ∈ Finset.univ.erase (0 : F), ∑ k₃ ∈ J,
      Ch j₁ j₃ k₁ k₃ b * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)) :=
    fun _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₃ _ => hs2 j₁ j₃]
  have hs3 : ∀ j₁ j₃ k₁ : ℕ, ∑ b ∈ Finset.univ.erase (0 : F), ∑ k₃ ∈ J,
      Ch j₁ j₃ k₁ k₃ b * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃))
      = ∑ k₃ ∈ J, ∑ b ∈ Finset.univ.erase (0 : F),
      Ch j₁ j₃ k₁ k₃ b * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)) :=
    fun _ _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₃ _ =>
    Finset.sum_congr rfl fun k₁ _ => hs3 j₁ j₃ k₁]
  -- Step 3: evaluate each inner b-sum via orthogonality + the modular criterion
  have hinner : ∀ j₁ j₃ k₁ k₃ : ℕ,
      ∑ b ∈ Finset.univ.erase (0 : F), Ch j₁ j₃ k₁ k₃ b
          * (τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃))
      = ((Fintype.card F - 1 : ℕ) : ℂ)
          * (if (j₁ + j₃) ≡ (k₁ + k₃) [MOD t]
             then τ j₁ * τ j₃ * (starRingEnd ℂ) (τ k₁) * (starRingEnd ℂ) (τ k₃)
             else 0) := by
    intro j₁ j₃ k₁ k₃
    rw [← Finset.sum_mul]
    have horth := char_orthogonality (F := F)
      (χ ^ (d * (j₁ + j₃))) (χ ^ (d * (k₁ + k₃)))
    rw [hCh]
    rw [horth]
    by_cases hcong : (j₁ + j₃) ≡ (k₁ + k₃) [MOD t]
    · rw [if_pos ((chi_pow_eq_iff_modEq hd hd0 hord _ _).mpr hcong), if_pos hcong]
    · rw [if_neg (fun heq => hcong ((chi_pow_eq_iff_modEq hd hd0 hord _ _).mp heq)),
        if_neg hcong, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₃ _ =>
    Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₃ _ =>
      hinner j₁ j₃ k₁ k₃]
  -- Step 4: pull the constant (q−1) out through the four sums
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j₃ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  rw [Finset.mul_sum]

#print axioms char_orthogonality
#print axioms chi_pow_eq_iff_modEq
#print axioms mellin_fourth_moment

end ArkLib.ProximityGap.R343MellinFourthMoment
