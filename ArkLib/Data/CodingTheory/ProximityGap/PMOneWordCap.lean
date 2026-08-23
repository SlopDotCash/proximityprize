/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ClassSupplyFloor

/-!
# The ±1-word agreement cap: the character family is capped, by theorem (#389)

The supply-side arc found the `±1`-valued (character-style) words to be the measured
extremizers of the agreement-capped per-word supply.  The probes verified the cap
numerically; this file proves it **in general** — no per-instance `decide`:

> **`pm_one_agreement_le`** — for a word `w` with values in `{1, −1}`, every codeword
> of `rsCode dom k` agrees with `w` on at most `max (2k−2) (max s₊ s₋)` points, where
> `s±` are the value-class sizes.  Mechanism: a degree-`< k` polynomial agreeing on
> more than `2k−2` points satisfies `P² = 1` there beyond the degree of `P² − 1`, so
> `P² = 1` identically, hence `P = ±1` constant (field), and constant agreement is a
> class size.

Combined with `class_supply_floor`, this makes the character family's role formal: at
balanced instances (`s± = n/2 ≥ 2k−2`) the word is **agreement-capped at `n/2`** while
carrying **`≥ C(n/2, k+m+1)` explainable cores** — the machine-checked statement that
the capped supply of residual (b) is class-covering-shaped (`C(n/2, t)`, exponentially
above the random mean `C(n,t)/q^{m+1}`).  Any positive supply route must absorb exactly
this family.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The ±1-word agreement cap.**  Every codeword of `rsCode dom k` (`1 ≤ k`) agrees
with a `{1, −1}`-valued word on at most `max (2k−2) (max s₊ s₋)` points. -/
theorem pm_one_agreement_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {w : Fin n → F} (hw : ∀ i, w i = 1 ∨ w i = -1)
    {c : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => c i = w i)).card
      ≤ max (2 * k - 2)
          (max ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card
               ((Finset.univ : Finset (Fin n)).filter (fun i => w i = -1)).card) := by
  classical
  obtain ⟨P, hPdeg, rfl⟩ := hc
  set A := (Finset.univ : Finset (Fin n)).filter
    (fun i => P.eval (dom i) = w i) with hA
  by_cases hbig : A.card ≤ 2 * k - 2
  · exact le_trans hbig (le_max_left _ _)
  push_neg at hbig
  -- P² − 1 vanishes on A, which exceeds its degree: P² = 1
  have hQdeg : (P * P - 1 : F[X]).degree < ((2 * k - 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · rcases eq_or_ne P 0 with rfl | hP0
      · rw [zero_mul, Polynomial.degree_zero]
        exact_mod_cast WithBot.bot_lt_coe _
      · have hPnat : P.natDegree < k :=
          (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
        have hPP0 : P * P ≠ 0 := mul_ne_zero hP0 hP0
        refine (Polynomial.natDegree_lt_iff_degree_lt hPP0).mp ?_
        rw [Polynomial.natDegree_mul hP0 hP0]
        omega
    · calc (1 : F[X]).degree ≤ 0 := Polynomial.degree_one_le
      _ < ((2 * k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : 0 < 2 * k - 1)
  have hQzero : ∀ i ∈ A, (P * P - 1 : F[X]).eval (dom i) = 0 := by
    intro i hi
    have hval := (Finset.mem_filter.mp hi).2
    rcases hw i with h1 | h1 <;>
      · rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one, hval, h1]
        ring
  have hQ : (P * P - 1 : F[X]) = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (s := A.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ dom.injective]
      exact lt_of_lt_of_le hQdeg (by exact_mod_cast (by omega : 2 * k - 1 ≤ A.card))
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hQzero i hi
  -- P² = 1 ⟹ P = 1 or P = −1
  have hPP : (P - 1) * (P + 1) = 0 := by
    have : P * P - 1 = (P - 1) * (P + 1) := by ring
    rw [← this, hQ]
  rcases mul_eq_zero.mp hPP with h | h
  · have hP1 : P = 1 := by linear_combination h
    refine le_trans (le_trans (Finset.card_le_card ?_) (le_max_left _ _)) (le_max_right _ _)
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [hP1] at this
    simp only [Polynomial.eval_one] at this
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.symm⟩
  · have hP1 : P = -1 := by linear_combination h
    refine le_trans (le_trans (Finset.card_le_card ?_) (le_max_right _ _)) (le_max_right _ _)
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [hP1] at this
    simp only [Polynomial.eval_neg, Polynomial.eval_one] at this
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.symm⟩

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.pm_one_agreement_le
