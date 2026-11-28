/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! # Power functions agreeing with a projectivity on a finite multiplicative group -/

namespace ProximityGap.PowerProjectivityMatches

open Finset Polynomial

variable {K G : Type*} [Field K] [Group G] [Fintype G]

/-- For a nonidentity source scaling the power matching equations have a nonzero
quadratic difference unless the projectivity is a scaling or a reciprocal scaling. -/
private theorem quadratic_nonzero (h l A B C E : K) (hh : h ≠ 0) (hne : h ≠ 1)
    (det : A * E - B * C ≠ 0) (nonscale : B ≠ 0 ∨ C ≠ 0) (nonrecip : A ≠ 0 ∨ E ≠ 0) :
    A * C * h * (1 - l) ≠ 0 ∨ A * E * (h - l) + B * C * (1 - l * h) ≠ 0 ∨ B * E * (1 - l) ≠ 0 := by
  by_cases hl : l = 1
  · right; left
    rw [hl]
    convert mul_ne_zero det (sub_ne_zero.mpr hne) using 1
    ring
  · have hn : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
    by_cases hAC : A * C = 0
    · right; right
      apply mul_ne_zero _ hn
      rcases mul_eq_zero.mp hAC with ha | hc
      · obtain he | he := nonrecip
        · exact False.elim (he ha)
        · apply mul_ne_zero _ he
          intro hb
          exact det (by simp [ha, hb])
      · obtain hb | hb := nonscale
        · apply mul_ne_zero hb
          intro he
          exact det (by simp [hc, he])
        · exact False.elim (hb hc)
    · exact Or.inl (mul_ne_zero (mul_ne_zero hAC hh) hn)

/-- On a finite multiplicative subgroup, if a power agrees with a projectivity at
`S.card` sites then every nonidentity ratio accounts for at most two ordered pairs.
The hypotheses on the matrix exclude the scaling and reciprocal-scaling cases. -/
theorem pair_count (i : G →* Kˣ) (hi : Function.Injective i) (S : Finset G) (k : ℕ)
    (A B C E : K) (det : A * E - B * C ≠ 0) (nonscale : B ≠ 0 ∨ C ≠ 0)
    (nonrecip : A ≠ 0 ∨ E ≠ 0)
    (hmatches : ∀ x ∈ S, (i x : K) ^ k * (C * (i x : K) + E) = A * (i x : K) + B) :
    S.card * (S.card - 1) ≤ 2 * (Fintype.card G - 1) := by
  classical
  let ratio (p : G × G) := p.2 * p.1⁻¹
  have maps : (S.offDiag : Set (G × G)).MapsTo ratio (univ.erase 1 : Finset G) := by
    intro p hp
    apply mem_erase.mpr
    refine ⟨?_, mem_univ _⟩
    intro he
    exact (mem_offDiag.mp hp).2.2 ((mul_inv_eq_one.mp he).symm)
  have fiber (h : G) (hh : h ∈ univ.erase (1 : G)) :
      (S.offDiag.filter (fun p => ratio p = h)).card ≤ 2 := by
    let T := S.offDiag.filter (fun p => ratio p = h)
    let z := (i h : K)
    let l := z ^ k
    let c₂ := A * C * z * (1 - l)
    let c₁ := A * E * (z - l) + B * C * (1 - l * z)
    let c₀ := B * E * (1 - l)
    let f : K[X] := Polynomial.C c₂ * X ^ 2 + Polynomial.C c₁ * X ^ 1 + Polynomial.C c₀
    have hn : z ≠ 1 := fun he => (mem_erase.mp hh).1 (hi (by
      apply Units.ext
      simpa [z] using he))
    have coeff := quadratic_nonzero z l A B C E (i h).ne_zero hn det nonscale nonrecip
    have degree : f.natDegree ≤ 2 := by
      exact natDegree_add_le_of_le (natDegree_add_le_of_le (natDegree_C_mul_X_pow_le c₂ 2)
        (natDegree_C_mul_X_pow_le c₁ 1)) (show (Polynomial.C c₀).natDegree ≤ 0 by simp)
    have second (p : T) : p.val.2 = h * p.val.1 := by
      have eq := (mem_filter.mp p.property).2
      change p.val.2 * p.val.1⁻¹ = h at eq
      rw [← eq, inv_mul_cancel_right]
    let site (p : T) : K := (i p.val.1 : K)
    have inj : Function.Injective site := by
      intro p q he
      have fst : p.val.1 = q.val.1 := hi (Units.ext he)
      exact Subtype.ext (Prod.ext fst (by rw [second p, second q, fst]))
    have zero (p : T) : f.eval (site p) = 0 := by
      obtain ⟨hp, hq,_⟩ := mem_offDiag.mp (mem_filter.mp p.property).1
      let x := site p
      have eq₁ : x ^ k * (C * x + E) = A * x + B := hmatches p.val.1 hp
      have eq₂ := hmatches p.val.2 hq
      rw [second p, map_mul, Units.val_mul] at eq₂
      change (z * x) ^ k * (C * (z * x) + E) = A * (z * x) + B at eq₂
      change f.eval x = 0
      simp only [f, eval_add, eval_mul, eval_pow, eval_X, eval_C, pow_one]
      dsimp only [c₂, c₁, c₀, l]
      rw [mul_pow] at eq₂
      linear_combination z ^ k * (C * (z * x) + E) * eq₁ - (C * x + E) * eq₂
    by_contra! large
    have big : 2 < Fintype.card T := (show 2 < T.card from large).trans_eq
      (Fintype.card_coe T).symm
    have allZero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero f inj zero (degree.trans_lt big)
    have hc (j : ℕ) := congrArg (fun g : K[X] => g.coeff j) allZero
    rcases coeff with h₂ | h₁ | h₀
    · apply h₂
      change c₂ = 0
      simpa [f, coeff_C_mul_X_pow, coeff_C] using hc 2
    · apply h₁
      change c₁ = 0
      simpa [f, coeff_C_mul_X_pow, coeff_C] using hc 1
    · apply h₀
      change c₀ = 0
      simpa [f, coeff_C_mul_X_pow, coeff_C] using hc 0
  calc
    S.card * (S.card - 1) = S.offDiag.card := by rw [offDiag_card, Nat.mul_sub, Nat.mul_one]
    _ = ∑ h ∈ univ.erase (1 : G), (S.offDiag.filter (fun p => ratio p = h)).card :=
      card_eq_sum_card_fiberwise maps
    _ ≤ ∑ _h ∈ univ.erase (1 : G), 2 := sum_le_sum fiber
    _ = 2 * (Fintype.card G - 1) := by simp [Nat.mul_comm]

#print axioms pair_count

end ProximityGap.PowerProjectivityMatches
