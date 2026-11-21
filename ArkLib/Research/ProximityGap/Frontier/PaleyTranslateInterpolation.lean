/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Affine checks on punctured Legendre translates

On at most half of the coordinates of an odd prime field, the translated quadratic
characters already have full affine hull over that field. Even shifts outside the
chosen coordinates suffice. Thus fitting all these words into a translated linear
code on these coordinates requires the full ambient space.
-/

namespace ProximityGap.PaleyTranslateInterpolation

open Polynomial Finset

variable {p n : ℕ} [Fact p.Prime]

/-- A constant linear check on more than half the shifts forces all its weights to vanish.
The coordinates may be any distinct field elements. -/
theorem translate_check_trivial (hp : p ≠ 2) (x : Fin n ↪ ZMod p) (hn : n ≤ p / 2)
    (B : Finset (ZMod p)) (hB : p / 2 < B.card) (c : Fin n → ZMod p) (t : ZMod p)
    (hcheck : ∀ b ∈ B, ∑ i, c i * (quadraticChar (ZMod p) (x i - b) : ZMod p) = t) :
    c = 0 := by
  classical
  let d := p / 2
  let P : (ZMod p)[X] := ∑ i, C (c i) * (X + C (x i)) ^ d
  have hdegree : P.natDegree ≤ d := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    apply (natDegree_C_mul_le ..).trans
    simp [Polynomial.natDegree_pow]
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ringChar.eq (ZMod p) p]
  have hpoly : P = C t := by
    apply sub_eq_zero.mp
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P - C t)
      (f := fun b : B => -(b : ZMod p)) (neg_injective.comp Subtype.val_injective)
    · intro b
      have h := hcheck b b.property
      simp_rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card] at h
      simpa [P, eval_finsetSum, sub_eq_add_neg, add_comm, d] using sub_eq_zero.mpr h
    · rw [Fintype.card_coe]
      exact (natDegree_sub_le _ _).trans_lt ((max_le hdegree (by simp)).trans_lt hB)
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero x.injective
  intro j
  let k := d - j.val
  have hj : j.val < d := j.isLt.trans_le hn
  have hk : k ≠ 0 := Nat.sub_ne_zero_of_lt hj
  have hsub : d - k = j.val := by dsimp [k]; omega
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff k) hpoly
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow, hsub,
    coeff_C, hk, ↓reduceIte] at hc
  have hprime := Fact.out (p := p.Prime)
  have hd : d < p := Nat.div_lt_self hprime.pos (by decide)
  have hchoose : (d.choose k : ZMod p) ≠ 0 :=
    fun h => hprime.coprime_iff_not_dvd.mp (hprime.coprime_choose_of_lt hd (Nat.sub_le ..))
      ((ZMod.natCast_eq_zero_iff _ _).mp h)
  apply (mul_eq_zero.mp _).resolve_right hchoose
  rw [Finset.sum_mul]
  simpa only [mul_assoc] using hc

/-- Outside the puncturing set, the translates still admit no nonzero affine check. -/
theorem off_domain_translate_check_trivial (hp : p ≠ 2) (x : Fin n ↪ ZMod p)
    (hn : n ≤ p / 2) (c : Fin n → ZMod p) (t : ZMod p)
    (hcheck : ∀ b ∉ Set.range x, ∑ i, c i * (quadraticChar (ZMod p) (x i - b) : ZMod p) = t) :
    c = 0 := by
  classical
  let B := (univ.map x)ᶜ
  apply translate_check_trivial hp x hn B _ c t
  · intro b hb
    apply hcheck
    simpa [B] using hb
  · obtain ⟨r, hr⟩ := Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp
    simpa [B, Finset.card_compl, ZMod.card] using (show p / 2 < p - n by omega)

/-- Every affine translate of a linear code containing the off-domain Legendre words
on these coordinates is the whole word space. -/
theorem code_eq_top_of_off_domain_translates (hp : p ≠ 2) (x : Fin n ↪ ZMod p)
    (hn : n ≤ p / 2) (V : Submodule (ZMod p) (Fin n → ZMod p)) (center : Fin n → ZMod p)
    (hmem : ∀ b ∉ Set.range x,
      (fun i => (quadraticChar (ZMod p) (x i - b) : ZMod p)) - center ∈ V) :
    V = ⊤ := by
  classical
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply V.dualAnnihilator.eq_bot_iff.mpr
  intro L hL
  let c (i : Fin n) := L (fun j => if i = j then 1 else 0)
  have hsum (v : Fin n → ZMod p) : ∑ i, c i * v i = L v := by
    simpa only [c, smul_eq_mul, mul_comm] using (L.pi_apply_eq_sum_univ v).symm
  have hc : c = 0 := by
    apply off_domain_translate_check_trivial hp x hn c (L center)
    intro b hb
    rw [hsum]
    have h := (Submodule.mem_dualAnnihilator L).mp hL _ (hmem b hb)
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  apply LinearMap.ext
  intro v
  simpa [hc] using (hsum v).symm

#print axioms code_eq_top_of_off_domain_translates
#print axioms translate_check_trivial
#print axioms off_domain_translate_check_trivial

end ProximityGap.PaleyTranslateInterpolation
