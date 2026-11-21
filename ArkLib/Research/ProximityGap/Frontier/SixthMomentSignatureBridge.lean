/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SixthMomentAntipodalShape

/-!
# Two signature comparisons for repeated entries in a zero sum of length six

Raising to the subgroup order removes a multiplicative subgroup factor. This
turns the two restricted additive equations into comparisons of field values.
The full set of nonzero difference signatures can be represented on one half of
the cyclic subgroup because inversion preserves the signature at even order.
-/

namespace ArkLib.ProximityGap.Frontier.SixthMomentSignatureBridge

open SixthMomentAntipodalShape

variable {F : Type*} [Field F] {n : ℕ}

/-- Signatures of nonzero differences after division by one of the two roots. -/
def signatures (F : Type*) [Field F] (n : ℕ) : Set F :=
  {v | ∃ x : F, x ^ n = 1 ∧ x ≠ 1 ∧ (x - 1) ^ n = v}

private theorem root_ne_zero (hn : n ≠ 0) {a : F} (ha : a ^ n = 1) : a ≠ 0 := by
  rintro rfl
  simp [zero_pow hn] at ha

/-- Inverse roots give identical difference signatures, justifying the half-window. -/
theorem signature_inv (hn : n ≠ 0) (heven : Even n) {x : F} (hx : x ^ n = 1) :
    (x⁻¹ - 1) ^ n = (x - 1) ^ n := by
  have h : x⁻¹ - 1 = -(x - 1) / x := by field_simp [root_ne_zero hn hx]; ring
  rw [h, div_pow, heven.neg_pow, hx, div_one]

/-- Every difference signature occurs in the integer range used by the scans. -/
theorem signature_half_window [NeZero n] {g : F} (hg : IsPrimitiveRoot g n)
    (heven : Even n) {v : F} (hv : v ∈ signatures F n) :
    ∃ i, 1 ≤ i ∧ i ≤ n / 2 ∧ (g ^ i - 1) ^ n = v := by
  obtain ⟨x, hx, hx1, rfl⟩ := hv
  obtain ⟨j, hj, hjx⟩ := hg.eq_pow_of_pow_eq_one hx
  have hjpos : 0 < j := Nat.pos_of_ne_zero (fun e => hx1 (by simpa [e] using hjx.symm))
  by_cases hhalf : j ≤ n / 2
  · exact ⟨j, hjpos, hhalf, by rw [hjx]⟩
  · have hprod : g ^ (n-j) * x = 1 := by rw [← hjx, ← pow_add, Nat.sub_add_cancel hj.le, hg.pow_eq_one]
    have hi : g ^ (n-j) = x⁻¹ := by
      apply mul_right_cancel₀ (root_ne_zero (NeZero.ne n) hx)
      simpa [root_ne_zero (NeZero.ne n) hx] using hprod
    exact ⟨n-j, by omega, by omega, by rw [hi, signature_inv (NeZero.ne n) heven hx]⟩

private theorem sum_signature (hn : n ≠ 0) (heven : Even n) {a b : F}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hsum : a + b ≠ 0) :
    (a + b) ^ n ∈ signatures F n := by
  have hb0 : -b ≠ 0 := neg_ne_zero.mpr (root_ne_zero hn hb)
  have hbn : (-b) ^ n = 1 := by rwa [heven.neg_pow]
  refine ⟨a / (-b), by rw [div_pow, ha, hbn, div_one], ?_, ?_⟩
  · intro h
    have hab := (div_eq_one_iff_eq hb0).mp h
    apply hsum
    rw [hab, neg_add_cancel]
  · have h : a / (-b) - 1 = (a + b) / (-b) := by
      field_simp [root_ne_zero hn hb]
      ring
    rw [h, div_pow, hbn, div_one]

/-- The Sidon law and two finite signature comparisons give exactly the hypotheses
needed for the multiplicity and orbit classification of six-term zero sums. -/
theorem fourTermConditions_of_signatures
    (hn : n ≠ 0) (heven : Even n) (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ^ n ≠ 1)
    (hsidon : ∀ a b c d : F, a ^ n = 1 → b ^ n = 1 → c ^ n = 1 → d ^ n = 1 →
      a + b = c + d → a + b = 0 ∨ a = c ∨ a = d)
    (hdoubled : ∀ v ∈ signatures F n, (2 : F) ^ n * v ∉ signatures F n)
    (htriple : ∀ x : F, x ^ n = 1 → x ≠ 1 → ((3 : F) - x) ^ n ∉ signatures F n) :
    FourTermConditions {x : F | x ^ n = 1} where
  neg_mem a ha := (heven.neg_pow a).trans ha
  ne_neg a ha heq := by
    have hzero : (2 : F) * a = 0 := by linear_combination heq
    exact (root_ne_zero hn ha) ((mul_eq_zero.mp hzero).resolve_left htwo)
  sidon a ha b hb c hc d hd := hsidon a b c d ha hb hc hd
  triple a ha b hb c hc d hd hsum := by
    by_contra hne
    have ha0 := root_ne_zero hn ha
    have hx : (b/a) ^ n = 1 := by rw [div_pow, hb, ha, div_one]
    have hx1 : b/a ≠ 1 := fun h => hne ((div_eq_one_iff_eq ha0).mp h).symm
    have hrel : 3 - b/a = (c+d)/a := by
      field_simp [ha0]
      linear_combination hsum
    have hcd : c + d ≠ 0 := by
      intro hz
      rw [hz, zero_div] at hrel
      exact hthree ((sub_eq_zero.mp hrel) ▸ hx)
    apply htriple (b/a) hx hx1
    rw [hrel, div_pow, ha, div_one]
    exact sum_signature hn heven hc hd hcd
  doubles a ha b hb c hc d hd hsum := by
    by_contra hab
    have hcd : c + d ≠ 0 := hsum ▸ mul_ne_zero htwo hab
    apply hdoubled _ (sum_signature hn heven ha hb hab)
    rw [← mul_pow, hsum]
    exact sum_signature hn heven hc hd hcd

/-- The two finite cross-comparisons, with the exact directed and undirected
exponent ranges of the verifier, suffice for the four-term conditions. -/
theorem fourTermConditions_of_window_checks [NeZero n] {g : F} (hg : IsPrimitiveRoot g n)
    (heven : Even n) (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ^ n ≠ 1)
    (hsidon : ∀ a b c d : F, a ^ n = 1 → b ^ n = 1 → c ^ n = 1 → d ^ n = 1 →
      a + b = c + d → a + b = 0 ∨ a = c ∨ a = d)
    (hd : ∀ i, 1 ≤ i → i ≤ n / 2 → ∀ j, 1 ≤ j → j ≤ n / 2 →
      (2 : F) ^ n * (g ^ i - 1) ^ n ≠ (g ^ j - 1) ^ n)
    (ht : ∀ i, 1 ≤ i → i < n → ∀ j, 1 ≤ j → j ≤ n / 2 →
      ((3 : F) - g ^ i) ^ n ≠ (g ^ j - 1) ^ n) :
    FourTermConditions {x : F | x ^ n = 1} := by
  apply fourTermConditions_of_signatures (NeZero.ne n) heven htwo hthree hsidon
  · intro v hv hv'
    obtain ⟨i, hi, hi', hvi⟩ := signature_half_window hg heven hv
    obtain ⟨j, hj, hj', hvj⟩ := signature_half_window hg heven hv'
    exact hd i hi hi' j hj hj' (by rw [hvi, hvj])
  · intro x hx hx1 hv
    obtain ⟨i, hi, rfl⟩ := hg.eq_pow_of_pow_eq_one hx
    obtain ⟨j, hj, hj', hvj⟩ := signature_half_window hg heven hv
    have hp : 0 < i := Nat.pos_of_ne_zero (fun e => hx1 (by simp [e]))
    exact ht i hp hi j hj hj' hvj.symm

#print axioms signature_inv
#print axioms signature_half_window
#print axioms fourTermConditions_of_signatures
#print axioms fourTermConditions_of_window_checks

end ArkLib.ProximityGap.Frontier.SixthMomentSignatureBridge
