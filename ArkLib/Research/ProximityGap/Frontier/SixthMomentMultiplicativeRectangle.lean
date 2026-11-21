/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SixthMomentAntipodalShape

/-!
# Six-term relations containing a multiplicative rectangle

When four entries split into two pairs of the same ratio, their sum factors.
The resulting condition on the two remaining roots can be tested using the
nonzero cosets of pair sums alone. A rectangle with no internal opposite pair
cannot belong to a sextuple consisting of three opposite pairs.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SixthMomentMultiplicativeRectangle

open SixthMomentAntipodalShape
variable {F : Type*} [Field F] {n : ℕ}

/-- Recover the last two roots from one equation in the quotient by the roots of unity. -/
theorem pair_representation_iff {w : F} (hw : w ≠ 0) :
    (∃ a b : F, a^n = 1 ∧ b^n = 1 ∧ w = a+b) ↔
      ∃ s : F, s^n = 1 ∧ 1+s ≠ 0 ∧ w^n = (1+s)^n := by
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn], by simp, by simp [hn]⟩
    have ha0 : a ≠ 0 := by rintro rfl; simp [zero_pow hn] at ha
    have he : a * (1+b/a) = a+b := by field_simp
    refine ⟨b/a, by rw [div_pow,hb,ha,div_one], ?_, ?_⟩
    · intro h
      exact hw (by rw [← he,h,mul_zero])
    · rw [← he,mul_pow,ha,one_mul]
  · rintro ⟨s,hs,hs',ht⟩
    refine ⟨w/(1+s), w/(1+s)*s, ?_, ?_, ?_⟩
    · rw [div_pow,ht,div_self (pow_ne_zero _ hs')]
    · rw [mul_pow,div_pow,ht,div_self (pow_ne_zero _ hs'),hs,one_mul]
    · field_simp

/-- A nondegenerate four-entry rectangle has a six-term completion precisely at a
multiplicative relation among the projective pair signatures. -/
theorem rectangle_completion {r q : F} (hr : 1+r ≠ 0) (hq : 1+q ≠ 0) :
    (∃ a b : F, a^n = 1 ∧ b^n = 1 ∧ 1+r+q+r*q = a+b) ↔
      ∃ s : F, s^n = 1 ∧ 1+s ≠ 0 ∧ (1+r)^n*(1+q)^n = (1+s)^n := by
  rw [show 1+r+q+r*q = (1+r)*(1+q) by ring, ← mul_pow]
  exact pair_representation_iff (mul_ne_zero hr hq)

private theorem neg_invariant {S : Multiset F} (h : Pairable S) : S = S.map (- ·) := by
  obtain ⟨a,b,c,rfl⟩ := h
  simp only [pair, Multiset.map_add, Multiset.map_singleton, neg_neg]
  ac_rfl

/-- In a pairable sextuple, any four selected entries contain an internal opposite pair. -/
theorem four_entries_contain_opposites {A B : Multiset F} (h : Pairable (A+B))
    (hl : B.card < A.card) : ∃ x ∈ A, -x ∈ A := by
  classical
  by_contra! hn
  have hle : A ≤ B.map (- ·) := by
    apply Multiset.le_iff_count.mpr
    intro x
    by_cases hx : x ∈ A
    · have hz : x ∉ A.map (- ·) := by
        rintro hm
        obtain ⟨y,hy,he⟩ := Multiset.mem_map.mp hm
        exact hn x hx (by simpa [← he] using hy)
      have eq := congrArg (Multiset.count x) (neg_invariant h)
      simp only [Multiset.map_add, Multiset.count_add, Multiset.count_eq_zero_of_notMem hz,
        Nat.zero_add] at eq
      omega
    · simp [Multiset.count_eq_zero_of_notMem hx]
  have hc := Multiset.card_le_card hle
  simp at hc
  omega

/-- The only possible internal opposite pairs in a nondegenerate multiplicative
rectangle lie on its two diagonals. This necessity holds for any two final entries. -/
theorem pairable_rectangle_diagonal {r q a b : F} (htwo : (2:F) ≠ 0)
    (hr : r ≠ 0) (hq : q ≠ 0) (hr' : 1+r ≠ 0) (hq' : 1+q ≠ 0)
    (h : Pairable (({1}+{r}+{q}+{r*q}) + ({a}+{b}))) : 1+r*q=0 ∨ r+q=0 := by
  obtain ⟨x,hx,hneg⟩ := four_entries_contain_opposites h (by simp)
  by_contra! hn
  have hrq := mul_ne_zero hr hq
  have hrr := mul_ne_zero htwo hr
  have hqq := mul_ne_zero htwo hq
  have hrrqq := mul_ne_zero htwo hrq
  have hra := mul_ne_zero hr hq'
  have hqa := mul_ne_zero hq hr'
  simp only [Multiset.mem_add, Multiset.mem_singleton] at hx hneg
  rcases hx with ((hx|hx)|hx)|hx <;> subst x <;>
    rcases hneg with ((he|he)|he)|he
  all_goals first
    | exact htwo (by linear_combination -he)
    | exact hr' (by linear_combination -he)
    | exact hq' (by linear_combination -he)
    | exact hn.1 (by linear_combination -he)
    | exact hn.2 (by linear_combination -he)
    | exact hrr (by linear_combination -he)
    | exact hqq (by linear_combination -he)
    | exact hrrqq (by linear_combination -he)
    | exact hra (by linear_combination -he)
    | exact hqa (by linear_combination -he)

/-- The doubled-sum exclusion precludes a zero sum of three roots. -/
theorem triple_sum_ne_zero {H : Set F} (h : FourTermConditions H)
    {a b c : F} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) : a+b+c ≠ 0 := by
  intro e
  have hneg := h.neg_mem c hc
  have hz := h.doubles a ha b hb (-c) hneg (-c) hneg (by linear_combination 2*e)
  have hc0 : c = 0 := by linear_combination e-hz
  exact h.ne_neg c hc (by simp [hc0])

/-- Three pairs of the same multiplicative ratio in a six-term zero sum must be opposite. -/
theorem same_ratio {H : Set F} (h : FourTermConditions H) {a b c r : F}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (hs : a+a*r+b+b*r+c+c*r = 0) : r = -1 := by
  have he : (a+b+c)*(1+r) = 0 := by linear_combination hs
  have hr := (mul_eq_zero.mp he).resolve_left (triple_sum_ne_zero h ha hb hc)
  linear_combination hr

#print axioms rectangle_completion
#print axioms four_entries_contain_opposites
#print axioms pairable_rectangle_diagonal
#print axioms same_ratio

end ArkLib.ProximityGap.Frontier.SixthMomentMultiplicativeRectangle
