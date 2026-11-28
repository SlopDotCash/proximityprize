/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Support of moments on a dyadic multiplicative coset -/

namespace ProximityGap.DyadicMomentSupport

open Finset
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The unnormalized moment of weights on the displayed sites. -/
def moment (T : Finset K) (w : K → K) (j : ℕ) : K := ∑ x ∈ T, w x * x ^ j

private noncomputable def mark (x : K) : ℕ := by
  classical
  exact if x = 0 then 0 else 1

/-- The number of nonzero moments before the cutoff. -/
noncomputable def count (n : ℕ) (f : ℕ → K) : ℕ := ∑ j ∈ range n, mark (f j)

private theorem count_double (n : ℕ) (f : ℕ → K) :
    count (2 * n) f = ∑ j ∈ range n, (mark (f j) + mark (f (j + n))) := by
  simp [count, two_mul, sum_range_add, sum_add_distrib, Nat.add_comm]

private theorem shift (T : Finset K) (w : K → K) (n j : ℕ) (v : K)
    (h : ∀ x ∈ T, x ^ n = v) : moment T w (j + n) = v * moment T w j := by
  simp only [moment, mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [pow_add, h x hx]
  ring

private theorem separate {e o v z : K} (hv : v ≠ z) (h : e + o = 0) (h' : v * e + z * o = 0) :
    e = 0 ∧ o = 0 := by
  have he : (v - z) * e = 0 := by linear_combination h' - z * h
  have := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hv)
  exact ⟨this, by simpa [this] using h⟩

private theorem mark_pair {x y a : K} (h : x = 0 → y = 0 → a = 0) :
    mark a ≤ mark x + mark y := by
  classical
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases ha : a = 0 <;> simp_all [mark]

/-- On a coset with a common nonzero power of order a power of two, fewer than
`2 ^ (a + 1)` occupied sites force at least `2 ^ k / 2 ^ a` nonzero moments. -/
theorem support_bound (k a : ℕ) (T : Finset K) (w : K → K) (c : K)
    (hc : c ≠ 0) (hT : T.Nonempty) (hpow : ∀ x ∈ T, x ^ (2 ^ k) = c)
    (hw : ∀ x ∈ T, w x ≠ 0) (hcard : T.card < 2 ^ (a + 1)) :
    2 ^ k ≤ 2 ^ a * count (2 ^ k) (moment T w) := by
  classical
  induction k generalizing a T c with
  | zero =>
    obtain ⟨x, hx⟩ := hT
    have hsingle : T = {x} := by
      ext y
      simp only [mem_singleton]
      constructor
      · intro hy
        simpa using (hpow y hy).trans (hpow x hx).symm
      · rintro rfl
        exact hx
    have hweight := hw x hx
    rw [hsingle]
    simpa [count, moment, mark, hweight] using (Nat.one_le_two_pow (n := a))
  | succ k ih =>
    let n := 2 ^ k
    obtain ⟨u, hu⟩ := hT
    let v := u ^ n
    have hv : v ≠ 0 := by
      intro h
      have hc' := hpow u hu
      rw [pow_succ, pow_mul, show u ^ (2 ^ k) = 0 from h] at hc'
      simp_all
    let E := T.filter (fun x => x ^ n = v)
    let O := T.filter (fun x => x ^ n ≠ v)
    have hE : E.Nonempty := ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩
    have ein : E ⊆ T := filter_subset _ _
    have oin : O ⊆ T := filter_subset _ _
    have ep : ∀ x ∈ E, x ^ n = v := fun _ h => (mem_filter.mp h).2
    have op : ∀ x ∈ O, x ^ n = -v := by
      intro x hx
      have hs := (hpow x (oin hx)).trans (hpow u hu).symm
      rw [pow_succ, pow_mul, pow_mul] at hs
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs).resolve_left (mem_filter.mp hx).2
    have double : 2 ^ (k + 1) = 2 * n := by simp [n, pow_succ, Nat.mul_comm]
    rw [double]
    by_cases ho : O.Nonempty
    · have diff : v ≠ -v := by
        obtain ⟨x, hx⟩ := ho
        exact fun h => (mem_filter.mp hx).2 ((op x hx).trans h.symm)
      have parts (j : ℕ) : moment E w j + moment O w j = moment T w j := by
        exact sum_filter_add_sum_filter_not _ _ _
      have vanish (j : ℕ) (h : moment T w j = 0) (h' : moment T w (j + n) = 0) :
          moment E w j = 0 ∧ moment O w j = 0 := by
        have h0 := (parts j).trans h
        have h1 := (parts (j + n)).trans h'
        rw [shift E w n j v ep, shift O w n j (-v) op] at h1
        exact separate diff h0 h1
      have bound (S : Finset K)
          (van : ∀ j, moment T w j = 0 → moment T w (j + n) = 0 → moment S w j = 0) :
          count n (moment S w) ≤ count (2 * n) (moment T w) := by
        rw [count_double]
        apply sum_le_sum
        intro j _
        exact mark_pair (van j)
      have sizes : E.card + O.card = T.card := card_filter_add_card_filter_not _
      cases a with
      | zero =>
        have := card_pos.mpr hE
        have := card_pos.mpr ho
        simp at hcard
        omega
      | succ a =>
        have small : E.card < 2 ^ (a + 1) ∨ O.card < 2 ^ (a + 1) := by
          rw [pow_succ (2 : ℕ) (a + 1)] at hcard
          omega
        have half : n ≤ 2 ^ a * count (2 * n) (moment T w) := by
          rcases small with hs | hs
          · exact (ih a E v hv hE ep (fun x hx => hw x (ein hx)) hs).trans
              (Nat.mul_le_mul_left _ (bound E (fun j h h' => (vanish j h h').1)))
          · exact (ih a O (-v) (neg_ne_zero.mpr hv) ho op (fun x hx => hw x (oin hx)) hs).trans
              (Nat.mul_le_mul_left _ (bound O (fun j h h' => (vanish j h h').2)))
        rw [pow_succ]
        nlinarith
    · have same : ∀ x ∈ T, x ^ n = v := by
        intro x hx
        by_contra hn
        exact ho ⟨x, mem_filter.mpr ⟨hx, hn⟩⟩
      have twice : count (2 * n) (moment T w) = 2 * count n (moment T w) := by
        rw [count_double, two_mul, count, ← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        rw [shift T w n j v same]
        simp [mark, hv]
      have previous := ih a T v hv ⟨u, hu⟩ same hw hcard
      rw [twice]
      dsimp [n] at *
      nlinarith

/-- Six nonzero weights on the production grid force at least a quarter of all moments. -/
theorem six_site_production (T : Finset K) (w : K → K) (hT : T.Nonempty)
    (hpow : ∀ x ∈ T, x ^ (2 ^ 30) = 1) (hw : ∀ x ∈ T, w x ≠ 0) (hs : T.card ≤ 6) :
    268435456 ≤ count (2 ^ 30) (moment T w) := by
  have h := support_bound 30 2 T w 1 one_ne_zero hT hpow hw (by omega)
  change 1073741824 ≤ 4 * count (2 ^ 30) (moment T w) at h
  omega

#print axioms support_bound
#print axioms six_site_production

end ProximityGap.DyadicMomentSupport
