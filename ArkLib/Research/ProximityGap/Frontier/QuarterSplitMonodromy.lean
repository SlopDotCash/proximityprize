/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime
import ArkLib.Research.ProximityGap.Frontier.QuarterSplitFiberSymmetry

/-! # Degree and classical-group order tests for a quarter-successor pencil -/

namespace ProximityGap.QuarterSplitMonodromy

/-- The possible degrees of the first primitive stage after at most one squaring
or reciprocal quotient. -/
def largeStage (m : ℕ) : Prop :=
  m = 19173961 ∨ m = 38347922 ∨ m = 134217727 ∨ m = 268435454

/-- Deleting an initial quadratic, if present, still leaves a large stage
whose degree is divisible by both large odd prime factors. -/
theorem stage_degree {inner m : ℕ} (pre : inner = 1 ∨ inner = 2)
    (divides : inner*m ∣ 268435454) (large : 4194300 < inner*m) :
    largeStage m := by
  have h := QuarterSplitFiberSymmetry.large_divisor _ divides large
  rcases pre with rfl | rfl <;> try simp only [one_mul] at h
  all_goals
    unfold largeStage
    omega

set_option maxRecDepth 4096 in
/-- Both large primes divide the degree of the primitive factor. Each of the
four candidate degrees is squarefree. -/
theorem stage_arithmetic {m : ℕ} (h : largeStage m) :
    73 ∣ m ∧ 262657 ∣ m ∧ Squarefree m ∧ 19173961 ≤ m ∧ m ≤ 268435454 := by
  have hs : Squarefree 268435454 := by
    rw [show 268435454 = 2*(7*(73*262657)) by decide]
    rw [Nat.squarefree_mul (by decide), Nat.squarefree_mul (by decide),
      Nat.squarefree_mul (by decide)]
    exact ⟨Nat.prime_two.squarefree, (by norm_num : Nat.Prime 7).squarefree,
      (by norm_num : Nat.Prime 73).squarefree, (by norm_num : Nat.Prime 262657).squarefree⟩
  rcases h with rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, hs.squarefree_of_dvd (by decide), by decide, by decide⟩

/-- If the large prime occurs in a classical order factor, only two positive
powers survive the degree bound, even if every integer from 2 to 113 is used
as a candidate field size. -/
theorem order_filter {q i : ℕ} (hq : 2 ≤ q) (hq' : q ≤ 113) (hi : 0 < i)
    (degree : i ≤ 6 ∨ q^(i-2) ≤ 268435454)
    (order : q^i % 262657 = 1 ∨ q^i % 262657 = 262656) :
    ((q = 2 ∧ i = 27) ∨ (q = 8 ∧ i = 9)) ∧ q^i % 262657 = 1 := by
  have small : i < 30 := by
    rcases degree with small | bound
    · omega
    · by_contra! bad
      have lower : 2^28 ≤ q^(i-2) := (Nat.pow_le_pow_left hq 28).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
      omega
  have check : ∀ (q : Fin 114) (i : Fin 30), 2 ≤ q.val → 0 < i.val →
      (i.val ≤ 6 ∨ q.val^(i.val-2) ≤ 268435454) →
      (q.val^i.val % 262657 = 1 ∨ q.val^i.val % 262657 = 262656) →
      ((q.val = 2 ∧ i.val = 27) ∨ (q.val = 8 ∧ i.val = 9)) ∧ q.val^i.val % 262657 = 1 := by
    set_option maxRecDepth 8192 in decide
  exact check ⟨q,by omega⟩ ⟨i,small⟩ hq hi degree order

/-- A nonlinear middle-dimensional flag for either remaining field/order
pair already has more points in its open cell than the full pencil degree. -/
theorem middle_flag {q d : ℕ} (h : (q=2 ∧ 27≤d) ∨ (q=8 ∧ 9≤d)) :
    268435454 < q^(2*(d-2)) := by
  rcases h with ⟨rfl,h⟩ | ⟨rfl,h⟩
  · exact (by decide : 268435454 < 2^50).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (by decide : 268435454 < 8^14).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- The line counts after the order test leave exactly the two natural
projective actions cited in the proof. -/
theorem point_degrees {q d m : ℕ} (stage : largeStage m)
    (dims : (q=2 ∧ 27≤d ∧ d≤29) ∨ (q=8 ∧ 9≤d ∧ d≤11))
    (pts : (q-1)*m=q^d-1) : (q=2 ∧ d=27 ∧ m=134217727) ∨ (q=8 ∧ d=9 ∧ m=19173961) := by
  rcases dims with ⟨rfl,lo,hi⟩ | ⟨rfl,lo,hi⟩ <;>
    interval_cases d <;> norm_num at pts <;> unfold largeStage at stage <;> omega

/-- At the first field size above the sieve, the hyperbolic signature and
fixed-point ratio already force total index at least twice the degree. -/
theorem fixed_point_threshold {q : ℕ} (hq : 114 ≤ q) : 2*(3*q*42) < (3*q-4)*85 := by omega

/-- A non-natural alternating action has room for at least these many cosets. -/
theorem alternating_index {a : ℕ} (ha : 262657 ≤ a) : 268435454 < a.choose 2 := by
  apply lt_of_lt_of_le _ (Nat.choose_le_choose 2 ha)
  rw [Nat.choose_two_right]
  decide

#print axioms point_degrees
#print axioms fixed_point_threshold
#print axioms alternating_index
#print axioms stage_degree
#print axioms stage_arithmetic
#print axioms order_filter
#print axioms middle_flag
end ProximityGap.QuarterSplitMonodromy
