/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SixthMomentSignatureBridge
import ArkLib.Research.ProximityGap.Frontier.ExactHistogramSquares

/-!
# A subgroup with the repeated-entry exclusions and an excessive sixth moment

The arithmetic certificate uses the order-64 subgroup modulo 173249. For every
ordered pair of roots it records the signature of the sum of one and those roots.
A nonzero coset with multiplicity m in this table has m ordered triples summing
to each of its 64 elements. There is no zero in the table. The centered sixth
moment therefore exceeds the unit Gaussian bound at this prime.
-/

namespace ArkLib.ProximityGap.Frontier.SixthMomentSparseCounterexample

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev p := 173249
abbrev g := 121218
abbrev n := 64

def roots : List ℕ := (List.range n).map fun i => Nat.powMod g i p
def signature (x : ℕ) : ℕ := Nat.powMod x n p
private def differences : List ℕ :=
  ((roots.drop 1).take (n/2)).map fun x => signature (x + p - 1)
private def directed : List ℕ := (roots.drop 1).map fun x => signature (3 + p - x)
def sums : List ℕ :=
  roots.flatMap fun x => roots.map fun y => signature (1 + x + y)

/-- The modulus, order, and all three finite comparisons used by the sparse tests. -/
theorem arithmetic :
    Nat.Prime p ∧ Nat.powMod g n p = 1 ∧ Nat.powMod g (n/2) p = p-1 ∧
    (differences.eraseDups.length = n/2) ∧ signature 3 ≠ 1 ∧
    (differences.all (fun v => !differences.contains ((signature 2 * v) % p))) = true ∧
    (directed.all (fun v => !differences.contains v)) = true := by
  constructor
  · norm_num
  · decide +kernel

instance : Fact (Nat.Prime p) := ⟨arithmetic.1⟩

/-- The actual order of the displayed generator in the prime field. -/
theorem primitive : IsPrimitiveRoot (g : ZMod p) n := by
  have hfull : (g : ZMod p) ^ (2 ^ 6 : ℕ) = 1 := by decide +kernel
  have hhalf : (g : ZMod p) ^ (2 ^ 5 : ℕ) ≠ 1 := by decide +kernel
  exact IsPrimitiveRoot.iff_orderOf.mpr (by
    have h := orderOf_eq_prime_pow (x := (g : ZMod p)) hhalf hfull
    exact h)

/-- An exhaustive check on two exponents suffices for Sidon: after scaling
the first entry to 1, the remaining left entry is c+d-1. -/
private theorem normalized_sidon (i j : Fin 64) :
    let c := (g : ZMod p) ^ i.val
    let d := (g : ZMod p) ^ j.val
    c+d = 0 ∨ (c+d-1)^n ≠ 1 ∨ c=1 ∨ d=1 := by
  revert i j
  decide +kernel

private theorem sidon (a b c d : ZMod p) (ha : a^n=1) (hb : b^n=1)
    (hc : c^n=1) (hd : d^n=1) (he : a+b=c+d) : a+b=0 ∨ a=c ∨ a=d := by
  have ha0 : a ≠ 0 := by rintro rfl; simp [n] at ha
  obtain ⟨i, hi, hic⟩ := primitive.eq_pow_of_pow_eq_one
    (show (c/a)^n=1 by rw [div_pow, hc, ha, div_one])
  obtain ⟨j, hj, hjd⟩ := primitive.eq_pow_of_pow_eq_one
    (show (d/a)^n=1 by rw [div_pow, hd, ha, div_one])
  have ht := normalized_sidon ⟨i, hi⟩ ⟨j, hj⟩
  dsimp only at ht
  rw [hic, hjd] at ht
  have hsum : c/a + d/a = 1 + b/a := by field_simp [ha0]; linear_combination -he
  rw [hsum] at ht
  rcases ht with hz | hbad | hca | hda
  · left
    field_simp [ha0] at hz
    linear_combination hz
  · exfalso
    apply hbad
    rw [show 1+b/a-1 = b/a by ring, div_pow, hb, ha, div_one]
  · exact Or.inr (Or.inl ((div_eq_one_iff_eq ha0).mp hca).symm)
  · exact Or.inr (Or.inr ((div_eq_one_iff_eq ha0).mp hda).symm)

private theorem doubled_check (i j : Fin 32) :
    (2 : ZMod p)^n * ((g : ZMod p)^(i.val+1)-1)^n ≠ ((g : ZMod p)^(j.val+1)-1)^n := by
  revert i j
  decide +kernel

private theorem triple_check (i : Fin 63) (j : Fin 32) :
    ((3 : ZMod p)-(g : ZMod p)^(i.val+1))^n ≠ ((g : ZMod p)^(j.val+1)-1)^n := by
  revert i j
  decide +kernel

/-- All hypotheses of the six-term multiplicity theorem hold on the literal field. -/
theorem fourTermConditions :
    SixthMomentAntipodalShape.FourTermConditions {x : ZMod p | x^n=1} := by
  apply SixthMomentSignatureBridge.fourTermConditions_of_window_checks primitive
    (by decide) (by decide) (by decide) sidon
  · intro i hi hi' j hj hj'
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact doubled_check ⟨a, by change a+1 ≤ 32 at hi'; omega⟩
      ⟨b, by change b+1 ≤ 32 at hj'; omega⟩
  · intro i hi hi' j hj hj'
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact triple_check ⟨a, by change a+1 < 64 at hi'; omega⟩
      ⟨b, by change b+1 ≤ 32 at hj'; omega⟩

/-- Both numbers concern the literal table of all 4096 normalized pairs. -/
theorem table :
    sums.length = 4096 ∧ sums.contains 0 = false ∧ _root_.ProximityGap.ExactHistogram.bucketSquares 18 sums = 68320 := by
  decide +kernel

/-- The table traverses standard representatives of field elements. -/
theorem bound (x : ℕ) (hx : x ∈ sums) : x < 2^18 := by
  have h : sums.all (fun i => decide (i < 2^18)) = true := by decide +kernel
  simpa using List.all_eq_true.mp h x hx

/-- The exact sum of squared normalized pair multiplicities in the field. -/
theorem sum_squares : ∑ x ∈ sums.toFinset, sums.count x ^ 2 = 68320 := by
  rw [← _root_.ProximityGap.ExactHistogram.bucketSquares_eq_sum 18 sums bound]
  exact table.2.2

/-- The exact integer excess after subtracting the zero-frequency term and
multiplying by the field size. -/
theorem strict_excess :
    p * (n * 68320) = n^6 + p * (15*n^3) + 7565522944 := by decide +kernel

#print axioms primitive
#print axioms fourTermConditions
#print axioms arithmetic
#print axioms table
#print axioms sum_squares
#print axioms strict_excess

end ArkLib.ProximityGap.Frontier.SixthMomentSparseCounterexample
