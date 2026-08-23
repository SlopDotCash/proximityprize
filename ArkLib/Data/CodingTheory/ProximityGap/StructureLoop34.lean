/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 34 — bounded-count linear spikes are absorbed

Loop 33 killed bounded-height sparse spikes. This file closes the next attempted disproof shape:
a bounded number of much taller spike levels, each allowed to have height linear in the final fold
depth `m`.

If the spike support has size at most `K`, and each spike is at most `m*h`, then the total spike
contribution is at most `m*(K*h)`. Thus a baseline exponent `c` plus these tall sparse spikes is
still bounded by the final-domain polynomial of degree `c + K*h`.

So a constant number of full-depth spike levels does not refute the prize. A spike-based
counterexample must make either the number of spikes or their height-density unbounded in the actual
GS/proximity mechanism. See `DISPROOF_LOG.md` (Loop34).
-/

namespace ArkLib.ProximityGap.StructureLoop34

open scoped BigOperators

/-- **A bounded number of height-linear spikes has linear total mass.** If the spike support has
cardinality at most `K`, and each active spike is at most `m*h`, then the total spike mass through
the first `m` levels is at most `m*(K*h)`. -/
theorem sparse_linear_spike_sum_le
    (spike : ℕ → ℕ) (S : Finset ℕ) {K h m : ℕ}
    (hcard : S.card ≤ K)
    (hsupport : ∀ j, j < m → j ∉ S → spike j = 0)
    (hheight : ∀ j, j < m → j ∈ S → spike j ≤ m * h) :
    ∑ j ∈ Finset.range m, spike j ≤ m * (K * h) := by
  let T := (Finset.range m).filter (fun j => j ∈ S)
  have hsum_eq : ∑ j ∈ Finset.range m, spike j = ∑ j ∈ T, spike j := by
    symm
    refine Finset.sum_subset (by intro j hj; exact (Finset.mem_filter.mp hj).1) ?_
    intro j hjRange hjNotT
    have hjlt : j < m := Finset.mem_range.mp hjRange
    have hjnotS : j ∉ S := by
      intro hjS
      exact hjNotT (Finset.mem_filter.mpr ⟨hjRange, hjS⟩)
    exact hsupport j hjlt hjnotS
  rw [hsum_eq]
  have hcardT : T.card ≤ K := by
    have hsubS : T ⊆ S := by
      intro j hjT
      exact (Finset.mem_filter.mp hjT).2
    exact (Finset.card_le_card hsubS).trans hcard
  calc
    ∑ j ∈ T, spike j ≤ ∑ _j ∈ T, m * h := by
      refine Finset.sum_le_sum ?_
      intro j hjT
      have hj := Finset.mem_filter.mp hjT
      exact hheight j (Finset.mem_range.mp hj.1) hj.2
    _ = T.card * (m * h) := by simp
    _ ≤ K * (m * h) := Nat.mul_le_mul_right (m * h) hcardT
    _ = m * (K * h) := by ring

/-- **Linear-spike products collapse to one power.** As usual, multiplicative exponent accounting is
controlled by the exponent sum. -/
theorem sparse_linear_spike_product_eq (e : ℕ → ℕ) (m : ℕ) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range m, e j) := by
  exact Finset.prod_pow_eq_pow_sum (Finset.range m) e (2 : ℝ)

/-- **Baseline plus bounded-count height-linear spikes is prize-safe.** A constant number of
spikes, each of height at most linear in the depth, only increases the final polynomial degree by
`K*h`. -/
theorem sparse_linear_spike_product_le_domain_pow
    (e spike : ℕ → ℕ) (S : Finset ℕ) {c K h m : ℕ}
    (he : ∀ j, j < m → e j ≤ c + spike j)
    (hcard : S.card ≤ K)
    (hsupport : ∀ j, j < m → j ∉ S → spike j = 0)
    (hheight : ∀ j, j < m → j ∈ S → spike j ≤ m * h) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) ≤ ((2 : ℝ) ^ m) ^ (c + K * h) := by
  have hspike := sparse_linear_spike_sum_le spike S hcard hsupport hheight
  have hsum : ∑ j ∈ Finset.range m, e j ≤ m * (c + K * h) := by
    calc
      ∑ j ∈ Finset.range m, e j ≤ ∑ j ∈ Finset.range m, (c + spike j) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact he j (Finset.mem_range.mp hj)
      _ = m * c + ∑ j ∈ Finset.range m, spike j := by
        rw [Finset.sum_add_distrib]
        simp [Nat.add_comm]
      _ ≤ m * c + m * (K * h) := Nat.add_le_add_left hspike (m * c)
      _ = m * (c + K * h) := by ring
  rw [sparse_linear_spike_product_eq]
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsum

end ArkLib.ProximityGap.StructureLoop34

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop34.sparse_linear_spike_sum_le
#print axioms ArkLib.ProximityGap.StructureLoop34.sparse_linear_spike_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop34.sparse_linear_spike_product_le_domain_pow
