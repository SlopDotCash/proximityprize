/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 33 — bounded sparse spikes are absorbed

Loops 31 and 32 reduced multiplicative-factor attacks to the cumulative exponent and showed that
block grouping cannot hide that exponent. This file records the next failed disproof shape: a
mostly bounded exponent sequence with a finite set of scary-looking spike levels.

If each level exponent decomposes as a baseline `c` plus a spike term, and the spike term is supported
on a set `S` and bounded by height `h`, then the total spike contribution through `m` levels is at
most `m*h`; hence the full product is bounded by the final-domain polynomial of degree `c+h`.

So bounded spikes do not refute the prize. A spike-based counterexample must make the spike heights,
or their average density, grow without bound in the actual GS/proximity process. See
`DISPROOF_LOG.md` (Loop33).
-/

namespace ArkLib.ProximityGap.StructureLoop33

open scoped BigOperators

/-- **Bounded supported spikes have linear total mass.** If `spike` vanishes outside `S` on the
first `m` levels and is bounded by `h` on `S`, then its total contribution over those levels is at
most `m*h`. -/
theorem sparse_spike_sum_le
    (spike : ℕ → ℕ) (S : Finset ℕ) {h m : ℕ}
    (hsupport : ∀ j, j < m → j ∉ S → spike j = 0)
    (hheight : ∀ j, j < m → j ∈ S → spike j ≤ h) :
    ∑ j ∈ Finset.range m, spike j ≤ m * h := by
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
  have hcard : T.card ≤ m := by
    have hcard' : T.card ≤ (Finset.range m).card :=
      Finset.card_le_card (by intro j hjT; exact (Finset.mem_filter.mp hjT).1)
    simpa using hcard'
  calc
    ∑ j ∈ T, spike j ≤ ∑ _j ∈ T, h := by
      refine Finset.sum_le_sum ?_
      intro j hjT
      have hj := Finset.mem_filter.mp hjT
      exact hheight j (Finset.mem_range.mp hj.1) hj.2
    _ = T.card * h := by simp
    _ ≤ m * h := by
      exact Nat.mul_le_mul_right h hcard

/-- **Spike exponent products collapse to one power.** As before, all multiplicative exponent
accounting reduces to the sum of exponents. -/
theorem sparse_spike_product_eq (e : ℕ → ℕ) (m : ℕ) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range m, e j) := by
  exact Finset.prod_pow_eq_pow_sum (Finset.range m) e (2 : ℝ)

/-- **Baseline plus bounded spikes is prize-safe.** If every exponent is at most a baseline `c`
plus a supported spike of height `h`, then the product is bounded by the final-domain degree-`c+h`
polynomial. -/
theorem sparse_spike_product_le_domain_pow
    (e spike : ℕ → ℕ) (S : Finset ℕ) {c h m : ℕ}
    (he : ∀ j, j < m → e j ≤ c + spike j)
    (hsupport : ∀ j, j < m → j ∉ S → spike j = 0)
    (hheight : ∀ j, j < m → j ∈ S → spike j ≤ h) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) ≤ ((2 : ℝ) ^ m) ^ (c + h) := by
  have hspike := sparse_spike_sum_le spike S hsupport hheight
  have hsum : ∑ j ∈ Finset.range m, e j ≤ m * (c + h) := by
    calc
      ∑ j ∈ Finset.range m, e j ≤ ∑ j ∈ Finset.range m, (c + spike j) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact he j (Finset.mem_range.mp hj)
      _ = m * c + ∑ j ∈ Finset.range m, spike j := by
        rw [Finset.sum_add_distrib]
        simp [Nat.add_comm]
      _ ≤ m * c + m * h := Nat.add_le_add_left hspike (m * c)
      _ = m * (c + h) := by ring
  rw [sparse_spike_product_eq]
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsum

end ArkLib.ProximityGap.StructureLoop33

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop33.sparse_spike_sum_le
#print axioms ArkLib.ProximityGap.StructureLoop33.sparse_spike_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop33.sparse_spike_product_le_domain_pow
