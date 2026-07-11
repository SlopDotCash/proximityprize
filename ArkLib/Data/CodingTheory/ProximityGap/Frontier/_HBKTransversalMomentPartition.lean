/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031SupTransversalCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

/-!
# Moment partition over a multiplicative-coset transversal

Every nonzero `μ_n`-coset has exactly `n` elements. Therefore any natural-valued statistic constant
on `cosetLabel` fibers has global nonzero sum equal to `n` times its sum over an
`IsCosetTransversal`. This file proves that generic identity; HBK uses it for `repCount` and its
square. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HBKTransversalMomentPartition

open scoped BigOperators
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Fibers indexed by distinct elements of a transversal are disjoint. -/
theorem transversal_label_fibers_pairwiseDisjoint
    {n : ℕ} {T : Finset F} (hT : IsCosetTransversal n T) :
    (T : Set F).PairwiseDisjoint
      (fun t => (nonzeroFreqs F).filter (fun x => cosetLabel n x = cosetLabel n t)) := by
  intro t₁ ht₁ t₂ ht₂ hne
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_filter] at hx₁ hx₂
  apply hne
  exact hT.inj t₁ (by simpa using ht₁) t₂ (by simpa using ht₂)
    (hx₁.2.symm.trans hx₂.2)

/-- **Uniform-coset moment partition.** -/
theorem sum_nonzero_eq_card_mul_sum_transversal
    {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T) (f : F → ℕ)
    (hconst : ∀ t ∈ T, ∀ x ∈ nonzeroFreqs F,
      cosetLabel n x = cosetLabel n t → f x = f t) :
    (∑ x ∈ nonzeroFreqs F, f x) = n * ∑ t ∈ T, f t := by
  rw [nonzeroFreqs_eq_biUnion_fibers hT]
  rw [Finset.sum_biUnion (transversal_label_fibers_pairwiseDisjoint hT)]
  calc
    (∑ t ∈ T, ∑ x ∈ (nonzeroFreqs F).filter
        (fun x => cosetLabel n x = cosetLabel n t), f x) =
        ∑ t ∈ T, n * f t := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht0 : t ≠ 0 := by
        have := hT.subset ht
        rwa [mem_nonzeroFreqs] at this
      rw [Finset.sum_const_nat]
      · rw [coset_fiber_card hζprim hn ht0]
      · intro x hx
        simp only [Finset.mem_filter] at hx
        exact hconst t ht x hx.1 hx.2
    _ = n * ∑ t ∈ T, f t := by rw [Finset.mul_sum]

end ArkLib.ProximityGap.Frontier.HBKTransversalMomentPartition

#print axioms
  ArkLib.ProximityGap.Frontier.HBKTransversalMomentPartition.sum_nonzero_eq_card_mul_sum_transversal
