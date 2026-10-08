/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.RingSwitching.Packing.CandidateList
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! # Fixed-list batching bounds and invalid adaptive-list controls -/
set_option autoImplicit false
noncomputable section
namespace RingSwitching.Packing.Tests.CandidateList
open MvPolynomial ProbabilityTheory
open scoped NNReal ENNReal
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
/-! ## Bounded candidate lists

Linear power batching over `ZMod 5` has loss `1/5`. Against the zero family, the candidate
`(-a, 1)` batches to `γ - a`, so it collides exactly at the challenge `γ = a`. -/

/-- Linear power batching of two claims over `ZMod 5`. -/
abbrev linear : BatchingStrategy (ZMod 5) (Fin 2) := BatchingStrategy.gammaPowers (ZMod 5) 2

/-- Linear power batching over `ZMod 5` has loss `(2 - 1)/5`. -/
theorem linear_error : linear.error = 1 / 5 := by
  simp [BatchingStrategy.gammaPowers]

/-- The loss of linear power batching as an extended real. -/
theorem linear_error_coe : (linear.error : ℝ≥0∞) = 5⁻¹ := by
  rw [linear_error, one_div, ENNReal.coe_inv (by norm_num)]
  norm_num

/-- Two incorrect candidates, a list fixed before the challenge, together with the correct
family `0`. -/
def list : Finset (Fin 2 → ZMod 5) := {0, ![-1, 1], ![-2, 1]}

/-- Excluding the correct family leaves the two collisions `γ = 1` and `γ = 2`. -/
theorem list_collisions :
    (Finset.univ.filter fun γ : ZMod 5 => ∃ s' ∈ list, s' ≠ 0 ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0).card = 2 := by
  decide

/-- The two incorrect candidates collide with probability exactly `2/5`. -/
theorem list_probability :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ list, s' ≠ 0 ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] = 2 / 5 := by
  rw [SampleableType.prEvent_uniformSample, list_collisions]
  simp

/-- The `L = 2` list bound applies to the two incorrect candidates. -/
theorem separates_finset_two :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ list.erase 0, s' ≠ 0 ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] ≤
      2 * (linear.error : ℝ≥0∞) :=
  linear.separates_finset 0 (list.erase 0) (by decide)

/-- The list bound with `L = 2` is attained once the correct family is dropped from the list:
two incorrect candidates collide with probability exactly `2 * (1/5)`. -/
theorem separates_finset_tight :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ list.erase 0, s' ≠ 0 ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] =
      2 * (linear.error : ℝ≥0∞) := by
  have hev : ∀ γ : ZMod 5,
      (∃ s' ∈ list.erase 0, s' ≠ 0 ∧
        ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0) ↔
      (∃ s' ∈ list, s' ≠ 0 ∧
        ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0) := fun γ =>
    ⟨fun ⟨s', hs', h⟩ => ⟨s', Finset.mem_of_mem_erase hs', h⟩,
      fun ⟨s', hs', h⟩ => ⟨s', Finset.mem_erase.mpr ⟨h.1, hs'⟩, h⟩⟩
  rw [prEvent_congr _ _ _ hev, list_probability, linear_error_coe, div_eq_mul_inv]

/-- Listing the correct family costs nothing: the three-element list has the same collision
probability `2/5` as its two incorrect members, below the list bound `3 * (1/5)`. -/
theorem separates_finset_correct_excluded :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ list, s' ≠ 0 ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] <
      3 * (linear.error : ℝ≥0∞) := by
  rw [list_probability, linear_error_coe, div_eq_mul_inv]
  gcongr <;> norm_num

/-- Without excluding correct candidates the event is certain: the correct family always
batches to its own value. -/
theorem correct_candidate_always_collides :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ ({0} : Finset (Fin 2 → ZMod 5)),
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ => ⟨0, by simp⟩

/-- The one-element list bound `1 * (1/5)` fails once correct candidates enter the event. -/
theorem correct_candidate_exceeds_bound :
    1 * (linear.error : ℝ≥0∞) < Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ ({0} : Finset (Fin 2 → ZMod 5)),
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] := by
  rw [correct_candidate_always_collides, one_mul, linear_error_coe]
  exact ENNReal.inv_lt_one.mpr (by norm_num)

/-- A list chosen after the challenge escapes the bound: the one-element list `{(-γ, 1)}`
collides with probability `1`. -/
theorem challenge_dependent_list_collides :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ ({![-γ, 1]} : Finset (Fin 2 → ZMod 5)), s' ≠ 0 ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun γ => by
    refine ⟨![-γ, 1], Finset.mem_singleton_self _, fun h => ?_, ?_⟩
    · simpa using congrFun h 1
    · simp [linear, BatchingStrategy.gammaPowers, Fin.sum_univ_two]

/-- The one-element list bound `1 * (1/5)` fails for the list chosen after the challenge. -/
theorem challenge_dependent_list_exceeds_bound :
    1 * (linear.error : ℝ≥0∞) <
      Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' ∈ ({![-γ, 1]} : Finset (Fin 2 → ZMod 5)), s' ≠ 0 ∧
        ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] := by
  rw [challenge_dependent_list_collides, one_mul, linear_error_coe]
  exact ENNReal.inv_lt_one.mpr (by norm_num)

/-- The `L = 1` list bound recovers the strategy's exact separation of one incorrect family. -/
theorem separates_singleton {P W : Type} [CommRing P] [Fintype W] (bat : BatchingStrategy P W) (s s' : W → P)
    (hne : s' ≠ s) :
    Pr{let c ← $ᵗ bat.Challenge}[
      ∑ u, bat.weight c u * s' u = ∑ u, bat.weight c u * s u] ≤ (bat.error : ℝ≥0∞) := by
  simpa [hne] using bat.separates_finset s {s'} (L := 1) (by simp)

/-- Exact-functional separation on a concrete instance: when the valid candidate is unique, the
bound is the strategy loss `1/5`, and it is attained by the candidate `(-1, 1)`. -/
theorem exact_functional_tight :
    Pr{let γ ← $ᵗ (ZMod 5)}[∃ s' : Fin 2 → ZMod 5, (s' = ![-1, 1] ∧ s' ≠ 0) ∧
      ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0] = linear.error := by
  refine le_antisymm ?_ ?_
  · simpa only [and_assoc] using
      (prEvent_exists_and_and_le_of_subsingleton ($ᵗ (ZMod 5))
        (fun s' : Fin 2 → ZMod 5 => s' = ![-1, 1]) (fun s' => s' ≠ 0)
        (fun s' γ => ∑ u, linear.weight γ u * s' u = ∑ u, linear.weight γ u * 0)
        (fun s' _ hne => linear.separates s' 0 hne)
        (fun _ ha _ hb => ha.trans hb.symm))
  ·
    have hcard : (Finset.univ.filter fun γ : ZMod 5 =>
        ∑ u, linear.weight γ u * ![-1, 1] u = ∑ u, linear.weight γ u * 0).card = 1 := by
      decide
    calc (linear.error : ℝ≥0∞)
        = Pr{let γ ← $ᵗ (ZMod 5)}[
            ∑ u, linear.weight γ u * ![-1, 1] u = ∑ u, linear.weight γ u * 0] := by
          rw [SampleableType.prEvent_uniformSample, hcard, linear_error]
          simp
      _ ≤ _ := prEvent_mono _ _ _ fun _ h => ⟨_, ⟨rfl, by decide⟩, h⟩
  

end RingSwitching.Packing.Tests.CandidateList
end
