/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DilationDoublingMassHalf

/-!
# The doubling-trajectory level-set budget (the factor-2 saving on the sign cocycle)

The naïve cross-mass Markov bound on a disjoint tower step caps the count of high-cross-mass
frequencies by `q·|G|/T`. This file sharpens it on the **doubling** (same-sign, `+`) trajectory —
the only frequencies that carry the trivial `2·M` scaling — to **`q·|G|/(2T)`**, exactly half the
budget. The saving is the level-set form of the `plusMass_le_half_card` halving law.

## The bound

For a negation-closed `G` with disjoint dilate (`ζ ≠ 0`, `Disjoint G (dilate ζ G)`) and threshold
`T`, let `S_T := {b : 0 ≤ s_b ∧ T ≤ ‖η_b‖·‖η_{ζb}‖}` be the **same-sign** frequencies whose
cross-mass clears `T`. Then

  `#S_T · T  ≤  plusMass  ≤  ½·q·|G|`,   hence for `T > 0`,   `#S_T ≤ q·|G|/(2T)`.

Proof: Markov on the `+`-set (sum the threshold over `S_T`, dominate by `plusMass`), then apply the
proven halving cap `plusMass_le_half_card`.

## Scope / honesty

A **deterministic level-set corollary** of `plusMass_le_half_card` (which is itself an exact
extension of `sign_balance_zero` + `total_doublingMass_le`). It is an average-case `½`-budget
statement on the doubling trajectory — NOT a CORE closure. The prize wall is the worst-case
single-frequency deep-descent sign word, which a count budget does not control. Thinness enters via
the negation-closure of the tower (`-1 ∈ μ_{2^i}`, `i ≥ 1`) underlying the halving.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

See `DilationDoublingMassHalf` (`plusMass`, `plusMass_le_half_card`).
-/

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The same-sign high-cross-mass level set: frequencies on the **doubling** trajectory
(`0 ≤ s_b`) whose cross-mass `‖η_b‖·‖η_{ζb}‖` clears the threshold `T`. -/
noncomputable def doublingLevelSet (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) (T : ℝ) : Finset F :=
  Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b ∧ T ≤ crossMass ψ G ζ b)

omit [DecidableEq F] in
/-- The doubling level set is contained in the `+`-sign set used by `plusMass`. -/
theorem doublingLevelSet_subset_plusSet {ψ : AddChar F ℂ} (G : Finset F) (ζ : F) (T : ℝ) :
    doublingLevelSet ψ G ζ T ⊆ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b) := by
  intro b hb
  rw [doublingLevelSet, Finset.mem_filter] at hb
  rw [Finset.mem_filter]
  exact ⟨hb.1, hb.2.1⟩

omit [DecidableEq F] in
/-- **Markov on the doubling trajectory.** The count of same-sign frequencies clearing the
cross-mass threshold `T`, scaled by `T`, is at most the total doubling mass `plusMass`. -/
theorem card_doublingLevelSet_mul_le_plusMass {ψ : AddChar F ℂ} (G : Finset F) (ζ : F) (T : ℝ) :
    ((doublingLevelSet ψ G ζ T).card : ℝ) * T ≤ plusMass ψ G ζ := by
  classical
  set S := doublingLevelSet ψ G ζ T with hS
  -- #S · T = ∑_{b ∈ S} T  ≤  ∑_{b ∈ S} crossMass  ≤  ∑_{+ set} crossMass = plusMass
  have h1 : (S.card : ℝ) * T = ∑ _b ∈ S, T := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _b ∈ S, T ≤ ∑ b ∈ S, crossMass ψ G ζ b := by
    apply Finset.sum_le_sum
    intro b hb
    rw [hS, doublingLevelSet, Finset.mem_filter] at hb
    exact hb.2.2
  have hsub : S ⊆ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b) :=
    doublingLevelSet_subset_plusSet G ζ T
  have h3 : ∑ b ∈ S, crossMass ψ G ζ b
      ≤ ∑ b ∈ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b), crossMass ψ G ζ b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro b _ _
    unfold crossMass
    positivity
  rw [h1]
  calc ∑ _b ∈ S, T
      ≤ ∑ b ∈ S, crossMass ψ G ζ b := h2
    _ ≤ plusMass ψ G ζ := by rw [plusMass]; exact h3

/-- **The doubling-trajectory level-set budget (the factor-2 saving).** Along a genuine disjoint
tower step, the count of same-sign frequencies clearing cross-mass `T`, scaled by `T`, is at most
**half** the second moment:

  `#{b : same-sign ∧ ‖η_b‖·‖η_{ζb}‖ ≥ T} · T ≤ ½·q·|G|`.

Exactly half the naïve cross-mass Markov budget `q·|G|`, the count form of the halving. -/
theorem card_doublingLevelSet_mul_le_half {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (T : ℝ) :
    ((doublingLevelSet ψ G ζ T).card : ℝ) * T ≤ (Fintype.card F : ℝ) * G.card / 2 := by
  have h1 : ((doublingLevelSet ψ G ζ T).card : ℝ) * T ≤ plusMass ψ G ζ :=
    card_doublingLevelSet_mul_le_plusMass G ζ T
  have h2 : plusMass ψ G ζ ≤ (Fintype.card F : ℝ) * G.card / 2 :=
    plusMass_le_half_card hψ G hG hζ hdisj
  linarith [h1, h2]

/-- **Divided form.** For `T > 0`, the doubling level set is sparse with the explicit half-budget:

  `#{b : same-sign ∧ ‖η_b‖·‖η_{ζb}‖ ≥ T} ≤ q·|G|/(2T)`. -/
theorem card_doublingLevelSet_le_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) {T : ℝ}
    (hT : 0 < T) :
    ((doublingLevelSet ψ G ζ T).card : ℝ) ≤ (Fintype.card F : ℝ) * G.card / (2 * T) := by
  have hmul : ((doublingLevelSet ψ G ζ T).card : ℝ) * T ≤ (Fintype.card F : ℝ) * G.card / 2 :=
    card_doublingLevelSet_mul_le_half hψ G hG hζ hdisj T
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * T)]
  -- #S · (2T) ≤ qG, from #S · T ≤ qG/2
  nlinarith [hmul]

#print axioms ProximityGap.SubgroupGaussSumSecondMoment.card_doublingLevelSet_mul_le_half
#print axioms ProximityGap.SubgroupGaussSumSecondMoment.card_doublingLevelSet_le_div

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
