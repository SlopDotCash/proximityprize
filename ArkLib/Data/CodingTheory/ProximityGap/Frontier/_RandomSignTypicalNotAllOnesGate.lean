/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Random-sign typical bounds do not control the deterministic all-ones sign

Sub-Gaussian random-matrix and noncommutative-Khintchine inputs naturally bound a random signing, or
all but a small exceptional set of signings.  The #464 period operator, however, is the deterministic
all-ones signing of the translation family indexed by `mu_n`.

This file records the finite last-mile obstruction: a bound on a typical set of signings, or an
average bound, is compatible with the distinguished all-ones signing being the unique spike.  Thus a
random-sign operator-norm theorem supplies the free `sqrt n` scale only after a separate theorem
controls the deterministic signing or pushes the exceptional budget below one atom.
-/

namespace ArkLib.ProximityGap.Frontier.RandomSignTypicalNotAllOnesGate

open Finset

variable {S : Type}

/-- A score is bounded on a chosen set of signings. -/
def GoodOn (score : S -> ℝ) (good : Finset S) (B : ℝ) : Prop :=
  ∀ σ ∈ good, score σ <= B

/-- The number of signings whose score is strictly above threshold `B`. -/
noncomputable def badSignCount [Fintype S] (score : S -> ℝ) (B : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun (σ : S) => B < score σ)).card

/-- At most `K` signings exceed threshold `B`. -/
def AtMostBadSignCount [Fintype S] (score : S -> ℝ) (B : ℝ) (K : ℕ) : Prop :=
  badSignCount score B <= K

/-- Uniform average score over all signings. -/
noncomputable def signAverage [Fintype S] (score : S -> ℝ) : ℝ :=
  (∑ σ : S, score σ) / (Fintype.card S : ℝ)

/-- A model score with one spike at the distinguished all-ones signing. -/
noncomputable def singletonSpike (allOnes : S) (H : ℝ) : S -> ℝ := by
  classical
  exact fun (σ : S) => if σ = allOnes then H else 0

/-- The singleton spike is nonnegative when its height is nonnegative. -/
theorem singletonSpike_nonneg {allOnes : S} {H : ℝ} (hH : 0 <= H) :
    ∀ σ : S, 0 <= singletonSpike allOnes H σ := by
  classical
  intro σ
  by_cases hσ : σ = allOnes
  · simp [singletonSpike, hσ, hH]
  · simp [singletonSpike, hσ]

/-- The singleton spike has average exactly `H / #S`. -/
theorem signAverage_singletonSpike [Fintype S] (allOnes : S) (H : ℝ) :
    signAverage (singletonSpike allOnes H) = H / (Fintype.card S : ℝ) := by
  classical
  unfold signAverage singletonSpike
  simp

/-- If `0 <= B < H`, the only signing above threshold in the singleton-spike model is the
distinguished all-ones signing. -/
theorem badSignCount_singletonSpike
    [Fintype S]
    {allOnes : S} {B H : ℝ}
    (hB : 0 <= B) (hBH : B < H) :
    badSignCount (singletonSpike allOnes H) B = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter (fun (σ : S) => B < singletonSpike allOnes H σ))
        = ({allOnes} : Finset S) := by
    ext σ
    by_cases hσ : σ = allOnes
    · simp [singletonSpike, hσ, hBH]
    · simp [singletonSpike, hσ, not_lt.mpr hB]
  unfold badSignCount
  rw [hfilter]
  simp

/-- A theorem bounding every signing except the distinguished all-ones signing is compatible with
the all-ones signing being a spike. -/
theorem goodOn_erased_allows_allOnes_spike
    [Fintype S] [DecidableEq S]
    (allOnes : S) {B H : ℝ}
    (hB : 0 <= B) (hBH : B < H) :
    ∃ score : (S -> ℝ),
      GoodOn score ((Finset.univ : Finset S).erase allOnes) B
        ∧ B < score allOnes := by
  classical
  refine ⟨singletonSpike allOnes H, ?_, ?_⟩
  · intro σ hσ
    have hne : σ ≠ allOnes := by
      exact (Finset.mem_erase.mp hσ).1
    simp [singletonSpike, hne, hB]
  · simp [singletonSpike, hBH]

/-- Any tail theorem allowing one exceptional signing is compatible with the all-ones signing being
the unique exception. -/
theorem one_exception_budget_allows_allOnes_spike
    [Fintype S]
    (allOnes : S) {B H : ℝ} {K : ℕ}
    (hB : 0 <= B) (hBH : B < H) (hK : 1 <= K) :
    ∃ score : (S -> ℝ),
      AtMostBadSignCount score B K ∧ B < score allOnes := by
  refine ⟨singletonSpike allOnes H, ?_, ?_⟩
  · unfold AtMostBadSignCount
    rw [badSignCount_singletonSpike hB hBH]
    exact hK
  · simp [singletonSpike, hBH]

/-- An average random-sign score bound can still hide a spike at the all-ones signing when the
budget can pay for that one atom. -/
theorem average_budget_allows_allOnes_spike
    [Fintype S]
    (allOnes : S) {B H A : ℝ}
    (hH : 0 <= H) (hBH : B < H)
    (hbudget : H / (Fintype.card S : ℝ) <= A) :
    ∃ score : (S -> ℝ),
      (∀ σ : S, 0 <= score σ)
        ∧ signAverage score <= A
        ∧ B < score allOnes := by
  refine ⟨singletonSpike allOnes H, singletonSpike_nonneg hH, ?_, ?_⟩
  · simpa [signAverage_singletonSpike] using hbudget
  · simp [singletonSpike, hBH]

/-! ## Axiom audit -/
#print axioms singletonSpike_nonneg
#print axioms signAverage_singletonSpike
#print axioms badSignCount_singletonSpike
#print axioms goodOn_erased_allows_allOnes_spike
#print axioms one_exception_budget_allows_allOnes_spike
#print axioms average_budget_allows_allOnes_spike

end ArkLib.ProximityGap.Frontier.RandomSignTypicalNotAllOnesGate
