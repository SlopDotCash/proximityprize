/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGS

/-!
# Anti-vacuity guard for the GS-exposed prize: the list family must be faithful (#121 / #141 / #171)

The GS-exposed Grand-Challenge-1 prize statements (`GrandChallenge141PrizeMath.lean`,
`MCAGS.lean`) bound `epsMCAgs C δ L` and always carry a **`FaithfulGSFamily`** hypothesis on the
list family `L`. This file proves *why that hypothesis is mathematically indispensable*: without
it, the `∃ L, epsMCAgs C δ L ≤ …` form is **vacuous** and proves nothing about the actual MCA error.

`epsMCAgs C δ L = ⨆ u, Pr_γ[mcaEventGSrow (L u) …]`, and `mcaEventGSrow` requires its line-witness
codeword to lie in `L u`. Taking `L u = ∅` therefore kills every bad event:

* `mcaEventGSrow_emptyList_false` — the GS-row event is impossible against the empty list.
* `epsMCAgs_emptyList_eq_zero` — hence `epsMCAgs C δ (fun _ => ∅) = 0`.
* `exists_list_epsMCAgs_le` — hence for *any* target `B`, `∃ L, epsMCAgs C δ L ≤ B` holds (via
  `L = ∅`). So a prize claim of the bare `∃ L` shape is content-free; the genuine content lives
  entirely in the faithfulness constraint (`epsMCA ≤ epsMCAgs`, i.e. `FaithfulGSFamily`), which
  forbids the empty (and any under-covering) list. The abstract `GrandChallenges.mcaConjecture`
  avoids the issue by bounding `epsMCA` directly.

This is an anti-vacuity guard (cf. #121): it certifies that the GS-exposed prize is not trivially
satisfiable and that its faithfulness hypothesis cannot be dropped. A structural/negative result,
not a closure of the open prize. Tracking: Issues #121, #141, #171.
-/

set_option linter.unusedSectionVars false

open Code
open scoped NNReal ProbabilityTheory

namespace ProximityGap.MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- With the empty list family, the GS-row bad event can never fire: its line-witness codeword is
required to lie in the (empty) list. -/
theorem mcaEventGSrow_emptyList_false (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    ¬ mcaEventGSrow (∅ : Finset (ι → A)) C δ u₀ u₁ γ := by
  rintro ⟨S, -, ⟨w, -, hwL, -⟩, -⟩
  simp at hwL

open Classical in
/-- **`epsMCAgs` with the empty list family is `0`.** Every per-stack GS-row probability is the
probability of an impossible event. -/
theorem epsMCAgs_emptyList_eq_zero (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAgs (F := F) C δ (fun _ => (∅ : Finset (ι → A))) = 0 := by
  unfold epsMCAgs
  have hzero : ∀ u : WordStack A (Fin 2) ι,
      Pr_{let γ ← $ᵖ F}[mcaEventGSrow (∅ : Finset (ι → A)) C δ (u 0) (u 1) γ] = 0 := by
    intro u
    rw [ProbabilityTheory.Pr_eq_tsum_indicator]
    have hfun : (fun γ : F => ($ᵖ F) γ *
        (if mcaEventGSrow (∅ : Finset (ι → A)) C δ (u 0) (u 1) γ then (1 : ENNReal) else 0))
        = fun _ => 0 := by
      funext γ
      rw [if_neg (mcaEventGSrow_emptyList_false C δ (u 0) (u 1) γ), mul_zero]
    rw [hfun, tsum_zero]
  simp only [hzero]
  exact iSup_const

/-- **The bare `∃ L` GS-exposed prize form is vacuous.** For any target bound `B`, the empty list
family already satisfies `epsMCAgs C δ L ≤ B`. Hence an unconstrained `∃ L, epsMCAgs ≤ …` claim is
content-free; the GS-exposed prize is meaningful only with a *faithfulness* constraint
(`FaithfulGSFamily`) forcing `L` to be the actual (poly-size) GS list. -/
theorem exists_list_epsMCAgs_le (C : Set (ι → A)) (δ : ℝ≥0) (B : ENNReal) :
    ∃ L : WordStack A (Fin 2) ι → Finset (ι → A), epsMCAgs (F := F) C δ L ≤ B :=
  ⟨fun _ => (∅ : Finset (ι → A)), by rw [epsMCAgs_emptyList_eq_zero]; exact zero_le B⟩

/-- **`epsMCAgs` is monotone in the radius `δ`.** A larger radius only weakens the size clause
`|S| ≥ (1 - δ)·n` of `mcaEventGSrow` (the witness-in-`L` and no-row clauses are `δ`-free), so the
GS-row bad event holds for at least as many witness sets, the per-stack probability grows
pointwise, and so does the supremum. The GS-exposed analogue of `epsMCA_mono`; it shows the prize
bound is hardest at the largest admissible radius (capacity), justifying the gap `η > 0`. -/
theorem epsMCAgs_mono
    (C : Set (ι → A)) (L : WordStack A (Fin 2) ι → Finset (ι → A)) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    epsMCAgs (F := F) C δ L ≤ epsMCAgs (F := F) C δ' L := by
  classical
  unfold epsMCAgs
  apply iSup_mono
  intro u
  apply Pr_le_Pr_of_implies
  intro γ h_event
  obtain ⟨S, hS_card, hline, hpair⟩ := h_event
  exact ⟨S, le_trans (mul_le_mul_of_nonneg_right (tsub_le_tsub_left h 1) (zero_le _)) hS_card,
    hline, hpair⟩

end ProximityGap.MCAGS

#print axioms ProximityGap.MCAGS.epsMCAgs_emptyList_eq_zero
#print axioms ProximityGap.MCAGS.exists_list_epsMCAgs_le
#print axioms ProximityGap.MCAGS.epsMCAgs_mono
