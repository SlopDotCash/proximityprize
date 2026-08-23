/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Collapse

/-!
# The §1 Grand MCA Challenge over-reaches past capacity (Finding F6b)

`GrandChallengeCollapse.grandMCAChallenge_iff_epsMCA_one` (Finding F6) shows the formal §1
encoding collapses to the single radius-one bound `ε_mca(C, 1) ≤ ε*`. This file records the
*directional* consequence of that collapse.

Because `ε_mca` is **monotone non-decreasing** in `δ` (`epsMCA_mono`) and `δ = 1` is its
global maximiser, the radius-one bound is the *strongest* point bound: it is equivalent to
demanding `ε_mca(C, δ) ≤ ε*` at **every** radius `δ ≤ 1` simultaneously
(`grandMCAChallenge_iff_forall_le_one`) — in particular across the whole regime
`δ ≥ 1 - ρ` at and beyond list-decoding capacity.

ABF26's actual §4.5 target (`mcaConjecture`) only asks for the bound at radii `δ < 1 - ρ`,
*strictly below capacity*. So the formal `grandMCAChallenge` / `mcaPrize` encoding is not
merely defect-collapsed (F6); it is **strictly stronger** than the paper's ask — it
additionally forces the bound on the closed-to-capacity window `[1 - ρ, 1]`, where for
realistic parameters `ε_mca(C, 1) = C(n, k+1)/|F| ≫ ε*` (`epsMCA_one_eq_choose_div`,
`grandMCAChallenge_iff_choose_le`) and the bound provably fails. The `M521` / `Fin 16`
"resolution" succeeds only because at `n = 16` even this over-strong radius-one bound holds
(`C(16, 8)/2^521 = 2^{-507} ≤ 2^{-128}`).

The honest takeaway: the radius-one collapse demands a proximity bound *past* capacity, which
is the wrong target. The faithful prize is the sub-capacity bound, and this file isolates the
clean **window-to-endpoint reduction** (`forall_epsMCA_le_iff_top`): the MCA bound throughout
a window `[0, t]` is equivalent to the single endpoint bound `ε_mca(C, t) ≤ ε*`. At
`t → (1 - ρ)⁻` that endpoint is exactly the open `mcaConjecture` inequality, and any such
endpoint bound is precisely an `MCALowerWitness` (`mcaLowerWitness_of_epsMCA_le`).

## Main results

* `forall_epsMCA_le_iff_top` — `(∀ δ ≤ t, ε_mca(C, δ) ≤ ε*) ↔ ε_mca(C, t) ≤ ε*`.
* `grandMCAChallenge_iff_forall_le_one` — the formal challenge is the `t = 1` instance:
  the MCA bound at *every* radius up to the full space (past capacity).
* `grandMCAChallenge_imp_le` — the formal challenge implies the bound at each `δ ≤ 1`,
  in particular ABF26's sub-capacity ask; the converse fails at realistic parameters.
* `mcaLowerWitness_of_epsMCA_le` — a sub-capacity endpoint bound *is* an `MCALowerWitness`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open GrandChallenges

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Window-to-endpoint reduction.** Since `ε_mca` is monotone non-decreasing in `δ`
(`epsMCA_mono`), the MCA bound holding throughout a window `[0, t]` is equivalent to it
holding at the single top radius `t`. This is the faithful shape of "the bound holds up to
`δ*`": one need only certify the endpoint. -/
theorem forall_epsMCA_le_iff_top (C : Set (ι → F)) (ε_star : ℝ≥0) (t : ℝ≥0) :
    (∀ δ : ℝ≥0, δ ≤ t → epsMCA (F := F) (A := F) C δ ≤ (ε_star : ENNReal)) ↔
      epsMCA (F := F) (A := F) C t ≤ (ε_star : ENNReal) := by
  constructor
  · intro h
    exact h t le_rfl
  · intro h δ hδ
    exact le_trans (epsMCA_mono (F := F) C hδ) h

/-- **The formal §1 MCA challenge is the `t = 1` window instance.** Via the radius-one
collapse plus monotonicity, `grandMCAChallenge C ε*` is equivalent to the MCA bound holding
at *every* radius `δ ≤ 1` — i.e. across the entire at-and-beyond-capacity regime
`[1 - ρ, 1]` that ABF26 deliberately excludes from its §4.5 conjecture. The encoded challenge
is therefore strictly stronger than the paper's sub-capacity ask. -/
theorem grandMCAChallenge_iff_forall_le_one (C : LinearCode ι F) (ε_star : ℝ≥0) :
    grandMCAChallenge C ε_star ↔
      ∀ δ : ℝ≥0, δ ≤ 1 →
        epsMCA (F := F) (A := F) (C : Set (ι → F)) δ ≤ (ε_star : ENNReal) := by
  rw [grandMCAChallenge_iff_epsMCA_one]
  exact (forall_epsMCA_le_iff_top (C : Set (ι → F)) ε_star 1).symm

/-- **Over-reach, forward direction.** If the formal `grandMCAChallenge` holds then the MCA
bound holds at *every* radius `δ ≤ 1`, in particular at every `δ < 1 - ρ` strictly below
capacity (ABF26's actual ask). The converse fails at realistic parameters: there
`ε_mca(C, 1) = C(n, k+1)/|F| ≫ ε*` (so the formal challenge is false), while the sub-capacity
bound is the genuinely open `mcaConjecture`. -/
theorem grandMCAChallenge_imp_le (C : LinearCode ι F) (ε_star : ℝ≥0)
    (h : grandMCAChallenge C ε_star) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    epsMCA (F := F) (A := F) (C : Set (ι → F)) δ ≤ (ε_star : ENNReal) :=
  (grandMCAChallenge_iff_forall_le_one C ε_star).mp h δ hδ

/-- **A sub-capacity endpoint bound is one-sided prize progress.** Any radius `t ≤ 1` with
`ε_mca(C, t) ≤ ε*` is exactly the data of an `MCALowerWitness`, certifying `δ* ≥ t`. The
faithful prize asks to push this certified `t` up to `(1 - ρ)⁻` (the open `mcaConjecture`),
in contrast to the formal challenge's degenerate demand of `t = 1`. -/
def mcaLowerWitness_of_epsMCA_le (C : Set (ι → F)) (ε_star t : ℝ≥0) (ht : t ≤ 1)
    (h : epsMCA (F := F) (A := F) C t ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star :=
  ⟨t, ht, h⟩

#print axioms forall_epsMCA_le_iff_top
#print axioms grandMCAChallenge_iff_forall_le_one
#print axioms grandMCAChallenge_imp_le
#print axioms mcaLowerWitness_of_epsMCA_le

end ProximityGap
