/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthREnergyLaw

/-!
# The first DISCHARGED instance of the BGK sup-bound Prop: the full group at `M = 1` — #466

Every prior consumer carries `WorstCaseIncompleteSumBound ψ G M` as a named OPEN hypothesis.
This file proves the Prop outright — with `M = 1`, exact — for the full multiplicative group
`G = F^*`:

* `eta_units_eq_neg_one` — Ramanujan-style exact cancellation: for primitive `ψ` and `b ≠ 0`,
  `η_b = ∑_{y≠0} ψ(b·y) = −1` (complete-sum orthogonality minus the `y = 0` term).
* `worstCase_units` — hence `WorstCaseIncompleteSumBound ψ (F^*) 1`: the sup-bound Prop HOLDS
  at `M = 1`, beating the trivial anchor `M = |G|² = (q−1)²` by the full square.
* `rEnergy_units_le` — feeding it to the landed tower: the depth-`r` energy of the full group
  obeys `q·E_r ≤ (q−1)^{2r} + q·(q−1)` for EVERY `r` — an unconditional, fully discharged
  instance of the whole BGK ⟹ energy pipeline.

**Honesty note.** This is the regime `|G| = q − 1` (index 1), the OPPOSITE extreme from the
prize instance (`|G| ≈ q^{0.19}`, deep BGK regime). It does not touch the open nine bits. Its
value is structural: the Prop is now *demonstrably satisfiable with real cancellation*, the
pipeline is exercised end-to-end with zero open inputs, and the instance ladder
(index 1 here; index 2 = quadratic-residue Gauss sums next; smooth small-index subgroups
after) is the honest downward path toward the prize regime. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw

namespace ArkLib.ProximityGap.Frontier.BGKProvenInstanceFullGroup

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact Ramanujan cancellation on the full multiplicative group**: for primitive `ψ` and
`b ≠ 0`, `∑_{y ≠ 0} ψ(b·y) = −1`. -/
theorem eta_units_eq_neg_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) :
    eta ψ ((Finset.univ : Finset F).erase 0) b = -1 := by
  have hfull : ∑ y : F, ψ (b * y) = 0 := by
    have h := AddChar.sum_mulShift b hψ
    rw [if_neg hb] at h
    calc ∑ y : F, ψ (b * y) = ∑ y : F, ψ (y * b) := by
          exact Finset.sum_congr rfl (fun y _ => by rw [mul_comm])
      _ = 0 := by exact_mod_cast h
  have hsplit : ∑ y : F, ψ (b * y)
      = ψ (b * 0) + ∑ y ∈ (Finset.univ : Finset F).erase 0, ψ (b * y) :=
    (Finset.add_sum_erase _ (fun y => ψ (b * y)) (Finset.mem_univ 0)).symm
  have h0 : ψ (b * 0) = 1 := by simp
  rw [eta]
  rw [hsplit, h0] at hfull
  linear_combination hfull

/-- **The BGK sup-bound Prop, DISCHARGED at `M = 1`** for the full multiplicative group:
`WorstCaseIncompleteSumBound ψ (F^*) 1` holds outright — exact square-root-free cancellation,
`(q−1)²` times better than the trivial anchor. -/
theorem worstCase_units {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    WorstCaseIncompleteSumBound ψ ((Finset.univ : Finset F).erase 0) 1 := by
  intro b hb
  rw [eta_units_eq_neg_one hψ hb]
  simp

/-- **The fully-discharged pipeline instance**: the depth-`r` energy of the full group obeys
`q·E_r ≤ (q−1)^{2r} + q·(q−1)` for every `r ≥ 1` — the landed BGK ⟹ energy chain with ZERO
open inputs. -/
theorem rEnergy_units_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {r : ℕ} (hr : 1 ≤ r) :
    (Fintype.card F : ℝ) * rEnergy ((Finset.univ : Finset F).erase 0) r
      ≤ (((Finset.univ : Finset F).erase 0).card : ℝ) ^ (2 * r)
        + 1 ^ (r - 1) * ((Fintype.card F : ℝ)
          * ((Finset.univ : Finset F).erase 0).card) :=
  rEnergy_le_of_worstCase hψ _ (by norm_num) (worstCase_units hψ) hr

end ArkLib.ProximityGap.Frontier.BGKProvenInstanceFullGroup

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKProvenInstanceFullGroup.eta_units_eq_neg_one
#print axioms ArkLib.ProximityGap.Frontier.BGKProvenInstanceFullGroup.worstCase_units
#print axioms ArkLib.ProximityGap.Frontier.BGKProvenInstanceFullGroup.rEnergy_units_le
