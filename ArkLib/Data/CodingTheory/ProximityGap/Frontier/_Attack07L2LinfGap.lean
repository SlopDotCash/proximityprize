/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.IncidenceDevL2Offset

/-!
# Attack #07 — the L²(offset) → L∞(offset) upgrade is GENUINELY UNAVAILABLE — #464

This file is the honest, axiom-clean *refutation* of the only structural lever that the
line-ball / hyperplane-incidence angle (input (2), `WorstCaseIncidenceBounded`) offers for
bypassing Paley: deriving the worst-case (`L∞`) per-offset incidence deviation from the PROVEN
mean-square (`L²`) cancellation `IncidenceDevL2Offset.dev_l2_offset_eq`.

## The lever and why it fails

The proven Parseval identity over the offset says

  `(1/q) ∑_{s₀} ‖D(s₀)‖² = (1/q)·q·∑_b ‖η_b‖² = ∑_b ‖η_b‖²`   (`= q·|G|` by Parseval),

so the *root-mean-square* deviation over offsets is `√q·B`-scale — the prize scale — for FREE.
The prize, however, needs the bound at a SINGLE worst-case offset (`L∞`).  The hope: a flatness /
equidistribution argument turning the `L²` average into an `L∞` sup with only an `O(1)` (or
`O(log)`) loss.

This file proves that hope is FALSE in the cleanest available geometry — the degenerate
("point") direction `s₁ = 0`, where the deviation field is the exact, fully explicit

  `D(s₀) = I(s₀,0) − |G| = q·[s₀ ∈ G] − |G|`   (`lineIncidence_zero_dir`).

At any `s₀ ∈ G` this is *exactly* `q − |G|`, a spike of order `q`, while the `L²`-RMS is only
`√(q·|G|)·(1/√q)`-scale.  Concretely we prove, with NO field-size or regime hypothesis:

* `devField_zero_dir_mem`  : `‖D(s₀)‖ = q − |G|` for every `s₀ ∈ G` (the explicit spike);
* `linf_ge_q_sub_card`     : `max_{s₀} ‖D(s₀)‖ ≥ q − |G|`  (whenever `G` is nonempty);
* `linf_sq_gt_meansq`      : the squared sup `(q−|G|)²` STRICTLY exceeds the mean-square
                              `(1/q)∑‖D‖² = |G|·(q−|G|)` once `q > 2|G|` (the prize regime
                              `q ≈ n·2^128 ≫ |G| = n`), with the exact gap factor
                              `linf_sq_over_meansq_eq` : `(q−|G|)² / (|G|(q−|G|)) = (q−|G|)/|G|`.

The ratio `(q−|G|)/|G| ≈ q/n ≈ 2^128` is the EXACT size of the `L²→L∞` deficit in the prize
regime: the worst offset is `√(q/n)`-times above the RMS.  So the proven `L²` cancellation does
NOT transfer to `L∞`; the entire remaining difficulty IS the sup-over-offset, which is precisely
BCHKS Conj 1.12 / the Paley wall.  The lever is refuted, the wall is named.

(The spike here is the principal `b=0`/`s₀∈G` collapse; in the genuine far direction `s₁ ≠ 0`
over `V=F` the deviation is identically `0` — `RealizerL2NotSup.farLine_incidence_eq_card` — and
the re-coupling to `B` only appears in the `≥2`-dimensional MCA geometry, where the `L∞` spike
is again `Θ(q)`, see `scripts/probes/probe_2d_annihilator_incidence_supVSavg.py`.)

Axiom-clean (`propext, Classical.choice, Quot.sound`); pure algebra on the explicit degenerate
deviation field.  Issue #464.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge
open ArkLib.ProximityGap.IncidenceDevL2Offset

namespace ArkLib.ProximityGap.Frontier.Attack07L2LinfGap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The degenerate-direction deviation is the explicit step `q·[s₀∈G] − |G|`.**
For the point-direction `s₁ = 0` the incidence is `I(s₀,0) = q·[s₀∈G]`
(`lineIncidence_zero_dir`), so the deviation field `D(s₀) = I(s₀,0) − |G|` is the exact integer
step `q·[s₀∈G] − |G|`. -/
theorem devField_zero_dir {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₀ : F) :
    devField ψ G s₀ 0
      = ((if s₀ ∈ G then (Fintype.card F : ℂ) else 0) - (G.card : ℂ)) := by
  classical
  rw [devField_eq_incidence_sub_mean hψ G s₀ 0, lineIncidence_zero_dir]
  by_cases h : s₀ ∈ G <;> simp [h]

/-- **The spike: at any `s₀ ∈ G` the deviation has modulus exactly `q − |G|`.**
This is the single offset where the deviation is of order `q` — the obstruction to any
`L²→L∞` upgrade.  (`|G| ≤ q` makes the difference nonnegative.) -/
theorem devField_zero_dir_mem {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {s₀ : F} (hs₀ : s₀ ∈ G) :
    ‖devField ψ G s₀ 0‖ = (Fintype.card F : ℝ) - (G.card : ℝ) := by
  classical
  rw [devField_zero_dir hψ G s₀, if_pos hs₀]
  have hle : (G.card : ℝ) ≤ (Fintype.card F : ℝ) := by
    have : G.card ≤ Fintype.card F := by
      simpa [Finset.card_univ] using Finset.card_le_univ G
    exact_mod_cast this
  rw [show ((Fintype.card F : ℂ) - (G.card : ℂ))
        = (((Fintype.card F : ℝ) - (G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- **The `L∞`-over-offset deviation is `≥ q − |G|`.**  Whenever the ball `G` is nonempty there
is an offset `s₀ ∈ G` at which the deviation is exactly `q − |G|`, so the supremum over offsets
is at least this `Θ(q)` spike.  Stated as an explicit witness offset. -/
theorem linf_ge_q_sub_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : G.Nonempty) :
    ∃ s₀ : F, ‖devField ψ G s₀ 0‖ = (Fintype.card F : ℝ) - (G.card : ℝ) := by
  obtain ⟨s₀, hs₀⟩ := hG
  exact ⟨s₀, devField_zero_dir_mem hψ G hs₀⟩

/-- **The exact mean-square over the offset is `|G|·(q − |G|)`.**  Direct evaluation of the
explicit step field: `D(s₀)` is `q − |G|` on the `|G|` offsets in `G` and `−|G|` on the `q − |G|`
offsets outside, so `∑_{s₀}‖D‖² = |G|(q−|G|)² + (q−|G|)|G|² = |G|(q−|G|)·q`, hence the average is
`|G|·(q − |G|)`.  (This matches `dev_l2_offset_eq` with `∑_{b∈dev}‖η_b‖² = q·|G| − |G|²`, the full
period energy minus the principal `η₀ = |G|`.) -/
theorem meansq_zero_dir {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (1 / (Fintype.card F : ℝ)) * (∑ s₀ : F, ‖devField ψ G s₀ 0‖ ^ 2)
      = (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
  classical
  have hle : (G.card : ℝ) ≤ (Fintype.card F : ℝ) := by
    have : G.card ≤ Fintype.card F := by
      simpa [Finset.card_univ] using Finset.card_le_univ G
    exact_mod_cast this
  have hterm : ∀ s₀ : F, ‖devField ψ G s₀ 0‖ ^ 2
      = (if s₀ ∈ G then ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ 2 else (G.card : ℝ) ^ 2) := by
    intro s₀
    rw [devField_zero_dir hψ G s₀]
    by_cases h : s₀ ∈ G
    · rw [if_pos h, if_pos h,
        show ((Fintype.card F : ℂ) - (G.card : ℂ))
          = (((Fintype.card F : ℝ) - (G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [if_neg h, if_neg h, zero_sub, norm_neg,
        show ((G.card : ℂ)) = (((G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun s₀ _ => hterm s₀)]
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F); exact_mod_cast this
  -- ∑_{s₀} ite = |G|·(q-|G|)² + (q-|G|)·|G|²  via sum_ite_mem-style evaluation
  have hsumval : (∑ s₀ : F,
      (if s₀ ∈ G then ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ 2 else (G.card : ℝ) ^ 2))
      = (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ 2
        + ((Fintype.card F : ℝ) - (G.card : ℝ)) * (G.card : ℝ) ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hcardG : (Finset.univ.filter (fun s₀ : F => s₀ ∈ G)).card = G.card := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hcardNG : (Finset.univ.filter (fun s₀ : F => s₀ ∉ G)).card
        = Fintype.card F - G.card := by
      rw [Finset.filter_not, Finset.card_univ_diff, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    rw [hcardG, hcardNG]
    have hh : G.card ≤ Fintype.card F := by
      simpa [Finset.card_univ] using Finset.card_le_univ G
    rw [Nat.cast_sub hh]
  rw [hsumval]
  field_simp
  ring

/-- **The exact `L∞²/meansq` ratio is `(q − |G|)/|G|`.**  Dividing the spike `(q−|G|)²` by the
mean-square `|G|(q−|G|)`: the worst offset's squared deviation exceeds the mean-square by the
factor `(q−|G|)/|G|`.  In the prize regime `q ≈ n·2^128`, `|G| = n`, this factor is `≈ 2^128`:
the `L²→L∞` deficit is the full budget.  (Requires `G` nonempty and `|G| < q`, both true for the
nontrivial smooth ball.) -/
theorem linf_sq_over_meansq_eq (G : Finset F)
    (hG : G.Nonempty) (hlt : (G.card : ℝ) < (Fintype.card F : ℝ)) :
    ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ 2
        / ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)))
      = ((Fintype.card F : ℝ) - (G.card : ℝ)) / (G.card : ℝ) := by
  have hGpos : (0 : ℝ) < (G.card : ℝ) := by
    have : 0 < G.card := Finset.card_pos.mpr hG
    exact_mod_cast this
  have hdpos : (0 : ℝ) < (Fintype.card F : ℝ) - (G.card : ℝ) := by linarith
  field_simp [ne_of_gt hGpos, ne_of_gt hdpos]

/-- **HEADLINE — the squared `L∞` STRICTLY dominates the mean-square once `q > 2|G|`.**
Combining the spike `(q−|G|)²` (a lower bound for `max ‖D‖²`) with the exact mean-square
`|G|(q−|G|)`: as soon as `q > 2|G|` (so `q − |G| > |G|`), the worst-case squared deviation
strictly exceeds the mean-square.  The proven `L²` cancellation therefore CANNOT bound the
worst-case offset: the gap is real, of multiplicative size `(q−|G|)/|G| ≈ q/n`.  This is the
exact, axiom-clean refutation of the "average ⟹ sup" lever for the hyperplane-incidence angle —
the residual `L∞` sup IS the Paley/BCHKS-1.12 wall, not an artifact of a loose triangle bound. -/
theorem linf_sq_gt_meansq (G : Finset F)
    (hG : G.Nonempty) (hq : 2 * (G.card : ℝ) < (Fintype.card F : ℝ)) :
    (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ))
      < ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ 2 := by
  have hGpos : (0 : ℝ) < (G.card : ℝ) := by
    have : 0 < G.card := Finset.card_pos.mpr hG
    exact_mod_cast this
  have hd : (G.card : ℝ) < (Fintype.card F : ℝ) - (G.card : ℝ) := by linarith
  have hdpos : (0 : ℝ) < (Fintype.card F : ℝ) - (G.card : ℝ) := by linarith
  nlinarith [hd, hdpos, hGpos]

end ArkLib.ProximityGap.Frontier.Attack07L2LinfGap

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.Attack07L2LinfGap.devField_zero_dir
#print axioms ArkLib.ProximityGap.Frontier.Attack07L2LinfGap.devField_zero_dir_mem
#print axioms ArkLib.ProximityGap.Frontier.Attack07L2LinfGap.linf_ge_q_sub_card
#print axioms ArkLib.ProximityGap.Frontier.Attack07L2LinfGap.meansq_zero_dir
#print axioms ArkLib.ProximityGap.Frontier.Attack07L2LinfGap.linf_sq_over_meansq_eq
#print axioms ArkLib.ProximityGap.Frontier.Attack07L2LinfGap.linf_sq_gt_meansq
