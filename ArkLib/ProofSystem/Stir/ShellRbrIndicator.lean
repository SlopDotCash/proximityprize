/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.AveragedRbr.Security.RoundByRound
import ArkLib.ProofSystem.Stir.MultiRoundAssembly

/-!
# The shell residual, discharged at the honest indicator budget (#347)

`stirMultiRoundRbrSoundnessResidual` (the SHELL verifier's rbr residual) is documented
likely-false at sub-1 budgets — the shell accepts everything, and the genuine sub-unit
obligation was discharged on the CHECKING verifier (`stirCheckingRbrSoundness_genuine`,
#301).  What IS true of the shell, and is proven here, is the **indicator-budget
discharge**: rbr knowledge soundness at the budget `1` concentrated on the initial fold
challenge and `0` everywhere else. The state function agrees with the input relation
at the root and is true after the fold challenge, so the bound holds at each fixed prefix.

* **`stirMultiRoundRbrSoundness_indicator`** — the residual HOLDS at
  `fun i => if i = foldChalIdx then 1 else 0`;
* `stirMultiRoundIOP_isSecureWithGap_indicator` — the secure-with-gap package at that
  budget through the existing general wiring.

HONESTY: the budget is `≥ 1` at one round — this carries no security content for
`secpar > 0` (exactly as the in-tree small-field discharges), and the sub-1 impossibility
for the shell stands.  The value is census hygiene: the named residual is now a proven
theorem at its honest budget instead of an open `Prop`, with the genuine sub-unit story
living on the checking verifier where it was discharged.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec NNReal VectorIOP
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- The initial fold challenge of the multi-round wire (round `0`). -/
def foldChalIdx (M : ℕ) : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨0, by omega⟩, by
    have h : (stirVSpec M (fun _ => Fintype.card ι) 1).dir ⟨0, by omega⟩ = .V_to_P := by
      rw [stirVSpec_dir_eq_chal_iff]
      simp
    exact h⟩

private theorem stirMultiRoundRbrSoundnessFixedPrefix_indicator
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    stirMultiRoundRbrSoundnessFixedPrefix M φ deg δ
      (fun i => if i = foldChalIdx (F := F) (ι := ι) M then 1 else 0) :=
  stirRbrKnowledgeSoundnessFixedPrefix_of_one_le_first M φ deg δ
    (stirMultiRoundIOP M φ deg).toOracleVerifier _ (fun i hi => by
      have h : i = foldChalIdx (F := F) (ι := ι) M := Subtype.ext (Fin.ext hi)
      simp [h])

/-- The averaged shell residual holds at the indicator budget, with `1` at the fold challenge
and `0` elsewhere. -/
theorem stirMultiRoundRbrSoundness_indicator (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (δ : ℝ≥0) :
    stirMultiRoundRbrSoundnessResidual M φ deg δ
      (fun i => if i = foldChalIdx (F := F) (ι := ι) M then 1 else 0) :=
  OracleProof.rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged
    (stirMultiRoundRbrSoundnessFixedPrefix_indicator M φ deg δ)

/-- The secure-with-gap package for the assembled shell IOPP at the indicator budget,
through the existing general wiring. -/
theorem stirMultiRoundIOP_isSecureWithGap_indicator (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (δ : ℝ≥0) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ)
      (fun i => if i = foldChalIdx (F := F) (ι := ι) M then 1 else 0)
      (stirMultiRoundIOP M φ deg) :=
  stirMultiRoundIOP_isSecureWithGap M φ deg δ _
    (stirMultiRoundRbrSoundnessFixedPrefix_indicator M φ deg δ)

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.stirMultiRoundRbrSoundness_indicator
#print axioms StirIOP.MultiRound.stirMultiRoundIOP_isSecureWithGap_indicator
