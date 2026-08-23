/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightMidLeaves
import ArkLib.ProofSystem.Spartan.ComposedRbrKnowledgeSoundness
import ArkLib.ProofSystem.Spartan.SumcheckDeterminismWitnesses

/-!
# The composed TIGHT Spartan rbr knowledge soundness — no `1`-slots (issue #329, K3+K5)

The old composed theorem `composedRbrKnowledgeSoundnessPreserving_unconditional`
(`ShortPhaseRbrKnowledgeLeaves.lean`) carries the proven-forced per-round error `err₅ = 1` at the
`linearCombination` round: on the target-dropping relation chain a prover sending the *true*
evaluation claims defeats any smaller bound (the v=t attack of #114). This module assembles the
**target-carrying tight chain**, in which that slot is `1/|R|` — Spartan Lemma 5.1's bound — and
no per-round error is `1`.

## Seam audit (the relation chain through the six phases)

The composed tight reduction is `composedTightPIOP :=`
`firstMessage ▷ firstChallenge ▷ firstSumcheckWithTarget ▷ sendEvalClaimWithTarget ▷`
`linearCombinationWithTarget ▷ prependRLCTargetWithTarget`, and the chain threads:

| # | phase                         | relIn → relOut                                  | err      |
|---|-------------------------------|--------------------------------------------------|----------|
| 1 | `firstMessage`                | `spartanRelIn → firstMessageRbrRelB`             | `0`      |
| 2 | `firstChallenge`              | `relB → firstSumcheckWithTargetRbrRelIn`         | `ℓ_m/|R|`|
| 3 | `firstSumcheckWithTarget`     | `…RelIn → firstSumcheckWithTargetRbrRelOut`      | `3/|R|`  |
| 4 | `sendEvalClaimWithTarget`     | `…RelOut → tightRelE`                            | `0`      |
| 5 | `linearCombinationWithTarget` | `tightRelE → tightRelF`                          | `1/|R|`  |
| 6 | `prependRLCTargetWithTarget`  | `tightRelF → tightRelG`                          | (0-round)|

Which leaves are reusable as-is, and where the seams needed work:

* **Seam 2→3** is the only genuinely new seam bridge of this assembly: the Schwartz–Zippel leaf
  `firstChallenge_rbrKnowledgeSoundness_schwartzZippel` ends at `firstSumcheckRbrRelIn` (the
  target-dropping pullback), while phase 3 starts at `firstSumcheckWithTargetRbrRelIn`. These
  coincide **definitionally** (`firstSumcheckWithTargetRbrRelIn_eq_relIn` below, by `rfl`): the
  two lenses share the projection `toFunA` and the pullback only reads the projection. So the SZ
  leaf is reusable verbatim — no conjoin needed at this seam.
* **Seams 3→4→5→6** were landed by the X-lane (`TightMidLeaves.lean`): the carried target `e₁`
  makes `firstSumcheckWithTargetRbrRelOut` genuinely pin the terminal, `tightRelE` conjoins the
  *binding identity* `e₁ = eq̃(τ)(r_x)·(v_A·v_B − v_C)` over the **sent** claims (the predicate
  that the generic conjoin combinator `Verifier.rbrKnowledgeSoundness_conjoin` (K3) threads;
  here it is baked into the leaf relations directly, which is the same architecture with the
  `hPres` content discharged inside `sendEvalClaimWithTarget_rbrKnowledgeSoundness_leaf` — the
  pass-through verifier preserves the statement, and the claims-message round needs **no**
  nontrivial flip bound for the pinning because the binding conjunct is carried as a *relation
  conjunct*, not certified at the message round: its violation is challenge-independent and is
  what makes the `1/|R|` kernel-event analysis of leaf 5 sound).
* **Phases 1, 2** are reusable as-is from `ShortPhaseRbrKnowledgeLeaves.lean`.
* The terminal `tightRelG` (carried target = true RLC + binding) is the composition surface for
  the future `secondSumcheckWithTarget ▷ finalCheckWithClaim` continuation (the landed K4 leaf
  `finalCheckWithClaim_rbrKnowledgeSoundness` consumes the doomed target at the far end); that
  continuation needs a target-carrying second sum-check lift, which does not exist in-tree yet
  and is tracked on #329.

## Main results

* `composedTightPIOP` — the 6-phase composed oracle reduction.
* `composedTightPIOP_rbrKnowledgeSoundness_of_leaves` — the relation-chain-agnostic 5-seam fold
  (all determinism witnesses discharged internally; only the six per-phase leaves are taken).
* `composedTightRbrKnowledgeSoundness_unconditional` — **the headline**: the composed tight
  chain is rbr knowledge-sound from `spartanRelIn` to `tightRelG` with per-round errors
  `(0, ℓ_m/|R|, 3/|R| per round, 0, 1/|R|)` — the `err₅ = 1` slot of the old composition is
  eliminated.
* `composedTightRbrError_unconditional_le` — the no-`1`-slot certificate: every per-round error
  of the headline error vector is `≤ max(ℓ_m, 3)/|R|`.

**Scope note (DRY audit 2026-06-11, item 10):** this 6-phase chain is a strict ancestor of the
full 8-phase apex — `TightComposedFull.lean` (`composedTightFull_rbrKnowledgeSoundness`) and
the paired chain `TightApexPure.lean` (`composedTightPure_rbrKnowledgeSoundness` +
`composedTightPure_perfectCompleteness`). Its endpoint (`tightRelG`) is interior to the full
chain. New consumers should target the apex; this file remains as the documented shorter
assembly pattern.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 512

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-! ### The combined protocol spec of the tight chain (right-associated suffixes) -/

/-- suffix `[linearCombinationWithTarget ▷ prependRLCTargetWithTarget]`
(= `⟨V_to_P, LinComb⟩ ++ₚ !p[]`). -/
abbrev tightSfx5 :=
  (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ (!p[] : ProtocolSpec 0)
instance : ∀ i, OracleInterface ((tightSfx5 (R := R)).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1))
    (pSpec₂ := (!p[] : ProtocolSpec 0))
instance : ∀ i, SampleableType ((tightSfx5 (R := R)).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1))
    (pSpec₂ := (!p[] : ProtocolSpec 0))

/-- suffix `[sendEvalClaimWithTarget ▷ …]` (= `⟨P_to_V, BundledEvalClaim⟩ ++ₚ tightSfx5`). -/
abbrev tightSfx4 :=
  (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) ++ₚ tightSfx5 (R := R)
instance : ∀ i, OracleInterface ((tightSfx4 (R := R)).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1))
    (pSpec₂ := tightSfx5 (R := R))
instance : ∀ i, SampleableType ((tightSfx4 (R := R)).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1))
    (pSpec₂ := tightSfx5 (R := R))

/-- suffix `[firstSumcheckWithTarget ▷ …]` (= `sumcheck₃ ++ₚ tightSfx4`). -/
abbrev tightSfx3 := Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ tightSfx4 (R := R)
instance : ∀ i, OracleInterface ((tightSfx3 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
    (pSpec₂ := tightSfx4 (R := R))
instance : ∀ i, SampleableType ((tightSfx3 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
    (pSpec₂ := tightSfx4 (R := R))

/-- suffix `[firstChallenge ▷ …]` (= `⟨V_to_P, FirstChallenge⟩ ++ₚ tightSfx3`). -/
abbrev tightSfx2 :=
  (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ tightSfx3 (R := R) pp
instance : ∀ i, OracleInterface ((tightSfx2 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1))
    (pSpec₂ := tightSfx3 (R := R) pp)
instance : ∀ i, SampleableType ((tightSfx2 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1))
    (pSpec₂ := tightSfx3 (R := R) pp)

/-- The full combined protocol-spec of the composed tight Spartan chain
(= `firstMessage ++ₚ tightSfx2`), right-associated to match the `.append <|` fold. -/
abbrev composedTightPSpec :=
  (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1) ++ₚ tightSfx2 (R := R) pp
instance : ∀ i, OracleInterface ((composedTightPSpec (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1))
    (pSpec₂ := tightSfx2 (R := R) pp)
instance : ∀ i, SampleableType ((composedTightPSpec (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1))
    (pSpec₂ := tightSfx2 (R := R) pp)

variable {ι : Type} (oSpec : OracleSpec ι)

/-! ### The composed tight reduction -/

/-- Reduction-level `AppendCoherent` alias for the carried `sendEvalClaim` round (the verifier
instance is keyed on the raw `sendEvalClaimWithTargetVerifier`). -/
instance instSendEvalClaimWithTargetReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (sendEvalClaimWithTarget (R := R) pp oSpec).verifier :=
  instSendEvalClaimWithTargetVerifierAppendCoherent pp oSpec

/-- Reduction-level `AppendCoherent` alias for the carried `linearCombination` round. -/
instance instLinearCombinationWithTargetReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (linearCombinationWithTarget (R := R) pp oSpec).verifier :=
  instLinearCombinationWithTargetVerifierAppendCoherent pp oSpec

/-- The carried honest RLC-target adapter pinned to the concrete oracle-interface universe used
by the rbr append keystones (mirror of the private `prependRLCTargetKS` of
`ComposedRbrKnowledgeSoundness.lean`). -/
private abbrev prependRLCTargetWTKS {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTargetWithTarget pp oSpec

/-- **The composed TIGHT Spartan PIOP oracle reduction** (issue #329): the first six phases with
the target-carrying middle, from the bare R1CS instance to the carried RLC-target statement
`(T, (r, (e₁, (r_x, τ, 𝕩))))`. -/
def composedTightPIOP :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (composedTightPSpec (R := R) pp) :=
  (oracleReduction.firstMessage R pp oSpec).append <|
  (oracleReduction.firstChallenge R pp oSpec).append <|
    (firstSumcheckReductionWithTarget pp oSpec).append <|
    (sendEvalClaimWithTarget pp oSpec).append <|
    (linearCombinationWithTarget pp oSpec).append <|
    (prependRLCTargetWTKS pp oSpec)

/-! ### Direction facts -/

/-- Positivity of two-step round counts (local mirror of the private helper). -/
private theorem tightVsum_two_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

/-- The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message
(local mirror of the private helper). -/
private theorem tightSumcheckPSpec_dir_zero (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

/-- `tightSfx5` opens `V_to_P` (the linear-combination challenge). -/
private theorem tightSfx5_dir_zero (h : 0 < 1 + 0) :
    (tightSfx5 (R := R)).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + 0))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- `tightSfx4` opens `P_to_V` (the bundled eval-claim message). -/
private theorem tightSfx4_dir_zero (h : 0 < 1 + (1 + 0)) :
    (tightSfx4 (R := R)).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + 0)))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `sendEvalClaimWithTarget ▷ tightSfx5`: the combined spec
(= `tightSfx4`) at the seam index `1` is `V_to_P`. -/
private theorem tightSfx4_dir_seam (h : 1 < 1 + (1 + 0)) :
    (tightSfx4 (R := R)).dir ⟨1, h⟩ = .V_to_P := by
  have h5 : 0 < 1 + 0 := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + 0)))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (1 + 0)) from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact tightSfx5_dir_zero h5

/-- `tightSfx3` opens `P_to_V` (first sum-check's leading message). -/
private theorem tightSfx3_dir_zero (hm : 0 < pp.ℓ_m)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))) :
    (tightSfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := tightVsum_two_pos hm
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact tightSumcheckPSpec_dir_zero 3 pp.ℓ_m hv

/-- Seam-direction fact for `firstSumcheckWithTarget ▷ tightSfx4`: the combined spec
(= `tightSfx3`) at the seam index `vsum 2` is `P_to_V`. -/
private theorem tightSfx3_dir_seam
    (h : Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))) :
    (tightSfx3 (R := R) pp).dir ⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ = .P_to_V := by
  have h4 : 0 < 1 + (1 + 0) := by omega
  rw [show (⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩
        : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))))
      = Fin.natAdd (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)) (⟨0, h4⟩ : Fin (1 + (1 + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact tightSfx4_dir_zero h4

/-- `tightSfx2` opens `V_to_P` (the first challenge). -/
private theorem tightSfx2_dir_zero
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0)))) :
    (tightSfx2 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `firstChallenge ▷ tightSfx3`: the combined spec (= `tightSfx2`) at
the seam index `1` is `P_to_V`. -/
private theorem tightSfx2_dir_seam (hm : 0 < pp.ℓ_m)
    (h : 1 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0)))) :
    (tightSfx2 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h3 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0)))))
      = Fin.natAdd 1 (⟨0, h3⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))))
      from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact tightSfx3_dir_zero pp hm h3

/-- Seam-direction fact for `firstMessage ▷ tightSfx2`: the combined spec
(= `composedTightPSpec`) at the seam index `1` is `V_to_P`. -/
private theorem composedTightPSpec_dir_seam
    (h : 1 < 1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))))) :
    (composedTightPSpec (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h1 : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0))))))
      = Fin.natAdd 1 (⟨0, h1⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + (1 + (1 + 0)))))
      from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact tightSfx2_dir_zero pp h1

/-! ### The seam-2→3 bridge and the `hV₃` witness -/

/-- **The seam-2→3 bridge (definitional).** The target-preserving pullback input relation of the
first sum-check coincides with the original (target-dropping) one: the two lenses share the
projection, and the pullback reads only the projection. This is what lets the Schwartz–Zippel
`firstChallenge` leaf be reused verbatim on the tight chain. -/
theorem firstSumcheckWithTargetRbrRelIn_eq_relIn :
    firstSumcheckWithTargetRbrRelIn (R := R) pp oSpec
      = firstSumcheckRbrRelIn (R := R) pp oSpec := rfl

/-- **`hV₃` witness for the tight fold: the target-preserving first sum-check verifier is
failing-deterministic** (mirror of `firstSumcheck_toVerifier_isFailingDet` at the
target-preserving lens, through the proven `firstSumcheckCoherentWithTarget` instance). -/
theorem firstSumcheckWithTarget_toVerifier_isFailingDet :
    (firstSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier.IsFailingDet := by
  letI coh : OracleVerifier.LiftContextCoherent (firstSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec) := by
    change OracleVerifier.LiftContextCoherent (firstSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier
    exact firstSumcheckCoherentWithTarget (R := R) pp oSpec
  show ((Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).liftContext
    (firstSumcheckOracleLensWithTarget pp oSpec)).toVerifier.IsFailingDet
  rw [OracleVerifier.liftContext_toVerifier_comm]
  obtain ⟨v?, hv⟩ := sumcheckFull_toVerifier_isFailingDet oSpec 3 (boolEmbedding R) pp.ℓ_m
  exact ⟨_, Verifier.liftContext_failingDet _ _ v? hv⟩

/-! ### The folded composed error -/

/-- The folded per-round rbr knowledge error of the composed tight Spartan chain: the five
per-phase challenge-carrying error families (plus the trailing empty one) combined through
`ChallengeIdx.sumEquiv` at each of the five (right-associated) seams. -/
def composedTightRbrError
    (err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0) :
    (composedTightPSpec (R := R) pp).ChallengeIdx → ℝ≥0 :=
  Sum.elim err₁
    (Sum.elim err₂
      (Sum.elim err₃
        (Sum.elim err₄
          (Sum.elim err₅ err₆ ∘ ChallengeIdx.sumEquiv.symm)
          ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm)
      ∘ ChallengeIdx.sumEquiv.symm)
    ∘ ChallengeIdx.sumEquiv.symm

/-! ### The five-seam fold -/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relA : Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relC : Set ((Statement.AfterFirstChallenge R pp ×
    ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)}
  {relD : Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)}
  {relEt : Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relFt : Set ((Statement.AfterLinearCombinationWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relGt : Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}

/-- **Composed tight Spartan chain round-by-round knowledge soundness, reduced to the six
per-phase rbr-KS leaves** (relation-chain agnostic, stateless regime). All five seams (two
message, two challenge, one empty) are discharged residual-free by the proven keystones; all
determinism witnesses are discharged internally (the forwarding phases by their closed forms,
the target-preserving sum-check by `firstSumcheckWithTarget_toVerifier_isFailingDet`). -/
theorem composedTightPIOP_rbrKnowledgeSoundness_of_leaves [Subsingleton σ]
    (hm : 0 < pp.ℓ_m)
    [Inhabited (Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    [Inhabited (Statement.AfterLinearCombinationWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)]
    {err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0}
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :
      ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    (h₁ : (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relA relB err₁)
    (h₂ : (oracleReduction.firstChallenge.{0} R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB relC err₂)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relC relD err₃)
    (h₄ : (sendEvalClaimWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relD relEt err₄)
    (h₅ : (linearCombinationWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relEt relFt err₅)
    (h₆ : (prependRLCTargetWTKS pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relFt relGt err₆)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i)) :
    (composedTightPIOP (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl relA relGt
      (composedTightRbrError pp err₁ err₂ err₃ err₄ err₅ err₆) := by
  obtain ⟨verify₁, hV₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₂, hV₂⟩ := firstChallenge_toVerifier_pure.{0} (R := R) pp oSpec
  obtain ⟨verify₃?, hV₃⟩ := firstSumcheckWithTarget_toVerifier_isFailingDet (R := R) pp oSpec
  -- Seam 5 (`linearCombinationWithTarget ▷ prependRLCTargetWithTarget`, empty right seam;
  -- pure (hence failing-deterministic) left verifier). Residual-free, no direction facts.
  have hS5 : ((linearCombinationWithTarget pp oSpec).append
      (prependRLCTargetWTKS pp oSpec)).verifier.rbrKnowledgeSoundness init impl
      relEt relGt (Sum.elim err₅ err₆ ∘ ChallengeIdx.sumEquiv.symm) :=
    OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty
      (linearCombinationWithTarget pp oSpec).verifier
      (prependRLCTargetWTKS pp oSpec).verifier
      (fun p tr => some
        (((tr.challenges ⟨0, rfl⟩ : LinearCombinationChallenge R), p.1), p.2))
      (by rw [linearCombinationWithTarget_toVerifier_closed]; rfl)
      hInit ⟨()⟩ h₅ h₆
  -- Seam 4 (`sendEvalClaimWithTarget ▷ …`, challenge seam; pure left verifier).
  have hS4 : ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append
        (prependRLCTargetWTKS pp oSpec))).verifier.rbrKnowledgeSoundness init impl
      relD relGt (Sum.elim err₄ (Sum.elim err₅ err₆ ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) :=
    OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
      (sendEvalClaimWithTarget pp oSpec).verifier
      ((linearCombinationWithTarget pp oSpec).append
        (prependRLCTargetWTKS pp oSpec)).verifier
      (fun p tr => sendEvalClaimWithTargetRouteMap (R := R) pp p (tr.messages ⟨0, rfl⟩))
      (sendEvalClaimWithTarget_toVerifier_closed pp oSpec)
      hInit hInitNF hNE_E ⟨()⟩ (by omega)
      (tightSfx4_dir_seam (by omega)) (tightSfx5_dir_zero (R := R) (by omega)) h₄ hS5
  -- Seam 3 (`firstSumcheckWithTarget ▷ …`, message seam; failing-deterministic left verifier).
  have hS3 : ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          (prependRLCTargetWTKS pp oSpec)))).verifier.rbrKnowledgeSoundness init impl
      relC relGt (Sum.elim err₃ (Sum.elim err₄
          (Sum.elim err₅ err₆ ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) :=
    OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton
      (firstSumcheckReductionWithTarget pp oSpec).verifier
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          (prependRLCTargetWTKS pp oSpec))).verifier
      verify₃? hV₃ hInit hInitNF ⟨()⟩ (by omega)
      (tightSfx3_dir_seam pp (by omega)) (tightSfx4_dir_zero (R := R) (by omega)) h₃ hS4
  -- Seam 2 (`firstChallenge ▷ …`, message seam; pure left verifier).
  have hS2 : ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            (prependRLCTargetWTKS pp oSpec))))).verifier.rbrKnowledgeSoundness init impl
      relB relGt (Sum.elim err₂ (Sum.elim err₃ (Sum.elim err₄
            (Sum.elim err₅ err₆ ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)
          ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) :=
    OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
      (oracleReduction.firstChallenge R pp oSpec).verifier
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            (prependRLCTargetWTKS pp oSpec)))).verifier
      verify₂ hV₂ hInit hInitNF hNE_C ⟨()⟩ (by omega)
      (tightSfx2_dir_seam pp hm (by omega)) (tightSfx3_dir_zero pp hm (by omega)) h₂ hS3
  -- Seam 1 (`firstMessage ▷ …`, challenge seam; pure left verifier).
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
    (oracleReduction.firstMessage R pp oSpec).verifier
    ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            (prependRLCTargetWTKS pp oSpec))))).verifier
    verify₁ hV₁ hInit hInitNF hNE_B ⟨()⟩ (by omega)
    (composedTightPSpec_dir_seam pp (by omega)) (tightSfx2_dir_zero pp (by omega)) h₁ hS2

/-! ### The unconditional headline -/

/-- **Unconditional composed TIGHT rbr knowledge soundness for the Spartan chain (issue #329):
the `err₅ = 1` slot is eliminated.** From `spartanRelIn` to `tightRelG` (carried target = true
RLC, claims bound to the first-terminal identity), with per-round errors `0`
(message/adapter rounds), `ℓ_m/|R|` (`firstChallenge`, Schwartz–Zippel), `3/|R|` per
first-sum-check round, and **`1/|R|`** at `linearCombination` (Spartan Lemma 5.1's bound) —
where the old chain `composedRbrKnowledgeSoundnessPreserving_unconditional` was proven-forced
to carry error `1`. -/
theorem composedTightRbrKnowledgeSoundness_unconditional [Subsingleton σ]
    (hm : 0 < pp.ℓ_m)
    [Inhabited (Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    [Inhabited (Statement.AfterLinearCombinationWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i)) :
    (composedTightPIOP (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (tightRelG (R := R) pp)
      (composedTightRbrError pp
        (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) := by
  have h₂ : (oracleReduction.firstChallenge.{0} R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstMessageRbrRelB (R := R) pp)
      (firstSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
      (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0)) := by
    rw [firstSumcheckWithTargetRbrRelIn_eq_relIn]
    exact firstChallenge_rbrKnowledgeSoundness_schwartzZippel pp oSpec hm
  exact composedTightPIOP_rbrKnowledgeSoundness_of_leaves.{0} pp oSpec hm
    (firstMessage_rbrKnowledgeSoundness_spartanRelIn pp oSpec)
    h₂
    (firstSumcheckWithTarget_rbrKnowledgeSoundness_honest_full pp oSpec hInit hInitNF)
    (sendEvalClaimWithTarget_rbrKnowledgeSoundness_leaf pp oSpec)
    (linearCombinationWithTarget_rbrKnowledgeSoundness_leaf.{0} pp oSpec)
    (prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf pp oSpec)
    hInit hInitNF hNE_B hNE_C hNE_E

/-! ### The no-`1`-slot certificate -/

/-- **No `1`-slots.** Every per-round error of the headline error vector is at most
`max(ℓ_m, 3)/|R|` — in particular, strictly below `1` whenever `|R| > max(ℓ_m, 3)`. This is the
quantitative form of "the `err₅ = 1` slot is eliminated". -/
theorem composedTightRbrError_unconditional_le
    (i : (composedTightPSpec (R := R) pp).ChallengeIdx) :
    composedTightRbrError pp
        (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0) i
      ≤ ((pp.ℓ_m : ℝ≥0) ⊔ 3) / (Fintype.card R : ℝ≥0) := by
  unfold composedTightRbrError
  simp only [Function.comp_apply]
  rcases ChallengeIdx.sumEquiv.symm i with j₁ | i₁
  · simp only [Sum.elim_inl, Pi.zero_apply]
    exact zero_le _
  · simp only [Sum.elim_inr, Function.comp_apply]
    rcases ChallengeIdx.sumEquiv.symm i₁ with j₂ | i₂
    · simp only [Sum.elim_inl]
      gcongr
      exact le_sup_left
    · simp only [Sum.elim_inr, Function.comp_apply]
      rcases ChallengeIdx.sumEquiv.symm i₂ with j₃ | i₃
      · simp only [Sum.elim_inl]
        gcongr
        exact le_sup_right
      · simp only [Sum.elim_inr, Function.comp_apply]
        rcases ChallengeIdx.sumEquiv.symm i₃ with j₄ | i₄
        · simp only [Sum.elim_inl, Pi.zero_apply]
          exact zero_le _
        · simp only [Sum.elim_inr, Function.comp_apply]
          rcases ChallengeIdx.sumEquiv.symm i₄ with j₅ | i₅
          · simp only [Sum.elim_inl]
            gcongr
            exact le_trans (by norm_num) (le_sup_right (a := (pp.ℓ_m : ℝ≥0)) (b := (3 : ℝ≥0)))
          · exact Fin.elim0 i₅.1

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedTightPIOP
#print axioms Spartan.Spec.Bricks.firstSumcheckWithTargetRbrRelIn_eq_relIn
#print axioms Spartan.Spec.Bricks.firstSumcheckWithTarget_toVerifier_isFailingDet
#print axioms Spartan.Spec.Bricks.composedTightPIOP_rbrKnowledgeSoundness_of_leaves
#print axioms Spartan.Spec.Bricks.composedTightRbrKnowledgeSoundness_unconditional
#print axioms Spartan.Spec.Bricks.composedTightRbrError_unconditional_le
