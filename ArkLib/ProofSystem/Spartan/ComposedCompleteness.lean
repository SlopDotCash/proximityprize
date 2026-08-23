/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeamChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges2
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype
import ArkLib.ProofSystem.Sumcheck.Spec.Completeness
import ArkLib.ProofSystem.Spartan.Composition
import ArkLib.ProofSystem.Spartan.FirstSumcheckBridgeFree
import ArkLib.ProofSystem.Spartan.SecondSumcheckBridgeFree

/-!
# #114 Spartan composed perfect completeness — frontier work (worktree-only; candidate for landing).

All declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`), zero `sorry`:

1. `Reduction.challenge_hStage2Bridge_perfect_114` — discharges the last per-phase bridge
   (`hStage2Bridge`, perfect case) of the challenge-seam append completeness.
2. `Reduction.append_perfectCompleteness_challenge_114` — Reduction-level challenge-seam append
   perfect completeness, UNCONDITIONAL (V_to_P analogue of `append_perfectCompleteness_message`).
3. `OracleReduction.append_perfectCompleteness_keystone_challenge_114` — oracle-level lift, the
   challenge-seam analogue of `append_perfectCompleteness_keystone`.
4. `OracleReduction.append_perfectCompleteness_keystone_empty_114` — oracle-level empty-seam
   keystone (`n = 0` trailing block).
5. `Spartan.Spec.Bricks` seam-direction lemmas + challenge-family `Fintype`/`Inhabited` chains
   for the composed Spartan spec (`sfx6 … sfx1`, `composedPSpec`).
6. `Spartan.Spec.Bricks.composedPIOP_Rc_perfectCompleteness_of_leaves` — the **8-fold composed-PC
   assembly** over all seven seams of `composedPIOP_Rc` (2 challenge + 4 message + 1 empty),
   reducing composed perfect completeness to the eight leaf perfect completenesses.
7. `Spartan.Spec.Bricks.composedCompletenessStatement_of_leaves` — the official `SpartanBricks`
   composed-completeness residual, from the leaf PCs.
8. `Spartan.Spec.Bricks.composedCompletenessStatement_of_five_leaves` — sharpened: `firstMessage`
   (SendSingleWitness) + both sum-checks (bridge-free) discharged; **five** named leaf obligations
   remain (`firstChallenge` [in-tree proof exists, module build-broken], `sendEvalClaim`,
   `linearCombination`, `prependRLCTarget`-honest-target [the genuine gap], `finalCheck`).
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 800000 in
/-- **Challenge-seam `hStage2Bridge` discharge (perfect case).** From a phase-1 success `a` (whose
intermediate pair lies in `rel₂` by `hgood`), the phase-2 stage game's bad event from the
state-preserved seed `s'` is dominated by `R₂`'s own completeness-game bad event — because, `R₂`
being *perfectly* complete, the latter is `0`, and the per-seed game from any `s' ∈ support init`
(which `s'` is, by state preservation through stage 1) contributes `0` to that zero average. -/
theorem challenge_hStage2Bridge_perfect_114
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (stmt : Stmt₁) (wit : Wit₁) (_hmem : (stmt, wit) ∈ rel₁)
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) (s' : σ)
    (hsupp : (some a, s') ∈ support
      (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
    (hgood : goodOf m pSpec₁ rel₂ a) :
    Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
        | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _))]
      ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
          | gameOf init impl R₂ a.2 a.1.2.2] := by
  obtain ⟨hrel₂, hag⟩ := hgood
  rw [appendStage₂_run_eq_liftM R₁ R₂ a hag]
  -- `R₂`'s completeness game has bad probability `0` (perfect completeness).
  have hRHS : Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
      | gameOf init impl R₂ a.2 a.1.2.2] = 0 := by
    refine le_antisymm ?_ (zero_le _)
    have hbad₂ := bad_le_of_optionT_mk_ge (gameOf init impl R₂ a.2 a.1.2.2)
      (goodOf n pSpec₂ rel₃) ((0 : ℝ≥0) : ℝ≥0∞) (h₂ a.2 a.1.2.2 hrel₂)
    simpa using hbad₂
  -- hence every output in its support is good (no `none`, and successes satisfy `goodOf rel₃`).
  have hAllGood : ∀ o ∈ support (gameOf init impl R₂ a.2 a.1.2.2),
      Option.elim o False (goodOf n pSpec₂ rel₃ ·) := by
    rw [probEvent_eq_zero_iff] at hRHS
    exact fun o ho => not_not.mp (hRHS o ho)
  -- `s' ∈ support init`: state preservation through the simulated stage-1 run.
  have hs' : s' ∈ support init := by
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hsupp
    obtain ⟨s₀, hs₀, hmem₁⟩ := hsupp
    have hpres := simulateQ_state_preserving _ (addLift_state_preserving impl himplSP)
      (OptionT.run (appendStage₁ R₁ R₂ stmt wit)) s₀ (some a, s') hmem₁
    simpa [show s' = s₀ from hpres] using hs₀
  -- It suffices to show the per-seed stage-2 bad probability vanishes.
  rw [hRHS]
  refine le_of_eq ?_
  -- Transfer the combined-challenge-oracle simulated run to `pSpec₂`'s own oracle.
  have hED := OracleReduction.evalDist_run'_challengeSeam_right (pSpec₁ := pSpec₁) impl
    (OptionT.run
      ((fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
          ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) <$>
        (R₂.run a.2 a.1.2.2 : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _))) s'
  simp only [probEvent]
  rw [hED]
  -- Push the transcript-merge post-map out of the simulated run.
  rw [OptionT.run_map, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [show ((𝒟[_]).run.toOuterMeasure _ = 0) = (Pr[fun o => ¬ Option.elim o False
        (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
      | (fun (p : Option ((FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃) × σ) =>
            Option.map (fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
              ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) p.1) <$>
          StateT.run (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (R₂.run a.2 a.1.2.2))) s'] = 0) from rfl]
  rw [probEvent_map, probEvent_eq_zero_iff]
  rintro ⟨o, so⟩ hx
  -- The value marginal lies in the support of `R₂`'s own per-seed game, hence of `gameOf R₂`.
  have ho : o ∈ support (gameOf init impl R₂ a.2 a.1.2.2) := by
    simp only [gameOf, support_bind, Set.mem_iUnion, exists_prop]
    refine ⟨s', hs', ?_⟩
    rw [StateT.run'_eq, support_map]
    exact ⟨(o, so), hx, rfl⟩
  have hgood₂ := hAllGood o ho
  cases o with
  | none => exact absurd hgood₂ id
  | some r =>
    simp only [Function.comp_apply, Option.map_some, Option.elim_some, not_not]
    exact ⟨hgood₂.1, hgood₂.2⟩

/-- **Challenge-seam append perfect completeness (Reduction level), UNCONDITIONAL.** The `V_to_P`
seam analogue of `append_perfectCompleteness_message`: from the two component perfect
completenesses and the challenge-seam directions, via the proven challenge-seam keystone
`append_completeness_challenge_via_seamFactor` at zero error, with all three per-phase residuals
(`hStage1Bridge`/`hStage2Bridge`/`hTot`) discharged. -/
theorem append_perfectCompleteness_challenge_114
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  have h := append_completeness_challenge_via_seamFactor R₁ R₂ (e₁ := 0) (e₂ := 0)
    h₁ h₂ hn hDir hDir₂ himplSP himplNF
    (fun stmt wit _ => challenge_hStage1Bridge R₁ R₂ stmt wit)
    (fun stmt wit hmem a s' hsupp hgood =>
      challenge_hStage2Bridge_perfect_114 R₁ R₂ h₂ himplSP stmt wit hmem a s' hsupp hgood)
    (fun stmt wit _ => challenge_hTot R₁ R₂ himplNF hInit stmt wit)
  show R₁.append R₂ |>.completeness init impl rel₁ rel₃ 0
  simpa using h

end Reduction

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (challenge seam).** The `V_to_P`
analogue of `append_perfectCompleteness_keystone`: perfect completeness of `R₁.append R₂` from the
component perfect-completenesses and the challenge-seam direction facts, with the verifier-fusion
residual discharged internally (`appendToReductionResidual_proof`) and the prover-side reorder by
the proven simulated seam-challenge swap. Hypotheses: `NeverFail init` + state-preserving /
never-failing `impl` (both vacuous for `oSpec = []ₒ`). -/
theorem append_perfectCompleteness_keystone_challenge_114
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_challenge_114 R₁.toReduction R₂.toReduction
    h₁ h₂ hn hDir hDir₂ hInit himplSP himplNF

end OracleReduction

/-! ## Oracle-level empty-seam keystone (right operand has zero rounds)

The `n = 0` analogue of `append_perfectCompleteness_keystone` (message seam) and
`append_perfectCompleteness_keystone_challenge_114` (challenge seam): the trailing oracle reduction
is over the empty protocol `!p[]`, so no seam-direction facts are needed. Routes the proven
`Reduction.append_perfectCompleteness_empty_proof` through the discharged verifier-fusion bridge
`appendToReductionResidual_proof`. -/

namespace OracleReduction

section EmptyKeystone

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (empty trailing seam).** -/
theorem append_perfectCompleteness_keystone_empty_114
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_empty_proof R₁.toReduction R₂.toReduction
    h₁ h₂ hInit hImplSupp

end EmptyKeystone

end OracleReduction

/-! ## Spartan composed-completeness assembly (#114)

Seam-direction facts and challenge-family `Fintype`/`Inhabited` instances for the composed
Spartan PIOP `composedPIOP_Rc` (right-associated 8-leaf `append` fold), feeding the three
keystones (message / challenge / empty) at the seven seams. -/

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

open Sumcheck.Spec.SingleRound (appendChalFintype appendChalInhab chalBaseFintypeP
  chalBaseFintypeV chalBaseFintypeE chalBaseInhabP chalBaseInhabV chalBaseInhabE)

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-- The honest RLC-target adapter pinned to the concrete oracle-interface universe used by the
current append-completeness keystones. -/
private abbrev prependRLCTargetPC {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTarget pp oSpec

/-! ### Direction facts -/

/-- Positivity of two-step round counts. -/
private theorem vsum_two_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

/-- The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message. -/
private theorem sumcheckPSpec_dir_zero (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

/-- `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message). -/
private theorem sfx6_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) :
    (sfx6 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 2 pp.ℓ_n hv

/-- `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the
`prependRLCTarget ▷ …` append, whose combined spec is literally `sfx5` at seam index `0`.) -/
private theorem sfx5_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) :
    (sfx5 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have h6 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0 := by omega
  rw [show (⟨0, h⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))
      = Fin.natAdd 0 (⟨0, h6⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx6_dir_zero pp hn h6

/-- `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge). -/
private theorem sfx4_dir_zero
    (h : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the
seam index `1` is `P_to_V`. -/
private theorem sfx4_dir_seam (hn : 0 < pp.ℓ_n)
    (h : 1 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h5 : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx5_dir_zero pp hn h5

/-- `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message). -/
private theorem sfx3_dir_zero
    (h : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam
index `1` is `V_to_P` (the linear-combination challenge). -/
private theorem sfx3_dir_seam
    (h : 1 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h4 : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.natAdd 1 (⟨0, h4⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx4_dir_zero pp h4

/-- `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message). -/
private theorem sfx2_dir_zero (hm : 0 < pp.ℓ_m)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_pos hm
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 3 pp.ℓ_m hv

/-- Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam
index `vsum 2` is `P_to_V` (the bundled eval-claim message). -/
private theorem sfx2_dir_seam
    (h : Fin.vsum (fun _ : Fin pp.ℓ_m => 2) < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ = .P_to_V := by
  have h3 : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) := by omega
  rw [show (⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.natAdd (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))
          (⟨0, h3⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx3_dir_zero pp h3

/-- `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`. -/
private theorem sfx1_dir_zero
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam
index `1` is `P_to_V` (the first sum-check's leading message). -/
private theorem sfx1_dir_seam (hm : 0 < pp.ℓ_m)
    (h : 1 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h2 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.natAdd 1 (⟨0, h2⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx2_dir_zero pp hm h2

/-- Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the
seam index `1` is `V_to_P` (the first challenge). -/
private theorem composedPSpec_dir_seam
    (h : 1 < 1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) :
    (composedPSpec (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h1 : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))))
      = Fin.natAdd 1 (⟨0, h1⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx1_dir_zero pp h1

/-! ### Challenge-family `Fintype`/`Inhabited` instances, bottom-up -/

/-- Per-round challenge finiteness for the degree-`deg` sum-check round spec. -/
@[reducible] def sumcheckChalF (deg n : ℕ) :
    ∀ j, Fintype ((Sumcheck.Spec.pSpec R deg n).Challenge j) :=
  @ProtocolSpec.seqComposeChallenge_fintype n (fun _ => 2)
    (fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
    (fun _ => Sumcheck.Spec.SingleRound.chalFintype)

@[reducible] def sumcheckChalI (deg n : ℕ) :
    ∀ j, Inhabited ((Sumcheck.Spec.pSpec R deg n).Challenge j) :=
  @ProtocolSpec.seqComposeChallenge_inhabited n (fun _ => 2)
    (fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
    (fun _ => Sumcheck.Spec.SingleRound.chalInhab)

@[reducible] def c6F : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) :=
  appendChalFintype _ _ (sumcheckChalF 2 pp.ℓ_n) chalBaseFintypeE
@[reducible] def c6I : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) :=
  appendChalInhab _ _ (sumcheckChalI 2 pp.ℓ_n) chalBaseInhabE

@[reducible] def c5F : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) :=
  appendChalFintype _ _ chalBaseFintypeE (c6F pp)
@[reducible] def c5I : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) :=
  appendChalInhab _ _ chalBaseInhabE (c6I pp)

@[reducible] def c4F : ∀ j, Fintype ((sfx4 (R := R) pp).Challenge j) :=
  appendChalFintype _ _ chalBaseFintypeV (c5F pp)
@[reducible] def c4I : ∀ j, Inhabited ((sfx4 (R := R) pp).Challenge j) :=
  appendChalInhab _ _ chalBaseInhabV (c5I pp)

@[reducible] def c3F : ∀ j, Fintype ((sfx3 (R := R) pp).Challenge j) :=
  appendChalFintype _ _ chalBaseFintypeP (c4F pp)
@[reducible] def c3I : ∀ j, Inhabited ((sfx3 (R := R) pp).Challenge j) :=
  appendChalInhab _ _ chalBaseInhabP (c4I pp)

@[reducible] def c2F : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) :=
  appendChalFintype _ _ (sumcheckChalF 3 pp.ℓ_m) (c3F pp)
@[reducible] def c2I : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) :=
  appendChalInhab _ _ (sumcheckChalI 3 pp.ℓ_m) (c3I pp)

@[reducible] def c1F : ∀ j, Fintype ((sfx1 (R := R) pp).Challenge j) :=
  appendChalFintype _ _ chalBaseFintypeV (c2F pp)
@[reducible] def c1I : ∀ j, Inhabited ((sfx1 (R := R) pp).Challenge j) :=
  appendChalInhab _ _ chalBaseInhabV (c2I pp)

@[reducible] def c0F : ∀ j, Fintype ((composedPSpec (R := R) pp).Challenge j) :=
  appendChalFintype _ _ chalBaseFintypeP (c1F pp)
@[reducible] def c0I : ∀ j, Inhabited ((composedPSpec (R := R) pp).Challenge j) :=
  appendChalInhab _ _ chalBaseInhabP (c1I pp)

/-! ### The seven-seam assembly -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relA : Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relC : Set ((Statement.AfterFirstChallenge R pp ×
    ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)}
  {relD : Set ((Statement.AfterFirstSumcheck R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)}
  {relE : Set ((Statement.AfterSendEvalClaim R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relF : Set ((Statement.AfterLinearCombination R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relG : Set (((R × Statement.AfterLinearCombination R pp) ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relH : Set ((FinalStatement R pp × ∀ i, FinalOracleStatement R pp i) × Unit)}
  {relI : Set ((FinalStatement R pp × ∀ i, FinalOracleStatement R pp i) × Unit)}

/-- Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam). -/
private theorem step8
    (h₇ : (secondSumcheckReduction pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheck R pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec)).perfectCompleteness
      init impl relG relI := by
  haveI : ∀ j, Fintype ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge j) := sumcheckChalF 2 pp.ℓ_n
  haveI : ∀ j, Inhabited ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge j) := sumcheckChalI 2 pp.ℓ_n
  haveI : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) := c6F pp
  haveI : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) := c6I pp
  haveI := ProtocolSpec.challengeOracle_fintype (Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
  haveI := ProtocolSpec.challengeOracle_inhabited (Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
  haveI := ProtocolSpec.challengeOracle_fintype
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_inhabited
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone_empty_114
    (secondSumcheckReduction pp oSpec) (finalCheck R pp oSpec) h₇ h₈ hInit hImplSupp

/-- Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter). -/
private theorem step7 (hn : 0 < pp.ℓ_n)
    (h₆ : (prependRLCTargetPC pp oSpec).perfectCompleteness init impl relF relG)
    (hRest : ((secondSumcheckReduction pp oSpec).append
      (finalCheck R pp oSpec)).perfectCompleteness init impl relG relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((prependRLCTargetPC pp oSpec).append ((secondSumcheckReduction pp oSpec).append
      (finalCheck R pp oSpec))).perfectCompleteness init impl relF relI := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  haveI : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) := c6F pp
  haveI : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) := c6I pp
  haveI : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) := c5F pp
  haveI : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) := c5I pp
  haveI := ProtocolSpec.challengeOracle_fintype (sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype ((!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited ((!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone
    (prependRLCTargetPC pp oSpec)
    ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec))
    h₆ hRest (by omega) (sfx5_dir_zero pp hn (by omega)) (sfx6_dir_zero pp hn (by omega))
    hInit hImplSupp

/-- Seam 5 (`linearCombination ▷ …`, message seam: the right block opens with the second
sum-check's leading message through the 0-round adapter). -/
private theorem step6 (hn : 0 < pp.ℓ_n)
    (h₅ : (oracleReduction.linearCombination R pp oSpec).perfectCompleteness init impl relE relF)
    (hRest : ((prependRLCTargetPC pp oSpec).append ((secondSumcheckReduction pp oSpec).append
      (finalCheck R pp oSpec))).perfectCompleteness init impl relF relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
      ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec)))).perfectCompleteness
      init impl relE relI := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  haveI : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) := c5F pp
  haveI : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) := c5I pp
  haveI : ∀ j, Fintype ((sfx4 (R := R) pp).Challenge j) := c4F pp
  haveI : ∀ j, Inhabited ((sfx4 (R := R) pp).Challenge j) := c4I pp
  haveI : ∀ j, Fintype
      ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseFintypeV
  haveI : ∀ j, Inhabited
      ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseInhabV
  haveI := ProtocolSpec.challengeOracle_fintype (sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
  exact OracleReduction.append_perfectCompleteness_keystone
    (oracleReduction.linearCombination R pp oSpec)
    ((prependRLCTargetPC pp oSpec).append
      ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec)))
    h₅ hRest (by omega) (sfx4_dir_seam pp hn (by omega)) (sfx5_dir_zero pp hn (by omega))
    hInit hImplSupp

/-- Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam: the right block opens with the
linear-combination `V_to_P` challenge). -/
private theorem step5
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).perfectCompleteness init impl relD relE)
    (hRest : ((oracleReduction.linearCombination R pp oSpec).append
      ((prependRLCTargetPC pp oSpec).append ((secondSumcheckReduction pp oSpec).append
        (finalCheck R pp oSpec)))).perfectCompleteness init impl relE relI)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    ((oracleReduction.sendEvalClaim R pp oSpec).append
      ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
        ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec))))).perfectCompleteness init impl relD relI := by
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (oracleReduction.sendEvalClaim R pp oSpec)
    ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
      ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec))))
    h₄ hRest (by omega) (sfx3_dir_seam pp (by omega)) (sfx4_dir_zero pp (by omega))
    hInit himplSP himplNF

/-- Seam 3 (`firstSumcheck ▷ …`, message seam: the right block opens with the bundled
eval-claim `P_to_V` message). -/
private theorem step4
    (h₃ : (firstSumcheckReduction pp oSpec).perfectCompleteness init impl relC relD)
    (hRest : ((oracleReduction.sendEvalClaim R pp oSpec).append
      ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
        ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec))))).perfectCompleteness init impl relD relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((firstSumcheckReduction pp oSpec).append ((oracleReduction.sendEvalClaim R pp oSpec).append
      ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
        ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec)))))).perfectCompleteness init impl relC relI := by
  haveI : ∀ j, Fintype ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge j) := sumcheckChalF 3 pp.ℓ_m
  haveI : ∀ j, Inhabited ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge j) := sumcheckChalI 3 pp.ℓ_m
  haveI : ∀ j, Fintype ((sfx3 (R := R) pp).Challenge j) := c3F pp
  haveI : ∀ j, Inhabited ((sfx3 (R := R) pp).Challenge j) := c3I pp
  haveI : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) := c2F pp
  haveI : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) := c2I pp
  haveI := ProtocolSpec.challengeOracle_fintype (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
  haveI := ProtocolSpec.challengeOracle_inhabited (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
  haveI := ProtocolSpec.challengeOracle_fintype (sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp)
  exact OracleReduction.append_perfectCompleteness_keystone
    (firstSumcheckReduction pp oSpec)
    ((oracleReduction.sendEvalClaim R pp oSpec).append
      ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
        ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec)))))
    h₃ hRest (by omega) (sfx2_dir_seam pp (by omega)) (sfx3_dir_zero pp (by omega))
    hInit hImplSupp

/-- Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the first
sum-check's leading `P_to_V` polynomial message). -/
private theorem step3 (hm : 0 < pp.ℓ_m)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (hRest : ((firstSumcheckReduction pp oSpec).append
      ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
          ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec)))))).perfectCompleteness init impl relC relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((oracleReduction.firstChallenge R pp oSpec).append ((firstSumcheckReduction pp oSpec).append
      ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
          ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec))))))).perfectCompleteness init impl relB relI := by
  haveI : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) := c2F pp
  haveI : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) := c2I pp
  haveI : ∀ j, Fintype ((sfx1 (R := R) pp).Challenge j) := c1F pp
  haveI : ∀ j, Inhabited ((sfx1 (R := R) pp).Challenge j) := c1I pp
  haveI : ∀ j, Fintype
      ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseFintypeV
  haveI : ∀ j, Inhabited
      ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseInhabV
  haveI := ProtocolSpec.challengeOracle_fintype (sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp)
  exact OracleReduction.append_perfectCompleteness_keystone
    (oracleReduction.firstChallenge R pp oSpec)
    ((firstSumcheckReduction pp oSpec).append
      ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
          ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec))))))
    h₂ hRest (by omega) (sfx1_dir_seam pp hm (by omega)) (sfx2_dir_zero pp hm (by omega))
    hInit hImplSupp

/-- **Composed Spartan PIOP perfect completeness, reduced to the eight leaf
perfect-completenesses** (issue #114). Seam 1 (`firstMessage ▷ …`) is a **challenge** seam,
closed by the challenge-seam keystone; the other six seams are handled inside the `step*`
lemmas (message / challenge / empty keystones as dictated by each right block's opening
direction). -/
theorem composedPIOP_Rc_perfectCompleteness_of_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl relA relB)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (h₃ : (firstSumcheckReduction pp oSpec).perfectCompleteness init impl relC relD)
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).perfectCompleteness init impl relD relE)
    (h₅ : (oracleReduction.linearCombination R pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetPC pp oSpec).perfectCompleteness init impl relF relG)
    (h₇ : (secondSumcheckReduction pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheck R pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOP_Rc (R := R) pp oSpec).perfectCompleteness init impl relA relI := by
  have hS8 := step8 pp oSpec h₇ h₈ hInit hImplSupp
  have hS7 := step7 pp oSpec hn h₆ hS8 hInit hImplSupp
  have hS6 := step6 pp oSpec hn h₅ hS7 hInit hImplSupp
  have hS5 := step5 pp oSpec h₄ hS6 hInit himplSP himplNF
  have hS4 := step4 pp oSpec h₃ hS5 hInit hImplSupp
  have hS3 := step3 pp oSpec hm h₂ hS4 hInit hImplSupp
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (oracleReduction.firstMessage R pp oSpec)
    ((oracleReduction.firstChallenge R pp oSpec).append ((firstSumcheckReduction pp oSpec).append
      ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append ((prependRLCTargetPC pp oSpec).append
          ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec)))))))
    h₁ hS3 (by omega) (composedPSpec_dir_seam pp (by omega)) (sfx1_dir_zero pp (by omega))
    hInit himplSP himplNF

/-- **`composedCompletenessStatement` reduced to the eight leaf perfect-completenesses**:
the official composed-completeness obligation of `SpartanBricks`, with input relation
`spartanRelIn` and output relation `finalCheckRelOut`, holds as soon as the eight phases are
perfectly complete along *any* chain of intermediate relations. -/
theorem composedCompletenessStatement_of_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl
      (spartanRelIn R pp) relB)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (h₃ : (firstSumcheckReduction pp oSpec).perfectCompleteness init impl relC relD)
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).perfectCompleteness init impl relD relE)
    (h₅ : (oracleReduction.linearCombination R pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetPC pp oSpec).perfectCompleteness init impl relF relG)
    (h₇ : (secondSumcheckReduction pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheck R pp oSpec).perfectCompleteness init impl relH (finalCheckRelOut R pp))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessStatement R pp oSpec (composedPIOP_Rc pp oSpec) init impl :=
  composedPIOP_Rc_perfectCompleteness_of_leaves pp oSpec hm hn
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hInit hImplSupp himplSP himplNF

/-- Honest output relation of the `firstMessage` phase: `spartanRelIn` with the witness moved
into the appended oracle slot. Definitionally `SendSingleWitness.toORelOut (spartanRelIn R pp)`,
restated over Spartan's `Sum.rec`-shaped oracle family (`OracleStatement.AfterFirstMessage`) so
elaboration uses the in-tree `⊕ᵥ` `OracleInterface` instances (the `Sum.elim` form of
`toORelOut`'s signature does not key the instance). -/
def firstMessageRelOut :
    Set ((Statement.AfterFirstMessage R pp ×
        ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit) :=
  setOf (fun x =>
    ((x.1.1, fun i => x.1.2 (Sum.inl i)), x.1.2 (Sum.inr 0)) ∈ spartanRelIn R pp)

/-- **Sharpened residual: three of the eight leaves discharged.** `firstMessage`
(`SendSingleWitness.oracleReduction_completeness`), `firstSumcheck` and `secondSumcheck`
(the bridge-free unconditional transfers) are machine-checked; the remaining **five** leaf
obligations are taken as named hypotheses, with the intermediate relations pinned to the
concrete in-tree chain (`firstMessageRelOut` → `firstSumcheckRelInBF` →
`firstSumcheckRelOutBF` → … → `secondSumcheckRelInBF` → `secondSumcheckRelOutBF`):

* `h₂` — `firstChallenge` (an in-tree proof `firstChallenge_perfectCompleteness` exists but its
  module `FirstChallengeComplete.lean` is currently build-broken on `main`, pre-existing);
* `h₄`/`h₅` — `sendEvalClaim` / `linearCombination` (pure forwarding phases, unproven);
* `h₆` — `prependRLCTarget` into `secondSumcheckRelInBF`: **the honest-target obligation**. The
  existence-only adapter emits target `0`, while `secondSumcheckRelInBF` pins the target to the
  honest linear-combination value, so this hypothesis demands the honest-target adapter (or a
  `relF` strengthening) — the known genuine remaining gap of #114's completeness layer;
* `h₈` — `finalCheck` (`CheckClaim` completeness into `finalCheckRelOut`). -/
theorem composedCompletenessStatement_of_five_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckRelInBF (R := R) pp))
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelOutBF (R := R) pp) relE)
    (h₅ : (oracleReduction.linearCombination R pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetPC pp oSpec).perfectCompleteness init impl relF
      (secondSumcheckRelInBF (R := R) pp))
    (h₈ : (finalCheck R pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelOutBF (R := R) pp) (finalCheckRelOut R pp))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessStatement R pp oSpec (composedPIOP_Rc pp oSpec) init impl :=
  composedCompletenessStatement_of_leaves pp oSpec hm hn
    (SendSingleWitness.oracleReduction_completeness (oSpec := oSpec)
      (Statement := Statement R pp) (OStatement := OracleStatement R pp)
      (Witness := Witness R pp) (init := init) (impl := impl)
      (oRelIn := spartanRelIn R pp) hInit)
    h₂
    (firstSumcheck_perfectCompleteness_bridgeFree pp oSpec hInit hImplSupp)
    h₄ h₅ h₆
    (secondSumcheck_perfectCompleteness_bridgeFree pp oSpec hInit hImplSupp)
    h₈ hInit hImplSupp himplSP himplNF

end

end Spartan.Spec.Bricks
