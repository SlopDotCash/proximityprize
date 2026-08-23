/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeamChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessTotal
import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

/-!
# Error-ful append completeness at an empty trailing seam, and the full error-ful total

The last missing leg of the error-carrying seam-agnostic append completeness: the trailing
protocol is empty (`pSpec₂ : ProtocolSpec 0`). The game-factoring (`append_game_factor_empty`)
mirrors the challenge-seam one, but the seam commute is **syntactic** here: the appended
prover's run factors on the nose (`Prover.append_run` + `appendRunRightResidual_holds_empty`),
so no distributional reorder of the prover head is needed; the (direction-agnostic)
`seam_swap_evalDist_eq` then reorders `P₂` past `V₁` exactly as in the other seams. The three
via-seamFactor bridges (`challenge_hStage1Bridge`, `challenge_hStage2Bridge_general`,
`challenge_hTot`) are seam-direction-agnostic and are reused verbatim.

With this leg, `Reduction.append_completeness_total` (error-ful, fully seam-agnostic) discharges
the general error-carrying append residuals from `Append.lean`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  [∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 1000000 in
/-- **The simulated appended honest game factors at an empty trailing seam (`evalDist`-level).**
Mirror of `append_game_factor_challenge`: the appended prover run factors *syntactically*
(`Prover.append_run` from `appendRunRightResidual_holds_empty`), and the (direction-agnostic)
`seam_swap_evalDist_eq` reorders `P₂` past `V₁`. -/
theorem append_game_factor_empty
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    evalDist (gameOf init impl (R₁.append R₂) stmt wit)
      = evalDist (init >>= fun s =>
          StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            ((appendStage₁ R₁ R₂ stmt wit) >>= (appendStage₂ R₁ R₂)).run) s) := by
  have hswap := seam_swap_evalDist_eq
    (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) init
    (impl.addLift (challengeQueryImpl))
    (addLift_state_preserving impl himplSP)
    (liftM (R₁.prover.run stmt wit)) (fun x => liftM (R₂.prover.run x.2.1 x.2.2))
    (fun x => (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂))
    (fun x a s₂ => (MonadLift.monadLift (R₂.verifier.verify s₂ a.1) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
      pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃))
    (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
  simp only [gameOf, appendStage₁, appendStage₂]
  refine Eq.trans ?_ hswap
  simp only [gameOf]
  rw [evalDist_bind, evalDist_bind]
  refine bind_congr fun s => ?_
  rw [append_run_eq_seamChain R₁ R₂ stmt wit]
  -- The appended prover run factors SYNTACTICALLY at the empty seam.
  rw [Prover.append_run stmt wit
    (Prover.appendRunRightResidual_holds_empty (P₁ := R₁.prover) (P₂ := R₂.prover) stmt wit)]
  simp only [OptionT.run_bind, Option.elimM, lift_run_elim, OptionT.run_pure]
  refine congrArg (fun X => evalDist (StateT.run'
      (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s)) ?_
  simp only [bind_assoc, pure_bind, FullTranscript.append_fst, FullTranscript.append_snd]

end Reduction

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 2000000 in
/-- **Empty-trailing-seam append completeness with additive error.** The error-ful analogue of
`append_perfectCompleteness_empty_proof`: the via-seamFactor union-bound engine with the empty
game-factoring and the three (seam-direction-agnostic) bridges. Stated at generic `n` with an
`n = 0` hypothesis: instantiating the engine at the literal `ProtocolSpec 0` whnf-explodes, so
the substitution happens only inside the factoring leg. -/
theorem append_completeness_empty_err
    {n : ℕ} {pSpec₂' : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₂'.Challenge i)]
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn0 : n = 0)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (hInit : NeverFail init) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) := by
  refine append_completeness_msg_proof R₁ R₂ h₁ h₂
    (so := impl.addLift challengeQueryImpl)
    (mx := fun p => appendStage₁ R₁ R₂ p.1 p.2)
    (my := fun p => appendStage₂ R₁ R₂)
    ?_ ?_ ?_ ?_
  · subst hn0
    exact fun stmt wit _ => append_game_factor_empty R₁ R₂ stmt wit himplSP himplNF
  · exact fun stmt wit _ => challenge_hStage1Bridge R₁ R₂ stmt wit
  · exact fun stmt wit hmem a s' hsupp hgood =>
      challenge_hStage2Bridge_general R₁ R₂ himplSP stmt wit hmem a s' hsupp hgood
        himplVB hInit
  · exact fun stmt wit _ => challenge_hTot R₁ R₂ himplNF hInit stmt wit


set_option maxHeartbeats 2000000 in
/-- **Fully seam-agnostic append completeness with additive error.** Total case split:
empty trailing protocol (`append_completeness_empty_err`), else the message/challenge split
(`append_completeness_total_pos`). Discharges the general error-carrying append residual. -/
theorem append_completeness_total
    {n : ℕ} {pSpec₂' : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₂'.Challenge i)]
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact append_completeness_empty_err R₁ R₂ h₁ h₂ hn himplSP himplNF himplVB hInit
  · exact append_completeness_total_pos R₁ R₂ h₁ h₂ hn hInit himplSP himplNF himplVB

set_option maxHeartbeats 2000000 in
/-- **`reductionAppendCompletenessResidual` is DISCHARGED** (fully seam-agnostic, additive
error). -/
theorem reductionAppendCompletenessResidual_holds
    {n : ℕ} {pSpec₂' : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₂'.Challenge i)]
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    reductionAppendCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_completeness_total R₁ R₂ h₁ h₂ hInit himplSP himplNF himplVB

end Reduction

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Reduction.append_game_factor_empty
#print axioms Reduction.append_completeness_empty_err
#print axioms Reduction.append_completeness_total
#print axioms Reduction.reductionAppendCompletenessResidual_holds

namespace OracleReduction

open Reduction in
set_option maxHeartbeats 2000000 in
/-- **The oracle-level general `appendCompletenessResidual` is DISCHARGED** (seam-agnostic,
additive error): definitionally the `toReduction` statement, collapsed by the unconditional
verifier-fusion bridge and closed by the error-ful seam-agnostic total. -/
theorem appendCompletenessResidual_holds
    {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)] {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)] {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)] {Wit₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    appendCompletenessResidual R₁ R₂ h₁ h₂ := by
  unfold appendCompletenessResidual
  change Reduction.completeness init impl rel₁ rel₃ (R₁.append R₂).toReduction (e₁ + e₂)
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_completeness_total R₁.toReduction R₂.toReduction h₁ h₂
    hInit himplSP himplNF himplVB

end OracleReduction

#print axioms OracleReduction.appendCompletenessResidual_holds
