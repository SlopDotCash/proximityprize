/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges2
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# Error-bearing message-seam append completeness — the keystone, fully discharged (issue #13)

`Reduction.append_completeness_msg_via_seamFactor` (`AppendChallengeSeam.lean`) proves the
**error-bearing** (non-perfect) message-seam append completeness modulo three residual hypotheses:
the two per-phase challenge-oracle seam relabels (`hStage1Bridge` / `hStage2Bridge`) and the game
totality (`hTot`). The two stage-body `liftM` factorings are proven in `AppendSeamBridges2.lean`
(`appendStage₁_run_eq_liftM` / `appendStage₂_run_eq_liftM`). This file discharges all three
residuals and assembles:

* `Reduction.appendStage1Bridge` — the `Prod.fst`-marginal of the state-threaded phase-1 stage game
  (run under the *combined* challenge oracle) has the same `evalDist` as the phase-1 completeness
  game `gameOf R₁` (run under `pSpec₁`'s own challenge oracle). Via `appendStage₁_run_eq_liftM` +
  the proven challenge-seam bridge `evalDist_run'_challengeSeam_left`.
* `Reduction.appendStage2Bridge` — for each phase-1 success, the phase-2 stage game's bad event
  equals the phase-2 completeness game's bad event: the transcript merge is invisible to the
  (transcript-blind) `goodOf` predicate, the challenge seam is relabelled by
  `evalDist_run'_challengeSeam_right`, and the seam state `s'` is reconciled with the `init`-average
  by state-independence (`evalDist_simulateQ_run'_state_indep`, using the value-blind side condition
  `himplVB` — the same side condition the proven soundness twin `append_soundness_msg` carries).
* `Reduction.append_completeness_msg` — **the keystone**: for a message seam, from
  `R₁.completeness … e₁` and `R₂.completeness … e₂` (plus the standard honest-`impl` side
  conditions), the appended reduction is complete with additive error `e₁ + e₂`. No residual
  hypothesis remains.
* `OracleReduction.append_completeness_msg` — the **oracle-level** keystone, transported along the
  proven verifier fusion `appendToReductionResidual_proof` (`AppendToVerifierKeystone.lean`). This
  is the exact shape of `OracleReduction.appendCompletenessResidual`, i.e. the completeness
  `hAppend` blocker of issue #13.

No `sorry`, no new axioms.
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

/-- **Phase-2 challenge-seam transfer at `probEvent`, `OracleComp` form.** Any event on a
`pSpec₂`-side computation `g`, lifted into the *combined* challenge oracle and simulated from state
`s'`, has the same probability as on `g` simulated under `pSpec₂`'s own challenge oracle. Immediate
from the proven `evalDist_run'_challengeSeam_right`. -/
private theorem probEvent_seam_transfer_right_oc {α : Type}
    (g : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) (P : α → Prop) (s' : σ) :
    Pr[P | (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM g : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s']
    = Pr[P | (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp)) g).run' s'] := by
  unfold probEvent
  rw [OracleReduction.evalDist_run'_challengeSeam_right impl g s']

/-- **Marginalization congruence for the `¬ Option.elim · False ·` (completeness bad-event) shape,
per-state.** Two `OptionT`-valued computations that agree after projecting through `g₁`/`g₂` give
the same bad-event probability for any event reading only the projection. The `¬`-shaped twin of
the soundness file's `marg_het_state`. -/
private theorem marg_het_state_neg {ιₛ : Type} {spec : OracleSpec ιₛ} {α₁ α₂ β : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (s' : σ)
    (X : OptionT (OracleComp spec) α₁) (Y : OptionT (OracleComp spec) α₂)
    (g₁ : α₁ → β) (g₂ : α₂ → β) (q : β → Prop) (h : (g₁ <$> X) = (g₂ <$> Y)) :
    Pr[fun o => ¬ Option.elim o False (fun a => q (g₁ a)) |
        (simulateQ so X.run).run' s']
    = Pr[fun o => ¬ Option.elim o False (fun a => q (g₂ a)) |
        (simulateQ so Y.run).run' s'] := by
  have h' : Option.map g₁ <$> X.run = Option.map g₂ <$> Y.run := by
    have := congrArg OptionT.run h; simpa only [OptionT.run_map] using this
  have h'' : (Option.map g₁ <$> simulateQ so X.run) = (Option.map g₂ <$> simulateQ so Y.run) := by
    rw [← simulateQ_map, ← simulateQ_map, h']
  have key : (Option.map g₁ <$> (simulateQ so X.run).run' s')
           = (Option.map g₂ <$> (simulateQ so Y.run).run' s') := by
    simp only [StateT.run'_eq]
    have h3 := congrFun (congrArg StateT.run h'') s'
    simp only [StateT.run_map] at h3
    have h4 := congrArg (fun z => Prod.fst <$> z) h3
    simp only [Functor.map_map, Function.comp_def] at h4 ⊢; exact h4
  have hpe1 : (fun o : Option α₁ => ¬ Option.elim o False (fun a => q (g₁ a)))
      = (fun ob => ¬ Option.elim ob False q) ∘ (Option.map g₁) := by funext o; cases o <;> rfl
  have hpe2 : (fun o : Option α₂ => ¬ Option.elim o False (fun a => q (g₂ a)))
      = (fun ob => ¬ Option.elim ob False q) ∘ (Option.map g₂) := by funext o; cases o <;> rfl
  rw [hpe1, hpe2, probEvent_comp, probEvent_comp, key]

/-- **The discharged `hStage1Bridge`.** The `Prod.fst`-marginal of the state-threaded phase-1 stage
game (combined challenge oracle) is distributionally the phase-1 completeness game `gameOf R₁`
(own challenge oracle). -/
theorem appendStage1Bridge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    evalDist (Prod.fst <$> (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
      = evalDist (gameOf init impl R₁ stmt wit) := by
  rw [appendStage₁_run_eq_liftM]
  show evalDist (Prod.fst <$> (init >>= fun s =>
      (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM ((R₁.run stmt wit).run) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)).run s))
    = evalDist (init >>= fun s =>
      (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
        QueryImpl _ (StateT σ ProbComp)) ((R₁.run stmt wit).run)).run' s)
  simp only [map_bind]
  rw [evalDist_bind, evalDist_bind]
  refine bind_congr fun s => ?_
  rw [← StateT.run'_eq]
  exact OracleReduction.evalDist_run'_challengeSeam_left impl (R₁.run stmt wit).run s

/-- **The discharged `hStage2Bridge`.** For a phase-1 success `a` (with the completeness agreement
`a.1.2.1 = a.2` from `goodOf`), the phase-2 stage game's bad event from the seam state `s'` is
*equal* to the phase-2 completeness game's bad event on the intermediate pair: the transcript merge
is invisible to `goodOf`, the challenge seam relabels distributionally, and state-independence
(value-blind `impl`) reconciles the pinned seam state with the `init` average. -/
theorem appendStage2Bridge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) (s' : σ)
    (hgood : goodOf m pSpec₁ rel₂ a) :
    Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
        | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _))]
      ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
        | gameOf init impl R₂ a.2 a.1.2.2] := by
  refine le_of_eq ?_
  rw [appendStage₂_run_eq_liftM R₁ R₂ a hgood.2]
  -- Step 1: challenge-seam relabel (combined → `pSpec₂`'s own oracle), from the seam state `s'`.
  rw [probEvent_seam_transfer_right_oc (pSpec₁ := pSpec₁)
    (OptionT.run ((fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
        ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) <$> R₂.run a.2 a.1.2.2))
    (fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)) s']
  -- Step 2: the transcript merge is invisible to the (transcript-blind) `goodOf` bad event.
  refine Eq.trans (marg_het_state_neg
    (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp)) s'
    ((fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
        ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) <$> R₂.run a.2 a.1.2.2)
    (R₂.run a.2 a.1.2.2)
    id (fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
        ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2))
    (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃) (by rw [id_map])) ?_
  -- Step 3: pinned seam state `s'` ↔ `init` average, by state-independence (value-blind `impl`).
  have hYpred : (fun o : Option ((FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃) =>
        ¬ Option.elim o False (fun r => goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃
          ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)))
      = (fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)) := by
    funext o; cases o <;> rfl
  rw [hYpred]
  have hstate : Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·) |
        init >>= fun s => (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s]
      = Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·) |
        init >>= fun _ => (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s'] := by
    have hed : evalDist (init >>= fun s => (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s)
        = evalDist (init >>= fun _ => (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s') := by
      rw [evalDist_bind, evalDist_bind]
      refine bind_congr fun s => ?_
      exact evalDist_simulateQ_run'_state_indep _ (addLift_state_preserving impl himplSP)
        (addLift_value_blind impl himplVB) _ s s'
    unfold probEvent
    rw [hed]
  have hconst : Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·) |
        init >>= fun _ => (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s']
      = Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·) |
        (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s'] := by
    rw [probEvent_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
  exact (hconst.symm.trans hstate.symm)

/-- **The discharged `hTot`.** The simulated appended honest game is a `ProbComp` and never
*samples* a failure (its only failure mode is the explicit `none` value, accounted in the bad
event). -/
theorem append_game_tot
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0 :=
  probFailure_eq_zero

/-- **The error-bearing message-seam append-completeness keystone — no residual hypothesis.**

For a message seam (`hDir`/`hDir₂`), from `R₁.completeness init impl rel₁ rel₂ e₁` and
`R₂.completeness init impl rel₂ rel₃ e₂` plus the three standard honest-`impl` side conditions
(state-preserving / never-failing / value-blind, the same triple as the proven soundness keystone
`append_soundness_msg`), the appended reduction is complete with additive error `e₁ + e₂`. -/
theorem append_completeness_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_msg_via_seamFactor R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF
    (fun stmt wit _ => appendStage1Bridge R₁ R₂ stmt wit)
    (fun _ _ _ a s' _ hgood => appendStage2Bridge R₁ R₂ himplSP himplVB a s' hgood)
    (fun stmt wit _ => append_game_tot R₁ R₂ stmt wit)

end Reduction

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level error-bearing append completeness — UNCONDITIONAL (message seam).**

Completeness (error `e₁ + e₂`) of `R₁.append R₂` for **oracle** reductions, from the two component
completenesses, the message-seam direction facts, and the honest-`impl` side conditions — with the
verifier-fusion bridge discharged internally (`appendToReductionResidual_proof`). This is exactly
the statement of `OracleReduction.appendCompletenessResidual`, i.e. the completeness `hAppend`
blocker of issue #13 (LogUp Protocol 2: `e₁ = logupCompletenessError`, `e₂ = 0`). -/
theorem append_completeness_msg
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) := by
  change Reduction.completeness init impl rel₁ rel₃ (R₁.append R₂).toReduction (e₁ + e₂)
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_completeness_msg R₁.toReduction R₂.toReduction h₁ h₂ hn hDir hDir₂
    himplSP himplNF himplVB

/-- **The named oracle-level append-completeness residual is a theorem (message seam).** The exact
`Prop` `OracleReduction.appendCompletenessResidual R₁ R₂ h₁ h₂` — the completeness `hAppend`
consumed throughout the LogUp issue-#13 assembly — discharged by the keystone. The `Oₛ₃` instance
is consumed only by the fusion bridge in the proof, so its `OracleInterface` output universe is a
free parameter of this theorem undetermined by the arguments — consumers with concrete (`Type 0`)
oracle interfaces should pin it explicitly (e.g. `.{0, 0}`). -/
theorem appendCompletenessResidual_msg
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    appendCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_completeness_msg R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

end OracleReduction

-- Axiom audit: the keystones must be axiom-clean (no `sorryAx`).
#print axioms Reduction.append_completeness_msg
#print axioms OracleReduction.append_completeness_msg
#print axioms OracleReduction.appendCompletenessResidual_msg
