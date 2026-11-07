/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeamChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges2
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer

/-!
# Challenge-seam append perfect completeness

`append_perfectCompleteness_challenge`: the `V_to_P`-seam analogue of
`append_perfectCompleteness_message`. The message-seam proof factors the prover *syntactically*
(`Prover.append_run_msg`), which is **false** at a challenge seam; so we route through the proven
challenge-seam completeness keystone `append_completeness_challenge_via_seamFactor` specialized to
zero error, discharging its three per-phase challenge-oracle relabel residuals
(`hStage1Bridge`/`hStage2Bridge`/`hTot`) from the proven seam-transfer infrastructure
(`appendStageᵢ_run_eq_liftM` + `evalDist_run'_challengeSeam_left/right`).
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

-- These historical events observe all subsets of the complete optional transcript output.
private local instance (A : Type) : MeasurableSpace A := ⊤
private local instance (A B : Type) : MeasurableSpace (A × B) := ⊤
private local instance (A : Type) : MeasurableSpace (Option A) := ⊤
private local instance (A : Type) : @DiscreteMeasurableSpace A ⊤ := ⟨fun _ => True.intro⟩

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Challenge-seam `hStage1Bridge` discharge.** The phase-1 game over the *combined* challenge
oracle agrees (as `evalDist`) with `R₁`'s own phase-1 game: `appendStage₁_run_eq_liftM` rewrites the
stage to `liftM (R₁.run …)` over the combined oracle.
`evalDist_run'_challengeSeam_left` transfers
the combined run back to `pSpec₁`'s own challenge oracle. -/
theorem challenge_hStage1Bridge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    evalDist (Prod.fst <$> (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
      = evalDist (gameOf init impl R₁ stmt wit) := by
  rw [appendStage₁_run_eq_liftM, map_bind, gameOf,
    evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  congr 1
  funext s
  rw [← StateT.run'_eq]
  exact OracleReduction.evalDist_run'_challengeSeam_left impl ((R₁.run stmt wit).run) s


/-- **Challenge-seam `hTot` discharge.** The appended simulated honest game never *samples* a
failure: `init` never fails (`hInit`) and the simulated run never fails (`simulateQ_run_neverFail`
from the never-failing honest implementation `addLift_neverFail`). -/
theorem challenge_hTot
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (hInit : NeverFail init)
    (stmt : Stmt₁) (wit : Wit₁) :
    prFail (gameOf init impl (R₁.append R₂) stmt wit) = 0 := by
  exact OracleComp.prFail_eq_zero _

/-- The second-stage bad event is unchanged by transcript merging and the right oracle seam. -/
private theorem challenge_stage2_bad_eq
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂)
    (hag : a.1.2.1 = a.2) (s' : σ) :
    probEvent (fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·))
      ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (appendStage₂ R₁ R₂ a).run).run' s') =
    probEvent (fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·))
      ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (R₂.run a.2 a.1.2.2).run).run' s') := by
  rw [appendStage₂_run_eq_liftM R₁ R₂ a hag]
  have hEvent := (EvalDistEq.of_evalDist_eq
    (OracleReduction.evalDist_run'_challengeSeam_right (pSpec₁ := pSpec₁) impl
      ((fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
        ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) <$>
        R₂.run a.2 a.1.2.2).run s')).prEvent_eq
    (fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·))
  change probEvent _ _ = probEvent _ _ at hEvent
  rw [hEvent, OptionT.run_map, simulateQ_map, StateT.run'_map']
  simp only [probEvent, prEvent_map]
  congr 1
  congr 1
  funext o
  cases o <;> rfl

/-- **Challenge-seam `hStage2Bridge` discharge (perfect case).** For a perfectly-complete `R₂`, the
phase-2 stage bad event (over the *combined* challenge oracle, from a phase-1 success state `s'`) is
`0`, hence bounded by `R₂`'s own phase-2 game bad event. LHS = 0 by: `appendStage₂_run_eq_liftM`
(stage-2 = `liftM` of `merge ≫ R₂.run`), `evalDist_run'_challengeSeam_right` (combined → `pSpec₂`
transfer), `probEvent_map` collapsing `goodOf (m+n) ∘ merge = goodOf n` (the transcript merge is
invisible to `goodOf`), and the per-state extraction of `h₂`'s perfect completeness at `s' ∈ support
init` (state-preservation). -/
theorem challenge_hStage2Bridge_perfect
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (stmt : Stmt₁) (wit : Wit₁) (hmem : (stmt, wit) ∈ rel₁)
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) (s' : σ)
    (hsupp : (some a, s') ∈ support
      (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
    (hgood : goodOf m pSpec₁ rel₂ a) :
    probEvent (fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·))
      ((StateT.run' (simulateQ
        (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _)))
      ≤ probEvent (fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·))
          (gameOf init impl R₂ a.2 a.1.2.2) := by
  obtain ⟨hrel₂, hag⟩ := hgood
  rw [challenge_stage2_bad_eq R₁ R₂ a hag s']
  have hs' : s' ∈ support init := by
    rw [mem_support_bind_iff] at hsupp
    obtain ⟨s, hs, hmem'⟩ := hsupp
    have hsp := simulateQ_state_preserving (impl.addLift challengeQueryImpl)
      (addLift_state_preserving impl himplSP) (OptionT.run (appendStage₁ R₁ R₂ stmt wit)) s
      (some a, s') hmem'
    rw [show s' = s from hsp]
    exact hs
  have hg : probEvent (fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·))
      (gameOf init impl R₂ a.2 a.1.2.2) = 0 :=
    le_antisymm
      (bad_le_of_optionT_mk_ge (gameOf init impl R₂ a.2 a.1.2.2) (goodOf n pSpec₂ rel₃) 0
        (by
          have hc := h₂ a.2 a.1.2.2 hrel₂
          change probEvent (goodOf n pSpec₂ rel₃)
            (OptionT.mk (gameOf init impl R₂ a.2 a.1.2.2)) ≥ 1 - (0 : ℝ≥0∞) at hc
          exact hc)) zero_le
  rw [hg]
  apply le_of_eq
  apply prEvent_eq_zero_of_forall_mem_support
  intro o ho hbad
  apply (OracleComp.prEvent_eq_zero_iff _ _).mp hg o ?_ hbad
  exact (mem_support_bind_iff _ _ _).2 ⟨s', hs', ho⟩


/-- **General (error-ful) stage-2 bad-event bridge at a challenge seam.** Unlike
`challenge_hStage2Bridge_perfect` (which shortcuts through the RHS being `0` under a perfect
`h₂`), this needs no completeness at all: after the same distributional pushes, the stage-2
game from the reachable seed `s'` *equals* `R₂`'s completeness game — state-blind
implementations make the per-seed value distribution constant, and `NeverFail init` collapses
the init-mixture. Consumed by the error-ful `append_completeness_challenge` below. -/
theorem challenge_hStage2Bridge_general
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (stmt : Stmt₁) (wit : Wit₁) (hmem : (stmt, wit) ∈ rel₁)
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) (s' : σ)
    (hsupp : (some a, s') ∈ support
      (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
    (hgood : goodOf m pSpec₁ rel₂ a)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (hInit : NeverFail init) :
    probEvent (fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·))
      ((StateT.run' (simulateQ
        (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _)))
      ≤ probEvent (fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·))
          (gameOf init impl R₂ a.2 a.1.2.2) := by
  obtain ⟨_hrel₂, hag⟩ := hgood
  rw [challenge_stage2_bad_eq R₁ R₂ a hag s']
  have hEq : EvalDistEq (gameOf init impl R₂ a.2 a.1.2.2)
      (init >>= fun _ =>
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (R₂.run a.2 a.1.2.2).run).run' s') := by
    apply EvalDistEq.bind_right init
    intro s
    exact EvalDistEq.of_evalDist_eq
      (evalDist_simulateQ_run'_state_indep (impl.addLift challengeQueryImpl)
        (addLift_state_preserving impl himplSP)
        (addLift_value_blind impl himplVB) _ s s')
  have hEvent := hEq.prEvent_eq
    (fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·))
  change probEvent _ _ = probEvent _ _ at hEvent
  rw [hEvent]
  simp only [probEvent, map_bind]
  rw [OracleComp.prEvent_bind_const]


/-- **Challenge-seam append completeness (error-ful, unconditional).** From components complete
with errors `e₁`/`e₂`, the appended reduction is complete with error `e₁ + e₂` at a `V_to_P`
seam: the via-seamFactor engine with the three challenge bridges, the stage-2 one in its
general (`challenge_hStage2Bridge_general`) form. The error-ful analogue of
`append_perfectCompleteness_challenge` and the challenge twin of
`Reduction.append_completeness_msg`. -/
theorem append_completeness_challenge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (hInit : NeverFail init) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_challenge_via_seamFactor R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF
    (fun stmt wit _ => challenge_hStage1Bridge R₁ R₂ stmt wit)
    (fun stmt wit hmem a s' hsupp hgood =>
      challenge_hStage2Bridge_general R₁ R₂ himplSP stmt wit hmem a s' hsupp hgood
        himplVB hInit)
    (fun stmt wit _ => challenge_hTot R₁ R₂ himplNF hInit stmt wit)

/-- **Challenge-seam append perfect completeness.** The `V_to_P`-seam analogue of
`append_perfectCompleteness_message`: from perfectly-complete components `R₁`, `R₂`, the appended
reduction `R₁.append R₂` is perfectly complete. It uses
`append_completeness_challenge_via_seamFactor` at zero error, discharging its residuals with
`challenge_hStage1Bridge`, `challenge_hStage2Bridge_perfect` and `challenge_hTot`. -/
theorem append_perfectCompleteness_challenge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (hInit : NeverFail init) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  have key := append_completeness_challenge_via_seamFactor R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF
    (fun stmt wit _ => challenge_hStage1Bridge R₁ R₂ stmt wit)
    (fun stmt wit hmem a s' hsupp hgood =>
      challenge_hStage2Bridge_perfect R₁ R₂ h₂ himplSP stmt wit hmem a s' hsupp hgood)
    (fun stmt wit _ => challenge_hTot R₁ R₂ himplNF hInit stmt wit)
  simpa [perfectCompleteness] using key

end Reduction

-- Axiom audit (error-ful challenge additions): only [propext, Classical.choice, Quot.sound].
#print axioms Reduction.challenge_hStage2Bridge_general
#print axioms Reduction.append_completeness_challenge

#print axioms Reduction.challenge_hStage1Bridge
#print axioms Reduction.challenge_hTot
#print axioms Reduction.challenge_hStage2Bridge_perfect
#print axioms Reduction.append_perfectCompleteness_challenge
