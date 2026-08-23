/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.ThresholdKSF

/-!
# The full-predicate KSF and the salvage-budget RBR theorem (#302/#301, hypothesis A5)

The **full-predicate knowledge state function**
and the salvage-budget RBR theorem — the corrected sub-unit shell. Unlike `thresholdKSF`
(whose state becomes `True` past the threshold, making the flip event challenge-independent),
the full-predicate KSF keeps the predicate at every round; flips at challenge rounds are then
genuine SALVAGE events (bad-before ∧ good-after-the-challenge), which the Schwartz–Zippel
machinery bounds per round. -/

open OracleSpec OracleComp ProtocolSpec NNReal
open scoped ENNReal

noncomputable section

namespace FullPredKSF

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **The full-predicate knowledge state function**: the round-indexed predicate IS the state
at every round (no threshold). Side conditions: round-0 ⟺ the input relation (`hEmpty`),
message-round stability (`hConcatMsg` — the prover cannot repair a broken state by sending a
message), and the knowledge leg (`hFull` — a verifier acceptance from a full transcript forces
the predicate; for a CHECKED verifier this is where the decision procedure enters). -/
def fullPredKSF (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcatMsg : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFull : ∀ stmtIn tr (witOut : WitOut),
      (Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0) →
      pred (.last n) stmtIn tr) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (ThresholdKSF.unitExtractor (WitOut := WitOut)) where
  toFun := fun m stmtIn tr _ => pred m stmtIn tr
  toFun_empty := fun stmtIn w => hEmpty stmtIn _
  toFun_next := fun m hdir stmtIn tr msg w h => hConcatMsg m hdir stmtIn tr msg h
  toFun_full := fun stmtIn tr witOut hacc => hFull stmtIn tr witOut hacc

/-- **The salvage-budget RBR theorem** (the corrected A5/sub-unit shell): with the
full-predicate KSF, the flip event at EVERY challenge round `i` is the genuine salvage event
`¬ pred (before) ∧ pred (after the challenge)`; given per-round salvage bounds `ε i`
(`hSalvage` — for PIT-style checked verifiers these are the Schwartz–Zippel `d/|F|` bounds via
`probEvent_salvage_le`), the verifier is RBR knowledge sound at budget `ε`. -/
theorem rbrKnowledgeSoundness_of_salvageBound (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcatMsg : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFull : ∀ stmtIn tr (witOut : WitOut),
      (Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0) →
      pred (.last n) stmtIn tr)
    (hSalvage : ∀ stmtIn witIn
      (prover : Prover oSpec StmtIn Unit StmtOut WitOut pSpec) (i : pSpec.ChallengeIdx),
      Pr[fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
          (oSpec + [pSpec.Challenge]ₒ).QueryLog =>
          ¬ pred i.1.castSucc stmtIn x.1 ∧ pred i.1.succ stmtIn (x.1.concat x.2.1)
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ (ε i : ℝ≥0∞)) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε := by
  classical
  refine ⟨fun _ => Unit, ThresholdKSF.unitExtractor,
    fullPredKSF init impl verifier relIn relOut pred hEmpty hConcatMsg hFull, ?_⟩
  intro stmtIn witIn prover i
  refine le_trans (probEvent_mono ?_) (hSalvage stmtIn witIn prover i)
  rintro ⟨tr, ch, log⟩ _ ⟨w, hne, hsucc⟩
  exact ⟨hne, hsucc⟩

end FullPredKSF

end

#print axioms FullPredKSF.fullPredKSF
#print axioms FullPredKSF.rbrKnowledgeSoundness_of_salvageBound
