/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FullPredKSF

/-!
# Threshold-KSF subsumption and budget monotonicity (#301, K2/K3)

The multi-flip combinator itself is the landed
`FullPredKSF.rbrKnowledgeSoundness_of_salvageBound` (the per-challenge bound family on the
salvage events `¬ pred` before ∧ `pred` after each challenge).  This file adds the two
missing pieces of the #301 K-program around it:

* `rbrKnowledgeSoundness_of_flipBound_via_salvageBounds` — **DRY subsumption,
  machine-checked**: the single-flip threshold theorem
  (`ThresholdKSF.rbrKnowledgeSoundness_of_flipBound`) re-derived through the multi-flip
  combinator with the SAME hypotheses, by retiring the predicate
  (`m ↦ if m ≤ c then pred m else True`) and showing the salvage events vanish pointwise
  away from the designated challenge.  The threshold construction is a special case of the
  full-predicate one — claimed in the FullPredKSF docstring, proven here.
* `rbrKnowledgeSoundness_mono` (#301, K3 generic half) — a valid rbr budget family remains
  valid after any pointwise increase; this is what transfers an exact budget `ε⋆` to every
  `≥`-budget front door.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

open OracleSpec OracleComp ProtocolSpec NNReal
open scoped ENNReal

noncomputable section

namespace ThresholdKSF

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **DRY check: the single-flip threshold theorem through the multi-flip combinator.**
Same hypotheses as `rbrKnowledgeSoundness_of_flipBound`; the retired predicate
`m ↦ (if m ≤ c then pred m else True)` discharges the message-round and closing conditions
exactly as `thresholdKSF` did, and the salvage events vanish pointwise away from `c`. -/
theorem rbrKnowledgeSoundness_of_flipBound_via_salvageBounds
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (c : pSpec.ChallengeIdx) (ε : ℝ≥0)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), m.val ≤ c.1.val →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFlip : ∀ stmtIn witIn
      (prover : Prover oSpec StmtIn Unit StmtOut WitOut pSpec),
      Pr[fun x : pSpec.Transcript c.1.castSucc × pSpec.Challenge c ×
          (oSpec + [pSpec.Challenge]ₒ).QueryLog =>
          ¬ pred c.1.castSucc stmtIn x.1
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound c.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge c) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ (ε : ℝ≥0∞)) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut
      (fun i => if i = c then ε else 0) := by
  classical
  -- the obligations, stated in beta-reduced form (definitional unfolding does the rest)
  have hEmpty' : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔
      (if (0 : Fin (n + 1)).val ≤ c.1.val then pred 0 stmtIn default else True) := by
    intro stmtIn w
    rw [if_pos (by simp)]
    exact hEmpty stmtIn w
  have hMsg' : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        (if (m.succ : Fin (n + 1)).val ≤ c.1.val then
          pred m.succ stmtIn (tr.concat msg) else True) →
        (if (m.castSucc : Fin (n + 1)).val ≤ c.1.val then
          pred m.castSucc stmtIn tr else True) := by
    intro m hdir stmtIn tr msg h
    by_cases hc : m.val ≤ c.1.val
    · rw [if_pos (by simpa using hc)]
      by_cases hc' : m.val + 1 ≤ c.1.val
      · rw [if_pos (by simpa using hc')] at h
        exact hConcat m hc stmtIn tr msg h
      · exfalso
        have heqm : m = c.1 := Fin.ext (le_antisymm hc (by omega))
        have hv : pSpec.dir m = Direction.V_to_P := by rw [heqm]; exact c.2
        rw [hdir] at hv
        exact Direction.noConfusion hv
    · rw [if_neg (by simpa using hc)]
      trivial
  refine FullPredKSF.rbrKnowledgeSoundness_of_salvageBound init impl verifier relIn relOut
    (fun m stmtIn tr => if m.val ≤ c.1.val then pred m stmtIn tr else True)
    (fun i => if i = c then ε else 0)
    hEmpty' hMsg'
    (fun stmtIn tr witOut _ => by
      show if (Fin.last n).val ≤ c.1.val then pred (.last n) stmtIn tr else True
      rw [if_neg (by simp only [Fin.val_last]; exact Nat.not_le.mpr c.1.isLt)]
      trivial)
    (fun stmtIn witIn prover i => ?_)
  -- salvage bounds: `ε` at `c`, pointwise-impossible elsewhere
  by_cases hic : i = c
  · subst hic
    simp only [if_pos rfl]
    refine le_trans (probEvent_mono ?_) (hFlip stmtIn witIn prover)
    rintro ⟨tr, ch, log⟩ _ ⟨hne, _⟩
    have hne' : ¬ (if (i.1.castSucc : Fin (n + 1)).val ≤ i.1.val then
        pred i.1.castSucc stmtIn tr else True) := hne
    rw [if_pos (by simp)] at hne'
    exact hne'
  · simp only [if_neg hic, ENNReal.coe_zero, nonpos_iff_eq_zero]
    rw [probEvent_eq_zero_iff]
    rintro ⟨tr, ch, log⟩ _ ⟨hne, hsucc⟩
    have hne' : ¬ (if (i.1.castSucc : Fin (n + 1)).val ≤ c.1.val then
        pred i.1.castSucc stmtIn tr else True) := hne
    have hsucc' : (if (i.1.succ : Fin (n + 1)).val ≤ c.1.val then
        pred i.1.succ stmtIn (tr.concat ch) else True) := hsucc
    rcases lt_trichotomy i.1.val c.1.val with hlt | heq | hgt
    · refine hne' ?_
      rw [if_pos (by simpa using hlt.le)]
      rw [if_pos (by simp; omega)] at hsucc'
      exact hConcat i.1 hlt.le stmtIn tr ch hsucc'
    · exact hic (Subtype.ext (Fin.ext heq))
    · rw [if_neg (by simp; omega)] at hne'
      exact hne' trivial

/-- **Budget monotonicity (#301, K3 generic half)**: round-by-round knowledge soundness
transfers to any pointwise-larger budget family. -/
theorem rbrKnowledgeSoundness_mono (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    {WitIn : Type}
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {ε ε' : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut ε)
    (hle : ∀ i, ε i ≤ ε' i) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε' := by
  obtain ⟨WitMid, ext, kSF, hbound⟩ := h
  exact ⟨WitMid, ext, kSF, fun stmtIn witIn prover i =>
    le_trans (hbound stmtIn witIn prover i) (by exact_mod_cast hle i)⟩

end ThresholdKSF

end

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ThresholdKSF.rbrKnowledgeSoundness_of_flipBound_via_salvageBounds
#print axioms ThresholdKSF.rbrKnowledgeSoundness_mono
