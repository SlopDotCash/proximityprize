/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Security.RoundByRound

/-!
# First-crossing for KNOWLEDGE state functions (the rbr union-bound pointwise core)

The plain-`StateFunction` first-crossing on a realized transcript is in-tree
(`Verifier.StateFunction.exists_challenge_flip_of_full`).  This file supplies the
**knowledge** analogue: the crossing event lands in the EXACT shape of the
`rbrKnowledgeSoundness` game (the extracted middle witness in the `¬`-side, the witness of
the successor state in the positive side), via the `toStateFunction` projection — the
existential witness of the successor state supplies the game's `witMid`, and the negated
existential kills the extracted one.

This is the deterministic heart of the rbr→soundness union-bound chain rule
("an accepting run from a not-in-relation input forces a flip at some challenge round");
the remaining probabilistic lift (the prefix-marginalization of the full run against the
per-round games, summing the budgets) is the named follow-up.

* `KnowledgeStateFunction.exists_challenge_flip_of_full` — the crossing;
* `KnowledgeStateFunction.toFun_zero_false_of_not_relIn` — the base supplier (a statement
  outside the input relation at every witness has `toFun 0` false at every middle witness).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

namespace Verifier

open OracleSpec OracleComp ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

namespace KnowledgeStateFunction

/-- A statement that is in the input relation with NO witness has `toFun 0` false at every
middle witness (the contrapositive reading of `toFun_empty`). -/
theorem toFun_zero_false_of_not_relIn
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (stmtIn : StmtIn) (hStmtIn : ∀ w : WitIn, (stmtIn, w) ∉ relIn)
    (witMid : WitMid 0) :
    ¬ kSF.toFun 0 stmtIn default witMid :=
  fun h => hStmtIn _ ((kSF.toFun_empty stmtIn witMid).mpr h)

/-- **First-crossing for knowledge state functions, in the rbr-game event shape.**
If the input statement has no witness in the input relation, and the knowledge state
function is true on the full realized transcript at SOME final middle witness, then at
some challenge round `i` the rbr knowledge game's flip event holds on the prefixes of
`tr`: there is a middle witness `witMid` with the successor state true and the
`extractMid`-extracted predecessor state false. -/
theorem exists_challenge_flip_of_full
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (stmtIn : StmtIn) (hStmtIn : ∀ w : WitIn, (stmtIn, w) ∉ relIn)
    (tr : pSpec.FullTranscript)
    {witLast : WitMid (Fin.last n)}
    (hlast : kSF.toFun (Fin.last n) stmtIn
      (tr.take (Fin.last n).val (Fin.last n).is_le) witLast) :
    ∃ i : pSpec.ChallengeIdx, ∃ witMid : WitMid i.1.succ,
      ¬ kSF.toFun i.1.castSucc stmtIn (tr.take i.1.castSucc.val i.1.castSucc.is_le)
          (extractor.extractMid i.1 stmtIn
            (Transcript.concat (tr i.1)
              (tr.take i.1.castSucc.val i.1.castSucc.is_le)) witMid) ∧
        kSF.toFun i.1.succ stmtIn
          (Transcript.concat (tr i.1)
            (tr.take i.1.castSucc.val i.1.castSucc.is_le)) witMid := by
  classical
  -- project to the plain state function and run the in-tree first-crossing
  have hlang : stmtIn ∉ relIn.language := by
    intro hmem
    obtain ⟨⟨s, w⟩, hsw, hfst⟩ := hmem
    cases hfst
    exact hStmtIn w hsw
  obtain ⟨i, hneg, hpos⟩ := StateFunction.exists_challenge_flip_of_full init impl
    kSF.toStateFunction stmtIn hlang tr ⟨witLast, hlast⟩
  -- the successor existential supplies the game's witness; the negated existential
  -- kills the extracted predecessor
  obtain ⟨witMid, hwitMid⟩ := hpos
  refine ⟨i, witMid, ?_, hwitMid⟩
  intro hext
  exact hneg ⟨_, hext⟩

end KnowledgeStateFunction

end Verifier

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Verifier.KnowledgeStateFunction.exists_challenge_flip_of_full
#print axioms Verifier.KnowledgeStateFunction.toFun_zero_false_of_not_relIn
