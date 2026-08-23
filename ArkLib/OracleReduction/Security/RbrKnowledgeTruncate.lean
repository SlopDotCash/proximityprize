/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Truncating rbr knowledge soundness at an error-`1` challenge round

**The truncation combinator.** If a verifier is round-by-round knowledge-sound for
`(relIn, relOut)` at error `err`, and some challenge round `j` already pays the trivial
per-round error (`1 ≤ err j`), then the verifier is rbr knowledge-sound for `(relIn, relOut')`
at the **same** error vector, for **any** output relation `relOut'`.

The proof is purely structural: replace the knowledge state function `kSF` by its truncation

  `kSF' m stmt tr w := (m ≤ j → kSF m stmt tr w)`,

i.e. the original state function up to (and including) the pre-challenge state of round `j`,
and identically `True` strictly after round `j`. Then:

* `toFun_empty` is unchanged (round `0` is `≤ j`);
* message rounds propagate as before below `j` and trivially above `j` (a message round can
  never *equal* the challenge round `j`, by direction clash);
* the flip event at a challenge round `i < j` is contained in the original flip event, so the
  original bound `err i` transfers;
* the flip event at round `j` itself is bounded by `1 ≤ err j`;
* challenge rounds strictly after `j` cannot flip (the truncated state is already `True`
  before the challenge), so their flip probability is `0`;
* `toFun_full` is trivial (`Fin.last n > j`), for **any** `relOut'`.

**Honesty note.** This combinator does *not* manufacture knowledge soundness: the truncated
state function carries exactly the rbr knowledge content of the protocol *prefix up to round
`j`* and pays the already-present trivial error at `j` for everything after. It converts a
relation-preserving rbr-KS fact whose error vector already contains a `1` (e.g. the Spartan
no-claim chain, where `err₅ = 1` at the `linearCombination` round is proven-forced) into the
same fact stated against an arbitrary — e.g. the broad `Set.univ` — terminal relation. Any
*tight* (error `< 1` at every round) statement against a nontrivial terminal relation remains
exactly as hard as before.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut WitIn WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

open scoped NNReal

/-- The truncated knowledge state function: the original state function up to the challenge
round `j`, and identically `True` strictly after it. Valid against **any** output relation
`relOut'`, since the full-transcript clause is trivial past `j`. -/
def KnowledgeStateFunction.truncateAfter
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : V.KnowledgeStateFunction init impl relIn relOut E)
    (j : pSpec.ChallengeIdx)
    (relOut' : Set (StmtOut × WitOut)) :
    V.KnowledgeStateFunction init impl relIn relOut' E where
  toFun := fun m stmtIn tr w => m.val ≤ j.1.val → kSF.toFun m stmtIn tr w
  toFun_empty := fun stmtIn witMid => by
    rw [kSF.toFun_empty stmtIn witMid]
    exact ⟨fun h _ => h, fun h => h (Nat.zero_le _)⟩
  toFun_next := fun m hdir stmtIn tr msg witMid h => by
    intro hm
    have hm' : m.val ≤ j.1.val := by simpa using hm
    have hne : m ≠ j.1 := by
      intro hEq
      rw [hEq, j.2] at hdir
      exact Direction.noConfusion hdir
    have hlt : m.val < j.1.val :=
      lt_of_le_of_ne hm' (fun hv => hne (Fin.ext hv))
    exact kSF.toFun_next m hdir stmtIn tr msg witMid (h (by simpa using hlt))
  toFun_full := fun stmtIn tr witOut _hPr hle => by
    exact absurd j.1.isLt (Nat.not_lt.mpr (by simpa using hle))

/-- **rbr knowledge soundness against an arbitrary output relation, at the same error vector,
once some challenge round already pays the trivial error `1`.** See the module docstring for
exactly what is (and is not) claimed. -/
theorem rbrKnowledgeSoundness_relOut_any_of_one_le_error
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {err : pSpec.ChallengeIdx → ℝ≥0}
    (hKS : V.rbrKnowledgeSoundness init impl relIn relOut err)
    (j : pSpec.ChallengeIdx) (hj : 1 ≤ err j)
    (relOut' : Set (StmtOut × WitOut)) :
    V.rbrKnowledgeSoundness init impl relIn relOut' err := by
  obtain ⟨WitMid, E, kSF, hbound⟩ := hKS
  refine ⟨WitMid, E, kSF.truncateAfter j relOut', ?_⟩
  intro stmtIn witIn prover i
  rcases lt_trichotomy i.1.val j.1.val with hlt | heq | hgt
  · -- strictly before `j`: the truncated flip event is contained in the original one
    refine le_trans (probEvent_mono ?_) (hbound stmtIn witIn prover i)
    rintro ⟨transcript, challenge, _log⟩ _ ⟨witMid, hnot, hsucc⟩
    exact ⟨witMid, fun hcast => hnot (fun _ => hcast),
      hsucc (by simpa using Nat.succ_le_of_lt hlt)⟩
  · -- at `j`: trivial bound `1 ≤ err j`
    have hij : i = j := Subtype.ext (Fin.ext heq)
    subst hij
    exact le_trans probEvent_le_one (by exact_mod_cast hj)
  · -- strictly after `j`: the truncated state is already `True` before the challenge,
    -- so the flip event is empty
    refine le_trans (le_of_eq ?_) (zero_le _)
    rw [probEvent_eq_zero_iff]
    rintro ⟨transcript, challenge, _log⟩ _ ⟨witMid, hnot, _⟩
    exact hnot (fun hle => absurd hle (by simpa using Nat.not_le.mpr hgt))

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

open scoped NNReal

omit [∀ i, OracleInterface (OStmt₂ i)] in
/-- `OracleVerifier` companion of `Verifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error`. -/
theorem rbrKnowledgeSoundness_relOut_any_of_one_le_error
    {relIn : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {relOut : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {V : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec}
    {err : pSpec.ChallengeIdx → ℝ≥0}
    (hKS : V.rbrKnowledgeSoundness init impl relIn relOut err)
    (j : pSpec.ChallengeIdx) (hj : 1 ≤ err j)
    (relOut' : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)) :
    V.rbrKnowledgeSoundness init impl relIn relOut' err := by
  unfold OracleVerifier.rbrKnowledgeSoundness at hKS ⊢
  exact Verifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error hKS j hj relOut'

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.KnowledgeStateFunction.truncateAfter
#print axioms Verifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error
#print axioms OracleVerifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error
