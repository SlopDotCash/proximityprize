/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Conjoining rbr knowledge soundness with a verifier-preserved statement predicate

**The conjoin-invariant combinator.** If a verifier is round-by-round knowledge-sound for
`(relIn, relOut)` at error `err`, and `P_in`/`P_out` are *statement-only* predicates such that
any positive-probability verifier output in `P_out` certifies `P_in` of the input statement
(the *preservation* hypothesis `hPres`, stated in the same probabilistic form as
`KnowledgeStateFunction.toFun_full` — trivially dischargeable for deterministic pass-through
verifiers), then the verifier is rbr knowledge-sound for the conjoined relations
`(relIn ∩ P_in, relOut ∩ P_out)` at the **same** per-round error.

This is the enabling brick for threading cross-phase *binding* predicates (e.g. the Spartan
first-sum-check terminal binding `e₁ = eq̃(τ,r_x)·(v_A·v_B − v_C)` of issue #114) through
composed relation chains whose interior endpoints are pinned by lifted component leaves (the
sum-check leaves): the pinned local relation is conjoined with the pass-through binding
predicate without re-proving the component's knowledge soundness.

The proof is purely structural: the conjoined knowledge state function is
`kSF' m stmt tr w := kSF m stmt tr w ∧ stmt ∈ P_in`. The `P_in` conjunct depends only on the
*input* statement, hence is constant across rounds: message rounds propagate it verbatim, and a
challenge-round false-to-true flip of the conjunction entails a flip of the original `kSF`
(the conjoined state is true after the challenge only if `P_in` holds, in which case the
pre-challenge falsity was the original `kSF`'s falsity), so the flip event is contained in the
original one and the error bound transfers unchanged.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut WitIn WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

open scoped NNReal

/-- The conjoined knowledge state function: the original state function strengthened with a
verifier-preserved input-statement predicate. -/
def KnowledgeStateFunction.conjoin
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : V.KnowledgeStateFunction init impl relIn relOut E)
    (P_in : Set StmtIn) (P_out : Set StmtOut)
    (hPres : ∀ stmtIn tr,
      Pr[fun stmtOut => stmtOut ∈ P_out
        | OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)] > 0 →
      stmtIn ∈ P_in) :
    V.KnowledgeStateFunction init impl
      (relIn ∩ {x | x.1 ∈ P_in}) (relOut ∩ {y | y.1 ∈ P_out}) E where
  toFun := fun m stmtIn tr w => kSF.toFun m stmtIn tr w ∧ stmtIn ∈ P_in
  toFun_empty := fun stmtIn witMid => by
    constructor
    · rintro ⟨hrel, hP⟩
      exact ⟨(kSF.toFun_empty stmtIn witMid).mp hrel, hP⟩
    · rintro ⟨hfun, hP⟩
      exact ⟨(kSF.toFun_empty stmtIn witMid).mpr hfun, hP⟩
  toFun_next := fun m hdir stmtIn tr msg witMid h =>
    ⟨kSF.toFun_next m hdir stmtIn tr msg witMid h.1, h.2⟩
  toFun_full := fun stmtIn tr witOut h => by
    refine ⟨kSF.toFun_full stmtIn tr witOut ?_, hPres stmtIn tr ?_⟩
    · refine lt_of_lt_of_le h (probEvent_mono ?_)
      intro x _ hx
      exact hx.1
    · refine lt_of_lt_of_le h (probEvent_mono ?_)
      intro x _ hx
      exact hx.2

/-- **rbr knowledge soundness conjoined with a verifier-preserved statement predicate, at the
same error.** -/
theorem rbrKnowledgeSoundness_conjoin
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {err : pSpec.ChallengeIdx → ℝ≥0}
    (hKS : V.rbrKnowledgeSoundness init impl relIn relOut err)
    (P_in : Set StmtIn) (P_out : Set StmtOut)
    (hPres : ∀ stmtIn tr,
      Pr[fun stmtOut => stmtOut ∈ P_out
        | OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)] > 0 →
      stmtIn ∈ P_in) :
    V.rbrKnowledgeSoundness init impl
      (relIn ∩ {x | x.1 ∈ P_in}) (relOut ∩ {y | y.1 ∈ P_out}) err := by
  obtain ⟨WitMid, E, kSF, hbound⟩ := hKS
  refine ⟨WitMid, E, kSF.conjoin P_in P_out hPres, ?_⟩
  intro stmtIn witIn prover i
  refine le_trans (le_trans (probEvent_mono ?_) le_rfl) (hbound stmtIn witIn prover i)
  rintro ⟨transcript, challenge, _log⟩ _ ⟨witMid, ⟨hnot, hsucc⟩⟩
  exact ⟨witMid, fun hcast => hnot ⟨hcast, hsucc.2⟩, hsucc.1⟩

end Verifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.KnowledgeStateFunction.conjoin
#print axioms Verifier.rbrKnowledgeSoundness_conjoin
