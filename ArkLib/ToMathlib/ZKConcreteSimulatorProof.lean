/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# ZK Concrete Simulator Preservation (Issue #112) — honest status

A `zk_concrete_simulator_breakthrough` once asserted (via `sorry`) `isHVZK init impl rel R` for an
**arbitrary** reduction `R`, later softened to a vacuous `(hHVZK) → isHVZK` passthrough. Neither
carries content: the universal HVZK claim is **false**. Honest-verifier zero-knowledge is not a
property every reduction enjoys — a reduction whose prover transmits the witness leaks it, and no
witness-free `TranscriptSimulator` can reproduce the resulting witness-dependent honest transcript
distribution for two distinct witnesses of one statement (this is exactly why ZK is a nontrivial
security goal).

So instead of a placebo we prove the honest mathematical content: the universal HVZK claim is
refuted by an explicit witness-leaking counterexample (fully proven, axiom-clean). The genuine
Issue #112 obligation — HVZK of the *specific* Spartan / BCS zero-knowledge construction with its
purpose-built witness-free simulator — remains open and is the real work; it cannot be obtained by
quantifying HVZK over all reductions.

(`Reduction.id` *is* HVZK, via `Reduction.id_isHVZK`; that the identity reduction is HVZK while the
*universal* claim is false is precisely the point — HVZK depends on the reduction.)
-/

namespace ZK112Refutation

open OracleComp OracleSpec ProtocolSpec

/-- A non-interactive reduction that **leaks the witness**: its single prover→verifier message is
the witness bit itself. -/
def leakProver : Prover []ₒ Unit Bool Unit Bool ⟨!v[.P_to_V], !v[Bool]⟩ where
  PrvState := fun _ => Bool
  input := fun x => x.2
  sendMessage := fun idx => match idx with
    | ⟨0, _⟩ => fun w => pure ⟨w, w⟩
  receiveChallenge := fun idx => Fin.elim0 (by
    rcases idx with ⟨i, hi⟩; rcases i with ⟨k, hk⟩; interval_cases k; · simp at hi)
  output := fun w => pure ⟨(), w⟩

instance instProverOnly : ProverOnly (⟨!v[.P_to_V], !v[Bool]⟩ : ProtocolSpec 1) where
  prover_first' := rfl

def leakVerifier : Verifier []ₒ Unit Unit ⟨!v[.P_to_V], !v[Bool]⟩ where
  verify := fun _ _ => pure ()

def leakReduction : Reduction []ₒ Unit Bool Unit Bool ⟨!v[.P_to_V], !v[Bool]⟩ where
  prover := leakProver
  verifier := leakVerifier

/-- The single message at index 0 of the transcript. -/
def msgOf (t : FullTranscript ⟨!v[.P_to_V], !v[Bool]⟩) : Bool := t 0

/-- The transcript produced for witness `w`. -/
def leakTranscript (w : Bool) : FullTranscript ⟨!v[.P_to_V], !v[Bool]⟩ :=
  fun i => match i with | ⟨0, _⟩ => w

/-- The honest run is deterministic: it returns the transcript whose message is the witness. -/
theorem leakReduction_run_eq (w : Bool) :
    leakReduction.run () w = pure ⟨⟨leakTranscript w, (), w⟩, ()⟩ := by
  rw [Reduction.run_of_prover_first]
  simp only [leakReduction, leakProver, leakVerifier, Verifier.run, leakTranscript, liftM_pure,
    monadLift_pure, OptionT.run_pure, Option.getM, bind_pure_comp, map_pure, pure_bind, bind_assoc]
  rfl

/-- The honest transcript distribution is the point mass at `leakTranscript w`. -/
theorem honest_evalDist {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (w : Bool) :
    evalDist (Reduction.honestTranscriptDist init impl leakReduction () w) =
      evalDist (pure (leakTranscript w) : OptionT ProbComp (FullTranscript _)) := by
  classical
  apply evalDist_ext
  intro t
  unfold Reduction.honestTranscriptDist
  simp only [leakReduction_run_eq, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- Distinct witnesses give distinct transcripts. -/
theorem leakTranscript_injOn (w w' : Bool) (h : leakTranscript w = leakTranscript w') : w = w' := by
  have := congrFun h ⟨0, by simp⟩
  simpa [leakTranscript] using this

/-- **Issue #112 refutation (per-instance).** The witness-leaking `leakReduction` is *not* HVZK: a
witness-free simulator would have to reproduce two different honest transcript distributions (one
per witness) of the same statement. -/
theorem leakReduction_not_isHVZK {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ Reduction.isHVZK init impl Set.univ leakReduction := by
  rintro ⟨sim, hsim⟩
  have h0 := hsim () false (Set.mem_univ _)
  have h1 := hsim () true (Set.mem_univ _)
  rw [honest_evalDist] at h0 h1
  classical
  have hpt : evalDist (pure (leakTranscript false) : OptionT ProbComp (FullTranscript _)) =
      evalDist (pure (leakTranscript true) : OptionT ProbComp (FullTranscript _)) :=
    h0.symm.trans h1
  have key : probOutput (pure (leakTranscript false) : OptionT ProbComp (FullTranscript _))
        (leakTranscript false)
      = probOutput (pure (leakTranscript true) : OptionT ProbComp (FullTranscript _))
        (leakTranscript false) := by
    unfold probOutput; rw [hpt]
  rw [probOutput_pure_self, probOutput_pure,
    if_neg (fun h => absurd (leakTranscript_injOn _ _ h) (by decide))] at key
  exact one_ne_zero key

/-- **Issue #112 refutation (universal).** Honest-verifier zero-knowledge does NOT hold for an
arbitrary reduction — the universal claim that *every* reduction is HVZK is false. -/
theorem not_forall_isHVZK :
    ¬ (∀ {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
        {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
        {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
        (rel : Set (StmtIn × WitIn)) (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec),
        Reduction.isHVZK init impl rel R) := by
  intro H
  exact leakReduction_not_isHVZK (pure ()) default
    (H (pure ()) default Set.univ leakReduction)

end ZK112Refutation
