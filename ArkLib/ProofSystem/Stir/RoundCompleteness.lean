/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RoundProtocol
import ArkLib.OracleReduction.Completeness

/-!
# Issue #301 — perfect completeness of the STIR fold round

Discharges the stated obligation `StirIOP.Round.stirRoundReduction_completeness`
(`RoundProtocol.lean`, previously deferred pending heterogeneous round-peeling infrastructure):

* `unroll_2_message_VP` — the generic `[V_to_P, P_to_V]` 2-message unroll lemma (the missing
  round-peeling piece), specialised from the in-tree
  `OracleReduction.unroll_n_message_reduction_perfectCompleteness`.
* `stirRoundReduction_perfectCompleteness` — the honest prover combines its single codeword at
  its own degree, which by `combine_single_self` is the input oracle itself; the verifier
  forwards it and accepts, so the output relation reduces to the input relation.
* `stirRoundReduction_completeness_proved` — the stated `def : Prop` obligation, discharged.
* `Reduction.completenessFromRun_mono_error` + `stirRoundReduction_completeness_any_error` —
  generic error monotonicity and the any-`ε` corollary.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal OracleReduction

namespace StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### `[V_to_P, P_to_V]` unroll lemma (heterogeneous `processRound` round-peeling) -/
section UnrollVP

variable {ιₒ : Type} {oSpec : OracleSpec ιₒ} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  {pSpecVP : ProtocolSpec 2} [∀ i, SampleableType (pSpecVP.Challenge i)]
  [[pSpecVP.Challenge]ₒ.Fintype] [[pSpecVP.Challenge]ₒ.Inhabited]
  [∀ i, OracleInterface (pSpecVP.Message i)]
  {σ : Type}

theorem unroll_2_message_VP
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpecVP)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
    (hDir0 : pSpecVP.dir 0 = .V_to_P) (hDir1 : pSpecVP.dir 1 = .P_to_V)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (OracleReduction.liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
          let r0 ← liftComp (pSpecVP.getChallenge ⟨0, hDir0⟩) (oSpec + [pSpecVP.Challenge]ₒ)
          let receiveChallengeFn ← liftComp (reduction.prover.receiveChallenge ⟨0, hDir0⟩
            (reduction.prover.input ((stmtIn, oStmtIn), witIn))) (oSpec + [pSpecVP.Challenge]ₒ)
          let state1 := receiveChallengeFn r0
          let ⟨msg1, state2⟩ ← liftComp (reduction.prover.sendMessage ⟨1, hDir1⟩ state1)
            (oSpec + [pSpecVP.Challenge]ₒ)
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state2)
            (oSpec + [pSpecVP.Challenge]ₒ)
          let transcript := ProtocolSpec.FullTranscript.mk2 r0 msg1
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
            (oSpec + [pSpecVP.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
        ) : OptionT (OracleComp (oSpec + [pSpecVP.Challenge]ₒ))
            ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
      ] = 1 := by
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness (n := 2)
    (reduction := reduction) relIn relOut init impl hInit hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_two : (Fin.last 2) = 2 := by rfl
  rw! (castMode := .all) [h_last_eq_two]
  conv_lhs =>
    simp only [Fin.induction_two']
    rw [Prover.processRound_V_to_P (h := hDir0)]
    rw [Prover.processRound_P_to_V (h := hDir1)]
    simp only
  dsimp
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc]
  congr!
  all_goals
    first
    | (funext i; fin_cases i <;> rfl)
    | (congr 1 <;> (try funext i) <;> (try fin_cases i) <;> rfl)
    | (congr 2 <;> (try funext i) <;> (try fin_cases i) <;> rfl)

end UnrollVP

variable [Nonempty ι]

/-- The empty oracle spec is vacuously inhabited (its query index type is empty). -/
instance : []ₒ.Inhabited where
  inhabited_B := fun i => i.elim

/-- Finiteness of the STIR fold-round challenge oracle spec (only index `0`, type `F`). -/
instance : [(pSpec ι F).Challenge]ₒ.Fintype where
  fintype_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by
      cases iv using Fin.cases with
      | zero => rfl
      | succ i1 => cases i1 using Fin.cases with
        | zero => simp [pSpec] at hiv
        | succ k => exact k.elim0
    subst h0
    simpa [pSpec, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (inferInstance : Fintype F)

/-- Inhabitedness of the STIR fold-round challenge oracle spec (response `F` at index `0`). -/
instance : [(pSpec ι F).Challenge]ₒ.Inhabited where
  inhabited_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by
      cases iv using Fin.cases with
      | zero => rfl
      | succ i1 => cases i1 using Fin.cases with
        | zero => simp [pSpec] at hiv
        | succ k => exact k.elim0
    subst h0
    simpa [pSpec, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (⟨(0 : F)⟩ : Inhabited F)


variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
/-- **Perfect completeness of the honest STIR fold-round object.** The honest prover combines its
single codeword at its own degree, which by `combine_single_self` is the input oracle itself; the
verifier forwards it and always accepts, so the output relation reduces to the input relation. -/
theorem stirRoundReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirRoundInputRel φ deg δ) (stirRoundOutputRel φ deg δ)
      (stirRoundReduction φ deg) := by
  rw [unroll_2_message_VP (stirRoundReduction φ deg)
    (stirRoundInputRel φ deg δ) (stirRoundOutputRel φ deg δ) init impl hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRoundReduction, stirRoundProver, stirRoundVerifier, OracleVerifier.toVerifier,
    OStmt, stirRoundInputRel, stirRoundOutputRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun α _hα => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_map, OptionT.probFailure_liftComp_of_OracleComp_Option]
      simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
        Function.comp_apply, Option.map_some, probFailure_map, HasEvalPMF.probFailure_eq_zero,
        probOutput_eq_zero_iff, support_map, support_liftM, Set.mem_image, reduceCtorEq,
        Set.mem_setOf_eq, not_exists, not_and, exists_const, not_false_eq_true, add_zero, zero_add]
      intro x hx
      erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp only [Option.map_some, reduceCtorEq, not_false_eq_true]
  · -- CORRECTNESS: every output in the support satisfies the relation + agreement
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, _hα, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    refine ⟨?_, trivial, by funext u; rfl⟩
    have hc : Combine.combine φ deg α (fun _ : Fin 1 => oStmtIn ()) (fun _ : Fin 1 => deg)
        = oStmtIn () := combine_single_self φ deg α (oStmtIn ())
    simpa [hc] using h_relIn

/-- The stated `stirRoundReduction_completeness` obligation is discharged: the STIR fold-round
object is (perfectly) complete whenever the shared randomness never fails. -/
theorem stirRoundReduction_completeness_proved (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    stirRoundReduction_completeness init impl φ deg δ :=
  stirRoundReduction_perfectCompleteness init impl φ deg δ hInit

/-- General error-monotonicity of `Reduction.completenessFromRun`: completeness with error `ε₁`
implies completeness with any larger error `ε₂` (the acceptance threshold `1 - ε` only drops). -/
theorem _root_.Reduction.completenessFromRun_mono_error
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιᵣ : Type} {runSpec : OracleSpec ιᵣ} {σᵣ : Type} {Trace : Type}
    (runInit : ProbComp σᵣ)
    (runImpl : QueryImpl runSpec (StateT σᵣ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (run : (stmtIn : StmtIn) → (witIn : WitIn) →
      OptionT (OracleComp runSpec) ((Trace × StmtOut × WitOut) × StmtOut))
    {ε₁ ε₂ : ℝ≥0} (hle : ε₁ ≤ ε₂)
    (h : Reduction.completenessFromRun runInit runImpl relIn relOut run ε₁) :
    Reduction.completenessFromRun runInit runImpl relIn relOut run ε₂ := by
  intro stmtIn witIn hIn
  refine le_trans ?_ (h stmtIn witIn hIn)
  exact tsub_le_tsub_left (by exact_mod_cast hle) 1

/-- **Strengthening**: the STIR fold-round object satisfies completeness with *every*
completeness error `ε` (not just `0`), as a corollary of its perfect completeness. -/
theorem stirRoundReduction_completeness_any_error (φ : ι ↪ F) (deg : ℕ) (δ ε : ℝ≥0)
    (hInit : NeverFail init) :
    (stirRoundReduction φ deg).completeness init impl
      (stirRoundInputRel φ deg δ) (stirRoundOutputRel φ deg δ) ε :=
  Reduction.completenessFromRun_mono_error _ _ _ _ _ (zero_le ε)
    (stirRoundReduction_perfectCompleteness init impl φ deg δ hInit)


end

end StirIOP.Round

#print axioms StirIOP.Round.unroll_2_message_VP
#print axioms StirIOP.Round.stirRoundReduction_perfectCompleteness
#print axioms StirIOP.Round.stirRoundReduction_completeness_proved
#print axioms Reduction.completenessFromRun_mono_error
#print axioms StirIOP.Round.stirRoundReduction_completeness_any_error
