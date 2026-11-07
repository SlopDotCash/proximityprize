/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness
import ArkLib.ToVCVio.Simulation
import ArkLib.ProofSystem.Binius.BinaryBasefold.FinalRelation

/-!
# Query execution and historical proximity bounds

The executable verifier uses canonical chronological challenges and canonical matrix rows.
Its native completeness and support laws below delegate to the canonical owners. Historical
newest-first predicates and probability bounds remain pure results in `Historical`; they do not
identify those predicates with the unconverted native verifier. Exact original command
retirements are recorded in `scripts/integration/binius-query-execution-consolidation.json`.
-/

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Binius.BinaryBasefold.CoreInteraction
open scoped ProbabilityTheory NNReal

/-- Uniform function sampling gives the product probability of the coordinate event. -/
private lemma uniform_forall_fin_probability {A : Type} [Fintype A] [Nonempty A]
    (n : ℕ) (P : A → Prop) :
    Pr_{ let f ← $ᵖ (Fin n → A) }[ ∀ i, P (f i) ] =
      (Pr_{ let x ← $ᵖ A }[ P x ]) ^ n := by
  classical
  have hcard : (Finset.univ.filter (fun f : Fin n → A => ∀ i, P (f i))).card =
      (Finset.univ.filter P).card ^ n := by
    calc
      _ = (Fintype.piFinset (fun _ : Fin n => Finset.univ.filter P)).card := by
        congr 1
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      _ = _ := by simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [prob_uniform_eq_card_filter_div_card, hcard, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, ENNReal.coe_pow]
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

/-- Compatibility spelling of the canonical chronological query-loop invariant. -/
@[reducible]
def checkSingleRepetition_foldRel
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
  CheckSingleRepetitionFoldRel 𝔽q β stmtIn oStmtIn v

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ in
/-- The original bounded-fold invariant equals the canonical chronological invariant. -/
theorem checkSingleRepetition_foldRel_eq_canonical
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oracles : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    checkSingleRepetition_foldRel 𝔽q β stmt oracles v =
      CheckSingleRepetitionFoldRel 𝔽q β stmt oracles v := by
  rfl

/-- Pair-support projection wrapper of `support_simulateQ_run'_eq`.
`Prod.fst` of the stateful run support matches the spec support. -/
lemma support_run_simulateQ_run_fst_eq {ι : Type}
    {oSpec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure oSpec] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    Prod.fst <$> support (m := ProbComp) (α := Option α × σ) ((simulateQ impl oa) s) =
      support (m := OracleComp oSpec) (α := Option α) oa := by
  have h_support := support_simulateQ_run'_eq (impl := impl) (oa := oa) (s := s)
    (hImplSupp := hImplSupp)
  rw [StateT.run'_eq, support_map] at h_support
  exact h_support

omit [CharP L 2] [SampleableType L] h_Fq_char_prime in
/-- The canonical query step accepts every strict honest input, with its exact native output.
The canonical simulation theorem proves equality to a pure accepted result, so this support
statement does not discard a failure or missing-mass branch. -/
theorem queryPhaseLogicStep_isStronglyComplete_native :
    (queryPhaseLogicStep 𝔽q β (ℓ := ℓ) (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  intro stmt wit oracles chals hstrict
  cases wit
  have hpure := queryPhaseLogicStep_simulate_honest 𝔽q β γ_repetitions
    stmt oracles chals hstrict
  refine ⟨?_, rfl, rfl, ?_⟩
  · change none ∉ support (simulateQ
      (OracleInterface.simOracle2 []ₒ oracles
        ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions).honestProverTranscript
          stmt () oracles chals).messages)
      ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions).verifierCheck stmt
        ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions).honestProverTranscript
          stmt () oracles chals)).run)
    rw [hpure]
    simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true]
  · exact Subsingleton.elim _ _

omit [CharP L 2] [SampleableType L] h_Fq_char_prime in
/-- Native query perfect completeness, retaining the former lossless-initial-state argument.
Canonical `ProbComp` is lossless already, so the owner theorem needs no extra premise. -/
theorem queryOracleProof_perfectCompleteness_native {σ : Type}
    (init : ProbComp σ) (_hInit : NeverFail init)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
      (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleProof := queryOracleReduction 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init) (impl := impl) :=
  queryOracleReduction_perfectCompleteness 𝔽q β γ_repetitions init impl

omit [CharP L 2] [SampleableType L] h_Fq_char_prime in
/-- Successful native query execution returns `true`, preserves the materialized empty output
family, and establishes the canonical chronological logical checks for every repetition. -/
theorem logical_consistency_checks_passed_of_mem_support_V_run_native {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem : (stmtOut, oStmtOut) ∈ support
      (OptionT.mk (Prod.fst <$> (simulateQ impl
        (Verifier.run (stmtIn, oStmtIn) tr
          (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
            (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions)))).run s))) :
    stmtOut = true ∧
      oStmtOut = OracleVerifier.materializeOutput
        (Oₛₒ := fun i : Empty => nomatch i)
        (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions)
        tr.challenges oStmtIn tr.messages ∧
      ∀ rep : Fin γ_repetitions,
        LogicalCheckSingleRepetition 𝔽q β oStmtIn
          (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.finalConstant :=
  logicalProximityChecksSpec_of_mem_support_verifier_run 𝔽q β γ_repetitions
    impl stmtIn oStmtIn tr s stmtOut oStmtOut h_mem

namespace Historical

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] in
private lemma getChallengeSuffix_heq
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    {k k' : Fin (ℓ / ϑ)} (h : k = k') :
    HEq (getChallengeSuffix 𝔽q β k v) (getChallengeSuffix 𝔽q β k' v) := by
  subst k'
  rfl


/-- The original pure historical state predicate. This is not the native verifier's
`QueryKnowledgeState` and does not construct a native knowledge-state function. -/
def queryKStateProp (m : Fin (1 + 1))
    (tr : ProtocolSpec.Transcript m
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
  (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (witMid : Unit)
  (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as last KState of finalSumcheck reduction (= relIn)
    Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β
      (input := ⟨⟨stmtIn, oStmtIn⟩, witMid⟩)
  | ⟨1, _⟩ => -- After V sends γ challenges: proximity tests must pass
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ :=
      tr.challenges ⟨0, rfl⟩
    logical_proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (γ_repetitions := γ_repetitions) (γ_challenges := γ_challenges)
      (final_constant := stmtIn.finalConstant) (oStmt := oStmtIn) (stmt := stmtIn)

/-- **Single Repetition Proximity Check Bound (Proposition 4.24)**

For a single repetition of the proximity check, the probability that a non-compliant
oracle (not close to RS codeword) passes the fold consistency check is bounded by:
  `(1/2) + 1/(2 * 2^𝓡)`

**Preconditions (from Proposition 4.24 in the archived DP24 PDF):**
- `h_not_oracleFoldingConsistent`: At least one oracle is non-compliant
- `h_no_bad_event`: No bad folding events occurred (Definition 4.20)

This is the fundamental proximity testing bound used in the soundness proof. -/
theorem prop_4_23_singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.finalConstant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- Delegates to Soundness Prop 4.24 (Lemma 4.26 supplies the query-rejection property).
  have h_res :=
    (Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_consistent := h_not_oracleFoldingConsistent)
      (h_no_bad := h_no_bad_event)
      (h_le := by
        apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)))
  dsimp only [queryRbrKnowledgeError_singleRepetition, queryRbrKnowledgeErrorSingleRepetition]
  simp only [one_div, mul_inv_rev, ENNReal.coe_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, ENNReal.coe_mul, pow_eq_zero_iff',
    false_and, ENNReal.coe_pow, ge_iff_le]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
    ENNReal.coe_ofNat, ENNReal.coe_one] at h_res
  rw [ENNReal.mul_inv (ha := by
    left; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
    (hb := by
      left; simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true]) , mul_comm] at h_res
  exact h_res

theorem singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.finalConstant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- This is Proposition 4.24 from the archived DP24 PDF specialized to a single repetition.
  exact
    prop_4_23_singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_oracleFoldingConsistent := h_not_oracleFoldingConsistent)
      (h_no_bad_event := h_no_bad_event)


end Historical

#print axioms checkSingleRepetition_foldRel_eq_canonical
#print axioms support_run_simulateQ_run_fst_eq
#print axioms queryPhaseLogicStep_isStronglyComplete_native
#print axioms queryOracleProof_perfectCompleteness_native
#print axioms logical_consistency_checks_passed_of_mem_support_V_run_native
#print axioms Historical.prop_4_23_singleRepetition_proximityCheck_bound
#print axioms Historical.singleRepetition_proximityCheck_bound

end
end Binius.BinaryBasefold.QueryPhase
