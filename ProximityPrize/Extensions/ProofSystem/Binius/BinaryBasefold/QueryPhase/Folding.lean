/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Folding

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Spec
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Soundness
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.OracleReduction.Completeness
import ProximityPrize.Extensions.OracleReduction.Basic
import ArkLib.Data.Misc.Basic

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.

The executable support and failure lemmas below use the canonical native query program.
The `Historical` namespace retains pure folding results for the explicit newest-first
coefficient convention; it does not identify that model with the native query program.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/

namespace Binius.BinaryBasefold.QueryPhase

set_option backward.isDefEq.respectTransparency false

noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Binius.BinaryBasefold.CoreInteraction

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

private local instance (A : Type) : MeasurableSpace A := ⊤
private noncomputable local instance :
    OracleSpec.UniformAnswerMeasure ([]ₒ : OracleSpec.{0, 0} PEmpty) := by
  letI : ∀ q, Finite (([]ₒ : OracleSpec.{0, 0} PEmpty).Range q) := fun q => isEmptyElim q
  letI : ∀ q, Nonempty (([]ₒ : OracleSpec.{0, 0} PEmpty).Range q) := fun q => isEmptyElim q
  exact OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

section FinalQueryRoundIOR

/-!
### Oracle-Aware Reduction Logic for Query Phase

The query phase uses `OracleAwareLogicStep` because its verifier check involves
oracle queries (querying committed codewords at fiber points).
-/

/-- The finite challenge sampler required by the canonical query phase. -/
instance instQueryChallengeFintype : ∀ j, Fintype ((pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)
  | ⟨0, _⟩ => by
    haveI : Fintype (sDomain 𝔽q β h_ℓ_add_R_rate 0) :=
      fintype_sDomain 𝔽q β h_ℓ_add_R_rate 0
    exact inferInstanceAs
      (Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0))

instance instQueryChallengeInhabited : ∀ j, Inhabited ((pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)
  | ⟨0, _⟩ => ⟨fun _ => 0⟩

namespace Historical

omit [CharP L 2] [SampleableType L] in
/-- Congruence of `single_point_localized_fold_matrix_form` under a (propositionally equal)
change of destination index. Reconstructed (the original was deleted); models
`extractSuffixFromChallenge_congr_destIdx`. -/
lemma single_point_localized_fold_matrix_form_congr_dest_index
    {i : Fin r} {steps : ℕ} {destIdx destIdx' : Fin r}
    {h_destIdx : destIdx.val = i.val + steps} {h_destIdx_le : destIdx ≤ ℓ}
    {r_challenges : Fin steps → L} {y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx}
    {fiber_eval_mapping : Fin (2 ^ steps) → L}
    (h_destIdx_eq_destIdx' : destIdx = destIdx') :
    single_point_localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le r_challenges y
        fiber_eval_mapping
      = single_point_localized_fold_matrix_form 𝔽q β i steps
          (h_destIdx_eq_destIdx' ▸ h_destIdx) (h_destIdx_eq_destIdx' ▸ h_destIdx_le) r_challenges
          (h_destIdx_eq_destIdx' ▸ y) fiber_eval_mapping := by
  subst h_destIdx_eq_destIdx'
  rfl

omit [CharP L 2] [SampleableType L] in
/-- Congruence of `single_point_localized_fold_matrix_form` under a (propositionally equal)
change of the `steps` index. Mirror of `single_point_localized_fold_matrix_form_congr_dest_index`
over the `steps` index. -/
lemma single_point_localized_fold_matrix_form_congr_steps_index
    {i : Fin r} {steps steps' : ℕ} {destIdx : Fin r}
    {h_destIdx : destIdx.val = i.val + steps} {h_destIdx_le : destIdx ≤ ℓ}
    {r_challenges : Fin steps → L} {y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx}
    {fiber_eval_mapping : Fin (2 ^ steps) → L}
    (h_steps_eq_steps' : steps = steps') :
    single_point_localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le r_challenges y
        fiber_eval_mapping
      = single_point_localized_fold_matrix_form 𝔽q β i steps'
          (h_steps_eq_steps' ▸ h_destIdx) h_destIdx_le
          (h_steps_eq_steps' ▸ r_challenges) y
          (h_steps_eq_steps' ▸ fiber_eval_mapping) := by
  subst h_steps_eq_steps'
  rfl

/-- For a block index `k < ℓ / ϑ` (with `ϑ ∣ ℓ`), the block end `(k + 1) * ϑ`
is `≤ ℓ`. Product-form companion of `k_succ_mul_ϑ_le_ℓ_₂`. -/
lemma k_succ_mul_ϑ_le_ℓ (k : Fin (ℓ / ϑ)) : (k.val + 1) * ϑ ≤ ℓ := by
  have h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  rw [Nat.add_mul, Nat.one_mul]
  omega

end Historical

def queryPhaseProverState : Fin (1 + 1) → Type := fun
  | 0 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit
  | 1 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit ×
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩

/-- The final query round as an `OracleProof` (since it outputs Bool and no oracle statements). -/
noncomputable def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

lemma OracleComp.liftM_query_eq_liftM_liftM.{u, v, z}
    {ι : Type u} {spec : OracleSpec ι} {m : Type v → Type z}
    [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) :
    (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

omit [CharP L 2] [SampleableType L] in
lemma mem_support_queryFiberPoints
    -- The number of oracles in query phase is toCodewordsCount(ℓ) = ℓ/ϑ
    {oraclePositionIdx : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn :
      ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) γ_repetitions
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oraclePositionIdx v)))) :
    let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨oraclePositionIdx, by simp only [toOutCodewordsCount, Fin.val_last,
        lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
    ∀ (fiberIndex : Fin (2 ^ ϑ)),
      f_i_on_fiber.get fiberIndex =
      (oStmtIn k_th_oracleIdx (getFiberPoint 𝔽q β oraclePositionIdx v fiberIndex)) := by
  dsimp only at h_fiber_mem ⊢
  erw [queryFiberPoints_simulate] at h_fiber_mem
  simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h_fiber_mem
  intro u
  have h := congrArg (fun v : Vector L (2 ^ ϑ) => v.get u) h_fiber_mem
  simpa [logicalQueryFiberPoints] using h

private lemma prFail_simulateQ_lift_empty {ι : Type} {spec : OracleSpec ι} {α : Type}
    (so : QueryImpl spec (OracleComp ([]ₒ : OracleSpec.{0, 0} PEmpty)))
    (mx : OracleComp spec α) :
    prFail (OptionT.mk (simulateQ so (liftM mx : OptionT (OracleComp spec) α).run)) = 0 := by
  simp only [OptionT.run_monadLift, monadLift_self, simulateQ_map]
  rw [ProximityPrize.Compatibility.prFail_mk]
  simp [OracleComp.prFail_eq_zero]

/-! Simulated `queryFiberPoints` has zero failure probability. -/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ in
lemma probFailure_simulateQ_queryFiberPoints_eq_zero
    (so : QueryImpl
      ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
        [(pSpecQuery 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))
      (OracleComp ([]ₒ : OracleSpec.{0, 0} PEmpty)))
    (k : Fin (List.finRange (ℓ / ϑ)).length)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    prFail (OptionT.mk
        (simulateQ.{0, 0, 0} so
          (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k) v))) = 0 := by
  dsimp only [queryFiberPoints]
  erw [OptionT.simulateQ_vector_mapM]
  apply OptionT.probFailure_vector_mapM_eq_zero
  intro u hu
  apply prFail_simulateQ_lift_empty

lemma getBit_eq_testBit (n k : ℕ) : Nat.getBit k n = 1 ↔ Nat.testBit n k = true := by
  unfold Nat.getBit Nat.testBit
  have h : n >>> k &&& 1 = 1 &&& n >>> k := Nat.land_comm _ _
  rw [h]
  cases h_eq : 1 &&& n >>> k
  · simp
  · case succ m =>
    have h_le : m + 1 ≤ 1 := by
      calc m + 1 = 1 &&& n >>> k := h_eq.symm
        _ ≤ 1 := Nat.and_le_left
    have h_m_0 : m = 0 := by omega
    subst h_m_0
    simp


namespace Historical

private lemma function_comp_cast_heq {A B C : Type} (h : A = B) (f : B → C) :
    HEq (fun x : A => f (cast h x)) f := by
  subst B
  rfl

omit [SampleableType L] in
private lemma iterated_fold_zero_heq
    (steps : ℕ) (hs : steps = 0) (destIdx : Fin r)
    (hd : destIdx.val = (0 : Fin r).val + steps) (hle : destIdx.val ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (challenges : Fin steps → L) :
    HEq (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := steps) (destIdx := destIdx) (h_destIdx := hd)
      (h_destIdx_le := hle) f challenges) f := by
  letI : SampleableType L := SampleableType.ofFintype L
  subst steps
  have hz : destIdx = (0 : Fin r) := Fin.ext (by simpa using hd)
  subst destIdx
  apply heq_of_eq
  funext y
  simpa only [eq_mp_eq_cast, cast_eq] using
    iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (h_destIdx := rfl) (h_destIdx_le := hle) f challenges y

omit [SampleableType L] in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- The first oracle in the historical consistency relation uses the historical Boolean
coefficient order. This is the zero-step specialization of that explicit relation. -/
lemma polyToOracleFunc_eq_getFirstOracle
    (t : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    (h_consistency : strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := i)
      (challenges := challenges) (oStmt := oStmt)) :
    let P₀ : L[X]_(2 ^ ℓ) :=
      polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    f₀ = getFirstOracle 𝔽q β oStmt := by
  intro P₀ f₀
  have h_pos : 0 < toOutCodewordsCount ℓ ϑ i :=
    (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos
  have hfirst := h_consistency ⟨0, h_pos⟩
  dsimp only [strictOracleFoldingConsistencyProp, id_eq] at hfirst
  have hzero : HEq (oStmt ⟨0, h_pos⟩) f₀ :=
    (heq_of_eq hfirst).trans
      (iterated_fold_zero_heq 𝔽q β (0 * ϑ) (Nat.zero_mul _) _ _ _ _ _)
  have hget : HEq (getFirstOracle 𝔽q β oStmt) (oStmt ⟨0, h_pos⟩) := by
    dsimp only [getFirstOracle]
    exact function_comp_cast_heq _ _
  exact eq_of_heq (hget.trans hzero).symm


/-- Lemma 1 (Safety):
Proves that if `c_k` is the result of `iterated_fold` up to step `k`,
it must match the oracle evaluation at that step (provided by `h_relIn`).
-/
lemma query_phase_consistency_guard_safe
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOutProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: c_k is the correct iterated fold value up to this point
    (h_c_k_correct :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
      c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
        (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := Compatibility.newestFirstFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
          stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)))
    -- Hypothesis: We are at a step > 0 where a check actually happens
    (h_k_pos : k.val * ϑ > 0)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) γ_repetitions
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v)))) :
  let := k_mul_ϑ_lt_ℓ (k := k)
  c_k = f_i_on_fiber.get (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
  have _ := h_k_pos
  have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v f_i_on_fiber stmtIn
    oStmtIn witIn challenges (h_fiber_mem := h_fiber_mem)
  simp only at h_fiber_val
  rw [h_c_k_correct]
  simp only
  have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
  set destIdx : Fin r := ⟨k.val * ϑ, by omega⟩ with h_destIdx_eq
  conv_rhs => rw [h_fiber_val]
  dsimp only [strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
  -- Now extract the oStmtIn equality at position k
  have h_oStmtIn_k_eq := h_strictOracleFoldingConsistency ⟨k.val,
    by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
  simp only [id_eq] at h_oStmtIn_k_eq
  conv_rhs => rw [h_oStmtIn_k_eq]
  -- The correctly-typed equivalent lives in `QueryPhaseSuffix.lean` (the deleted local lemma was
  -- ill-typed: it fed a `Fin r`-indexed source into an `Fin ℓ`-typed obligation, so elaborating its
  -- statement ground `isDefEq` to the heartbeat cap). `previousSuffix_eq_getFiberPoint…` is exactly
  -- `extractSuffixFromChallenge (block source j·ϑ) = getFiberPoint j (extractMiddleFinMask …)`.
  have h_point_eq : extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ, by omega⟩ (by simp only; omega) =
      getFiberPoint 𝔽q β k v (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, by omega⟩ ϑ) :=
    previousSuffix_eq_getFiberPoint_extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v
  -- `set destIdx` above folded the literal `⟨k*ϑ, _⟩`; expose it again so `h_point_eq` matches.
  rw [h_point_eq]
  rw [← polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn)
    (h_consistency := h_strictOracleFoldingConsistency)]
  rfl

set_option maxHeartbeats 200000 in
private lemma logical_fold_preserves_direct
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOutProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
 :
    let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    logical_computeFoldedValue 𝔽q β k v stmtIn
      (logical_queryFiberPoints 𝔽q β oStmtIn k v) = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (k.val * ϑ + ϑ))
        (destIdx := ⟨(k.val * ϑ + ϑ), by
          have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
          omega⟩)
        (h_destIdx_le := by
          have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
          simp only
          omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := Compatibility.newestFirstFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by
            have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
            simp only [zero_add, Fin.val_last]
            omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(k.val * ϑ + ϑ), by
            have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
            omega⟩)
          (h_destIdx_le := by
            have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
            simp only
            omega)) := by
  have h₁ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val * ϑ + ϑ), by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  let fiber_vec : Vector L (2 ^ ϑ) := Vector.ofFn (logical_queryFiberPoints 𝔽q β oStmtIn k v)
  have h_vec : fiber_vec.get = logical_queryFiberPoints 𝔽q β oStmtIn k v := by
    funext u
    simp [fiber_vec]
  have h_fiber_val : let j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨k.val, by simpa only [toOutCodewordsCount_last] using k.isLt⟩
      ∀ u, fiber_vec.get u = oStmtIn j (getFiberPoint 𝔽q β k v u) := by
    intro j u
    rw [h_vec]
    rfl
  dsimp only [logical_computeFoldedValue]
  rw [←h_vec]
  dsimp only [getChallengeSuffix] -- extractSuffixFromChallenge  arise here
  have h_destIdx_eq : destIdx.val = k.val * ϑ + ϑ := by
    rfl
  --  iterated_fold 𝔽q β 0 ((↑k * ϑ + ϑ)) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (Compatibility.newestFirstFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) (extractSuffixFromChallenge
  -- 𝔽q β v ⟨(↑k * ϑ + ϑ), ⋯⟩ ⋯)
  set challenges_full := Compatibility.newestFirstFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val * ϑ + ϑ))
    (i := Fin.last ℓ) stmtIn.challenges (k := 0)
    (h := by simpa only [zero_add, Fin.val_last] using h₁) with h_challenges_full_defs
  set challenges_mid := Compatibility.newestFirstFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k.val * ϑ)
    (i := Fin.last ℓ) stmtIn.challenges (k := 0)
    (h := by simp only [zero_add, Fin.val_last]; omega) with h_challenges_mid_defs
  set challenges_last : Fin ϑ → L := fun j =>
    foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges
      ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩ with h_challenges_last_defs
  set y_left := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
    (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_left_defs
  set y_right := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
    (destIdx := ⟨(k.val * ϑ + ϑ), by have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩)
    (h_destIdx_le := by omega) with hy_right_defs
  -- -- Step 2: Transform the RHS
  -- Define f_mid directly from oStmtIn k, which is simpler and aligns with fiber_vec.get
  let k_oracle_idx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
  let f_mid : ↥(sDomain 𝔽q β h_ℓ_add_R_rate midIdx) → L := oStmtIn k_oracle_idx
  set fiber_vec_actual_def := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := midIdx) (steps := ϑ) (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by
      simp only [Nat.add_right_cancel_iff]; rfl)
    (h_destIdx_le := by omega) (f := f_mid)
    (y := y_left) with h_fiber_vec_actual_def
  have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
    rw [h_vec]
    funext x
    dsimp only [fiber_vec_actual_def]
    rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β (h_i_add_steps_le := h₁)]
    exact congrArg (oStmtIn k_oracle_idx)
      (getFiberPoint_eq_qMap_total_fiber 𝔽q β k v x)
  rw [h_fiber_vec_get]; dsimp only [fiber_vec_actual_def]
  have h_eq := single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := ϑ)
    (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by simp only [Nat.add_right_cancel_iff]; rfl)
    (h_destIdx_le := by omega) (h_i_lt := by dsimp only [midIdx]; exact k_mul_ϑ_lt_ℓ (k := k))
    (f := f_mid) (y := y_left) (r_challenges :=
      fun j => foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges
        ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩)
  erw [h_eq]
  dsimp only [f_mid]
  -- Now rw the oStmtIn k_oracle_idx into the iterated_fold of f⁽⁰⁾ form
  -- Extract t and strictOracleFoldingConsistencyProp from h_relIn
  dsimp only [strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
  -- Get the equality for k_oracle_idx: oStmtIn k_oracle_idx = iterated_fold from 0 to k.val * ϑ
  have h_f_mid_eq_iterated_fold := h_strictOracleFoldingConsistency k_oracle_idx
  simp only [id_eq] at h_f_mid_eq_iterated_fold
  rw [h_f_mid_eq_iterated_fold]
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.eval (statementOrderBitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_transitivity := iterated_fold_transitivity 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r))
    (midIdx := ⟨k.val * ϑ, by omega⟩)
    (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩)
    (steps₁ := k.val * ϑ) (steps₂ := ϑ)
    (h_midIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
    (h_midIdx_le := by change k.val * ϑ ≤ ℓ; omega)
    (h_destIdx := by simp only [Nat.add_right_cancel_iff])
    (h_destIdx_le := by change k.val * ϑ + ϑ ≤ ℓ; exact h₁)
    (f := f₀)
    (r_challenges₁ := Compatibility.newestFirstFoldingChallenges (𝓡 := 𝓡) (r := r)
      (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    (r_challenges₂ := fun j =>
      foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges
        ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩)
  have h_transitivity_at := congrFun h_transitivity y_left
  refine h_transitivity_at.trans ?_
  rw [← h_challenges_mid_defs, ← h_challenges_last_defs]
  have h_f₀_eq_getFirstOracle : f₀ = getFirstOracle 𝔽q β oStmtIn := by
    exact polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
      (challenges := stmtIn.challenges) (oStmt := oStmtIn)
      (h_consistency := h_strictOracleFoldingConsistency)
  rw [h_f₀_eq_getFirstOracle]
  have h_challenges_eq : Fin.append challenges_mid challenges_last = challenges_full := by
    funext j
    dsimp only [Fin.append, Fin.addCases, challenges_full, challenges_mid, challenges_last]
    by_cases h : j.val < k.val * ϑ
    · simp only [h, ↓reduceDIte, Fin.castLT_mk]
      rfl
    · dsimp only [Compatibility.newestFirstFoldingChallenges]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk,
        Fin.val_last, eq_rec_constant]
      apply congrArg (foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges)
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_subNat, Fin.val_cast]
      omega
  rw [h_challenges_eq]

omit [SampleableType L] in
/-- Folding the first oracle through all challenges evaluates its multilinear witness. -/
lemma firstOracle_fullFold_eq_eval
    (t : MultilinearPoly L ℓ) (challenges : Fin (Fin.last ℓ) → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_oracle : strictOracleFoldingConsistencyProp 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Fin.last ℓ) challenges oStmt)
    (m : ℕ) (hm : m = ℓ) (destIdx : Fin r) (hd : destIdx.val = m)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := m) (destIdx := destIdx)
      (h_destIdx := by simpa only [Fin.val_zero, zero_add] using hd)
      (h_destIdx_le := by change destIdx.val ≤ ℓ; omega)
      (f := getFirstOracle 𝔽q β oStmt)
      (r_challenges := Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡)
        (i := Fin.last ℓ) challenges 0 (by simp [hm])) y = t.val.eval challenges := by
  subst m
  have hdest : destIdx = ⟨ℓ, lt_r_of_le_ℓ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Nat.le_refl ℓ)⟩ := Fin.ext hd
  subst destIdx
  rw [← polyToOracleFunc_eq_getFirstOracle 𝔽q β t (Fin.last ℓ) challenges oStmt h_oracle]
  have h := Compatibility.newestFirstCodeword_last_apply_eq_eval 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t challenges y
  rw [Compatibility.newestFirstCodeword_eq_legacy] at h
  have h_ch : Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡)
      (ϑ := ℓ) (i := Fin.last ℓ) challenges 0 (by simp) =
      foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) challenges := by
    funext j
    simp [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges,
      foldOrderChallenges]
  rw [h_ch]
  convert h using 1 <;> rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
omit [SampleableType L] [DecidableEq 𝔽q] in
/-- The full prefix fold equals the final constant in a strictly consistent statement. -/
lemma query_phase_final_fold_eq_constant
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c : L)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOutProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: x is the result of folding all the way to ℓ
    (h_c_correct :
      have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
      c = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (ℓ / ϑ) * ϑ)
        (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := Compatibility.newestFirstFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
    ) :
    c = stmtIn.finalConstant := by
  classical
  letI : SampleableType L := SampleableType.ofFintype L
  rcases h_relIn with ⟨t, hOracle, hFinal⟩
  have hm : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have hϑ : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
  let j := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  have hj : j.val * ϑ = ℓ - ϑ := by
    dsimp [j]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, hm]
  have h_end := getLastOracle_finalFold_eq_eval' 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn) hOracle
    (curIdx := ⟨j.val * ϑ, by omega⟩)
    (destIdx := ⟨j.val * ϑ + ϑ, by omega⟩)
    (hcur := hj) (hdest := rfl) (hdest_le := by simp only [Fin.val_mk]; omega)
    (h_destIdx_oracle := rfl) (hpos := by omega)
    (rchal := Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (j.val * ϑ) (by simp only [Fin.val_last]; omega))
    (hrchal := rfl) (y := 0)
  have hcst : stmtIn.finalConstant = t.val.eval stmtIn.challenges :=
    (congrFun hFinal 0).symm.trans h_end
  exact h_c_correct.trans ((firstOracle_fullFold_eq_eval 𝔽q β
    t stmtIn.challenges oStmtIn hOracle (ℓ / ϑ * ϑ) hm _ rfl _).trans hcst.symm)

end Historical

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase

#print axioms Binius.BinaryBasefold.QueryPhase.mem_support_queryFiberPoints
#print axioms Binius.BinaryBasefold.QueryPhase.probFailure_simulateQ_queryFiberPoints_eq_zero
#print axioms Binius.BinaryBasefold.QueryPhase.Historical.polyToOracleFunc_eq_getFirstOracle
#print axioms Binius.BinaryBasefold.QueryPhase.Historical.query_phase_consistency_guard_safe
#print axioms Binius.BinaryBasefold.QueryPhase.Historical.logical_fold_preserves_direct
#print axioms Binius.BinaryBasefold.QueryPhase.Historical.firstOracle_fullFold_eq_eval
#print axioms Binius.BinaryBasefold.QueryPhase.Historical.query_phase_final_fold_eq_constant
