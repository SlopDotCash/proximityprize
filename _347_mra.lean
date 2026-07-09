/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Stir.MainThm
import ArkLib.ProofSystem.Stir.MultiRoundSpec
import ArkLib.ProofSystem.Stir.RoundVector
import ArkLib.ProofSystem.Stir.RoundCompleteness
import ArkLib.OracleReduction.Completeness

/-!
# Issue #301 (STIR, mechanical track): the (M+1)-round STIR Vector IOPP assembly.

* `stirMultiVSpec M ι` — the landed multi-round STIR wire shape (`stirVSpec`) instantiated
  with uniform message length `|ι|` and challenge length `1`.
* `stirMultiRoundProver` / `stirMultiRoundVerifier` / `stirMultiRoundIOP` — the multi-round
  protocol object over that shape: the honest prover stores each fold challenge and sends the
  genuine packed `Combine.combine` fold of its codeword at every one of the `M + 1` message
  rounds (the `(M+1)`-fold lift of the landed `stirRoundVectorProver`); the verifier accepts.
* `stirMultiRoundIOP_perfectCompleteness` — perfect completeness of the assembled object,
  for arbitrary symbolic `M`, via the generic (n-ary)
  `unroll_n_message_reduction_perfectCompleteness` keystone: the `3M + 3`-round
  `runToRound` prefix is kept opaque (it never fails — failure lives only in the `OptionT`
  layer — and the always-accepting outputs are support-independent), so no per-round
  peeling is needed at symbolic `M`.
* `stir_rbr_soundness_of_secure_vectorIOP` / `stir_main_of_secure_vectorIOP` — general
  wiring: ANY secure-with-gap vector IOP over the `stirMultiVSpec` shape discharges the
  `stir_rbr_soundness` / `stir_main` existentials (given the error/complexity legs).
* `stir_rbr_soundness_of_residuals` / `stir_main_of_residuals` — the existentials
  instantiated with the assembled `π`, consuming the genuinely-open legs (rbr knowledge
  soundness of the verifier — Johnson-CA-gated — and the numeric complexity claims about
  the free parameters) as named residual hypotheses.

HONESTY NOTES (no fabrication):
* The assembled verifier is a *shell*: like the in-tree single-round
  `stirRoundVectorVerifier` (`verify := pure ()`), it performs no consistency checks (its
  checks are exactly the open soundness side). Consequently the named residual
  `stirMultiRoundRbrSoundnessResidual` for THIS `π` is open-and-likely-false in regimes
  demanding `ε_rbr < 1` while δ-far oracles exist; for a future *checking* verifier it is
  the genuine Johnson-CA-gated open obligation. The `…_of_secure_vectorIOP` versions are
  the non-vacuous wiring: they accept any future `π` with proven security.
* The complexity legs (`hM`/`hLen`/`hQin`/`hQpf`) of `stir_main` and the per-round error
  legs (`hfold`/`hrest`) of `stir_rbr_soundness` are constraints on universally-quantified
  free parameters of the statements (`M`, `proofLen`, …, `ε_fold`, …); they cannot be
  derived from any construction and are consumed as hypotheses.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι]

/-- The multi-round STIR vector spec, with uniform message length `|ι|` (each prover message is
a packed oracle over the evaluation domain) and challenge length `1` (field-element
challenges): `3M + 3` rounds in the landed `stirVSpec` layout
`[C₀^fold, P g₁, C₁^out, C₁^shift, P g₂, …, C_M^out, C_M^shift, P p, C^fin]`. -/
@[reducible]
def stirMultiVSpec (M : ℕ) (ι : Type) [Fintype ι] : ProtocolSpec.VectorSpec (3 * M + 3) :=
  stirVSpec M (fun _ => Fintype.card ι) 1

/-- Message rounds of `stirMultiVSpec` have length `|ι|`. -/
theorem stirMultiVSpec_length_msg {M : ℕ}
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx) :
    Fintype.card ι = (stirMultiVSpec M ι).length i.1 := by
  have h := i.2
  rw [show ((stirMultiVSpec M ι).toProtocolSpec F).dir i.1 = (stirMultiVSpec M ι).dir i.1
    from rfl, stirVSpec_dir_eq_msg_iff] at h
  simp [stirVSpec, h]

/-- Challenge rounds of `stirMultiVSpec` have positive length (length `1`). -/
theorem stirMultiVSpec_length_chal_pos {M : ℕ} [Nonempty ι]
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx) :
    0 < (stirMultiVSpec M ι).length i.1 := by
  by_cases h : ((i.1 : Fin (3 * M + 3)) : ℕ) % 3 = 1
  · simp [stirVSpec, h]
  · simp [stirVSpec, h]

/-- **The multi-round STIR prover** (the `(M+1)`-fold lift of the landed
`stirRoundVectorProver`): it stores the most recent fold challenge (read off a length-`1`
field vector) and, at each of the `M + 1` message rounds, sends the genuine
`Combine.combine` fold of its single codeword at its own degree, packed via
`packFiniteFunction`. Its final output is acceptance. -/
noncomputable def stirMultiRoundProver (M : ℕ) (φ : ι ↪ F) (deg : ℕ) :
    OracleProver []ₒ Unit (OracleStatement ι F) Unit Bool (fun _ : Empty => Unit) Unit
      ((stirMultiVSpec M ι).toProtocolSpec F) where
  PrvState := fun _ => ((Unit × (∀ i, OracleStatement ι F i)) × Unit) × F
  input := fun x => (x, 0)
  receiveChallenge := fun i st => pure (fun r =>
    (st.1, if h : 0 < (stirMultiVSpec M ι).length i.1 then r.get ⟨0, h⟩ else 0))
  sendMessage := fun i st => pure
    ⟨Vector.cast (stirMultiVSpec_length_msg i)
      (packFiniteFunction ι
        (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ()) (fun _ : Fin 1 => deg))),
     st⟩
  output := fun _ => pure ((true, isEmptyElim), ())

/-- **The multi-round STIR verifier shell**: forwards acceptance (no output oracles). The
genuine per-round consistency checks are the open soundness side (see the residuals below). -/
def stirMultiRoundVerifier (M : ℕ) :
    OracleVerifier []ₒ Unit (OracleStatement ι F) Bool (fun _ : Empty => Unit)
      ((stirMultiVSpec M ι).toProtocolSpec F) where
  verify := fun _ _ => pure true
  embed := ⟨fun i => i.elim, fun i => i.elim⟩
  hEq := fun i => i.elim

/-- **The assembled (M+1)-round STIR Vector IOPP** — the protocol object that the `∃ π` of
`stir_main` / `stir_rbr_soundness` quantifies over, with the `stirVSpec` wire shape. -/
noncomputable def stirMultiRoundIOP (M : ℕ) (φ : ι ↪ F) (deg : ℕ) :
    VectorIOP Unit (OracleStatement ι F) Unit (stirMultiVSpec M ι) F where
  prover := stirMultiRoundProver M φ deg
  verifier := stirMultiRoundVerifier M

section Instances

variable {M : ℕ}

/-- Local `VCVCompatible` packaging of the ambient `Field`/`Fintype`/`DecidableEq` data
(needed for `Fintype (Vector F n)` on the challenge ranges). -/
instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-- Finiteness of the multi-round challenge oracle spec (every challenge range is
`Vector F len`), pinned to the canonical `challengeOracleInterface` (the interface that the
completeness machinery elaborates `[pSpec.Challenge]ₒ` with). -/
instance :
    ([((stirMultiVSpec M ι).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).Fintype where
  fintype_B := fun q => by
    show Fintype (((stirMultiVSpec M ι).toProtocolSpec F).Challenge q.1)
    dsimp
    infer_instance

/-- Inhabitedness of the multi-round challenge oracle spec (pinned as above). -/
instance :
    ([((stirMultiVSpec M ι).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).Inhabited
    where
  inhabited_B := fun q => by
    show Inhabited (((stirMultiVSpec M ι).toProtocolSpec F).Challenge q.1)
    dsimp
    infer_instance

end Instances

section Completeness

open OracleReduction

variable [Nonempty ι]

set_option maxHeartbeats 1000000 in
/-- **Perfect completeness of the assembled (M+1)-round STIR Vector IOPP**, for arbitrary
depth `M` and arbitrary input relation: on the honest run the prover's output is acceptance
and the always-forwarding verifier accepts, so the accept/reject output relation holds with
probability one. (The genuine fold messages are exercised but not inspected — the verifier's
checks are the open soundness side.) -/
theorem stirMultiRoundIOP_perfectCompleteness (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (relIn : Set ((Unit × ∀ i, OracleStatement ι F i) × Unit)) :
    OracleReduction.perfectCompleteness (pure ()) isEmptyElim relIn acceptRejectOracleRel
      (stirMultiRoundIOP M φ deg) := by
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness
    (reduction := stirMultiRoundIOP M φ deg) relIn acceptRejectOracleRel (pure ()) isEmptyElim
    inferInstance
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirMultiRoundIOP, stirMultiRoundProver, stirMultiRoundVerifier,
    OracleVerifier.toVerifier]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure, OptionT.simulateQ_pure]
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
        Set.mem_setOf_eq, not_exists, not_and, exists_const, not_false_eq_true, add_zero,
        zero_add]
      intro y hy
      erw [OptionT.simulateQ_pure, OptionT.run_pure] at hy
      simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy
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
    have hfn : ∀ (f g : ∀ _ : Empty, Unit), f = g := fun _ _ => funext fun i => i.elim
    refine ⟨?_, rfl, hfn _ _⟩
    simp only [acceptRejectOracleRel, Set.mem_singleton_iff, Prod.mk.injEq]

end Completeness

section Security

open VectorIOP

variable [Nonempty ι]

/-- **SHELL-verifier residual — LIKELY FALSE for sub-1 budgets; superseded.**  Round-by-round
knowledge soundness of the multi-round STIR verifier with respect to the δ-far soundness
relation — but for the SHELL verifier (`verify = pure true`), which accepts everything, so no
nontrivial rbr budget can be discharged (see the warning at `stirCheckingRbrSoundnessResidual`,
`CheckingVerifier.lean`).  The genuine open obligation of #301 lives on the CHECKING verifier:
`stirCheckingRbrSoundnessResidual` + `stirCheckingCABridge` (`CheckingVerifier.lean`).  This def
is retained only because `stirMultiRoundIOP_isSecureWithGap` below is general wiring over it;
do not try to discharge it at a sub-1 budget.  Consumed as a hypothesis below; NOT fabricated. -/
def stirMultiRoundRbrSoundnessResidual (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0) : Prop :=
  OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
    (stirRelation deg φ δ) (stirMultiRoundIOP M φ deg).verifier ε_rbr

/-- The assembled multi-round STIR IOPP is `IsSecureWithGap`, given the (open) rbr-soundness
residual: the completeness leg is the proven `stirMultiRoundIOP_perfectCompleteness`. -/
theorem stirMultiRoundIOP_isSecureWithGap (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hSound : stirMultiRoundRbrSoundnessResidual M φ deg δ ε_rbr) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirMultiRoundIOP M φ deg) where
  is_complete := stirMultiRoundIOP_perfectCompleteness M φ deg _
  is_rbr_knowledge_sound := hSound

end Security

end MultiRound

section FrontDoors

open MultiRound VectorIOP LinearCode ReedSolomon STIR NNReal Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- **Lemma 5.4 general wiring**: any secure-with-gap vector IOP over the STIR multi-round
shape `stirMultiVSpec M (ι 0)` (whose challenge count is `2M + 2` by the landed
`stirVSpec_card_challengeIdx`) discharges the `stir_rbr_soundness` existential, given the
per-round error-bound legs. `CheckingVerifier.lean` supplies the checking-verifier
instantiation of this general wiring, conditional on its named soundness bridge. -/
theorem stir_rbr_soundness_of_secure_vectorIOP
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    {s : ℕ} {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι P Dist}
    (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) P.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j)))))
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (π : VectorIOP Unit (OracleStatement (ι 0) F) Unit (stirMultiVSpec M (ι 0)) F)
    (hSecure : IsSecureWithGap
      (stirRelation (degree ι P 0) (P.φ 0) 0)
      (stirRelation (degree ι P 0) (P.φ 0) (Dist.δ 0))
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
      π)
    (hfold : ε_fold ≤ proximityError F (P.deg / P.foldingParam 0)
      (rate (code (P.φ 0) P.deg)) (Dist.δ 0) (P.repeatParam 0))
    (hrest : ∀ j : Fin M,
        (ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s)
        ∧
        (ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc) +
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc) + s +
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.succ))
        ∧
        ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M))) :
    stir_rbr_soundness (s := s) (hParams := hParams) (Codes := Codes)
      ι hδ₀ hδᵢ ε_fold ε_out ε_shift ε_fin :=
  ⟨3 * M + 3, stirMultiVSpec M (ι 0), stirVSpec_card_challengeIdx, π, hSecure,
    hfold, hrest⟩

/-- **Lemma 5.4 front door (#301, mechanical track)**: `stir_rbr_soundness` instantiated with
the assembled multi-round object. The existential witnesses are fully constructed —
`n := 3M + 3`, `vPSpec := stirMultiVSpec M (ι 0)` (challenge count `2M + 2` by the landed
`stirVSpec_card_challengeIdx`), `π := stirMultiRoundIOP` — and the completeness leg of
`IsSecureWithGap` is proven. The genuinely open legs are consumed as hypotheses:
the rbr-soundness residual (`hSound`, Johnson-CA-gated) and the per-round error bounds
(`hfold`/`hrest`, statements about the free parameters `ε_fold/ε_out/ε_shift/ε_fin`). -/
theorem stir_rbr_soundness_of_residuals
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    {s : ℕ} {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι P Dist}
    (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) P.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j)))))
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    -- the open rbr-soundness residual, at the statement's prescribed `ε_rbr`
    (hSound : stirMultiRoundRbrSoundnessResidual M (P.φ 0) (degree ι P 0) (Dist.δ 0)
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp)))
    -- the open per-round error-bound legs (free-parameter constraints)
    (hfold : ε_fold ≤ proximityError F (P.deg / P.foldingParam 0)
      (rate (code (P.φ 0) P.deg)) (Dist.δ 0) (P.repeatParam 0))
    (hrest : ∀ j : Fin M,
        (ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s)
        ∧
        (ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc) +
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc) + s +
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.succ))
        ∧
        ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M))) :
    stir_rbr_soundness (s := s) (hParams := hParams) (Codes := Codes)
      ι hδ₀ hδᵢ ε_fold ε_out ε_shift ε_fin :=
  stir_rbr_soundness_of_secure_vectorIOP (hParams := hParams) (Codes := Codes)
    ι hδ₀ hδᵢ ε_fold ε_out ε_shift ε_fin
    (stirMultiRoundIOP M (P.φ 0) (degree ι P 0))
    (stirMultiRoundIOP_isSecureWithGap M (P.φ 0) (degree ι P 0) (Dist.δ 0) _ hSound)
    hfold hrest

/-- **Theorem 5.1 general wiring**: any secure-with-gap vector IOP over the STIR multi-round
shape discharges the `stir_main` existential, given the rbr error bound and the complexity
legs (which are constraints on universally-quantified inputs of the statement, not
consequences of the construction). A future checking verifier slots in here directly. -/
theorem stir_main_of_secure_vectorIOP
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (π : VectorIOP Unit (OracleStatement ι F) Unit (stirMultiVSpec M ι) F)
    (hSecure : IsSecureWithGap (stirRelation degree φ 0) (stirRelation degree φ δ) ε_rbr π)
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF := by
  obtain ⟨c, hc, hMle⟩ := hM
  obtain ⟨cₖ, hLenle⟩ := hLen
  obtain ⟨cₖ', hQle⟩ := hQpf
  exact ⟨3 * M + 3, stirMultiVSpec M ι, ε_rbr, π, hSecure,
    fun i => ⟨hε i, c, hc, hMle, cₖ, hLenle, hQin, cₖ', hQle⟩⟩

/-- **Theorem 5.1 front door (#301, mechanical track)**: `stir_main` instantiated with the
assembled multi-round object (`n := 3M + 3`, `vPSpec := stirMultiVSpec M ι`,
`π := stirMultiRoundIOP M φ degree`), with the completeness leg of `IsSecureWithGap` proven.
Consumed as hypotheses (the genuinely open legs): the rbr-soundness residual (`hSound`,
Johnson-CA-gated), the rbr error bound (`hε`), and the complexity claims about the free
parameters `M`/`proofLen`/`qNumtoInput`/`qNumtoProofstr` (`hM`/`hLen`/`hQin`/`hQpf`). -/
theorem stir_main_of_residuals
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hSound : stirMultiRoundRbrSoundnessResidual M φ degree δ ε_rbr)
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_secure_vectorIOP secpar hk hkGe δ hδub hF ε_rbr
    (stirMultiRoundIOP M φ degree)
    (stirMultiRoundIOP_isSecureWithGap M φ degree δ ε_rbr hSound)
    hε hM hLen hQin hQpf

end FrontDoors

end StirIOP

/-! ### Axiom audit (#301) -/

#print axioms StirIOP.MultiRound.stirMultiRoundIOP
#print axioms StirIOP.MultiRound.stirMultiRoundIOP_perfectCompleteness
#print axioms StirIOP.MultiRound.stirMultiRoundIOP_isSecureWithGap
#print axioms StirIOP.stir_rbr_soundness_of_secure_vectorIOP
#print axioms StirIOP.stir_rbr_soundness_of_residuals
#print axioms StirIOP.stir_main_of_secure_vectorIOP
#print axioms StirIOP.stir_main_of_residuals
