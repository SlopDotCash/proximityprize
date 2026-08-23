/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriCompletePerRound
import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# FRI: final folding round perfect completeness — final Brick A/B residual DISCHARGED

This module **discharges** `finalFoldRoundPerfectCompletenessResidual` from
`ArkLib.ToMathlib.FriComplete`: the honest final folding round
`FinalFoldPhase.finalFoldOracleReduction` is perfectly complete w.r.t. the FRI final-round
input/output relations, given `hInit : NeverFail init`.

Structure (mirrors the proven non-final sibling
`foldRoundPerfectCompletenessResidual_holds` in `FriCompletePerRound.lean`):
* unroll the `[V_to_P, P_to_V]` run via `WhirIOP.FoldRound.unroll_2_message_VP`;
* SAFETY: the verifier's `getConst` query collapses through
  `RingSwitching.simulateQ_simOracle2_query` (`instDefault`: the response IS the in-the-clear
  polynomial), and the degree `guard` is discharged by `natDegree_lt_of_mem_degreeLT` applied
  to the folded witness's `Witness … (Fin.last (k+1))` bound (`degreeLT (2^0 * d) = d`);
* CORRECTNESS: the routed-oracle facts are HEq-stated against
  `OracleVerifier.mkVerifierOStmtOut` (defeq to the inlined `toVerifier` routing — shared
  matcher) and collapsed via `eqRec_heq`/`eqRec_eq_cast`/`cast_heq`; the prover's dite-built
  `FinalOracleStatement` output is reconciled per index against the verifier's routing by
  `split` (no over-application here: the final oracle entries are values, not functions),
  with `Eq.mpr`/`Eq.mp` casts killed by the `eqRec_heq_iff_heq`/`cast_heq_iff_heq` simp set.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- A `CPolynomial` in `degreeLT D` (for positive `D`) has `natDegree < D`. Bridges the FRI
final-round witness bound to the verifier's degree `guard`. -/
lemma natDegree_lt_of_mem_degreeLT {p : CompPoly.CPolynomial F} {D : ℕ} (hD : 0 < D)
    (hp : p ∈ CompPoly.CPolynomial.degreeLT (R := F) D) : p.natDegree < D := by
  rw [CompPoly.CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT] at hp
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  rcases eq_or_ne p.toPoly 0 with h0 | h0
  · simpa [h0] using hD
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hp)

/-! ### Challenge oracle-spec instances for the final fold round -/

instance instFinalFoldChallengeSpecFintype :
    [(FinalFoldPhase.pSpec F).Challenge]ₒ.Fintype where
  fintype_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by
      cases iv using Fin.cases with
      | zero => rfl
      | succ j1 => cases j1 using Fin.cases with
        | zero => simp [FinalFoldPhase.pSpec] at hiv
        | succ j2 => exact j2.elim0
    subst h0
    simpa [FinalFoldPhase.pSpec, challengeOracleInterface, ProtocolSpec.Challenge,
      ProtocolSpec.«Type», OracleInterface.Response, OracleInterface.toOC]
      using (inferInstance : Fintype F)

instance instFinalFoldChallengeSpecInhabited :
    [(FinalFoldPhase.pSpec F).Challenge]ₒ.Inhabited where
  inhabited_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by
      cases iv using Fin.cases with
      | zero => rfl
      | succ j1 => cases j1 using Fin.cases with
        | zero => simp [FinalFoldPhase.pSpec] at hiv
        | succ j2 => exact j2.elim0
    subst h0
    simpa [FinalFoldPhase.pSpec, challengeOracleInterface, ProtocolSpec.Challenge,
      ProtocolSpec.«Type», OracleInterface.Response, OracleInterface.toOC]
      using (⟨(0 : F)⟩ : Inhabited F)


/-- The default oracle interface answers its only (unit) query with the message itself
(local copy of `RingSwitching.BatchingPhase.answer_instDefault`). -/
@[simp] private lemma answer_instDefault' {M : Type _} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

/-- Evaluating `Fin.append u ![a]`-style singleton appends at an index with value `m`. -/
private lemma append_singleton_val' {m : ℕ} {α : Type} (u : Fin m → α) (a : α)
    (j : Fin (m + 1)) (hj : (j : ℕ) = m) :
    Fin.append u (fun _ : Fin 1 => a) j = a := by
  have hidx : j = ⟨m, by omega⟩ := Fin.ext hj
  rw [hidx]
  have hidx2 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.natAdd m 0 := by ext; simp
  rw [hidx2, Fin.append_right]

/-- The honestly folded final witness lies in `degreeLT d` (the `Fin.last (k+1)` bound has
zero exponent: the full `finRangeTo` window is `univ`). -/
private lemma finalFold_witness_degreeLT
    (witIn : ↥(Witness F s d (Fin.last k).castSucc)) (r0 : F) :
    CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
        (witIn : CompPoly.CPolynomial F) (2 ^ ((s (Fin.last k)) : ℕ)) r0
      ∈ CompPoly.CPolynomial.degreeLT (R := F) d := by
  have hmem := witness_lift (i := Fin.last k) (α := r0) witIn.2
  convert hmem using 2
  have hfull : finRangeTo (k + 1) ((Fin.last k).succ : ℕ)
      = (Finset.univ : Finset (Fin (k + 1))) := by
    apply Finset.eq_univ_of_forall
    intro x
    simp [finRangeTo, Fin.val_last, List.take_of_length_le, List.length_finRange]
  rw [hfull]
  simp

/-- The honestly folded final witness passes the final verifier's degree `guard`. -/
private lemma finalFold_guard_natDegree
    (witIn : ↥(Witness F s d (Fin.last k).castSucc)) (r0 : F) :
    (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
        (witIn : CompPoly.CPolynomial F) (2 ^ ((s (Fin.last k)) : ℕ)) r0).natDegree
      < (d : ℕ) :=
  natDegree_lt_of_mem_degreeLT d.pos (finalFold_witness_degreeLT witIn r0)

set_option maxHeartbeats 4000000 in
/-- **Brick A/B — final folding round perfect completeness (residual DISCHARGED).** -/
theorem finalFoldRoundPerfectCompletenessResidual_holds
    (hInit : NeverFail init)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0) :
    finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit cond δ := by
  classical
  unfold finalFoldRoundPerfectCompletenessResidual
  rw [WhirIOP.FoldRound.unroll_2_message_VP
    (FinalFoldPhase.finalFoldOracleReduction s d (ω := ω))
    (FinalFoldPhase.inputRelation s (ω := ω) d cond δ)
    (FinalFoldPhase.outputRelation s (ω := ω) d cond δ)
    init impl hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [FinalFoldPhase.finalFoldOracleReduction, FinalFoldPhase.finalFoldProver,
    FinalFoldPhase.finalFoldVerifier, OracleVerifier.toVerifier]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure, id_eq]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun r0 _hr0 => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · simp only [FinalFoldPhase.getConst]
      rw [simulateQ_optionT_bind]
      erw [RingSwitching.simulateQ_simOracle2_query]
      rw [answer_instDefault']
      have hg := finalFold_guard_natDegree (F := F) (s := s) (d := d) witIn r0
      simp only [OptionT.lift_pure, pure_bind, guard, hg, if_true, decide_true, ite_true,
        map_pure, probFailure_map, probFailure_bind_eq_zero_iff, OptionT.probFailure_liftM,
        OptionT.probFailure_lift, _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero,
        probFailure_pure]
      rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
      simp only [OptionT.run_map, OptionT.run_bind, OptionT.run_pure, Option.elimM, pure_bind,
        guard, hg, decide_true, ite_true, if_true, simulateQ_map, simulateQ_pure, map_pure,
        OptionT.run_monadLift, _root_.map_pure, probFailure_map, HasEvalPMF.probFailure_eq_zero,
        probFailure_pure, Option.map_some, Function.comp_apply]
      simp only [OptionT.run_pure, pure_bind, Option.elim_some, simulateQ_map, guard, hg,
        decide_true, ite_true, if_true, OptionT.run_map, simulateQ_pure, map_pure,
        Option.map_some, zero_add, probOutput_eq_zero_iff, support_map, support_pure,
        Set.mem_image, Set.mem_singleton_iff, reduceCtorEq, not_exists, not_and,
        exists_eq_left, and_false, not_false_eq_true]
      intro x hx
      erw [OptionT.run_pure] at hx
      simp only [pure_bind, Option.elim_some] at hx
      erw [if_pos hg] at hx
      erw [map_pure] at hx
      erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp only [Option.map_some, reduceCtorEq, not_false_eq_true]
  · -- CORRECTNESS: every output in the support satisfies the relation + agreement
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨r0, _hr0, hx⟩ := hx
    have hg := finalFold_guard_natDegree (F := F) (s := s) (d := d) witIn r0
    simp only [FinalFoldPhase.getConst] at hx
    rw [simulateQ_optionT_bind] at hx
    erw [RingSwitching.simulateQ_simOracle2_query] at hx
    rw [answer_instDefault'] at hx
    simp only [OptionT.lift_pure] at hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_map, OptionT.run_bind, OptionT.run_pure, Option.elimM, pure_bind,
      Option.elim_some, _root_.map_pure, Function.comp_apply] at hx
    erw [pure_bind] at hx
    simp only [guard] at hx
    erw [if_pos hg] at hx
    erw [map_pure] at hx
    simp only [OptionT.simulateQ_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.map_some, Option.some.injEq] at hx
    subst hx
    obtain ⟨⟨hδpos, hprox⟩, hbind⟩ := h_relIn
    -- Routed output oracle at the last index is the in-the-clear final polynomial.
    have hroute : HEq
        (OracleVerifier.mkVerifierOStmtOut
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).embed
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).hEq
          oStmtIn
          (FullTranscript.mk2 r0
            (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
              ((witIn : CompPoly.CPolynomial F)) (2 ^ ((s (Fin.last k)) : ℕ)) r0))
          (Fin.last (k + 1)))
        ((FullTranscript.mk2 (pSpec := FinalFoldPhase.pSpec F) r0
          (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
            ((witIn : CompPoly.CPolynomial F)) (2 ^ ((s (Fin.last k)) : ℕ)) r0)).messages
          ⟨1, rfl⟩) := by
      refine HEq.trans (heq_of_eq
        (OracleVerifier.mkVerifierOStmtOut_inr
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).embed
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).hEq
          oStmtIn
          (FullTranscript.mk2 r0
            (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
              ((witIn : CompPoly.CPolynomial F)) (2 ^ ((s (Fin.last k)) : ℕ)) r0))
          (Fin.last (k + 1))
          ⟨1, rfl⟩
          (dif_pos rfl))) ?_
      refine HEq.trans (eqRec_heq (φ := fun T : Type => T)
        (((FinalFoldPhase.finalFoldVerifier s d (ω := ω)).hEq (Fin.last (k + 1))).symm) _) ?_
      rw [eqRec_eq_cast]
      exact cast_heq _ _
    -- Routed output oracle at the previous (round-k) index is the carried input oracle.
    let jPrevOut : Fin (k + 2) :=
      ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_succ (k + 1))⟩
    have hroutePrev : ∀ (i : Fin (k + 2)) (hni : ¬ (i : ℕ) = k + 1), HEq
        (OracleVerifier.mkVerifierOStmtOut
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).embed
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).hEq
          oStmtIn
          (FullTranscript.mk2 r0
            (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
              ((witIn : CompPoly.CPolynomial F)) (2 ^ ((s (Fin.last k)) : ℕ)) r0))
          i)
        (oStmtIn ⟨(i : ℕ), by have := i.isLt; simp only [Fin.val_last]; omega⟩) := by
      intro i hni
      refine HEq.trans (heq_of_eq
        (OracleVerifier.mkVerifierOStmtOut_inl
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).embed
          (FinalFoldPhase.finalFoldVerifier s d (ω := ω)).hEq
          oStmtIn
          (FullTranscript.mk2 r0
            (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
              ((witIn : CompPoly.CPolynomial F)) (2 ^ ((s (Fin.last k)) : ℕ)) r0))
          i
          ⟨(i : ℕ), by have := i.isLt; simp only [Fin.val_last]; omega⟩
          (dif_neg hni))) ?_
      refine HEq.trans (eqRec_heq (φ := fun T : Type => T)
        (((FinalFoldPhase.finalFoldVerifier s d (ω := ω)).hEq i).symm) _) ?_
      rw [eqRec_eq_cast]
      exact cast_heq _ _
    refine ⟨?_, ?_, ?_⟩
    · -- output relation
      refine ⟨⟨hδpos, ?_⟩, witIn, ?_, ?_⟩
      · -- (1) plaintext match: the routed final oracle entry IS the folded witness
        exact cast_eq_iff_heq.mpr hroute
      · -- (2) the carried round-k oracle matches the input witness's evaluations
        intro idx
        refine Eq.trans ((hbind idx).symm) ?_
        exact congrFun (eq_of_heq ((cast_heq _ _).trans (hroutePrev ⟨k, by omega⟩ (by simp)))).symm _
      · -- (3) folding consistency at the verifier's challenge
        rw [append_singleton_val' _ _ _ (by simp)]
    · -- prover statement = verifier statement
      dsimp only
      rw [Fin.vappend_eq_append]
      refine congrArg (Fin.append stmtIn) ?_
      funext x
      fin_cases x
      rfl
    · -- prover oracle family = verifier oracle family
      dsimp only
      funext j
      apply eq_of_heq
      obtain ⟨jv, hjv⟩ := j
      simp only [Function.Embedding.coeFn_mk]
      by_cases hj : jv = k + 1
      · subst hj
        rw [dif_pos rfl]
        split
        next j' h =>
          rw [dif_pos rfl] at h
          exact absurd h (by simp)
        next j₂ h =>
          rw [dif_pos rfl] at h
          have hj₂ : j₂ = ⟨1, by simp⟩ := (Sum.inr.inj h).symm
          subst hj₂
          simp only [eqRec_heq_iff_heq, heq_eqRec_iff_heq, eq_mp_eq_cast, eq_mpr_eq_cast,
            cast_heq_iff_heq, heq_cast_iff_heq]
          exact HEq.rfl
      · have hjlt : jv < k + 1 := by
          omega
        rw [dif_neg hj]
        split
        next j' h =>
          rw [dif_neg hj] at h
          have hj' : j' = ⟨jv, hjlt⟩ := by
            apply Fin.ext
            exact (congrArg Fin.val (Sum.inl.inj h)).symm
          subst hj'
          simp only [eqRec_heq_iff_heq, heq_eqRec_iff_heq, eq_mp_eq_cast, eq_mpr_eq_cast,
            cast_heq_iff_heq, heq_cast_iff_heq]
          exact cast_heq _ _
        next j₂ h =>
          rw [dif_neg hj] at h
          exact absurd h (by simp)

end Fri.Spec.Completeness

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Fri.Spec.Completeness.finalFoldRoundPerfectCompletenessResidual_holds
