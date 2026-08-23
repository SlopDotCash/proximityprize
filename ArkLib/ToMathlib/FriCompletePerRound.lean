/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriComplete
import ArkLib.ProofSystem.Whir.FoldRound

/-!
# FRI: per-round perfect completeness — discharging the Brick A/B residuals (issue #117)

This module **discharges** the named per-round FRI perfect-completeness residuals from
`ArkLib.ToMathlib.FriComplete`:

* `foldRoundPerfectCompletenessResidual_holds` : the honest non-final folding round
  `FoldPhase.foldOracleReduction` is perfectly complete w.r.t. the FRI per-round
  input/output relations, given `hInit : NeverFail init`.

The proof mirrors the proven WHIR sibling `WhirIOP.FoldRound.foldOracleReduction_perfectCompleteness`
(same `[V_to_P, P_to_V]` round shape): unroll the 2-message run via the generic
`WhirIOP.FoldRound.unroll_2_message_VP` keystone, observe that prover and (`guard`-free) verifier
are `pure` chains so the run never fails, and check the unique reachable output against
`FoldPhase.outputRelation`. The algebraic content is:
* the folded witness `cpolyFold witIn (2^(s i)) α` has the round-`(i+1)` degree bound
  (`witness_lift`, proven in `Fri/Spec/SingleRound.lean`), so its evaluation on the round-`(i+1)`
  domain is a Reed–Solomon codeword — proximity clause `(1)` holds with distance `0`;
* the input witness itself witnesses the folding-consistency clause `(2)`;
* the oracle-consistency clause `(3)` is definitional for the honest prover.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ### Challenge oracle-spec instances for the fold round -/

instance instFoldChallengeSpecFintype {i : Fin k} :
    [(FoldPhase.pSpec s (ω := ω) i).Challenge]ₒ.Fintype where
  fintype_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by
      cases iv using Fin.cases with
      | zero => rfl
      | succ j1 => cases j1 using Fin.cases with
        | zero => simp [FoldPhase.pSpec] at hiv
        | succ j2 => exact j2.elim0
    subst h0
    simpa [FoldPhase.pSpec, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (inferInstance : Fintype F)

instance instFoldChallengeSpecInhabited {i : Fin k} :
    [(FoldPhase.pSpec s (ω := ω) i).Challenge]ₒ.Inhabited where
  inhabited_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by
      cases iv using Fin.cases with
      | zero => rfl
      | succ j1 => cases j1 using Fin.cases with
        | zero => simp [FoldPhase.pSpec] at hiv
        | succ j2 => exact j2.elim0
    subst h0
    simpa [FoldPhase.pSpec, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (⟨(0 : F)⟩ : Inhabited F)

/-! ### Reed–Solomon membership and distance helpers -/

/-- The evaluation of a `CompPoly` polynomial of (computable) degree `< D` on any embedded domain
is a Reed–Solomon codeword of degree bound `D`. -/
lemma eval_mem_code {ι : Type} [Fintype ι] {D : ℕ} (dom : ι ↪ F)
    (p : CompPoly.CPolynomial F) (hp : p ∈ CompPoly.CPolynomial.degreeLT (R := F) D) :
    (fun idx => p.eval (dom idx)) ∈ (_root_.ReedSolomon.code dom D : Set (ι → F)) := by
  refine Submodule.mem_map.mpr ⟨p.toPoly, CompPoly.CPolynomial.degreeLT_toPoly.mp hp, ?_⟩
  funext idx
  exact (CompPoly.CPolynomial.eval_toPoly (dom idx) p).symm

/-- A vector in the code has relative distance `0 ≤ δ` from it (power-of-two index version,
as used by the FRI evaluation domains). -/
lemma relDistFromCode_le_of_mem {m : ℕ} {f : Fin (2 ^ m) → F}
    {C : Set (Fin (2 ^ m) → F)} (hf : f ∈ C) (δ : ℝ≥0) :
    δᵣ(f, C) ≤ (δ : ENNReal) := by
  haveI : Nonempty (Fin (2 ^ m)) := Fin.pos_iff_nonempty.mp (Nat.two_pow_pos _)
  refine le_trans (Code.relDistFromCode_le_relDist_to_mem f f hf) ?_
  refine le_trans (le_of_eq ?_) (zero_le _)
  rw [Code.relHammingDist, hammingDist_self]
  simp only [Nat.cast_zero, zero_div]
  rw [← ENNReal.coe_nnratCast]
  simp only [NNRat.cast_zero, ENNReal.coe_zero]

/-- Evaluating `Fin.append u ![a]`-style singleton appends at the last index. -/
private lemma append_singleton_last {m : ℕ} {α : Type} (u : Fin m → α) (a : α) (h : m < m + 1) :
    Fin.append u (fun _ : Fin 1 => a) ⟨m, h⟩ = a := by
  have hidx : (⟨m, h⟩ : Fin (m + 1)) = Fin.natAdd m 0 := by ext; simp
  rw [hidx, Fin.append_right]

/-- `append_singleton_last`, keyed on the index *value* instead of the literal `⟨m, h⟩`
(so it rewrites when the index is e.g. `⟨↑i, _⟩ : Fin (↑i.castSucc + 1)`). -/
private lemma append_singleton_val {m : ℕ} {α : Type} (u : Fin m → α) (a : α)
    (j : Fin (m + 1)) (hj : (j : ℕ) = m) :
    Fin.append u (fun _ : Fin 1 => a) j = a := by
  have hidx : j = ⟨m, by omega⟩ := Fin.ext hj
  rw [hidx]
  exact append_singleton_last u a (by omega)

/-- Spec-lifting an `OptionT`-level `pure` is `pure` (definitional); cf. the WHIR sibling
`liftComp_optionT_pure` (`Whir/ThresholdKSF.lean`). -/
private lemma liftComp_optionT_pure {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} [MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)]
    {α : Type} (y : α) :
    (OracleComp.liftComp (pure y : OptionT (OracleComp spec₁) α) spec₂ :
      OptionT (OracleComp spec₂) α) = pure y := rfl

/-- Transport collapse for the `Sum.inr` branch of the `toVerifier` oracle routing
(local copy of the Binius `verifier_inr_transport_heq` idiom). -/
private lemma verifier_inr_transport_heq' {m : ℕ} {pSpec : ProtocolSpec m}
    {ιsi ιso : Type} {OStmtIn : ιsi → Type} {OStmtOut : ιso → Type}
    (embed : ιso ↪ ιsi ⊕ pSpec.MessageIdx)
    (hTypes : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    {idx : ιso} {msgIdx : pSpec.MessageIdx}
    (h : embed idx = Sum.inr msgIdx) (x : pSpec.Message msgIdx) :
    HEq ((hTypes idx ▸ h ▸ x : OStmtOut idx)) x := by
  refine (eqRec_heq (φ := fun T : Type => T) (hTypes idx).symm (h ▸ x)).trans ?_
  rw [eqRec_eq_cast]
  exact cast_heq _ x

/-! ### Brick A/B — non-final folding round: residual discharged -/

set_option maxHeartbeats 4000000 in
/-- **Brick A/B — non-final folding round perfect completeness (residual DISCHARGED).** -/
theorem foldRoundPerfectCompletenessResidual_holds
    (hInit : NeverFail init) (i : Fin k)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0) :
    foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i cond δ := by
  classical
  unfold foldRoundPerfectCompletenessResidual
  rw [WhirIOP.FoldRound.unroll_2_message_VP
    (FoldPhase.foldOracleReduction s d i (ω := ω))
    (FoldPhase.inputRelation s (ω := ω) d i cond δ)
    (FoldPhase.outputRelation s (ω := ω) d i cond δ)
    init impl hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [FoldPhase.foldOracleReduction, FoldPhase.foldProver, FoldPhase.foldVerifier,
    OracleVerifier.toVerifier]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_optionT_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun r0 _hr0 => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun prvOut _hprv => ?_⟩
      · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
          _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
      · rw [probFailure_map, OptionT.probFailure_liftComp_of_OracleComp_Option]
        simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
          Function.comp_apply, Option.map_some, probFailure_map, HasEvalPMF.probFailure_eq_zero,
          probOutput_eq_zero_iff, support_map, support_liftM, Set.mem_image, reduceCtorEq,
          Set.mem_setOf_eq, not_exists, not_and, exists_const, not_false_eq_true, add_zero,
          zero_add]
        intro x hx
        erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        simp only [Option.map_some, reduceCtorEq, not_false_eq_true]
  · -- CORRECTNESS: every output in the support satisfies the relation + agreement
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨r0, _hr0, hx⟩ := hx
    simp only [OptionT.support_liftM, support_liftM, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop, exists_eq_left] at hx
    obtain ⟨prvOut, hprvOut, hx⟩ := hx
    simp only [_root_.support_liftComp, support_pure, Set.mem_singleton_iff] at hprvOut
    subst hprvOut
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    refine ⟨?_, ?_, ?_⟩
    · -- output relation
      obtain ⟨⟨hδpos, hprox⟩, hbind⟩ := h_relIn
      -- The routed output oracle at the last index is the fresh fold message (proved once,
      -- consumed by clauses (1) and (3); `mkVerifierOStmtOut` is defeq to the `toVerifier`
      -- inlined routing match, sharing its auto-generated matcher).
      have hroute : OracleVerifier.mkVerifierOStmtOut
          (FoldPhase.foldVerifier s (ω := ω) i).embed
          (FoldPhase.foldVerifier s (ω := ω) i).hEq
          oStmtIn
          (FullTranscript.mk2 r0 (fun x =>
            CompPoly.CPolynomial.eval ((↑x : F))
              (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
                ((↑(id ((stmtIn, oStmtIn), witIn)).2 : CompPoly.CPolynomial F))
                (2 ^ ((s i.castSucc) : ℕ)) ((r0 : F)))))
          (Fin.last ((i.succ : Fin (k + 1)) : ℕ))
        = (FullTranscript.mk2 r0 (fun x =>
            CompPoly.CPolynomial.eval ((↑x : F))
              (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
                ((↑(id ((stmtIn, oStmtIn), witIn)).2 : CompPoly.CPolynomial F))
                (2 ^ ((s i.castSucc) : ℕ)) ((r0 : F))))).messages ⟨1, rfl⟩ := by
        refine Eq.trans
          (OracleVerifier.mkVerifierOStmtOut_inr
            (FoldPhase.foldVerifier s (ω := ω) i).embed
            (FoldPhase.foldVerifier s (ω := ω) i).hEq
            oStmtIn
            (FullTranscript.mk2 r0 (fun x =>
              CompPoly.CPolynomial.eval ((↑x : F))
                (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
                  ((↑(id ((stmtIn, oStmtIn), witIn)).2 : CompPoly.CPolynomial F))
                  (2 ^ ((s i.castSucc) : ℕ)) ((r0 : F)))))
            (Fin.last ((i.succ : Fin (k + 1)) : ℕ))
            ⟨1, rfl⟩
            (dif_pos rfl)) ?_
        apply eq_of_heq
        refine HEq.trans (eqRec_heq (φ := fun T : Type => T)
          (((FoldPhase.foldVerifier s (ω := ω) i).hEq
            (Fin.last ((i.succ : Fin (k + 1)) : ℕ))).symm) _) ?_
        rw [eqRec_eq_cast]
        exact cast_heq _ _
      -- Routed output oracle at a previous index is the input oracle (inl branch).
      have hroutePrev : OracleVerifier.mkVerifierOStmtOut
          (FoldPhase.foldVerifier s (ω := ω) i).embed
          (FoldPhase.foldVerifier s (ω := ω) i).hEq
          oStmtIn
          (FullTranscript.mk2 r0 (fun x =>
            CompPoly.CPolynomial.eval ((↑x : F))
              (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
                ((↑(id ((stmtIn, oStmtIn), witIn)).2 : CompPoly.CPolynomial F))
                (2 ^ ((s i.castSucc) : ℕ)) ((r0 : F)))))
          ⟨((Fin.last ((i.castSucc : Fin (k + 1)) : ℕ)) : ℕ), by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ]; omega⟩
        = oStmtIn ⟨((Fin.last ((i.castSucc : Fin (k + 1)) : ℕ)) : ℕ), by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ]; omega⟩ := by
        refine Eq.trans
          (OracleVerifier.mkVerifierOStmtOut_inl
            (FoldPhase.foldVerifier s (ω := ω) i).embed
            (FoldPhase.foldVerifier s (ω := ω) i).hEq
            oStmtIn
            (FullTranscript.mk2 r0 (fun x =>
              CompPoly.CPolynomial.eval ((↑x : F))
                (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
                  ((↑(id ((stmtIn, oStmtIn), witIn)).2 : CompPoly.CPolynomial F))
                  (2 ^ ((s i.castSucc) : ℕ)) ((r0 : F)))))
            ⟨((Fin.last ((i.castSucc : Fin (k + 1)) : ℕ)) : ℕ), by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ]; omega⟩
            ⟨((Fin.last ((i.castSucc : Fin (k + 1)) : ℕ)) : ℕ), by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ]; omega⟩
            (dif_neg (by simp))) ?_
        apply eq_of_heq
        refine HEq.trans (eqRec_heq (φ := fun T : Type => T)
          (((FoldPhase.foldVerifier s (ω := ω) i).hEq _).symm) _) ?_
        rw [eqRec_eq_cast]
        exact cast_heq _ _
      refine ⟨⟨hδpos, ?_⟩, ⟨witIn, ?_, ?_⟩, ?_⟩
      · -- (1) proximity: the folded oracle is a codeword, distance 0
        have hmem := eval_mem_code (F := F)
          ⟨⇑(ω.subdomain (∑ j' ∈ finRangeTo (k + 1) ((i : ℕ) + 1), ((s j') : ℕ))),
            CosetFftDomainClass.injective _⟩
          (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold witIn.1 (2 ^ ((s i.castSucc) : ℕ)) r0)
          (witness_lift witIn.2)
        exact relDistFromCode_le_of_mem
          (Set.mem_of_eq_of_mem (funext fun idx => congrFun hroute _) hmem) δ
      · -- (2a) the input witness matches the routed previous-round oracle
        intro idx
        symm
        exact (congrFun hroutePrev _).trans (hbind idx)
      · -- (2b) the output witness is the fold of the input witness at the round challenge
        rw [Fin.vappend_eq_append, append_singleton_val _ _ _ (by simp)]
        rfl
      · -- (3) the output oracle is the evaluation of the output witness
        intro idx
        exact congrFun hroute _
    · -- prover statement = verifier statement
      show Fin.append stmtIn (fun _ => r0) = _
      rw [← Fin.vappend_eq_append]
      rfl
    · -- prover oracles = verifier oracles
      funext j
      apply eq_of_heq
      obtain ⟨jv, hjv⟩ := j
      simp only [Function.Embedding.coeFn_mk]
      by_cases hj : jv = (i : ℕ) + 1
      · subst hj
        rw [dif_neg (by omega)]
        split
        next j' h =>
          rw [dif_pos rfl] at h
          exact absurd h (by simp)
        next j₂ h =>
          rw [dif_pos rfl] at h
          have hj₂ : j₂ = ⟨1, by simp⟩ := (Sum.inr.inj h).symm
          subst hj₂
          simp only [eqRec_heq_iff_heq, heq_eqRec_iff_heq]
          exact heq_of_eq rfl
      · have hjlt : jv < (i : ℕ) + 1 := by
          simp only [Fin.val_succ] at hjv
          omega
        rw [dif_pos hjlt]
        split
        next j' h =>
          rw [dif_neg hj] at h
          have hj' : j' = ⟨jv, by simp only [Fin.val_castSucc]; omega⟩ := by
            apply Fin.ext
            exact (congrArg Fin.val (Sum.inl.inj h)).symm
          subst hj'
          simp only [eqRec_heq_iff_heq, heq_eqRec_iff_heq, eq_mp_eq_cast, eq_mpr_eq_cast,
            cast_heq_iff_heq, heq_cast_iff_heq]
          exact heq_of_eq rfl
        next j₂ h =>
          rw [dif_neg hj] at h
          exact absurd h (by simp)

end Fri.Spec.Completeness

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Fri.Spec.Completeness.foldRoundPerfectCompletenessResidual_holds
