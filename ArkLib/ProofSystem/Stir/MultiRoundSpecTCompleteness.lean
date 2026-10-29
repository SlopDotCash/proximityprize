/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.MultiRoundSpecT

/-!
# Perfect completeness of the t-repetition checking STIR IOPP (#301, A1 part 4)

The honest prover's messages are challenge-independent, so the `t = 1` completeness
argument ports: on the support of every honest run prefix the carried context is the input
context and every transcript message is the honest packed fold of the input codeword
(= the packed input codeword, by `combine_single_self`); hence every one of the `t`-point
binding/consistency checks compares equal values, and the final full-read low-degree check
sees the input codeword, which the `δ = 0` relation forces into the code.

* `stirMultiRoundProverT_runToRound_invariant` — the run-support invariant (port);
* `checkingBoolT_honest` — the honest decision bit is `true` (all `t` coordinates pass);
* `stirCheckingIOPT_perfectCompleteness` — **perfect completeness of the t-repetition
  checking IOPP**, symbolic in both `M` and `t`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec OracleInterface STIR ReedSolomon NNReal
open WhirIOP.Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι]

private local instance : VCVCompatible F :=
  { toFintype := inferInstance, toInhabited := ⟨0⟩ }
private noncomputable local instance stirMultiTUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

/-! ## Instances (mirroring the `t = 1` `MultiRoundAssembly` packaging) -/

/-- Finiteness of the t-repetition challenge oracle spec (every range is `Vector F t`). -/
instance instStirMultiTChallengeRangeFintype {M t : ℕ} :
    ∀ q, Fintype (([((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).Range q) :=
  fun q => by
    show Fintype (((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge q.1)
    dsimp
    infer_instance

/-- Inhabitedness of the t-repetition challenge oracle spec. -/
instance instStirMultiTChallengeRangeInhabited {M t : ℕ} :
    ∀ q, Inhabited (([((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).Range q) :=
  fun q => by
    show Inhabited (((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge q.1)
    dsimp
    infer_instance

/-! ## The run-support invariant -/

/-- The honest packed message at a message round of the t-repetition wire. -/
noncomputable def honestMsgT (M t : ℕ) (f : ι → F) (iv : ℕ) (h : iv < 3 * M + 3)
    (hdir : iv % 3 = 1) : Vector F ((stirMultiVSpecT M ι t).length ⟨iv, h⟩) :=
  Vector.cast (stirMultiVSpecT_length_msg (ι := ι) (F := F) (M := M) (t := t)
    ⟨⟨iv, h⟩, by
      show (stirMultiVSpecT M ι t).dir _ = .P_to_V
      rw [show (stirMultiVSpecT M ι t).dir ⟨iv, h⟩
        = (stirVSpec M (fun _ => Fintype.card ι) t).dir ⟨iv, h⟩ from rfl,
        stirVSpec_dir_eq_msg_iff]
      exact hdir⟩)
    (packFiniteFunction ι f)

/-- **Run-support invariant of the honest t-repetition prover** (port of the `t = 1`
invariant; the prover's strategy is challenge-length-agnostic). -/
theorem stirMultiRoundProverT_runToRound_invariant (M : ℕ) (φ : ι ↪ F) (deg t : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (k : Fin (3 * M + 3 + 1)) :
    ∀ ts ∈ support
      ((stirMultiRoundProverT M φ deg t).runToRound k stmtIn witIn),
      ts.2.1 = (stmtIn, witIn) ∧
      ∀ (iv : ℕ) (hik : iv < k.val) (hdir : iv % 3 = 1),
        ts.1 ⟨iv, hik⟩ = honestMsgT M t (stmtIn.2 ()) iv
          (by have := k.isLt; omega) hdir := by
  induction k using Fin.induction with
  | zero =>
      intro ts hts
      rw [Prover.runToRound_zero_of_prover_first] at hts
      simp only [support_pure, Set.mem_singleton_iff] at hts
      subst hts
      exact ⟨rfl, fun iv hik _ => absurd hik (Nat.not_lt_zero iv)⟩
  | succ j ih =>
      intro ts hts
      rw [Prover.runToRound_succ] at hts
      unfold Prover.processRound at hts
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hts
      obtain ⟨⟨tr, st⟩, hprev, hout⟩ := hts
      obtain ⟨ihSt, ihTr⟩ := ih ⟨tr, st⟩ hprev
      split at hout
      · -- challenge (V_to_P) round
        rename_i hDir
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hout
        obtain ⟨chal, -, fch, hfch, rfl⟩ := hout
        have hfch' : fch = fun r => (st.1,
            if h : 0 < (stirMultiVSpecT M ι t).length ⟨(j : ℕ), j.isLt⟩
            then r.get ⟨0, h⟩ else 0) := by
          dsimp only [stirMultiRoundProverT] at hfch
          set_option backward.isDefEq.respectTransparency false in
            simpa only [liftM_pure, support_pure, Set.mem_singleton_iff] using hfch
        refine ⟨by rw [hfch']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpecT M ι t).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr chal (Fin.castSucc ⟨iv, hlt⟩) = _
          set_option backward.isDefEq.respectTransparency false in
            rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · exfalso
          have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          replace hDir : (stirVSpec M (fun _ => Fintype.card ι) t).dir j = .V_to_P := hDir
          rw [stirVSpec_dir_eq_chal_iff] at hDir
          exact hDir hdir
      · -- message (P_to_V) round
        rename_i hDir
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hout
        obtain ⟨⟨msg, st'⟩, hms, rfl⟩ := hout
        have hms' : msg = Vector.cast (stirMultiVSpecT_length_msg ⟨j, hDir⟩)
            (packFiniteFunction ι
              (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ())
                (fun _ : Fin 1 => deg))) ∧ st' = st := by
          dsimp only [stirMultiRoundProverT] at hms
          simp only [liftM_pure, liftComp_pure, support_pure] at hms
          exact Prod.ext_iff.mp (Set.mem_singleton_iff.mp hms)
        obtain ⟨hmsg, hst'⟩ := hms'
        refine ⟨by rw [hst']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpecT M ι t).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.castSucc ⟨iv, hlt⟩) = _
          set_option backward.isDefEq.respectTransparency false in
            rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          letI : DecidableEq ι := Classical.decEq ι
          show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpecT M ι t).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.last (j : ℕ)) = _
          set_option backward.isDefEq.respectTransparency false in
            rw [Fin.snoc_last, hmsg, ihSt]
          show Vector.cast _ (packFiniteFunction ι
            (Combine.combine φ deg st.2 (fun _ : Fin 1 => stmtIn.2 ())
              (fun _ : Fin 1 => deg))) = _
          rw [Round.combine_single_self]
          rfl

/-! ## The honest checks pass -/

/-- Answer of the honest packed t-repetition message oracle. -/
theorem answer_honest_packT (M t : ℕ) (f : ι → F)
    (j : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecT M ι t).length j.1)) :
    OracleInterface.answer
      ((Vector.cast (stirMultiVSpecT_length_msg j) (packFiniteFunction ι f)
        : Vector F ((stirMultiVSpecT M ι t).length j.1))
        : ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j) k
      = f ((Fintype.equivFin ι).symm ⟨(k : ℕ),
          lt_of_lt_of_eq k.isLt (stirMultiVSpecT_length_msg j).symm⟩) := by
  show (Vector.cast (stirMultiVSpecT_length_msg j) (packFiniteFunction ι f))[(k : ℕ)] = _
  rw [Vector.getElem_cast, packFiniteFunction, Vector.getElem_ofFn]

variable (M : ℕ) (φ : ι ↪ F) (deg t : ℕ)

open scoped Classical in
/-- **The honest prover passes every t-point check.** -/
theorem checkingBoolT_honest (f : ι → F) (hmem : f ∈ ReedSolomon.code φ deg)
    (oStmt : ∀ i, OracleStatement ι F i) (hOStmt : oStmt () = f)
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j)
    (hmsgs : ∀ j, msgs j
      = Vector.cast (stirMultiVSpecT_length_msg j) (packFiniteFunction ι f))
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges) :
    checkingBoolT M φ deg t oStmt msgs chals = true := by
  have hans : ∀ (j) (x : ι), msgAnsT msgs j (msgPosT M t j x) = f x := by
    intro j x
    rw [msgAnsT, hmsgs j, answer_honest_packT]
    show f ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)) = f x
    rw [Equiv.symm_apply_apply]
  have hfin : ∀ k : Fin (Fintype.card ι),
      msgAnsT msgs (msgIdxT M t (Fin.last M))
        (Fin.cast (stirMultiVSpecT_length_msg (msgIdxT M t (Fin.last M))) k)
      = f ((Fintype.equivFin ι).symm k) := by
    intro k
    rw [msgAnsT, hmsgs _, answer_honest_packT]
    rfl
  unfold checkingBoolT
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the t binding checks
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨j', -, rfl⟩ := hb
    simp only [inputAns, hOStmt, hans, decide_eq_true_eq]
    rfl
  · -- the per-round t-point consistency checks
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨j, -, rfl⟩ := hb
    rw [List.all_eq_true]
    intro b' hb'
    rw [List.mem_map] at hb'
    obtain ⟨j', -, rfl⟩ := hb'
    simp only [hans, Bool.and_eq_true, decide_eq_true_eq, and_self]
  · -- the final low-degree check
    have hfun : (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAnsT msgs (msgIdxT M t (Fin.last M))
            (Fin.cast (stirMultiVSpecT_length_msg (msgIdxT M t (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0)) = f := by
      funext x
      rw [List.getD_eq_getElem _ _ (by
        simp only [List.length_map, List.length_finRange]
        exact (Fintype.equivFin ι x).isLt)]
      rw [List.getElem_map, List.getElem_finRange, hfin]
      simp only [Fin.cast_mk, Fin.eta, Equiv.symm_apply_apply]
    rw [hfun]
    exact hmem

/-! ## The verifier collapse -/

open scoped Classical in
/-- `simulateQ` collapse of the t-point checking computation at the `OptionT` layer. -/
theorem simulateQ_lift_checkingCompT
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges) :
    (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (OptionT.lift (checkingCompT M φ deg t chals)) : OptionT (OracleComp []ₒ) Bool)
      = pure (checkingBoolT M φ deg t oStmt msgs chals) := by
  show (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (checkingCompT M φ deg t chals
        >>= fun b => (pure (some b) : OracleComp _ (Option Bool)))
      : OracleComp []ₒ (Option Bool))
    = pure (some (checkingBoolT M φ deg t oStmt msgs chals))
  rw [simulateQ_bind, simulateQ_checkingCompT]
  simp

open scoped Classical in
/-- Pure form of the t-point checking verifier's non-oracle run. -/
theorem checkingVerifierT_toVerifier_verify
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpecT M ι t).toProtocolSpec F)) :
    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i) (stirCheckingVerifierT M φ deg t)).verify stmtIn tr
      = pure (checkingBoolT M φ deg t stmtIn.2 tr.messages tr.challenges,
          fun i : Empty => i.elim) := by
  dsimp only [OracleVerifier.toVerifier, stirCheckingVerifierT]
  erw [simulateQ_lift_checkingCompT, pure_bind]
  apply OptionT.ext
  simp only [OptionT.run_mk, LawfulApplicative.map_pure, Option.map_some, OptionT.run_pure]

/-! ## Perfect completeness -/

open OracleReduction in
open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **Perfect completeness of the t-repetition checking STIR IOPP** (symbolic `M`, `t`). -/
theorem stirCheckingIOPT_perfectCompleteness :
    OracleReduction.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i) (pure ()) isEmptyElim
      (stirRelation deg φ 0) acceptRejectOracleRel (stirCheckingIOPT M φ deg t) := by
  letI : Inhabited F := ⟨0⟩
  letI : ∀ q, Fintype (([((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge]ₒ' ProtocolSpec.challengeOracleInterface).Range q) :=
    fun ⟨i, _⟩ => by
      change Fintype (((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge i)
      dsimp [ProtocolSpec.Challenge]
      infer_instance
  letI : ∀ q, Inhabited (([((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge]ₒ' ProtocolSpec.challengeOracleInterface).Range q) :=
    fun ⟨i, _⟩ => by
      change Inhabited (((stirMultiVSpecT M ι t).toProtocolSpec F).Challenge i)
      dsimp [ProtocolSpec.Challenge]
      infer_instance
  -- Supply the vacuous output interface before elaborating the native unroll lemma.
  rw [@OracleReduction.unroll_n_message_reduction_perfectCompleteness
    _ _ _ _ _ _ _ _ _ Empty _ (fun _ : Empty => Unit) _ (fun i => nomatch i)
    _ _ _ _ _ (stirCheckingIOPT M φ deg t) (stirRelation deg φ 0) acceptRejectOracleRel
    (pure ()) isEmptyElim (OracleComp.prFail_eq_zero _)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- the δ = 0 input relation is genuine code membership
  have hmem : oStmtIn () ∈ ReedSolomon.code φ deg := by
    have h0 : Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg)
        ≤ ((0 : ℝ≥0) : ENNReal) := h_relIn
    exact mem_of_relDistFromCode_le_zero ⟨0, Submodule.zero_mem _⟩ (by simpa using h0)
  have hverify (tr : Transcript (Fin.last (3 * M + 3))
      ((stirMultiVSpecT M ι t).toProtocolSpec F)) :
      (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
        (stirCheckingVerifierT M φ deg t)).verify (stmtIn, oStmtIn) tr =
        pure (checkingBoolT M φ deg t oStmtIn (FullTranscript.messages tr)
          (FullTranscript.challenges tr), fun i : Empty => i.elim) :=
    checkingVerifierT_toVerifier_verify M φ deg t (stmtIn, oStmtIn) tr
  dsimp only [stirCheckingIOPT, stirMultiRoundProverT]
  simp only [hverify]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, _root_.map_pure, liftComp_pure, liftM_pure]
  apply (OptionT.prEvent_mk_eq_one_iff _ _).2
  intro x hx
  have hopt {κ : Type} {spec : OracleSpec.{0, 0} κ} {β : Type} (mx : OracleComp spec β) :
      (liftM mx : OptionT (OracleComp spec) β) = some <$> mx := by
    change (mx >>= fun x => pure (some x)) = some <$> mx
    rw [map_eq_bind_pure_comp]
    rfl
  obtain ⟨a, ha, hx⟩ := OracleComp.mem_support_bind_peel _ _ hx
  erw [hopt] at ha
  obtain ⟨α, hα', heq⟩ := OracleComp.mem_support_map_peel _ _ ha
  subst a
  have hinv := stirMultiRoundProverT_runToRound_invariant M φ deg t (stmtIn, oStmtIn) witIn
    (Fin.last (3 * M + 3)) α hα'
  have hmsgs : ∀ j, FullTranscript.messages (pSpec := (stirMultiVSpecT M ι t).toProtocolSpec F)
      α.1 j
      = Vector.cast (stirMultiVSpecT_length_msg j) (packFiniteFunction ι (oStmtIn ())) := by
    intro j
    have hdir : ((j.1 : Fin (3 * M + 3)) : ℕ) % 3 = 1 :=
      (stirVSpec_dir_eq_msg_iff (M := M) (msgLen := fun _ => Fintype.card ι)
        (chalLen := t)).mp j.2
    exact hinv.2 j.1.val j.1.isLt hdir
  have hbool : checkingBoolT M φ deg t oStmtIn
      (FullTranscript.messages (pSpec := (stirMultiVSpecT M ι t).toProtocolSpec F) α.1)
      (FullTranscript.challenges (pSpec := (stirMultiVSpecT M ι t).toProtocolSpec F) α.1)
      = true :=
    checkingBoolT_honest M φ deg t (oStmtIn ()) hmem oStmtIn rfl _ hmsgs _
  simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure,
    simulateQ_pure, LawfulApplicative.map_pure, Option.map_some, liftComp_pure] at hx
  have hv := OracleComp.eq_of_mem_support_pure _ hx
  subst x
  have hfn : ∀ (f g : ∀ _ : Empty, Unit), f = g := fun _ _ => funext fun i => i.elim
  refine ⟨_, rfl, ?_, ?_, hfn _ _⟩
  · simp only [acceptRejectOracleRel, Set.mem_singleton_iff, Prod.mk.injEq, hbool]
  · show (true : Bool) = checkingBoolT M φ deg t oStmtIn _ _
    rw [hbool]

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.stirMultiRoundProverT_runToRound_invariant
#print axioms StirIOP.MultiRound.checkingBoolT_honest
#print axioms StirIOP.MultiRound.stirCheckingIOPT_perfectCompleteness
