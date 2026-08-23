/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.ProofSystem.Whir.Folding
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness

/-!
# WHIR single fold round (Construction 5.1 brick) and its perfect completeness — issue #113

This file constructs ONE honest WHIR folding round as an `OracleReduction` and proves its
**perfect completeness** from first principles (no `sorry`, no residual, no `: True`).

## Structure of the round (paper Construction 5.1, ABF26)

Following the FRI fold-round template (`Fri/Spec/SingleRound.lean`), one WHIR fold round is the
2-message protocol `pSpec = [V_to_P (α : F), P_to_V (g : ι_{j+1} → F)]`:

* the verifier sends a uniform fold challenge `α : F`;
* the honest prover replies with the folded oracle `g := fun y => foldf S φ y f α`, an evaluation
  of the single-step fold of its committed codeword `f`.

The verifier of the *fold round itself* performs no oracle-consistency `guard` — exactly as the FRI
fold verifier (`foldVerifier`, `pure (Fin.vappend …)`) — because fold/oracle consistency is enforced
later by the query phase. Hence the round verifier never aborts, the *safety* half of completeness
(`probFailure = 0`) is immediate, and completeness reduces to the **correctness** statement that the
honest prover's reply lands in the next-level code: `g ∈ smoothCode φ_{j+1} M`. That is precisely the
proven folding lemma `Fold.foldf_step_mem_smoothCode`.

## What is and is not proved here

* **Proved (non-gated):** perfect completeness of the honest fold round, i.e. the honest interaction
  succeeds with probability 1 and the output oracle satisfies the next-level codeword relation. This
  uses only the already-proven, `sorry`-free fold algebra in `Whir/Folding.lean` — it does *not*
  depend on the folding list-decoding lemmas (L4.20–4.23) or `mca_johnson_bound_CONJECTURE`, which
  are *soundness* content (the round-by-round soundness `whir_rbr_soundness` stays open and gated on
  the MCA conjecture, as recorded in `RBRSoundness.lean`).
-/

namespace WhirIOP.FoldRound

open OracleSpec OracleComp ProtocolSpec NNReal Fold BlockRelDistance ReedSolomon

noncomputable section

/-! ### `[V_to_P, P_to_V]` unroll lemma

`OracleReduction.Completeness` provides `unroll_2_message_reduction_perfectCompleteness` only for the
`[P_to_V, V_to_P]` order. WHIR's fold round is `[V_to_P, P_to_V]` (challenge first, then the folded
oracle), so we prove the analogous explicit-`liftComp` unrolling here, by the same argument
(generic `n`-message unroll + `runToRound` unfolding with the round directions swapped). -/
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

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Pow ι ℕ]
variable {S : Finset ι} {φ : ι ↪ F}
variable {j M : ℕ}
-- the per-level evaluation-domain embeddings of the smooth tower
variable {φ_j : (indexPowT S φ j) ↪ F} {φ_j1 : (indexPowT S φ (j + 1)) ↪ F}
variable [Fintype (indexPowT S φ j)] [DecidableEq (indexPowT S φ j)] [Smooth φ_j]
variable [Fintype (indexPowT S φ (j + 1))] [DecidableEq (indexPowT S φ (j + 1))] [Smooth φ_j1]
variable [Neg (indexPowT S φ j)]

/-- The oracle message type for this round: the single committed codeword as a function on the
relevant evaluation domain. Indexed by `Unit`, mirroring `WhirIOP.OracleStatement`. -/
@[reducible]
def OStmtIn : Unit → Type := fun _ => indexPowT S φ j → F

@[reducible]
def OStmtOut : Unit → Type := fun _ => indexPowT S φ (j + 1) → F

instance : ∀ u, OracleInterface (OStmtIn (S := S) (φ := φ) (j := j) u) :=
  fun _ => OracleInterface.instFunction

instance : ∀ u, OracleInterface (OStmtOut (S := S) (φ := φ) (j := j) u) :=
  fun _ => OracleInterface.instFunction

/-- Protocol spec: the verifier sends a fold challenge `α : F`, then the prover sends the folded
oracle `g : indexPowT S φ (j+1) → F`. -/
@[reducible]
def pSpec : ProtocolSpec 2 :=
  ⟨!v[.V_to_P, .P_to_V], !v[F, indexPowT S φ (j + 1) → F]⟩

instance : ∀ i, OracleInterface ((pSpec (S := S) (φ := φ) (j := j)).Message i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by unfold pSpec ProtocolSpec.Message; simpa using OracleInterface.instFunction

instance : ∀ i, OracleInterface ((pSpec (S := S) (φ := φ) (j := j)).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ idx, SampleableType ((pSpec (S := S) (φ := φ) (j := j)).Challenge idx)
  | ⟨idx, hidx⟩ => by
    -- `pSpec.dir = ![V_to_P, P_to_V]`, so the only challenge index is `0`, of type `F`.
    have h_idx_eq_0 : idx = 0 := by
      cases idx using Fin.cases with
      | zero => rfl
      | succ i1 =>
        cases i1 using Fin.cases with
        | zero => simp [pSpec] at hidx
        | succ k => exact k.elim0
    subst h_idx_eq_0
    simpa [pSpec, ProtocolSpec.Challenge] using (inferInstance : SampleableType F)

/-- The honest fold-round prover. It receives `α`, folds its committed function, and sends the
folded oracle. -/
def foldProver :
    OracleProver []ₒ Unit (OStmtIn (S := S) (φ := φ) (j := j)) Unit
      Unit (OStmtOut (S := S) (φ := φ) (j := j)) Unit
      (pSpec (S := S) (φ := φ) (j := j)) where
  PrvState
  | 0 => (indexPowT S φ j → F)
  | _ => (indexPowT S φ j → F) × F
  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt ()
  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨f, α⟩ => pure ⟨fun y => foldf S φ y f α, ⟨f, α⟩⟩
  receiveChallenge
  | ⟨0, _⟩ => fun f => pure (fun (α : F) => ⟨f, α⟩)
  | ⟨1, h⟩ => nomatch h
  output := fun ⟨f, α⟩ => pure ⟨⟨(), fun _ => fun y => foldf S φ y f α⟩, ()⟩

/-- The honest fold-round verifier. It performs no consistency check (that is deferred to the query
phase), simply routing the folded-oracle message to the output oracle. -/
def foldVerifier :
    OracleVerifier []ₒ Unit (OStmtIn (S := S) (φ := φ) (j := j))
      Unit (OStmtOut (S := S) (φ := φ) (j := j))
      (pSpec (S := S) (φ := φ) (j := j)) where
  verify := fun _ _ => pure ()
  embed := ⟨fun _ => Sum.inr ⟨1, by simp⟩, by intro a b _; rfl⟩
  hEq := by intro u; unfold OStmtOut pSpec ProtocolSpec.Message; rfl

/-- The honest WHIR fold round as an oracle reduction. -/
def foldOracleReduction :
    OracleReduction []ₒ Unit (OStmtIn (S := S) (φ := φ) (j := j)) Unit
      Unit (OStmtOut (S := S) (φ := φ) (j := j)) Unit
      (pSpec (S := S) (φ := φ) (j := j)) where
  prover := foldProver (S := S) (φ := φ) (j := j)
  verifier := foldVerifier (S := S) (φ := φ) (j := j)

/-- Input relation: the committed oracle is a codeword of the level-`j` smooth code of degree-budget
`M + 1`. -/
def inputRelation :
    Set ((Unit × ∀ u, OStmtIn (S := S) (φ := φ) (j := j) u) × Unit) :=
  { x | x.1.2 () ∈ smoothCode φ_j (M + 1) }

/-- Output relation: the folded oracle is a codeword of the level-`(j+1)` smooth code of
degree-budget `M`. -/
def outputRelation :
    Set ((Unit × ∀ u, OStmtOut (S := S) (φ := φ) (j := j) u) × Unit) :=
  { x | x.1.2 () ∈ smoothCode φ_j1 M }

/-! ### Perfect completeness -/

/-- The empty oracle spec is vacuously inhabited (its query index type is empty). -/
instance : []ₒ.Inhabited where
  inhabited_B := fun i => i.elim

/-- Finiteness of the challenge oracle spec. Its query domain is `(i : ChallengeIdx) × Unit` and the
response at index `i` is `Challenge i`; the only challenge index is `0`, of finite type `F`. -/
instance : [(pSpec (S := S) (φ := φ) (j := j)).Challenge]ₒ.Fintype where
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

/-- Inhabitedness of the challenge oracle spec (response type `F` at the only index `0`). -/
instance : [(pSpec (S := S) (φ := φ) (j := j)).Challenge]ₒ.Inhabited where
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
/-- **Perfect completeness of the honest WHIR fold round.** The honest prover folds its committed
codeword `f ∈ smoothCode φ_j (M+1)` by the challenge `α`; the no-`guard` verifier always accepts. The
run is `getChallenge >>= fun α => (a lifted, never-failing OracleComp computation)`, so it never
fails (safety), and its unique reachable output's oracle is `fun z => foldf S φ z (oStmtIn ()) α`,
which lands in `smoothCode φ_{j+1} M` by the already-proven `Fold.foldf_step_mem_smoothCode`
(correctness). Non-gated (independent of the open folding list-decoding lemmas and the MCA
conjecture). -/
theorem foldOracleReduction_perfectCompleteness (hInit : NeverFail init)
    (hφj : ∀ x : indexPowT S φ j, φ_j x = x.val)
    (hφj1 : ∀ z : indexPowT S φ (j + 1), φ_j1 z = z.val)
    (hneg : ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    OracleReduction.perfectCompleteness init impl
      (inputRelation (S := S) (φ := φ) (M := M) (φ_j := φ_j))
      (outputRelation (S := S) (φ := φ) (M := M) (φ_j1 := φ_j1))
      (foldOracleReduction (S := S) (φ := φ) (j := j)) := by
  rw [unroll_2_message_VP (foldOracleReduction (S := S) (φ := φ) (j := j))
    (inputRelation (S := S) (φ := φ) (M := M) (φ_j := φ_j))
    (outputRelation (S := S) (φ := φ) (M := M) (φ_j1 := φ_j1)) init impl hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  have h_fold_mem : ∀ α : F,
      (fun z : indexPowT S φ (j + 1) => foldf S φ z (oStmtIn ()) α) ∈ smoothCode φ_j1 M := fun α =>
    foldf_step_mem_smoothCode (φ_j := φ_j) (φ_j1 := φ_j1)
      ⟨oStmtIn (), h_relIn⟩ α hφj hφj1 hneg hx0 h2
  dsimp only [foldOracleReduction, foldProver, foldVerifier, OracleVerifier.toVerifier,
    OStmtIn, OStmtOut, inputRelation, outputRelation]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run is `getChallenge >>= fun α => ↑(never-failing OracleComp)`. The challenge
    -- sample never fails, and the (no-`guard`) verifier body is `liftComp` of an `OptionT` whose
    -- `.run` is a lifted, always-`some` `OracleComp` — so the whole run never fails, without ever
    -- evaluating the verifier's `simulateQ`.
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
  · -- CORRECTNESS: with `α` extracted the verifier's `simulateQ (simOracle2 …) (pure ())` is at the
    -- top level, where `OptionT.simulateQ_pure`/`run_pure` reduce it to `pure (some ())`; the unique
    -- reachable output's oracle is the honest fold, which lands in `relOut` via `h_fold_mem`.
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, _hα, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    exact ⟨h_fold_mem α, trivial, by funext u; rfl⟩

end

end WhirIOP.FoldRound
