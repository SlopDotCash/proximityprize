/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# The t-repetition STIR wire shape (#301, hypothesis A1, part 1)

The single-query wire model (`stirMultiVSpec`, challenge length `1`) provably cannot reach
paper-STIR's L5.4 budgets: the switch prover pins every valid rbr budget family at
`Σᵢ εᵢ ≥ 1 − (⌊δ|ι|⌋+1)/|F|` (the K4 fence; quantitative core in
`CheckingRbrTightnessCore`).  The honest path to genuine `2^{-secpar}` budgets is
**t-fold repetition per challenge**: each binding check samples `t` points, and the flip
probability becomes a product (`≤ ((|F| − D)/|F|)ᵗ`), supplied by the landed
product-marginal engine (`ArkLib.Data.Probability.ProductMarginal`,
`probEvent_uniform_vector_bind_le`) over the pass sets bounded by
`TightnessCore.pass_count_ge`.

This file lands the wire shape itself:

* `stirMultiVSpecT M ι t` — the `(3M+3)`-round STIR shape with `t`-point vector challenges
  (the challenge length was ALWAYS a parameter of `stirVSpec`; the single-query model pinned
  it to `1`);
* `stirMultiVSpecT_one` — at `t = 1` it is DEFINITIONALLY the landed `stirMultiVSpec`;
* the length lemmas (`_length_msg`, `_length_chal`, `_length_chal_pos`) mirroring the
  `t = 1` versions;
* `chalCoordT` — reading the `j`-th field element off a committed `t`-point vector
  challenge (the multi-point analogue of `chalFE`).

Next bricks (tracked on issue #301): the `t`-point checking computation (fold the
binding/consistency checks over all `t` coordinates), its `simulateQ` collapse and
completeness, and the door-die soundness re-run with product flip bounds.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

open ProtocolSpec

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι]

/-- **The t-repetition STIR multi-round wire shape**: `3M + 3` rounds, message length
`|ι|`, challenge length `t`. -/
@[reducible]
def stirMultiVSpecT (M : ℕ) (ι : Type) [Fintype ι] (t : ℕ) :
    ProtocolSpec.VectorSpec (3 * M + 3) :=
  stirVSpec M (fun _ => Fintype.card ι) t

/-- At `t = 1` the repetition shape degenerates to the landed single-query shape,
definitionally. -/
@[simp] theorem stirMultiVSpecT_one (M : ℕ) :
    stirMultiVSpecT M ι 1 = stirMultiVSpec M ι := rfl

/-- Message rounds of `stirMultiVSpecT` have length `|ι|`. -/
theorem stirMultiVSpecT_length_msg {M t : ℕ}
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx) :
    Fintype.card ι = (stirMultiVSpecT M ι t).length i.1 := by
  have h := i.2
  rw [show ((stirMultiVSpecT M ι t).toProtocolSpec F).dir i.1
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir i.1 from rfl,
    stirVSpec_dir_eq_msg_iff] at h
  simp [stirMultiVSpecT, stirVSpec, h]

/-- Challenge rounds of `stirMultiVSpecT` have length `t`. -/
theorem stirMultiVSpecT_length_chal {M t : ℕ}
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx) :
    (stirMultiVSpecT M ι t).length i.1 = t := by
  have h := i.2
  rw [show ((stirMultiVSpecT M ι t).toProtocolSpec F).dir i.1
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir i.1 from rfl,
    stirVSpec_dir_eq_chal_iff] at h
  simp [stirMultiVSpecT, stirVSpec, h]

/-- Challenge rounds of `stirMultiVSpecT` have positive length when `t > 0`. -/
theorem stirMultiVSpecT_length_chal_pos {M t : ℕ} (ht : 0 < t)
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx) :
    0 < (stirMultiVSpecT M ι t).length i.1 := by
  rw [stirMultiVSpecT_length_chal i]
  exact ht

/-- **Read the `j`-th field element off a `t`-point vector challenge** — the multi-point
analogue of `chalFE`. -/
def chalCoordT {M t : ℕ}
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx) (j : Fin t) : F :=
  (chals i).get (Fin.cast (stirMultiVSpecT_length_chal i).symm j)

/-- At `t = 1`, the coordinate reader recovers `chalFE` at the unique coordinate. -/
theorem chalCoordT_one [SampleableType F] {M : ℕ} [Nonempty ι]
    (chals : ((stirMultiVSpecT M ι 1).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpecT M ι 1).toProtocolSpec F).ChallengeIdx) :
    chalCoordT chals i 0 = chalFE chals i := rfl

/-! ## The t-point checking verifier surface -/

section CheckingT

open OracleSpec OracleComp OracleInterface STIR ReedSolomon NNReal WhirIOP.Construction
open scoped NNReal

variable [Nonempty ι] [SampleableType F]

/-- The `j`-th message round of the t-repetition shape (round `3j + 1`). -/
def msgIdxT (M t : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx :=
  ⟨⟨3 * (j : ℕ) + 1, by omega⟩, by
    show (stirMultiVSpecT M ι t).dir _ = .P_to_V
    rw [show (stirMultiVSpecT M ι t).dir ⟨3 * (j : ℕ) + 1, by omega⟩
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir ⟨3 * (j : ℕ) + 1, by omega⟩ from rfl,
      stirVSpec_dir_eq_msg_iff]
    simp only [Fin.val_mk]
    omega⟩

/-- The out-challenge round of the t-repetition shape (round `3j + 2`). -/
def outChalIdxT (M t : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 2, by omega⟩, by
    show (stirMultiVSpecT M ι t).dir _ = .V_to_P
    rw [show (stirMultiVSpecT M ι t).dir ⟨3 * (j : ℕ) + 2, by omega⟩
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir ⟨3 * (j : ℕ) + 2, by omega⟩ from rfl,
      stirVSpec_dir_eq_chal_iff]
    simp only [Fin.val_mk]
    omega⟩

/-- The shift-challenge round of the t-repetition shape (round `3j + 3`). -/
def shiftChalIdxT (M t : ℕ) (j : Fin M) :
    ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 3, by omega⟩, by
    show (stirMultiVSpecT M ι t).dir _ = .V_to_P
    rw [show (stirMultiVSpecT M ι t).dir ⟨3 * (j : ℕ) + 3, by omega⟩
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir ⟨3 * (j : ℕ) + 3, by omega⟩ from rfl,
      stirVSpec_dir_eq_chal_iff]
    simp only [Fin.val_mk]
    omega⟩

/-- The position of domain point `x` inside a packed t-repetition message vector. -/
noncomputable def msgPosT (M t : ℕ)
    (j : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx) (x : ι) :
    Fin ((stirMultiVSpecT M ι t).length j.1) :=
  Fin.cast (stirMultiVSpecT_length_msg j) (Fintype.equivFin ι x)

/-- Query the input codeword oracle at a domain point (t-repetition wire). -/
noncomputable def askInputT (M t : ℕ) (x : ι) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpecT M ι t).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [OracleStatement ι F]ₒ)
    (⟨(), x⟩ : (Σ i : Unit, OracleInterface.Query (OracleStatement ι F i))))

/-- Query the `j`-th prover message oracle at a vector position (t-repetition wire). -/
noncomputable def askMsgT (M t : ℕ)
    (j : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecT M ι t).length j.1)) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpecT M ι t).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query
    (spec := [((stirMultiVSpecT M ι t).toProtocolSpec F).Message]ₒ)
    (⟨j, k⟩ : (Σ i, OracleInterface.Query
      (((stirMultiVSpecT M ι t).toProtocolSpec F).Message i))))

/-- The honest answer of a t-repetition message oracle. -/
noncomputable def msgAnsT {M t : ℕ}
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecT M ι t).length j.1)) : F :=
  OracleInterface.answer (msgs j) k

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ)

open scoped Classical in
/-- **The t-point checking computation**: every binding and consistency check is performed
at ALL `t` challenge-derived points; the final low-degree check reads the last message in
full.  At `t = 1` this is (a reshuffling of) the landed `checkingComp`. -/
noncomputable def checkingCompT
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpecT M ι t).toProtocolSpec F).Message]ₒ)) Bool := do
  -- (1) the t-point round-0 binding checks
  let binds ← askList (List.finRange t) (fun j' => do
      let x0 := queryPoint φ (chalCoordT chals (outChalIdxT M t 0) j')
      let vIn ← askInputT M t x0
      let v0 ← askMsgT M t (msgIdxT M t 0) (msgPosT M t (msgIdxT M t 0) x0)
      pure (decide (vIn = v0)))
  -- (2) the t-point per-round consistency checks
  let consist ← askList (List.finRange M) (fun j => do
      let inner ← askList (List.finRange t) (fun j' => do
          let xa := queryPoint φ (chalCoordT chals (outChalIdxT M t j.succ) j')
          let xb := queryPoint φ (chalCoordT chals (shiftChalIdxT M t j) j')
          let va ← askMsgT M t (msgIdxT M t j.castSucc)
            (msgPosT M t (msgIdxT M t j.castSucc) xa)
          let vb ← askMsgT M t (msgIdxT M t j.succ)
            (msgPosT M t (msgIdxT M t j.succ) xa)
          let vc ← askMsgT M t (msgIdxT M t j.castSucc)
            (msgPosT M t (msgIdxT M t j.castSucc) xb)
          let vd ← askMsgT M t (msgIdxT M t j.succ)
            (msgPosT M t (msgIdxT M t j.succ) xb)
          pure (decide (va = vb) && decide (vc = vd)))
      pure (inner.all (fun b => b)))
  -- (3) the final full-read low-degree check
  let finalVals ← askList (List.finRange (Fintype.card ι)) (fun k =>
      askMsgT M t (msgIdxT M t (Fin.last M))
        (Fin.cast (stirMultiVSpecT_length_msg (msgIdxT M t (Fin.last M))) k))
  pure (binds.all (fun b => b) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg))

open scoped Classical in
/-- **The pure value of the t-point checking computation** under the honest oracle
implementation. -/
noncomputable def checkingBoolT (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges) : Bool :=
  let binds := (List.finRange t).map (fun j' =>
      let x0 := queryPoint φ (chalCoordT chals (outChalIdxT M t 0) j')
      decide (inputAns oStmt x0
        = msgAnsT msgs (msgIdxT M t 0) (msgPosT M t (msgIdxT M t 0) x0)))
  let consist := (List.finRange M).map (fun j =>
      ((List.finRange t).map (fun j' =>
        let xa := queryPoint φ (chalCoordT chals (outChalIdxT M t j.succ) j')
        let xb := queryPoint φ (chalCoordT chals (shiftChalIdxT M t j) j')
        decide (msgAnsT msgs (msgIdxT M t j.castSucc)
            (msgPosT M t (msgIdxT M t j.castSucc) xa)
          = msgAnsT msgs (msgIdxT M t j.succ) (msgPosT M t (msgIdxT M t j.succ) xa)) &&
        decide (msgAnsT msgs (msgIdxT M t j.castSucc)
            (msgPosT M t (msgIdxT M t j.castSucc) xb)
          = msgAnsT msgs (msgIdxT M t j.succ)
              (msgPosT M t (msgIdxT M t j.succ) xb)))).all (fun b => b))
  let finalVals := (List.finRange (Fintype.card ι)).map (fun k =>
      msgAnsT msgs (msgIdxT M t (Fin.last M))
        (Fin.cast (stirMultiVSpecT_length_msg (msgIdxT M t (Fin.last M))) k))
  binds.all (fun b => b) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg)

/-- `simulateQ` collapse for the t-repetition input-oracle query. -/
theorem simulateQ_askInputT (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j) (x : ι) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askInputT M t x)
      = (pure (inputAns oStmt x) : OracleComp []ₒ F) := rfl

/-- `simulateQ` collapse for a t-repetition message-oracle query. -/
theorem simulateQ_askMsgT (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecT M ι t).length j.1)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askMsgT M t j k)
      = (pure (msgAnsT msgs j k) : OracleComp []ₒ F) := rfl

open scoped Classical in
/-- **Central collapse for the t-point checking computation**: under the honest oracle
implementation it is the pure computation of `checkingBoolT` (for ARBITRARY oracle and
message values). -/
theorem simulateQ_checkingCompT (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecT M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        (checkingCompT M φ deg t chals)
      = pure (checkingBoolT M φ deg t oStmt msgs chals) := by
  unfold checkingCompT checkingBoolT
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun j' =>
      let x0 := queryPoint φ (chalCoordT chals (outChalIdxT M t 0) j')
      decide (inputAns oStmt x0
        = msgAnsT msgs (msgIdxT M t 0) (msgPosT M t (msgIdxT M t 0) x0)))
      (fun j' => by
        rw [simulateQ_bind, simulateQ_askInputT]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsgT]
        simp only [pure_bind, simulateQ_pure])]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun j =>
      ((List.finRange t).map (fun j' =>
        let xa := queryPoint φ (chalCoordT chals (outChalIdxT M t j.succ) j')
        let xb := queryPoint φ (chalCoordT chals (shiftChalIdxT M t j) j')
        decide (msgAnsT msgs (msgIdxT M t j.castSucc)
            (msgPosT M t (msgIdxT M t j.castSucc) xa)
          = msgAnsT msgs (msgIdxT M t j.succ) (msgPosT M t (msgIdxT M t j.succ) xa)) &&
        decide (msgAnsT msgs (msgIdxT M t j.castSucc)
            (msgPosT M t (msgIdxT M t j.castSucc) xb)
          = msgAnsT msgs (msgIdxT M t j.succ)
              (msgPosT M t (msgIdxT M t j.succ) xb)))).all (fun b => b))
      (fun j => by
        rw [simulateQ_bind,
          simulateQ_askList _ _ _ (fun j' =>
            let xa := queryPoint φ (chalCoordT chals (outChalIdxT M t j.succ) j')
            let xb := queryPoint φ (chalCoordT chals (shiftChalIdxT M t j) j')
            decide (msgAnsT msgs (msgIdxT M t j.castSucc)
                (msgPosT M t (msgIdxT M t j.castSucc) xa)
              = msgAnsT msgs (msgIdxT M t j.succ)
                  (msgPosT M t (msgIdxT M t j.succ) xa)) &&
            decide (msgAnsT msgs (msgIdxT M t j.castSucc)
                (msgPosT M t (msgIdxT M t j.castSucc) xb)
              = msgAnsT msgs (msgIdxT M t j.succ)
                  (msgPosT M t (msgIdxT M t j.succ) xb)))
            (fun j' => by
              rw [simulateQ_bind, simulateQ_askMsgT]
              simp only [pure_bind]
              rw [simulateQ_bind, simulateQ_askMsgT]
              simp only [pure_bind]
              rw [simulateQ_bind, simulateQ_askMsgT]
              simp only [pure_bind]
              rw [simulateQ_bind, simulateQ_askMsgT]
              simp only [pure_bind, simulateQ_pure])]
        simp only [pure_bind, simulateQ_pure])]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun k =>
      msgAnsT msgs (msgIdxT M t (Fin.last M))
        (Fin.cast (stirMultiVSpecT_length_msg (msgIdxT M t (Fin.last M))) k))
      (fun k => simulateQ_askMsgT M t oStmt msgs _ _)]
  simp only [pure_bind, simulateQ_pure]

/-- **The t-point checking verifier** (IOP shape: no forwarded oracles). -/
noncomputable def stirCheckingVerifierT :
    OracleVerifier []ₒ Unit (OracleStatement ι F) Bool (fun _ : Empty => Unit)
      ((stirMultiVSpecT M ι t).toProtocolSpec F) where
  verify := fun _ chals => OptionT.lift (checkingCompT M φ deg t chals)
  embed := ⟨fun i => i.elim, fun i => i.elim⟩
  hEq := fun i => i.elim

/-- **The t-repetition multi-round STIR prover**: verbatim the landed honest prover — it
already reads only coordinate `0` of each vector challenge (`dite` on length positivity),
so its strategy is chalLen-agnostic; messages do not depend on `t` at all. -/
noncomputable def stirMultiRoundProverT (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ) :
    OracleProver []ₒ Unit (OracleStatement ι F) Unit Bool (fun _ : Empty => Unit) Unit
      ((stirMultiVSpecT M ι t).toProtocolSpec F) where
  PrvState := fun _ => ((Unit × (∀ i, OracleStatement ι F i)) × Unit) × F
  input := fun x => (x, 0)
  receiveChallenge := fun i st => pure (fun r =>
    (st.1, if h : 0 < (stirMultiVSpecT M ι t).length i.1 then r.get ⟨0, h⟩ else 0))
  sendMessage := fun i st => pure
    ⟨Vector.cast (stirMultiVSpecT_length_msg i)
      (packFiniteFunction ι
        (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ()) (fun _ : Fin 1 => deg))),
     st⟩
  output := fun _ => pure ((true, isEmptyElim), ())

/-- **The t-repetition checking STIR Vector IOPP**: the honest folding prover with the
t-point checking verifier. -/
noncomputable def stirCheckingIOPT (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ) :
    VectorIOP Unit (OracleStatement ι F) Unit (stirMultiVSpecT M ι t) F where
  prover := stirMultiRoundProverT M φ deg t
  verifier := stirCheckingVerifierT M φ deg t

/-- The t-repetition rbr knowledge-soundness residual — the A1 soundness target, to be
discharged by the door-die predicate with PRODUCT flip bounds
(`((|F|−D)/|F|)ᵗ` at the binding challenges via
`TightnessCore.pass_count_ge` × `ProductMarginal.probEvent_uniform_vector_bind_le`).

Ledger status (#351): the genuine open soundness target of #301 at repetition parameter t
(#335 A1); consumed as a hypothesis, never fabricated. -/
noncomputable def stirCheckingRbrSoundnessResidualT
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ) (δ : ℝ≥0)
    (ε_rbr : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx → ℝ≥0) : Prop :=
  OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
    (stirRelation deg φ δ) (stirCheckingIOPT M φ deg t).verifier ε_rbr

end CheckingT

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.stirMultiVSpecT_length_msg
#print axioms StirIOP.MultiRound.stirMultiVSpecT_length_chal
#print axioms StirIOP.MultiRound.chalCoordT_one
#print axioms StirIOP.MultiRound.simulateQ_checkingCompT
#print axioms StirIOP.MultiRound.stirCheckingVerifierT
#print axioms StirIOP.MultiRound.stirCheckingIOPT
