/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Stir.SubUnitRbr
import ArkLib.ProofSystem.Stir.SwitchAttack
import ArkLib.Data.Probability.ProductMarginal
import ArkLib.ProofSystem.Component.SendWitness

set_option linter.style.longFile 0
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

/-!
# Issue #335 item A1 — the t-repetition STIR wire model (core)

The t-generalization of the landed t=1 checking-verifier stack
(`Stir/CheckingVerifier.lean`): the `stirVSpec` shape at challenge length `t`, the
repetition checking verifier (every binding check repeated at each of the `t` challenge
coordinates), its `simulateQ` collapse, the honest prover at the rep spec, the run-support
invariant, perfect completeness, and the exact `checkingBoolRep_eq_true_iff` decomposition.
-/


set_option linter.style.longFile 1800

/-!
# Issue #335 (A1) — the t-REPETITION STIR checking verifier: real security parameters

The honest path past the single-query wire model's tightness fence
(`Stir/SwitchAttack.lean`): every binding check of the checking verifier is repeated at all
`t` coordinates of one freshly drawn length-`t` vector challenge, and the per-challenge rbr
budgets become the `t`-fold POWERS of the single-query bases — meeting every `2^{-secpar}`
target at sufficiently large `t`.

Contents (all mirroring `Stir/SubUnitRbr.lean`, the landed `t = 1` template):
1. **The rep wire**: `stirMultiVSpecRep M ι t := stirVSpec M (fun _ => |ι|) t`;
   `checkingCompRep`/`checkingBoolRep` conjoin every binding check over `s : Fin t`
   (final full-read check unchanged); `simulateQ` collapse; honest prover
   `stirMultiRoundProverRep` + run-support invariant + PERFECT COMPLETENESS
   (`stirCheckingIOPRep_perfectCompleteness`), all for symbolic `M` and `t`.
2. **The state predicate** `stirCheckingPredRep` (retired-prefix winnable; the committed
   checks hold at every coordinate, the pending-pair lock and last-in-code clauses are
   `t`-independent) + the six seam lemmas + the `∀ s` flip characterizations.
3. **The flip bounds**: `stirFlipRep_le_zero`, and via the product-marginal machinery
   (`Data/Probability/ProductMarginal.lean`, #335 A2)
   `stirFlipRep_le_round2 ≤ ((|F|−(⌊δ|ι|⌋+1))/|F|)^t`,
   `stirFlipRep_le_out ≤ ((|F|−1)/|F|)^t`.
4. **The discharge**: `stirEpsStarRep` (the `(·)^t` budget),
   `stirCheckingRepRbrSoundness_genuine` (T1-rep, outright — no CA residuals, no vacuity),
   `stirCheckingIOPRep_isSecureWithGap_genuine` (hypothesis-free), and
   `stir_main_of_checkingIOP_rep` (Theorem 5.1 with the rep witness; the `hε` leg is
   satisfiable for every `secpar` by choosing `t` — `stirEpsStarRep_le_pow_max` gives the
   uniform `((|F|−1)/|F|)^t` domination; the analytic choice of `t(secpar)` is the
   caller's).

HONESTY: the out-challenge base `(|F|−1)/|F|` reflects the worst-case one-point pair
deviation of the degenerate identity-fold model; achieving small budgets thus needs
`t ≈ secpar·|F|` at the later rounds (the round-2 base needs only
`t ≈ secpar·|F|/(δ|ι|)`). Paper-STIR's per-round δ-closeness guarantees (which would
restore `δ`-dependent bases at every round) require the genuine degree-reducing fold —
the #304/#302 correlated-agreement lane. No claim beyond the stated budgets.
-/

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction VectorIOP
open scoped ENNReal
open OracleInterface

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι]

/-! ### 1. The t-repetition spec and its length lemmas -/

section RepSpec

/-- The t-repetition multi-round STIR vector spec: uniform message length `|ι|` and challenge
length `t` (each verifier challenge round samples `t` independent field elements). -/
@[reducible]
def stirMultiVSpecRep (M : ℕ) (ι : Type) [Fintype ι] (t : ℕ) :
    ProtocolSpec.VectorSpec (3 * M + 3) :=
  stirVSpec M (fun _ => Fintype.card ι) t

/-- Message-round payload length of `stirMultiVSpecRep` at a raw index. -/
theorem stirMultiRep_length_msg_raw {M t : ℕ} (k : ℕ) (hk : k < 3 * M + 3)
    (hmod : k % 3 = 1) :
    Fintype.card ι = (stirMultiVSpecRep M ι t).length ⟨k, hk⟩ := by
  simp [stirVSpec, hmod]

/-- Challenge-round payload length of `stirMultiVSpecRep` at a raw index. -/
theorem stirMultiRep_length_chal_raw {M t : ℕ} (k : ℕ) (hk : k < 3 * M + 3)
    (hmod : k % 3 ≠ 1) :
    (stirMultiVSpecRep M ι t).length ⟨k, hk⟩ = t := by
  simp [stirVSpec, hmod]

/-- Challenge-round payload length of `stirMultiVSpecRep` at a `Fin` index. -/
theorem stirMultiRep_length_chal {M t : ℕ} (i : Fin (3 * M + 3)) (hmod : (i : ℕ) % 3 ≠ 1) :
    (stirMultiVSpecRep M ι t).length i = t := by
  simp [stirVSpec, hmod]

/-- Message rounds of `stirMultiVSpecRep` have length `|ι|`. -/
theorem stirMultiVSpecRep_length_msg {M t : ℕ}
    (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx) :
    Fintype.card ι = (stirMultiVSpecRep M ι t).length i.1 := by
  have h := i.2
  rw [show ((stirMultiVSpecRep M ι t).toProtocolSpec F).dir i.1
    = (stirMultiVSpecRep M ι t).dir i.1 from rfl, stirVSpec_dir_eq_msg_iff] at h
  simp [stirVSpec, h]

/-- Challenge rounds of `stirMultiVSpecRep` have length `t`. -/
theorem stirMultiVSpecRep_length_chal {M t : ℕ}
    (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx) :
    (stirMultiVSpecRep M ι t).length i.1 = t := by
  have h := i.2
  rw [show ((stirMultiVSpecRep M ι t).toProtocolSpec F).dir i.1
    = (stirMultiVSpecRep M ι t).dir i.1 from rfl, stirVSpec_dir_eq_chal_iff] at h
  simp [stirVSpec, h]

end RepSpec

/-! ### The honest prover at the rep spec -/

/-- **The multi-round STIR prover at the t-repetition spec**: identical construction to the
landed `stirMultiRoundProver` (it echoes the genuine packed `Combine.combine` fold of its
codeword at every message round and ignores all but the first coordinate of each challenge),
instantiated at challenge length `t`. -/
noncomputable def stirMultiRoundProverRep (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ) :
    OracleProver []ₒ Unit (OracleStatement ι F) Unit Bool (fun _ : Empty => Unit) Unit
      ((stirMultiVSpecRep M ι t).toProtocolSpec F) where
  PrvState := fun _ => ((Unit × (∀ i, OracleStatement ι F i)) × Unit) × F
  input := fun x => (x, 0)
  receiveChallenge := fun i st => pure (fun r =>
    (st.1, if h : 0 < (stirMultiVSpecRep M ι t).length i.1 then r.get ⟨0, h⟩ else 0))
  sendMessage := fun i st => pure
    ⟨Vector.cast (stirMultiVSpecRep_length_msg i)
      (packFiniteFunction ι
        (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ()) (fun _ : Fin 1 => deg))),
     st⟩
  output := fun _ => pure ((true, isEmptyElim), ())

/-! ### 2. The t-repetition checking verifier -/

section CheckingVerifierRep

variable [Nonempty ι]

/-- The `j`-th message round of the rep shape (round `3j + 1`). -/
def msgIdxRep (M t : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx :=
  ⟨⟨3 * (j : ℕ) + 1, by omega⟩, by
    show (stirMultiVSpecRep M ι t).dir _ = .P_to_V
    rw [stirVSpec_dir_eq_msg_iff]; simp only [Fin.val_mk]; omega⟩

/-- The out-challenge round following the `j`-th message round (round `3j + 2`). -/
def outChalIdxRep (M t : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 2, by omega⟩, by
    show (stirMultiVSpecRep M ι t).dir _ = .V_to_P
    rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega⟩

/-- The shift-challenge round between message rounds `j` and `j + 1` (round `3j + 3`). -/
def shiftChalIdxRep (M t : ℕ) (j : Fin M) :
    ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 3, by omega⟩, by
    show (stirMultiVSpecRep M ι t).dir _ = .V_to_P
    rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega⟩

/-- Read the `s`-th field element off a (length-`t`) vector challenge. -/
def chalFERep {M t : ℕ} (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx) (s : Fin t) : F :=
  (chals i).get ⟨(s : ℕ), by rw [stirMultiVSpecRep_length_chal i]; exact s.isLt⟩

/-- The position of domain point `x` inside a packed message vector of the rep spec. -/
noncomputable def msgPosRep (M t : ℕ)
    (j : ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx) (x : ι) :
    Fin ((stirMultiVSpecRep M ι t).length j.1) :=
  Fin.cast (stirMultiVSpecRep_length_msg j) (Fintype.equivFin ι x)

/-- Query the input codeword oracle at a domain point (rep spec). -/
noncomputable def askInputRep (M t : ℕ) (x : ι) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpecRep M ι t).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [OracleStatement ι F]ₒ)
    (⟨(), x⟩ : (Σ i : Unit, OracleInterface.Query (OracleStatement ι F i))))

/-- Query the `j`-th prover message oracle at a vector position (rep spec). -/
noncomputable def askMsgRep (M t : ℕ)
    (j : ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecRep M ι t).length j.1)) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpecRep M ι t).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [((stirMultiVSpecRep M ι t).toProtocolSpec F).Message]ₒ)
    (⟨j, k⟩ : (Σ i, OracleInterface.Query
      (((stirMultiVSpecRep M ι t).toProtocolSpec F).Message i))))

/-- The honest answer of a message oracle of the rep spec (ascribed at `F`). -/
noncomputable def msgAnsRep {M t : ℕ}
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecRep M ι t).length j.1)) : F :=
  OracleInterface.answer (msgs j) k

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ)

open scoped Classical in
/-- **The t-repetition checking computation**: the round-0 fold-query check, the per-round
out/shift consistency checks, and the final full-read low-degree check — with each of the
binding point-checks repeated at every one of the `t` challenge coordinates. -/
noncomputable def checkingCompRep
    (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpecRep M ι t).toProtocolSpec F).Message]ₒ)) Bool := do
  -- (1) round-0 fold-query checks: g₁ agrees with (the fold of) the input codeword at the
  -- t points derived from the first out-challenge
  let foldChecks ← askList (List.finRange t) (fun s => do
      let x0 := queryPoint φ (chalFERep chals (outChalIdxRep M t 0) s)
      let vIn ← askInputRep M t x0
      let v0 ← askMsgRep M t (msgIdxRep M t 0) (msgPosRep M t (msgIdxRep M t 0) x0)
      pure (decide (vIn = v0)))
  -- (2) per-round consistency checks: consecutive folded oracles agree at the t points derived
  -- from each of the round's out- and shift-challenge coordinates
  let consist ← askList (List.finRange M) (fun j => do
      let inner ← askList (List.finRange t) (fun s => do
          let xa := queryPoint φ (chalFERep chals (outChalIdxRep M t j.succ) s)
          let xb := queryPoint φ (chalFERep chals (shiftChalIdxRep M t j) s)
          let va ← askMsgRep M t (msgIdxRep M t j.castSucc)
            (msgPosRep M t (msgIdxRep M t j.castSucc) xa)
          let vb ← askMsgRep M t (msgIdxRep M t j.succ)
            (msgPosRep M t (msgIdxRep M t j.succ) xa)
          let vc ← askMsgRep M t (msgIdxRep M t j.castSucc)
            (msgPosRep M t (msgIdxRep M t j.castSucc) xb)
          let vd ← askMsgRep M t (msgIdxRep M t j.succ)
            (msgPosRep M t (msgIdxRep M t j.succ) xb)
          pure (decide (va = vb) && decide (vc = vd)))
      pure (inner.all (fun b => b)))
  -- (3) final low-degree check: read the final message (the final polynomial, in the clear)
  -- in full and check membership in the Reed-Solomon code (unchanged from t = 1)
  let finalVals ← askList (List.finRange (Fintype.card ι)) (fun k =>
      askMsgRep M t (msgIdxRep M t (Fin.last M))
        (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))
  pure (foldChecks.all (fun b => b) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg))

open scoped Classical in
/-- **The pure value of the t-repetition checking computation** under the honest oracle
implementation. -/
noncomputable def checkingBoolRep (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges) : Bool :=
  let foldChecks := (List.finRange t).map (fun s =>
      let x0 := queryPoint φ (chalFERep chals (outChalIdxRep M t 0) s)
      let vIn := inputAns oStmt x0
      let v0 := msgAnsRep msgs (msgIdxRep M t 0) (msgPosRep M t (msgIdxRep M t 0) x0)
      decide (vIn = v0))
  let consist := (List.finRange M).map (fun j =>
      ((List.finRange t).map (fun s =>
        let xa := queryPoint φ (chalFERep chals (outChalIdxRep M t j.succ) s)
        let xb := queryPoint φ (chalFERep chals (shiftChalIdxRep M t j) s)
        let va := msgAnsRep msgs (msgIdxRep M t j.castSucc)
          (msgPosRep M t (msgIdxRep M t j.castSucc) xa)
        let vb := msgAnsRep msgs (msgIdxRep M t j.succ)
          (msgPosRep M t (msgIdxRep M t j.succ) xa)
        let vc := msgAnsRep msgs (msgIdxRep M t j.castSucc)
          (msgPosRep M t (msgIdxRep M t j.castSucc) xb)
        let vd := msgAnsRep msgs (msgIdxRep M t j.succ)
          (msgPosRep M t (msgIdxRep M t j.succ) xb)
        decide (va = vb) && decide (vc = vd))).all (fun b => b))
  let finalVals := (List.finRange (Fintype.card ι)).map (fun k =>
      msgAnsRep msgs (msgIdxRep M t (Fin.last M))
        (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))
  foldChecks.all (fun b => b) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg)

/-- `simulateQ` collapse for the input-oracle query (rep spec). -/
theorem simulateQ_askInputRep (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j) (x : ι) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askInputRep M t x)
      = (pure (inputAns oStmt x) : OracleComp []ₒ F) := rfl

/-- `simulateQ` collapse for a message-oracle query (rep spec). -/
theorem simulateQ_askMsgRep (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecRep M ι t).length j.1)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askMsgRep M t j k)
      = (pure (msgAnsRep msgs j k) : OracleComp []ₒ F) := rfl

/-- **Central collapse**: under the honest oracle implementation, the t-repetition checking
computation is a pure computation of `checkingBoolRep` (for ARBITRARY oracle/message
values). -/
theorem simulateQ_checkingCompRep (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (checkingCompRep M φ deg t chals)
      = pure (checkingBoolRep M φ deg t oStmt msgs chals) := by
  unfold checkingCompRep checkingBoolRep
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun s =>
      let x0 := queryPoint φ (chalFERep chals (outChalIdxRep M t 0) s)
      let vIn := inputAns oStmt x0
      let v0 := msgAnsRep msgs (msgIdxRep M t 0) (msgPosRep M t (msgIdxRep M t 0) x0)
      decide (vIn = v0))
      (fun s => by
        rw [simulateQ_bind, simulateQ_askInputRep]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsgRep]
        simp only [pure_bind, simulateQ_pure])]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun j =>
      ((List.finRange t).map (fun s =>
        let xa := queryPoint φ (chalFERep chals (outChalIdxRep M t j.succ) s)
        let xb := queryPoint φ (chalFERep chals (shiftChalIdxRep M t j) s)
        let va := msgAnsRep msgs (msgIdxRep M t j.castSucc)
          (msgPosRep M t (msgIdxRep M t j.castSucc) xa)
        let vb := msgAnsRep msgs (msgIdxRep M t j.succ)
          (msgPosRep M t (msgIdxRep M t j.succ) xa)
        let vc := msgAnsRep msgs (msgIdxRep M t j.castSucc)
          (msgPosRep M t (msgIdxRep M t j.castSucc) xb)
        let vd := msgAnsRep msgs (msgIdxRep M t j.succ)
          (msgPosRep M t (msgIdxRep M t j.succ) xb)
        decide (va = vb) && decide (vc = vd))).all (fun b => b))
      (fun j => by
        rw [simulateQ_bind,
          simulateQ_askList _ _ _ (fun s =>
            let xa := queryPoint φ (chalFERep chals (outChalIdxRep M t j.succ) s)
            let xb := queryPoint φ (chalFERep chals (shiftChalIdxRep M t j) s)
            let va := msgAnsRep msgs (msgIdxRep M t j.castSucc)
              (msgPosRep M t (msgIdxRep M t j.castSucc) xa)
            let vb := msgAnsRep msgs (msgIdxRep M t j.succ)
              (msgPosRep M t (msgIdxRep M t j.succ) xa)
            let vc := msgAnsRep msgs (msgIdxRep M t j.castSucc)
              (msgPosRep M t (msgIdxRep M t j.castSucc) xb)
            let vd := msgAnsRep msgs (msgIdxRep M t j.succ)
              (msgPosRep M t (msgIdxRep M t j.succ) xb)
            decide (va = vb) && decide (vc = vd))
            (fun s => by
              rw [simulateQ_bind, simulateQ_askMsgRep]
              simp only [pure_bind]
              rw [simulateQ_bind, simulateQ_askMsgRep]
              simp only [pure_bind]
              rw [simulateQ_bind, simulateQ_askMsgRep]
              simp only [pure_bind]
              rw [simulateQ_bind, simulateQ_askMsgRep]
              simp only [pure_bind, simulateQ_pure])]
        simp only [pure_bind, simulateQ_pure])]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun k =>
      msgAnsRep msgs (msgIdxRep M t (Fin.last M))
        (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))
      (fun k => simulateQ_askMsgRep M t oStmt msgs _ _)]
  simp only [pure_bind, simulateQ_pure]

/-- **The t-repetition checking multi-round STIR verifier.** Forwards no oracles; its
`verify` is the genuine t-repetition checking computation. -/
noncomputable def stirCheckingVerifierRep :
    OracleVerifier []ₒ Unit (OracleStatement ι F) Bool (fun _ : Empty => Unit)
      ((stirMultiVSpecRep M ι t).toProtocolSpec F) where
  verify := fun _ chals => OptionT.lift (checkingCompRep M φ deg t chals)
  embed := ⟨fun i => i.elim, fun i => i.elim⟩
  hEq := fun i => i.elim

/-- **The t-repetition checking (M+1)-round STIR Vector IOPP**: the honest folding prover at
the rep spec together with the t-repetition checking verifier. -/
noncomputable def stirCheckingIOPRep :
    VectorIOP Unit (OracleStatement ι F) Unit (stirMultiVSpecRep M ι t) F where
  prover := stirMultiRoundProverRep M φ deg t
  verifier := stirCheckingVerifierRep M φ deg t

end CheckingVerifierRep

/-! ### 3. The honest prover's run-support invariant (rep spec) -/

section InvariantRep

variable [Nonempty ι]

/-- The honest packed message value at message round `iv` of the rep spec. -/
noncomputable def honestMsgRep (M t : ℕ) (f : ι → F) (iv : ℕ) (h : iv < 3 * M + 3)
    (hdir : iv % 3 = 1) : Vector F ((stirMultiVSpecRep M ι t).length ⟨iv, h⟩) :=
  Vector.cast (stirMultiVSpecRep_length_msg (ι := ι) (F := F) (M := M) (t := t)
    ⟨⟨iv, h⟩, by
      show (stirMultiVSpecRep M ι t).dir _ = .P_to_V
      rw [stirVSpec_dir_eq_msg_iff]; exact hdir⟩)
    (packFiniteFunction ι f)

/-- **Run-support invariant of the honest multi-round STIR prover at the rep spec** (symbolic
`M`, any round `k`): on the support of `runToRound k`, the carried context is the input
context and every transcript message is the honest packed fold of the input codeword (= the
packed input codeword, by `combine_single_self`). The proof is challenge-agnostic: the
challenge length `t` enters only through the (ignored) stored fold challenge. -/
theorem stirMultiRoundProverRep_runToRound_invariant (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (k : Fin (3 * M + 3 + 1)) :
    ∀ ts ∈ _root_.support
      ((stirMultiRoundProverRep M φ deg t).runToRound k stmtIn witIn),
      ts.2.1 = (stmtIn, witIn) ∧
      ∀ (iv : ℕ) (hik : iv < k.val) (hdir : iv % 3 = 1),
        ts.1 ⟨iv, hik⟩ = honestMsgRep M t (stmtIn.2 ()) iv
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
      · -- challenge (V_to_P) round: the new entry is a challenge; earlier entries unchanged
        rename_i hDir
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hout
        obtain ⟨chal, -, fch, hfch, rfl⟩ := hout
        have hfch' : fch = fun r => (st.1,
            if h : 0 < (stirMultiVSpecRep M ι t).length ⟨(j : ℕ), j.isLt⟩
            then r.get ⟨0, h⟩ else 0) := by
          dsimp only [stirMultiRoundProverRep] at hfch
          simpa only [support_pure, Set.mem_singleton_iff] using hfch
        refine ⟨by rw [hfch']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpecRep M ι t).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr chal (Fin.castSucc ⟨iv, hlt⟩) = _
          rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · -- the new entry is at the challenge round, whose direction contradicts `hdir`
          exfalso
          have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          rw [stirVSpec_dir_eq_chal_iff] at hDir
          exact hDir hdir
      · -- message (P_to_V) round: the new entry is the honest packed fold
        rename_i hDir
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hout
        obtain ⟨⟨msg, st'⟩, hms, rfl⟩ := hout
        have hms' : msg = Vector.cast (stirMultiVSpecRep_length_msg ⟨j, hDir⟩)
            (packFiniteFunction ι
              (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ())
                (fun _ : Fin 1 => deg))) ∧ st' = st := by
          dsimp only [stirMultiRoundProverRep] at hms
          simp only [liftM_pure, liftComp_pure, support_pure] at hms
          exact Prod.ext_iff.mp (Set.mem_singleton_iff.mp hms)
        obtain ⟨hmsg, hst'⟩ := hms'
        refine ⟨by rw [hst']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpecRep M ι t).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.castSucc ⟨iv, hlt⟩) = _
          rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          letI : DecidableEq ι := Classical.decEq ι
          show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpecRep M ι t).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.last (j : ℕ)) = _
          rw [Fin.snoc_last, hmsg, ihSt]
          show Vector.cast _ (packFiniteFunction ι
            (Combine.combine φ deg st.2 (fun _ : Fin 1 => stmtIn.2 ())
              (fun _ : Fin 1 => deg))) = _
          rw [Round.combine_single_self]
          rfl

end InvariantRep

/-! ### The honest checks pass (rep spec) -/

section HonestChecksRep

variable [Nonempty ι]

/-- Answer of the honest packed message oracle at the rep spec: reading position `k` returns
the function value at the `k`-th enumeration point of the domain. -/
theorem answer_honest_packRep (M t : ℕ) (f : ι → F)
    (j : ((stirMultiVSpecRep M ι t).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpecRep M ι t).length j.1)) :
    OracleInterface.answer
      ((Vector.cast (stirMultiVSpecRep_length_msg j) (packFiniteFunction ι f)
        : Vector F ((stirMultiVSpecRep M ι t).length j.1))
        : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j) k
      = f ((Fintype.equivFin ι).symm ⟨(k : ℕ),
          lt_of_lt_of_eq k.isLt (stirMultiVSpecRep_length_msg j).symm⟩) := by
  show (Vector.cast (stirMultiVSpecRep_length_msg j) (packFiniteFunction ι f))[(k : ℕ)] = _
  rw [Vector.getElem_cast, packFiniteFunction, Vector.getElem_ofFn]

/-- Boolean `all` over a `List.finRange`-map is the universal statement. -/
theorem all_map_finRange_iff {n : ℕ} (f : Fin n → Bool) :
    (((List.finRange n).map f).all (fun b => b) = true) ↔ ∀ i : Fin n, f i = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (f i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · intro h b hb
    rw [List.mem_map] at hb
    obtain ⟨i, -, rfl⟩ := hb
    exact h i

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ)

open scoped Classical in
/-- **The honest prover passes every t-repetition check**: if the input oracle is a genuine
codeword and every transcript message is its honest packed fold, the t-repetition checking
verifier's decision bit is `true`, for every challenge vector. -/
theorem checkingBoolRep_honest (f : ι → F) (hmem : f ∈ ReedSolomon.code φ deg)
    (oStmt : ∀ i, OracleStatement ι F i) (hOStmt : oStmt () = f)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (hmsgs : ∀ j, msgs j
      = Vector.cast (stirMultiVSpecRep_length_msg j) (packFiniteFunction ι f))
    (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges) :
    checkingBoolRep M φ deg t oStmt msgs chals = true := by
  -- the uniform honest-message evaluation at a domain point
  have hans : ∀ (j) (x : ι), msgAnsRep msgs j (msgPosRep M t j x) = f x := by
    intro j x
    rw [msgAnsRep, hmsgs j, answer_honest_packRep]
    show f ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)) = f x
    rw [Equiv.symm_apply_apply]
  -- the honest final-message evaluation at an enumeration index
  have hfin : ∀ k : Fin (Fintype.card ι),
      msgAnsRep msgs (msgIdxRep M t (Fin.last M))
        (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k)
      = f ((Fintype.equivFin ι).symm k) := by
    intro k
    rw [msgAnsRep, hmsgs _, answer_honest_packRep]
    rfl
  unfold checkingBoolRep
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- round-0 fold-query checks
    rw [all_map_finRange_iff]
    intro s
    simp only [decide_eq_true_eq]
    rw [inputAns_apply, hOStmt, hans]
  · -- per-round consistency checks
    rw [all_map_finRange_iff]
    intro j
    rw [all_map_finRange_iff]
    intro s
    simp only [hans, Bool.and_eq_true, decide_eq_true_eq, and_self]
  · -- final low-degree check
    have hfun : (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAnsRep msgs (msgIdxRep M t (Fin.last M))
            (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0)) = f := by
      funext x
      rw [List.getD_eq_getElem _ _ (by
        simp only [List.length_map, List.length_finRange]
        exact (Fintype.equivFin ι x).isLt)]
      rw [List.getElem_map, List.getElem_finRange, hfin]
      simp only [Fin.cast_mk, Fin.eta, Equiv.symm_apply_apply]
    rw [hfun]
    exact hmem

/-! #### 4. Exact decomposition of the t-repetition checking predicate -/

open scoped Classical in
/-- Exact decomposition of the t-repetition checking predicate: the initial fold query agrees
at EVERY repetition coordinate, every sampled adjacent-round pair agrees at the out and shift
challenges at EVERY repetition coordinate, and the final message is a Reed-Solomon
codeword. -/
theorem checkingBoolRep_eq_true_iff
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges) :
    checkingBoolRep M φ deg t oStmt msgs chals = true ↔
      (∀ s : Fin t,
        inputAns oStmt (queryPoint φ (chalFERep chals (outChalIdxRep M t 0) s))
          = msgAnsRep msgs (msgIdxRep M t 0)
              (msgPosRep M t (msgIdxRep M t 0)
                (queryPoint φ (chalFERep chals (outChalIdxRep M t 0) s)))) ∧
      (∀ j : Fin M, ∀ s : Fin t,
        (msgAnsRep msgs (msgIdxRep M t j.castSucc)
            (msgPosRep M t (msgIdxRep M t j.castSucc)
              (queryPoint φ (chalFERep chals (outChalIdxRep M t j.succ) s)))
          = msgAnsRep msgs (msgIdxRep M t j.succ)
            (msgPosRep M t (msgIdxRep M t j.succ)
              (queryPoint φ (chalFERep chals (outChalIdxRep M t j.succ) s)))) ∧
        (msgAnsRep msgs (msgIdxRep M t j.castSucc)
            (msgPosRep M t (msgIdxRep M t j.castSucc)
              (queryPoint φ (chalFERep chals (shiftChalIdxRep M t j) s)))
          = msgAnsRep msgs (msgIdxRep M t j.succ)
            (msgPosRep M t (msgIdxRep M t j.succ)
              (queryPoint φ (chalFERep chals (shiftChalIdxRep M t j) s))))) ∧
      (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAnsRep msgs (msgIdxRep M t (Fin.last M))
            (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0))
        ∈ ReedSolomon.code φ deg := by
  unfold checkingBoolRep
  simp only [Bool.and_eq_true, decide_eq_true_eq, all_map_finRange_iff]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

end HonestChecksRep

/-! ### Completeness of the t-repetition checking IOP -/

section CompletenessRep

open OracleReduction

variable [Nonempty ι]

/-- Finiteness of the rep-spec challenge oracle spec (every challenge range is
`Vector F t`), pinned to the canonical `challengeOracleInterface` (the interface that the
completeness machinery elaborates `[pSpec.Challenge]ₒ` with). -/
instance {M t : ℕ} :
    ([((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).Fintype
    where
  fintype_B := fun q => by
    show Fintype (((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge q.1)
    dsimp
    infer_instance

/-- Inhabitedness of the rep-spec challenge oracle spec (pinned as above). -/
instance {M t : ℕ} :
    ([((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).Inhabited
    where
  inhabited_B := fun q => by
    show Inhabited (((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge q.1)
    dsimp
    infer_instance

/-- `simulateQ` collapse of the t-repetition checking verifier's core computation at the
`OptionT` layer. -/
theorem simulateQ_lift_checkingCompRep (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ)
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpecRep M ι t).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenges) :
    (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (OptionT.lift (checkingCompRep M φ deg t chals)) : OptionT (OracleComp []ₒ) Bool)
      = pure (checkingBoolRep M φ deg t oStmt msgs chals) := by
  show (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (checkingCompRep M φ deg t chals >>= fun b => (pure (some b) : OracleComp _ (Option Bool)))
      : OracleComp []ₒ (Option Bool))
    = pure (some (checkingBoolRep M φ deg t oStmt msgs chals))
  rw [simulateQ_bind, simulateQ_checkingCompRep]
  simp

/-- **Pure form of the t-repetition checking verifier's non-oracle run**: `toVerifier.verify`
is the `pure` of the decision bit, for every transcript. -/
theorem checkingVerifierRep_toVerifier_verify (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpecRep M ι t).toProtocolSpec F)) :
    (stirCheckingVerifierRep M φ deg t).toVerifier.verify stmtIn tr
      = pure (checkingBoolRep M φ deg t stmtIn.2 tr.messages tr.challenges,
          fun i : Empty => i.elim) := by
  dsimp only [OracleVerifier.toVerifier, stirCheckingVerifierRep]
  erw [simulateQ_lift_checkingCompRep, pure_bind]

set_option maxHeartbeats 1600000 in
/-- **Perfect completeness of the t-repetition checking (M+1)-round STIR Vector IOPP**, for
arbitrary symbolic depth `M` and repetition parameter `t`, against the genuine
perfect-completeness relation `stirRelation deg φ 0`: by the run-support invariant every
consistency check compares equal values FOR EVERY repetition coordinate `s`, and the final
full-read low-degree check sees exactly the input codeword, which the `δ = 0` input relation
forces into the code. -/
theorem stirCheckingIOPRep_perfectCompleteness (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (t : ℕ) :
    OracleReduction.perfectCompleteness (pure ()) isEmptyElim
      (stirRelation deg φ 0) acceptRejectOracleRel (stirCheckingIOPRep M φ deg t) := by
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness
    (reduction := stirCheckingIOPRep M φ deg t) (stirRelation deg φ 0) acceptRejectOracleRel
    (pure ()) isEmptyElim inferInstance
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- the δ = 0 input relation is genuine code membership
  have hmem : oStmtIn () ∈ ReedSolomon.code φ deg := by
    have h0 : Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg)
        ≤ ((0 : ℝ≥0) : ENNReal) := h_relIn
    exact mem_of_relDistFromCode_le_zero ⟨0, Submodule.zero_mem _⟩ (by simpa using h0)
  dsimp only [stirCheckingIOPRep, stirMultiRoundProverRep]
  simp only [checkingVerifierRep_toVerifier_verify]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, _root_.map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails (the prefix is plain `OracleComp`; the rest is pure)
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun α _hα => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_map, OptionT.probFailure_liftComp_of_OracleComp_Option]
      simp only [OptionT.run_pure, HasEvalPMF.probFailure_eq_zero, zero_add,
        probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff, reduceCtorEq,
        not_false_eq_true]
  · -- CORRECTNESS: every output in the support satisfies the relation + agreement
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, hα, hx⟩ := hx
    -- the run-support invariant: every transcript message is the honest packed codeword
    have hα' : α ∈ _root_.support
        ((stirMultiRoundProverRep M φ deg t).runToRound (Fin.last (3 * M + 3))
          (stmtIn, oStmtIn) witIn) := by
      simpa only [OptionT.support_liftM] using hα
    have hinv := stirMultiRoundProverRep_runToRound_invariant M φ deg t (stmtIn, oStmtIn) witIn
      (Fin.last (3 * M + 3)) α hα'
    have hmsgs : ∀ j, FullTranscript.messages
        (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) α.1 j
        = Vector.cast (stirMultiVSpecRep_length_msg j)
            (packFiniteFunction ι (oStmtIn ())) := by
      intro j
      have hdir : ((j.1 : Fin (3 * M + 3)) : ℕ) % 3 = 1 :=
        (stirVSpec_dir_eq_msg_iff (M := M) (msgLen := fun _ => Fintype.card ι)
          (chalLen := t)).mp j.2
      exact hinv.2 j.1.val j.1.isLt hdir
    have hbool : checkingBoolRep M φ deg t oStmtIn
        (FullTranscript.messages (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) α.1)
        (FullTranscript.challenges (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) α.1)
        = true :=
      checkingBoolRep_honest M φ deg t (oStmtIn ()) hmem oStmtIn rfl _ hmsgs _
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_map, support_map, Set.mem_image] at hx
    erw [OptionT_run_liftComp_pure] at hx
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, Option.map_some,
      Option.some.injEq] at hx
    subst hx
    have hfn : ∀ (f g : ∀ _ : Empty, Unit), f = g := fun _ _ => funext fun i => i.elim
    refine ⟨?_, ?_, hfn _ _⟩
    · simp only [acceptRejectOracleRel, Set.mem_singleton_iff, Prod.mk.injEq, hbool]
    · show (true : Bool) = checkingBoolRep M φ deg t oStmtIn _ _
      rw [hbool]

end CompletenessRep

section ReadersRep

variable [Nonempty ι]
variable {M t : ℕ}

/-- Read the raw vector payload at round `k` from a partial transcript. -/
def trVecRep {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (k : ℕ) (hk : k < (m : ℕ)) :
    Vector F ((stirMultiVSpecRep M ι t).length ⟨k, lt_of_lt_of_le hk m.is_le⟩) :=
  tr ⟨k, hk⟩

/-- Read the (unpacked) message function at message round `3j + 1` (raw `ℕ` index `j ≤ M`). -/
noncomputable def trMsgFRep {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (j : ℕ) (h : 3 * j + 1 < (m : ℕ)) : ι → F :=
  fun x => (trVecRep tr (3 * j + 1) h).get
    (Fin.cast (stirMultiRep_length_msg_raw _ _ (by omega)) (Fintype.equivFin ι x))

/-- Read the field value of coordinate `s` of the (length-`t`) challenge at round `k`. -/
def trChalFRep {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (k : ℕ) (hk : k < (m : ℕ)) (hmod : k % 3 ≠ 1) (s : Fin t) : F :=
  (trVecRep tr k hk).get ⟨(s : ℕ), by
    rw [stirMultiRep_length_chal_raw (M := M) (ι := ι) k _ hmod]; exact s.isLt⟩

/-- Reading strictly below the concatenation point is reading the original transcript. -/
theorem trVecRep_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (msg : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (k : ℕ) (hk : k < (m.castSucc : ℕ)) (hk' : k < (m.succ : ℕ)) :
    trVecRep (tr.concat msg) k hk' = trVecRep tr k hk := by
  exact Fin.snoc_castSucc
    (α := fun j => ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type
      (Fin.castLE m.succ.is_le j)) msg tr ⟨k, hk⟩

/-- Reading at the concatenation point gives the new element. -/
theorem trVecRep_concat_last {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (msg : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (hk' : (m : ℕ) < (m.succ : ℕ)) :
    trVecRep (tr.concat msg) (m : ℕ) hk' = msg := by
  exact Fin.snoc_last
    (α := fun j => ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type
      (Fin.castLE m.succ.is_le j)) msg tr

/-- Message reads below the concat point are unchanged. -/
theorem trMsgFRep_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (msg : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (j : ℕ) (h : 3 * j + 1 < (m.castSucc : ℕ))
    (h' : 3 * j + 1 < (m.succ : ℕ)) :
    trMsgFRep (tr.concat msg) j h' = trMsgFRep tr j h := by
  funext x
  unfold trMsgFRep
  rw [trVecRep_concat (hk := h)]

/-- Challenge reads below the concat point are unchanged. -/
theorem trChalFRep_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (msg : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (k : ℕ) (hk : k < (m.castSucc : ℕ)) (hk' : k < (m.succ : ℕ)) (hmod : k % 3 ≠ 1)
    (s : Fin t) :
    trChalFRep (tr.concat msg) k hk' hmod s = trChalFRep tr k hk hmod s := by
  unfold trChalFRep
  congr 1
  rw [trVecRep_concat (hk := hk)]

end ReadersRep

section PredRep

variable [Nonempty ι]
variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) (t : ℕ)

/-- All point-checks fully committed strictly below round `m` hold at EVERY repetition
coordinate `s : Fin t`. -/
def stirChecksBelowRep (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F)) : Prop :=
  (∀ _ : 3 ≤ (m : ℕ), ∀ s : Fin t,
    inputAns stmtIn.2 (queryPoint φ (trChalFRep tr 2 (by omega) (by omega) s))
      = trMsgFRep tr 0 (by omega) (queryPoint φ (trChalFRep tr 2 (by omega) (by omega) s))) ∧
  (∀ j : Fin M, ∀ _ : 3 * (j : ℕ) + 6 ≤ (m : ℕ), ∀ s : Fin t,
    trMsgFRep tr (j : ℕ) (by omega)
        (queryPoint φ (trChalFRep tr (3 * (j : ℕ) + 5) (by omega) (by omega) s))
      = trMsgFRep tr ((j : ℕ) + 1) (by omega)
        (queryPoint φ (trChalFRep tr (3 * (j : ℕ) + 5) (by omega) (by omega) s))) ∧
  (∀ j : Fin M, ∀ _ : 3 * (j : ℕ) + 5 ≤ (m : ℕ), ∀ s : Fin t,
    trMsgFRep tr (j : ℕ) (by omega)
        (queryPoint φ (trChalFRep tr (3 * (j : ℕ) + 3) (by omega) (by omega) s))
      = trMsgFRep tr ((j : ℕ) + 1) (by omega)
        (queryPoint φ (trChalFRep tr (3 * (j : ℕ) + 3) (by omega) (by omega) s)))

/-- The fully-committed pair with pending binding challenge is locked (unchanged from t=1:
it speaks only about messages). -/
def stirPendingLockedRep (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F)) : Prop :=
  (∀ _ : (m : ℕ) = 2, ∀ x : ι,
    inputAns stmtIn.2 x = trMsgFRep tr 0 (by omega) x) ∧
  (∀ j : Fin M, ∀ _ : (m : ℕ) = 3 * (j : ℕ) + 5, ∀ x : ι,
    trMsgFRep tr (j : ℕ) (by omega) x
      = trMsgFRep tr ((j : ℕ) + 1) (by omega) x)

/-- The last committed message is a codeword (unchanged from t=1). -/
def stirLastInRSRep (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F)) : Prop :=
  ((m : ℕ) ≤ 1 → stmtIn.2 () ∈ ReedSolomon.code φ deg) ∧
  (∀ j : ℕ, ∀ h1 : 3 * j + 1 < (m : ℕ), (m : ℕ) ≤ 3 * j + 4 →
    trMsgFRep tr j h1 ∈ ReedSolomon.code φ deg)

/-- The retired-prefix winnable state at the rep spec. -/
def stirWinnableRep (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F)) : Prop :=
  stirChecksBelowRep M φ t m stmtIn tr ∧ stirPendingLockedRep M t m stmtIn tr ∧
    stirLastInRSRep M φ deg t m stmtIn tr

/-- The checking-verifier state predicate at the rep spec. -/
def stirCheckingPredRep (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpecRep M ι t).toProtocolSpec F)) : Prop :=
  ((stmtIn, ()) ∈ stirRelation deg φ δ) ∨ stirWinnableRep M φ deg t m stmtIn tr

/-- Seam lemma `hEmpty` at the rep spec. -/
theorem stirCheckingPredRep_empty (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript 0 ((stirMultiVSpecRep M ι t).toProtocolSpec F)) :
    (stmtIn, ()) ∈ stirRelation deg φ δ ↔ stirCheckingPredRep M φ deg δ t 0 stmtIn tr := by
  constructor
  · intro h; exact Or.inl h
  · rintro (h | ⟨_, _, hlast, _⟩)
    · exact h
    · exact relDist_le_of_mem φ deg δ (hlast (by simp))

/-- Generalized concat-at-last for the rep challenge reads. -/
theorem trChalFRep_concat_last' {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (c : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (k : ℕ) (hkm : k = (m : ℕ)) (hk' : k < (m.succ : ℕ)) (hmod : k % 3 ≠ 1) (s : Fin t) :
    trChalFRep (tr.concat c) k hk' hmod s
      = c.get ⟨(s : ℕ), by
          subst hkm
          rw [stirMultiRep_length_chal (M := M) (ι := ι) m hmod]; exact s.isLt⟩ := by
  subst hkm
  unfold trChalFRep
  congr 1
  exact trVecRep_concat_last tr c hk'

/-- Uniform down-transport of committed checks (rep spec). -/
theorem stirChecksBelowRep_concat {m : Fin (3 * M + 3)}
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (msg : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (h : stirChecksBelowRep M φ t m.succ stmtIn (tr.concat msg)) :
    stirChecksBelowRep M φ t m.castSucc stmtIn tr := by
  obtain ⟨h0, ha, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro h3 s
    simp only [Fin.val_castSucc] at h3
    have := h0 (by simp only [Fin.val_succ]; omega) s
    rwa [trChalFRep_concat tr msg 2 (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgFRep_concat tr msg 0 (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this
  · intro j hj s
    simp only [Fin.val_castSucc] at hj
    have := ha j (by simp only [Fin.val_succ]; omega) s
    rwa [trChalFRep_concat tr msg (3 * (j : ℕ) + 5) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgFRep_concat tr msg (j : ℕ) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega),
      trMsgFRep_concat tr msg ((j : ℕ) + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this
  · intro j hj s
    simp only [Fin.val_castSucc] at hj
    have := hb j (by simp only [Fin.val_succ]; omega) s
    rwa [trChalFRep_concat tr msg (3 * (j : ℕ) + 3) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgFRep_concat tr msg (j : ℕ) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega),
      trMsgFRep_concat tr msg ((j : ℕ) + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this

/-- No up-flip at the fold and shift challenges (rep spec). -/
theorem stirCheckingPredRep_concat_zero {m : Fin (3 * M + 3)}
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (c : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (hmod : (m : ℕ) % 3 = 0)
    (h : stirCheckingPredRep M φ deg δ t m.succ stmtIn (tr.concat c)) :
    stirCheckingPredRep M φ deg δ t m.castSucc stmtIn tr := by
  rcases h with h | ⟨hchk, hpend, hlast⟩
  · exact Or.inl h
  refine Or.inr ⟨stirChecksBelowRep_concat M φ t stmtIn tr c hchk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h2; exfalso; simp only [Fin.val_castSucc] at h2; omega
  · intro j h5; exfalso; simp only [Fin.val_castSucc] at h5; omega
  · intro h1
    simp only [Fin.val_castSucc] at h1
    exact hlast.1 (by simp only [Fin.val_succ]; omega)
  · intro j h1 h2
    simp only [Fin.val_castSucc] at h1 h2
    have := hlast.2 j (by simp only [Fin.val_succ]; omega)
      (by simp only [Fin.val_succ]; omega)
    rwa [trMsgFRep_concat tr c j (by simp only [Fin.val_castSucc]; omega)
      (by simp only [Fin.val_succ]; omega)] at this

/-- No up-flip at message rounds (rep spec). -/
theorem stirCheckingPredRep_concat_msg {m : Fin (3 * M + 3)}
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (msg : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (hmod : (m : ℕ) % 3 = 1)
    (h : stirCheckingPredRep M φ deg δ t m.succ stmtIn (tr.concat msg)) :
    stirCheckingPredRep M φ deg δ t m.castSucc stmtIn tr := by
  rcases h with h | ⟨hchk, hpend, hlast⟩
  · exact Or.inl h
  by_cases hm1 : (m : ℕ) = 1
  · refine Or.inl ?_
    have hpend1 := hpend.1 (by simp only [Fin.val_succ]; omega)
    have hlast1 := hlast.2 0 (by simp only [Fin.val_succ]; omega)
      (by simp only [Fin.val_succ]; omega)
    have hf : stmtIn.2 () = trMsgFRep (tr.concat msg) 0
        (by simp only [Fin.val_succ]; omega) := by
      funext x; exact hpend1 x
    show δᵣ(stmtIn.2 (), (ReedSolomon.code φ deg : Set (ι → F))) ≤ (δ : ℝ≥0∞)
    exact relDist_le_of_mem φ deg δ (by rw [hf]; exact hlast1)
  · refine Or.inr ⟨stirChecksBelowRep_concat M φ t stmtIn tr msg hchk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro h2; exfalso; simp only [Fin.val_castSucc] at h2; omega
    · intro j h5; exfalso; simp only [Fin.val_castSucc] at h5; omega
    · intro h1; exfalso; simp only [Fin.val_castSucc] at h1; omega
    · intro j h1 h2
      simp only [Fin.val_castSucc] at h1 h2
      have hmj : (m : ℕ) = 3 * j + 4 := by omega
      have hjM : j < M := by have := m.isLt; omega
      have hpend2 := hpend.2 ⟨j, hjM⟩ (by simp only [Fin.val_succ]; omega)
      have hlast2 := hlast.2 (j + 1) (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)
      have hEq : trMsgFRep (tr.concat msg) j
          (by simp only [Fin.val_succ]; omega)
            = trMsgFRep (tr.concat msg) (j + 1) (by simp only [Fin.val_succ]; omega) := by
        funext x; exact hpend2 x
      have hmem : trMsgFRep (tr.concat msg) j (by simp only [Fin.val_succ]; omega)
          ∈ ReedSolomon.code φ deg := by rw [hEq]; exact hlast2
      rwa [trMsgFRep_concat tr msg j (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at hmem

/-- Acceptance forces the predicate at the final round (rep spec). -/
theorem stirCheckingPredRep_full_of_accept
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript (Fin.last (3 * M + 3)) ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (hacc : checkingBoolRep M φ deg t stmtIn.2
      (FullTranscript.messages (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) tr)
      (FullTranscript.challenges (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) tr)
      = true) :
    stirCheckingPredRep M φ deg δ t (Fin.last (3 * M + 3)) stmtIn tr := by
  obtain ⟨h0, hcons, hfin⟩ :=
    (checkingBoolRep_eq_true_iff (M := M) (φ := φ) (deg := deg) (t := t)
      stmtIn.2 _ _).mp hacc
  refine Or.inr ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro _ s
    exact h0 s
  · intro j _ s
    exact (hcons j s).1
  · intro j _ s
    exact (hcons j s).2
  · intro h2; exfalso; simp only [Fin.val_last] at h2; omega
  · intro j h5; exfalso; simp only [Fin.val_last] at h5; omega
  · intro h1; exfalso; simp only [Fin.val_last] at h1; omega
  · intro j h1 h2
    simp only [Fin.val_last] at h1 h2
    have hjM : M = j := by omega
    subst hjM
    have hbridge : (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAnsRep (FullTranscript.messages
              (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) tr)
            (msgIdxRep M t (Fin.last M))
            (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0))
        = trMsgFRep tr M h1 := by
      funext x
      rw [listGetD_finRange_map
        (fun k => msgAnsRep (FullTranscript.messages
            (pSpec := (stirMultiVSpecRep M ι t).toProtocolSpec F) tr)
          (msgIdxRep M t (Fin.last M))
          (Fin.cast (stirMultiVSpecRep_length_msg (msgIdxRep M t (Fin.last M))) k))
        ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) (Fin.isLt _)]
      rfl
    rw [← hbridge]
    exact hfin

/-- Flip characterization at the round-2 challenge (rep spec): a genuine flip forces the
input δ-far, the first message a codeword, and the input-link check passing at EVERY
repetition coordinate of the fresh challenge. -/
theorem stirCheckingPredRep_flip_two {m : Fin (3 * M + 3)} (hm : (m : ℕ) = 2)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (c : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (hno : ¬ stirCheckingPredRep M φ deg δ t m.castSucc stmtIn tr)
    (hyes : stirCheckingPredRep M φ deg δ t m.succ stmtIn (tr.concat c)) :
    ¬ ((stmtIn, ()) ∈ stirRelation deg φ δ) ∧
    trMsgFRep tr 0 (by simp only [Fin.val_castSucc]; omega) ∈ ReedSolomon.code φ deg ∧
    (∀ s : Fin t,
      inputAns stmtIn.2 (queryPoint φ
        (c.get ⟨(s : ℕ), by
          rw [stirMultiRep_length_chal (M := M) (ι := ι) m (by omega)]; exact s.isLt⟩))
      = trMsgFRep tr 0 (by simp only [Fin.val_castSucc]; omega) (queryPoint φ
        (c.get ⟨(s : ℕ), by
          rw [stirMultiRep_length_chal (M := M) (ι := ι) m (by omega)]; exact s.isLt⟩))) := by
  have hrel : ¬ ((stmtIn, ()) ∈ stirRelation deg φ δ) := fun h => hno (Or.inl h)
  rcases hyes with h | ⟨hchk, _, hlast⟩
  · exact absurd h hrel
  refine ⟨hrel, ?_, ?_⟩
  · have := hlast.2 0 (by simp only [Fin.val_succ]; omega) (by simp only [Fin.val_succ]; omega)
    rwa [trMsgFRep_concat tr c 0 (by simp only [Fin.val_castSucc]; omega)
      (by simp only [Fin.val_succ]; omega)] at this
  · intro s
    have hC0 := hchk.1 (by simp only [Fin.val_succ]; omega) s
    rwa [trChalFRep_concat_last' M t tr c 2 hm.symm (by simp only [Fin.val_succ]; omega)
        (by omega) s,
      trMsgFRep_concat tr c 0 (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at hC0

/-- Flip characterization at a later out-challenge (rep spec). -/
theorem stirCheckingPredRep_flip_out {m : Fin (3 * M + 3)} {j : ℕ} (hjM : j < M)
    (hm : (m : ℕ) = 3 * j + 5)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpecRep M ι t).toProtocolSpec F))
    (c : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Type m)
    (hno : ¬ stirCheckingPredRep M φ deg δ t m.castSucc stmtIn tr)
    (hyes : stirCheckingPredRep M φ deg δ t m.succ stmtIn (tr.concat c)) :
    (∃ x : ι, trMsgFRep tr j (by simp only [Fin.val_castSucc]; omega) x
      ≠ trMsgFRep tr (j + 1) (by simp only [Fin.val_castSucc]; omega) x) ∧
    (∀ s : Fin t,
      trMsgFRep tr j (by simp only [Fin.val_castSucc]; omega) (queryPoint φ
        (c.get ⟨(s : ℕ), by
          rw [stirMultiRep_length_chal (M := M) (ι := ι) m (by omega)]; exact s.isLt⟩))
      = trMsgFRep tr (j + 1) (by simp only [Fin.val_castSucc]; omega) (queryPoint φ
        (c.get ⟨(s : ℕ), by
          rw [stirMultiRep_length_chal (M := M) (ι := ι) m (by omega)]; exact s.isLt⟩))) := by
  have hrel : ¬ ((stmtIn, ()) ∈ stirRelation deg φ δ) := fun h => hno (Or.inl h)
  rcases hyes with h | ⟨hchk, hpend, hlast⟩
  · exact absurd h hrel
  constructor
  · by_contra hcon
    push_neg at hcon
    refine hno (Or.inr ⟨stirChecksBelowRep_concat M φ t stmtIn tr c hchk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩)
    · intro h2; exfalso; simp only [Fin.val_castSucc] at h2; omega
    · intro j' hj'
      simp only [Fin.val_castSucc] at hj'
      have hjj : (j' : ℕ) = j := by omega
      intro x
      simp only [hjj]
      exact hcon x
    · intro h1; exfalso; simp only [Fin.val_castSucc] at h1; omega
    · intro j'' h1 h2
      simp only [Fin.val_castSucc] at h1 h2
      have hj'' : j'' = j + 1 := by omega
      subst hj''
      have := hlast.2 (j + 1) (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)
      rwa [trMsgFRep_concat tr c (j + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this
  · intro s
    have hxa := hchk.2.1 ⟨j, hjM⟩ (by simp only [Fin.val_succ]; omega) s
    rwa [trChalFRep_concat_last' M t tr c (3 * j + 5) hm.symm
        (by simp only [Fin.val_succ]; omega) (by omega) s,
      trMsgFRep_concat tr c j (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega),
      trMsgFRep_concat tr c (j + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at hxa

end PredRep


section FlipBoundsRep

variable [Nonempty ι]
variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) (t : ℕ)

variable {ιo : Type} {oSpec : OracleSpec ιo} {σ : Type}
variable {StmtOut WitOut : Type}
variable [∀ i, SampleableType ((((stirMultiVSpecRep M ι t)).toProtocolSpec F).Challenge i)]

/-- Zero flip probability at the fold and shift challenges (rep spec). -/
theorem stirFlipRep_le_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx) (hi : (i.1 : ℕ) % 3 = 0)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (prover : Prover oSpec (Unit × ∀ i, OracleStatement ι F i) Unit StmtOut WitOut
      ((stirMultiVSpecRep M ι t).toProtocolSpec F)) :
    Pr[fun x : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Transcript i.1.castSucc ×
          ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge i ×
          (oSpec + [((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        ¬ stirCheckingPredRep M φ deg δ t i.1.castSucc stmtIn x.1 ∧
          stirCheckingPredRep M φ deg δ t i.1.succ stmtIn (x.1.concat x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp
              (((stirMultiVSpecRep M ι t).toProtocolSpec F).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (0 : ℝ≥0∞) := by
  refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
  rintro ⟨tr, ch, lg⟩ _ ⟨hn, hy⟩
  exact hn (stirCheckingPredRep_concat_zero M φ deg δ t stmtIn tr ch hi hy)

/-- **The round-2 flip bound at the rep spec**: the flip probability at the input-link
binding challenge is at most `((|F| − (⌊δ·|ι|⌋ + 1))/|F|)^t` — the `t`-fold power of the
single-query bound, by the product-marginal domination over the coordinates of the one
freshly drawn vector challenge. -/
theorem stirFlipRep_le_round2
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx) (hi : (i.1 : ℕ) = 2)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (prover : Prover oSpec (Unit × ∀ i, OracleStatement ι F i) Unit StmtOut WitOut
      ((stirMultiVSpecRep M ι t).toProtocolSpec F)) :
    Pr[fun x : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Transcript i.1.castSucc ×
          ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge i ×
          (oSpec + [((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        ¬ stirCheckingPredRep M φ deg δ t i.1.castSucc stmtIn x.1 ∧
          stirCheckingPredRep M φ deg δ t i.1.succ stmtIn (x.1.concat x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp
              (((stirMultiVSpecRep M ι t).toProtocolSpec F).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (((Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞)) ^ t := by
  classical
  have hmod : (i.1 : ℕ) % 3 ≠ 1 := by omega
  have hlen : (stirMultiVSpecRep M ι t).length i.1 = t :=
    stirMultiRep_length_chal (M := M) (ι := ι) i.1 hmod
  refine probEvent_bind_le_of_forall_support init _ _ _ (fun s0 _ => ?_)
  rw [simulateQ_bind, StateT.run'_bind_lib]
  refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
  obtain ⟨⟨⟨tr, pst⟩, log⟩, s'⟩ := rk
  dsimp only
  rw [liftComp_eq_liftM]
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s' i
    (fun ch => pure (tr, ch, log)) _]
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [← probEvent_bind_eq_tsum]
  by_cases hno : stirCheckingPredRep M φ deg δ t i.1.castSucc stmtIn tr
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro x hx ⟨hn, -⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨ch, -, rfl⟩ := hx
    exact hn hno
  · by_cases hrel : (stmtIn, ()) ∈ stirRelation deg φ δ
    · exact absurd (Or.inl hrel) hno
    · have h1 : 3 * 0 + 1 < (i.1.castSucc : ℕ) := by
        simp only [Fin.val_castSucc]; omega
      by_cases hg : trMsgFRep tr 0 h1 ∈ ReedSolomon.code φ deg
      · set f : ι → F := stmtIn.2 () with hf
        set g1 : ι → F := trMsgFRep tr 0 h1 with hg1
        have hfar : (δ : ℝ≥0∞) < δᵣ(f, (ReedSolomon.code φ deg : Set (ι → F))) :=
          not_le.mp (fun hle => hrel hle)
        have hle : δᵣ(f, (ReedSolomon.code φ deg : Set (ι → F)))
            ≤ ((Code.relHammingDist f g1 : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_nnratCast]
          exact Code.relDistFromCode_le_relDist_to_mem f g1 hg
        have hδrel : δ < (Code.relHammingDist f g1 : ℝ≥0) := by
          exact_mod_cast lt_of_lt_of_le hfar hle
        set D : Finset ι := Finset.univ.filter (fun x => f x ≠ g1 x) with hD
        have hham : hammingDist f g1 = D.card := rfl
        have hcard : δ * (Fintype.card ι : ℝ≥0) < (D.card : ℝ≥0) := by
          have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
            exact_mod_cast Fintype.card_pos
          have hrw : (Code.relHammingDist f g1 : ℝ≥0)
              = (D.card : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
            rw [Code.relHammingDist, hham]
            push_cast
            ring
          rw [hrw] at hδrel
          calc δ * (Fintype.card ι : ℝ≥0)
              < ((D.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0) :=
                mul_lt_mul_of_pos_right hδrel hn
            _ = (D.card : ℝ≥0) := div_mul_cancel₀ _ (ne_of_gt hn)
        have hfloor : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ D.card := by
          have := (Nat.floor_lt (zero_le _)).mpr hcard
          omega
        -- the per-coordinate agreement set
        set L : Set F := {r : F | inputAns stmtIn.2 (queryPoint φ r)
          = trMsgFRep tr 0 h1 (queryPoint φ r)} with hL
        -- the product-marginal bound over the coordinates of the fresh vector challenge
        refine le_trans (probEvent_bind_le_uniform_vector_marginal
          ($ᵗ (((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge i))
          (fun ch => pure (tr, ch, log)) _ (fun _ => L)
          (fun v => le_of_eq (probOutput_uniform_vector v)) ?_) ?_
        · -- a coordinate outside the agreement set kills the flip event
          rintro v ⟨s, hs⟩
          refine probEvent_eq_zero ?_
          rintro x hx ⟨hn, hy⟩
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          have hflip := stirCheckingPredRep_flip_two M φ deg δ t (m := i.1) hi stmtIn tr v hn hy
          refine hs ?_
          show inputAns stmtIn.2 (queryPoint φ (v.get s))
            = trMsgFRep tr 0 h1 (queryPoint φ (v.get s))
          have := hflip.2.2 (Fin.cast hlen s)
          simpa using this
        · -- counting: per-coordinate |L| ≤ |F| − (⌊δ|ι|⌋+1), then the product is the power
          have hsub : (Finset.univ.filter (· ∈ L)) ⊆ (D.image φ)ᶜ := by
            intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
            rw [Finset.mem_compl]
            intro hmem
            obtain ⟨x, hxD, rfl⟩ := Finset.mem_image.mp hmem
            have hqp : queryPoint φ (φ x) = x :=
              Function.leftInverse_invFun φ.injective x
            have hLx := hr
            rw [hL] at hLx
            simp only [Set.mem_setOf_eq, hqp] at hLx
            have hfx : f x ≠ g1 x := by
              simpa [hD] using hxD
            exact hfx hLx
          have hcardL : (Finset.univ.filter (· ∈ L)).card
              ≤ Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) := by
            refine le_trans (Finset.card_le_card hsub) ?_
            rw [Finset.card_compl, Finset.card_image_of_injective _ φ.injective]
            omega
          calc ∏ _s : Fin ((stirMultiVSpecRep M ι t).length i.1),
                (((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              = (((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                  ^ ((stirMultiVSpecRep M ι t).length i.1) := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = (((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
                rw [hlen]
            _ ≤ (((Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ≥0∞)
                  / (Fintype.card F : ℝ≥0∞)) ^ t := by
                refine pow_le_pow_left' ?_ t
                exact ENNReal.div_le_div_right (by exact_mod_cast hcardL) _
      · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
        rintro x hx ⟨hn, hy⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hx
        obtain ⟨ch, -, rfl⟩ := hx
        exact hg (stirCheckingPredRep_flip_two M φ deg δ t (m := i.1) hi
          stmtIn tr ch hn hy).2.1

/-- **The later out-challenge flip bound at the rep spec**: at most `((|F|−1)/|F|)^t`. -/
theorem stirFlipRep_le_out
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx)
    (j : ℕ) (hjM : j < M) (hi : (i.1 : ℕ) = 3 * j + 5)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (prover : Prover oSpec (Unit × ∀ i, OracleStatement ι F i) Unit StmtOut WitOut
      ((stirMultiVSpecRep M ι t).toProtocolSpec F)) :
    Pr[fun x : ((stirMultiVSpecRep M ι t).toProtocolSpec F).Transcript i.1.castSucc ×
          ((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge i ×
          (oSpec + [((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        ¬ stirCheckingPredRep M φ deg δ t i.1.castSucc stmtIn x.1 ∧
          stirCheckingPredRep M φ deg δ t i.1.succ stmtIn (x.1.concat x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp
              (((stirMultiVSpecRep M ι t).toProtocolSpec F).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (((Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
  classical
  have hmod : (i.1 : ℕ) % 3 ≠ 1 := by omega
  have hlen : (stirMultiVSpecRep M ι t).length i.1 = t :=
    stirMultiRep_length_chal (M := M) (ι := ι) i.1 hmod
  refine probEvent_bind_le_of_forall_support init _ _ _ (fun s0 _ => ?_)
  rw [simulateQ_bind, StateT.run'_bind_lib]
  refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
  obtain ⟨⟨⟨tr, pst⟩, log⟩, s'⟩ := rk
  dsimp only
  rw [liftComp_eq_liftM]
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s' i
    (fun ch => pure (tr, ch, log)) _]
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [← probEvent_bind_eq_tsum]
  by_cases hno : stirCheckingPredRep M φ deg δ t i.1.castSucc stmtIn tr
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro x hx ⟨hn, -⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨ch, -, rfl⟩ := hx
    exact hn hno
  · have hA : 3 * j + 1 < (i.1.castSucc : ℕ) := by simp only [Fin.val_castSucc]; omega
    have hB : 3 * (j + 1) + 1 < (i.1.castSucc : ℕ) := by simp only [Fin.val_castSucc]; omega
    by_cases hAB : ∀ x : ι, trMsgFRep tr j hA x = trMsgFRep tr (j + 1) hB x
    · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
      rintro x hx ⟨hn, hy⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        exists_prop] at hx
      obtain ⟨ch, -, rfl⟩ := hx
      obtain ⟨⟨x₀, hx₀⟩, -⟩ :=
        stirCheckingPredRep_flip_out M φ deg δ t (m := i.1) hjM hi stmtIn tr ch hn hy
      exact hx₀ (hAB x₀)
    · obtain ⟨x₀, hx₀⟩ := not_forall.mp hAB
      set L : Set F := {r : F | trMsgFRep tr j hA (queryPoint φ r)
        = trMsgFRep tr (j + 1) hB (queryPoint φ r)} with hL
      refine le_trans (probEvent_bind_le_uniform_vector_marginal
        ($ᵗ (((stirMultiVSpecRep M ι t).toProtocolSpec F).Challenge i))
        (fun ch => pure (tr, ch, log)) _ (fun _ => L)
        (fun v => le_of_eq (probOutput_uniform_vector v)) ?_) ?_
      · rintro v ⟨s, hs⟩
        refine probEvent_eq_zero ?_
        rintro x hx ⟨hn, hy⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        have hflip := stirCheckingPredRep_flip_out M φ deg δ t (m := i.1) hjM hi
          stmtIn tr v hn hy
        refine hs ?_
        show trMsgFRep tr j hA (queryPoint φ (v.get s))
          = trMsgFRep tr (j + 1) hB (queryPoint φ (v.get s))
        have := hflip.2 (Fin.cast hlen s)
        simpa using this
      · have hsub : (Finset.univ.filter (· ∈ L)) ⊆ Finset.univ.erase (φ x₀) := by
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ r⟩
          intro hreq
          subst hreq
          have hqp : queryPoint φ (φ x₀) = x₀ :=
            Function.leftInverse_invFun φ.injective x₀
          rw [hL] at hr
          simp only [Set.mem_setOf_eq, hqp] at hr
          exact hx₀ hr
        have hcardL : (Finset.univ.filter (· ∈ L)).card ≤ Fintype.card F - 1 := by
          refine le_trans (Finset.card_le_card hsub) ?_
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        calc ∏ _s : Fin ((stirMultiVSpecRep M ι t).length i.1),
              (((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
            = (((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                ^ ((stirMultiVSpecRep M ι t).length i.1) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = (((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
              rw [hlen]
          _ ≤ (((Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
              refine pow_le_pow_left' ?_ t
              exact ENNReal.div_le_div_right (by exact_mod_cast hcardL) _

end FlipBoundsRep


section WeldRep

variable [Nonempty ι]
variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) (t : ℕ)

/-- **The genuine per-challenge budget of the t-repetition checking verifier** (#335 A1):
the `t`-fold powers of the single-query bases — `((|F|−(⌊δ|ι|⌋+1))/|F|)^t` at the round-2
input-link challenge, `((|F|−1)/|F|)^t` at the later pair-binding out-challenges, `0` at
fold/shift.  Strictly decreasing in `t` (bases < 1), so every target `2^{-secpar}` is met at
sufficiently large `t` — the honest path to real security parameters that the single-query
model (`stirEpsStar`, proven essentially tight by `stirChecking_switch_attack`) cannot reach. -/
noncomputable def stirEpsStarRep (M : ℕ) (δ : ℝ≥0) (t : ℕ) :
    ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx → ℝ≥0 := fun c =>
  if (c.1 : ℕ) = 2 then
    (((Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ≥0)
      / ((Fintype.card F : ℕ) : ℝ≥0)) ^ t
  else if (c.1 : ℕ) % 3 = 2 then
    (((Fintype.card F - 1 : ℕ) : ℝ≥0) / ((Fintype.card F : ℕ) : ℝ≥0)) ^ t
  else 0

/-- The rep-spec rbr knowledge-soundness statement (mirror of
`stirCheckingRbrSoundnessResidual`); proven outright at the canonical `(·)^t` budget by
`stirCheckingRepRbrSoundness_genuine` below. -/
def stirCheckingRepRbrSoundnessStatement (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) (t : ℕ)
    (ε_rbr : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx → ℝ≥0) : Prop :=
  OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
    (stirRelation deg φ δ) (stirCheckingIOPRep M φ deg t).verifier ε_rbr

/-- **T1-rep — genuine rbr knowledge soundness of the t-repetition checking verifier at the
`(·)^t` budget**: outright, with no correlated-agreement residuals and no vacuity. -/
theorem stirCheckingRepRbrSoundness_genuine :
    stirCheckingRepRbrSoundnessStatement M φ deg δ t (stirEpsStarRep (F := F) (ι := ι) M δ t) := by
  have hcardF : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  refine ThresholdKSF.rbrKnowledgeSoundness_of_flipBounds (pure ()) isEmptyElim
    ((stirCheckingIOPRep M φ deg t).verifier.toVerifier)
    (stirRelation deg φ δ) acceptRejectOracleRel
    (stirCheckingPredRep M φ deg δ t) (stirEpsStarRep (F := F) (ι := ι) M δ t)
    (fun stmtIn _ => stirCheckingPredRep_empty M φ deg δ t stmtIn default)
    (fun m hdir stmtIn tr msg h => by
      rw [show ((stirMultiVSpecRep M ι t).toProtocolSpec F).dir m
          = (stirMultiVSpecRep M ι t).dir m from rfl,
        stirVSpec_dir_eq_msg_iff] at hdir
      exact stirCheckingPredRep_concat_msg M φ deg δ t stmtIn tr msg hdir h)
    (fun stmtIn tr witOut hpr => by
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      have hrun : Verifier.run stmtIn tr (stirCheckingIOPRep M φ deg t).verifier.toVerifier
          = (pure (checkingBoolRep M φ deg t stmtIn.2 tr.messages tr.challenges,
              fun i : Empty => i.elim) : OptionT (OracleComp []ₒ) _) :=
        checkingVerifierRep_toVerifier_verify M φ deg t stmtIn tr
      erw [hrun, simulateQ_optionT_pure_run'] at hx
      cases (Option.some.inj hx)
      refine stirCheckingPredRep_full_of_accept M φ deg δ t stmtIn tr ?_
      simpa [acceptRejectOracleRel, Prod.ext_iff] using hrel)
    (fun i stmtIn witIn prover => by
      by_cases h2 : (i.1 : ℕ) = 2
      · refine le_trans
          (stirFlipRep_le_round2 M φ deg δ t (pure ()) isEmptyElim i h2 stmtIn witIn prover) ?_
        rw [stirEpsStarRep, if_pos h2, ENNReal.coe_pow, ENNReal.coe_div hcardF]
        simp only [ENNReal.coe_natCast]
        exact le_refl _
      · by_cases hmod2 : (i.1 : ℕ) % 3 = 2
        · obtain ⟨j, hj⟩ : ∃ j, (i.1 : ℕ) = 3 * j + 5 := ⟨((i.1 : ℕ) - 5) / 3, by omega⟩
          have hjM : j < M := by have := i.1.isLt; omega
          refine le_trans
            (stirFlipRep_le_out M φ deg δ t (pure ()) isEmptyElim i j hjM hj
              stmtIn witIn prover) ?_
          rw [stirEpsStarRep, if_neg h2, if_pos hmod2, ENNReal.coe_pow,
            ENNReal.coe_div hcardF]
          simp only [ENNReal.coe_natCast]
          exact le_refl _
        · have hdir := i.2
          rw [show ((stirMultiVSpecRep M ι t).toProtocolSpec F).dir i.1
              = (stirMultiVSpecRep M ι t).dir i.1 from rfl,
            stirVSpec_dir_eq_chal_iff] at hdir
          have h0 : (i.1 : ℕ) % 3 = 0 := by omega
          refine le_trans
            (stirFlipRep_le_zero M φ deg δ t (pure ()) isEmptyElim i h0
              stmtIn witIn prover) ?_
          rw [stirEpsStarRep, if_neg h2, if_neg hmod2]
          simp)

/-- **`IsSecureWithGap` for the t-repetition checking IOPP, hypothesis-free**: perfect
completeness (the core) + the genuine `(·)^t` rbr soundness (T1-rep). -/
theorem stirCheckingIOPRep_isSecureWithGap_genuine :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ)
      (stirEpsStarRep (F := F) (ι := ι) M δ t) (stirCheckingIOPRep M φ deg t) where
  is_complete := stirCheckingIOPRep_perfectCompleteness M φ deg t
  is_rbr_knowledge_sound := stirCheckingRepRbrSoundness_genuine M φ deg δ t

/-- Every coordinate of the rep budget is dominated by the `t`-th power of the worst
single-query base `(|F|−1)/|F| < 1`.  Driving `t` up therefore meets every `2^{-secpar}`
target — the choice of `t` for a given `secpar` is the caller's (analytic) step. -/
theorem stirEpsStarRep_le_pow_max (i : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx) :
    stirEpsStarRep (F := F) (ι := ι) M δ t i
      ≤ (((Fintype.card F - 1 : ℕ) : ℝ≥0) / ((Fintype.card F : ℕ) : ℝ≥0)) ^ t := by
  rw [stirEpsStarRep]
  by_cases h2 : (i.1 : ℕ) = 2
  · rw [if_pos h2]
    refine pow_le_pow_left' ?_ t
    refine div_le_div_of_nonneg_right ?_ ?_ |>.trans (le_refl _)
    · exact_mod_cast Nat.sub_le_sub_left (by omega) _
    · exact_mod_cast Nat.zero_le _
  · rw [if_neg h2]
    by_cases hm : (i.1 : ℕ) % 3 = 2
    · rw [if_pos hm]
    · rw [if_neg hm]
      exact zero_le _

/-- **Theorem 5.1 through the t-repetition checking IOPP** (#335 A1): `stir_main` with the
soundness leg PROVEN at the `(·)^t` budget; the `hε` leg is satisfiable for every `secpar`
by choosing `t` large enough (the bases are `< 1`), and the remaining legs are the
statement's own free parameters. -/
theorem stir_main_of_checkingIOP_rep
    {M : ℕ} (secpar : ℕ) (t : ℕ)
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / LinearCode.rate (code φ degree)))
    (hε : ∀ i, stirEpsStarRep (F := F) (ι := ι) M δ t i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) /
          Real.log (1 / LinearCode.rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF := by
  obtain ⟨c, hc, hMle⟩ := hM
  obtain ⟨cₖ, hLenle⟩ := hLen
  obtain ⟨cₖ', hQle⟩ := hQpf
  exact ⟨3 * M + 3, stirMultiVSpecRep M ι t, stirEpsStarRep (F := F) (ι := ι) M δ t,
    stirCheckingIOPRep M φ degree t,
    stirCheckingIOPRep_isSecureWithGap_genuine M φ degree δ t,
    fun i => ⟨hε i, c, hc, hMle, cₖ, hLenle, hQin, cₖ', hQle⟩⟩

end WeldRep

end MultiRound

end StirIOP

#print axioms StirIOP.MultiRound.stirMultiRep_length_msg_raw
#print axioms StirIOP.MultiRound.stirMultiRep_length_chal_raw
#print axioms StirIOP.MultiRound.stirMultiRep_length_chal
#print axioms StirIOP.MultiRound.stirMultiVSpecRep_length_msg
#print axioms StirIOP.MultiRound.stirMultiVSpecRep_length_chal
#print axioms StirIOP.MultiRound.simulateQ_askInputRep
#print axioms StirIOP.MultiRound.simulateQ_askMsgRep
#print axioms StirIOP.MultiRound.answer_honest_packRep
#print axioms StirIOP.MultiRound.all_map_finRange_iff
#print axioms StirIOP.MultiRound.simulateQ_lift_checkingCompRep
#print axioms StirIOP.MultiRound.checkingVerifierRep_toVerifier_verify
#print axioms StirIOP.MultiRound.simulateQ_checkingCompRep
#print axioms StirIOP.MultiRound.stirMultiRoundProverRep_runToRound_invariant
#print axioms StirIOP.MultiRound.checkingBoolRep_honest
#print axioms StirIOP.MultiRound.checkingBoolRep_eq_true_iff
#print axioms StirIOP.MultiRound.stirCheckingIOPRep_perfectCompleteness

#print axioms StirIOP.MultiRound.stirCheckingPredRep_full_of_accept
#print axioms StirIOP.MultiRound.stirCheckingPredRep_flip_two
#print axioms StirIOP.MultiRound.stirCheckingPredRep_flip_out
#print axioms StirIOP.MultiRound.stirFlipRep_le_zero
#print axioms StirIOP.MultiRound.stirFlipRep_le_round2
#print axioms StirIOP.MultiRound.stirFlipRep_le_out
#print axioms StirIOP.MultiRound.stirCheckingRepRbrSoundness_genuine
#print axioms StirIOP.MultiRound.stirCheckingIOPRep_isSecureWithGap_genuine
#print axioms StirIOP.MultiRound.stirEpsStarRep_le_pow_max
#print axioms StirIOP.MultiRound.stir_main_of_checkingIOP_rep
