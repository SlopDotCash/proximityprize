/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Stir.MultiRoundAssembly
import ArkLib.ProofSystem.Stir.ErrorAccumulation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionVacuous
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffLargeReduction
import ArkLib.ToVCVio.Simulation

set_option linter.style.longFile 1900

/-!
# Issue #301 (STIR): the CHECKING multi-round verifier

`MultiRoundAssembly.lean` assembles the (M+1)-round STIR Vector IOPP with an honest folding
prover but a *forwarding shell* verifier (`verify := pure true`). This file builds the
**checking** multi-round verifier and welds it into the durable wiring
(`stir_main_of_secure_vectorIOP` / `stir_rbr_soundness_of_secure_vectorIOP`):

* `stirCheckingVerifier` — per-round checks lifted to the multi-round wire shape:
  - **fold-query check** (round 0): the first folded oracle `g₁` agrees with the genuine fold of
    the input codeword at a point derived from the first out-challenge (in this single-domain
    identity-fold model `Fold(f,r) = f` by `combine_single_self`, so the check is agreement with
    the input oracle itself);
  - **out-of-domain-style + fold-query consistency checks** (rounds 1..M): consecutive folded
    oracles agree at the points derived from the out- and shift-challenges of the round;
  - **final low-degree check**: the final prover message is read in full (it is the final
    polynomial, sent in the clear in STIR) and checked for membership in `RS[F, φ, deg]`.
* `stirCheckingIOP` — the checking IOPP: the landed honest `stirMultiRoundProver` together with
  the checking verifier.
* `stirMultiRoundProver_runToRound_invariant` — PROVEN: on the support of every honest-prover
  run prefix, the carried context is the input context and every transcript message is the
  honest packed fold of the input codeword (= the packed input codeword itself, by
  `combine_single_self`).
* `stirCheckingIOP_perfectCompleteness` — PROVEN (axiom-clean), for symbolic `M`: by the
  invariant all consistency checks compare equal values, and the final low-degree check passes
  because the `δ = 0` relation `stirRelation deg φ 0` forces the input codeword into the code
  (`mem_of_relDistFromCode_le_zero`).
* `stirCheckingRbrSoundnessResidual` + `stirCheckingCABridge` — the soundness side, HONESTLY
  split: the rbr knowledge soundness of the checking verifier is the named open residual; the
  bridge residual states that it follows from the EXISTING Johnson-CA residuals
  (`ProximityGap.StrictCoeffPolysResidual`, the §5/Johnson-regime correlated-agreement
  extraction) plus the per-round accounting keystone
  (`ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap`). The general bridge is the
  genuine open protocol-soundness math of #301.
* `stir_rbr_soundness_of_checkingIOP_CA` / `stir_main_of_checkingIOP_CA` — the headline
  existentials discharged through the landed `…_of_secure_vectorIOP` front doors, with the
  completeness leg PROVEN (this file) and the soundness leg consumed via
  (CA residuals + bridge residual).
* `strictCoeffPolys_all_of_card_le` plus
  `stir_rbr_soundness_of_checkingIOP_card_le` / `stir_main_of_checkingIOP_card_le` — the
  small-field route: `|F| ≤ |ι|` discharges the full positive-width
  `StrictCoeffPolysResidual` family via the in-tree vacuous-regime BCIKS theorem, leaving only
  the protocol-level checking bridge.
* `strictCoeffPolys_all_of_large` plus the `…_large` front doors — the #304-aligned
  route: STIR may consume the honest large-sector residual family
  (`StrictCoeffPolysLargeResidual`) directly; the small-good-set sector is discharged by the
  landed Lagrange interpolation reduction.
* `…_card_le_e7` variants — the same discharge through the sharp vacuous-regime bound
  `|F| ≤ deg² * 10⁷`.

HONESTY NOTES:
* The checking verifier's checks are *real* (they constrain the prover's messages: a prover whose
  final message is not a codeword, or whose oracles are caught inconsistent at the sampled
  points, is rejected) — unlike the shell verifier, `verify = pure true` is false for it.
* The single-domain model folds `RS[F,φ,deg]` into itself (`combine_single_self`), so the
  per-round degree reduction of paper-STIR is degenerate here; the out-of-domain check
  correspondingly degenerates to consistency at a challenge-derived in-domain point. This is
  inherited from the landed `stirRoundVectorProver`/`stirMultiRoundProver` model.
* The implication (Johnson-CA + per-round gap accounting ⟹ rbr knowledge soundness of this
  verifier) is NOT proven in the general (large-field) regime; it is isolated as
  `stirCheckingCABridge`. No fabrication.
* SMALL-FIELD REGIME (#301 Part B): in `|F| ≤ (m−1)·|ι|` with `δ ≤ (1−ρ)/2`, the prescribed
  proximity error `err⋆` is ≥ 1 (`one_le_proximityError_of_card_le`), so the rbr-soundness
  residual AND the bridge are discharged outright (`stirCheckingRbrSoundness_of_small_field`,
  `stirCheckingCABridge_of_small_field`); the public
  `stir_rbr_soundness_of_checkingIOP_small_field` and `stir_main_of_checkingIOP_small_field`
  front doors consume NO soundness residual at all. This is the same vacuity that makes
  `STIR.proximity_gap_of_card_le` unconditional; it carries no security content for
  `secpar > 0` (the `hε` leg then pins `secpar = 0`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction
open OracleInterface

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι]

section CheckingVerifier

variable [Nonempty ι]

/-- The `j`-th message round of the multi-round STIR shape (round `3j + 1`). -/
def msgIdx (M : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx :=
  ⟨⟨3 * (j : ℕ) + 1, by omega⟩, by
    show (stirMultiVSpec M ι).dir _ = .P_to_V
    rw [stirVSpec_dir_eq_msg_iff]; simp only [Fin.val_mk]; omega⟩

/-- The out-challenge round following the `j`-th message round (round `3j + 2`). -/
def outChalIdx (M : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 2, by omega⟩, by
    show (stirMultiVSpec M ι).dir _ = .V_to_P
    rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega⟩

/-- The shift-challenge round between message rounds `j` and `j + 1` (round `3j + 3`). -/
def shiftChalIdx (M : ℕ) (j : Fin M) :
    ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 3, by omega⟩, by
    show (stirMultiVSpec M ι).dir _ = .V_to_P
    rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega⟩

/-- Read the field element off a (length-`1`) vector challenge. -/
def chalFE {M : ℕ} (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx) : F :=
  (chals i).get ⟨0, stirMultiVSpec_length_chal_pos i⟩

/-- Map a field challenge to a query point of the evaluation domain (the `φ`-preimage when the
challenge lands in the domain's image, an arbitrary point otherwise). -/
noncomputable def queryPoint (φ : ι ↪ F) (r : F) : ι := Function.invFun φ r

/-- The position of domain point `x` inside a packed message vector. -/
noncomputable def msgPos (M : ℕ) (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx) (x : ι) :
    Fin ((stirMultiVSpec M ι).length j.1) :=
  Fin.cast (stirMultiVSpec_length_msg j) (Fintype.equivFin ι x)

/-- Query the input codeword oracle at a domain point. -/
noncomputable def askInput (M : ℕ) (x : ι) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [OracleStatement ι F]ₒ)
    (⟨(), x⟩ : (Σ i : Unit, OracleInterface.Query (OracleStatement ι F i))))

/-- Query the `j`-th prover message oracle at a vector position. -/
noncomputable def askMsg (M : ℕ) (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)
    (⟨j, k⟩ : (Σ i, OracleInterface.Query (((stirMultiVSpec M ι).toProtocolSpec F).Message i))))

/-- Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s
tail-recursive loop), so that `simulateQ` collapse is a one-line induction. -/
def askList {ιq : Type} {spec : OracleSpec ιq} {β γ : Type}
    (xs : List β) (ask : β → OracleComp spec γ) : OracleComp spec (List γ) :=
  match xs with
  | [] => pure []
  | x :: xs => do
      let v ← ask x
      let vs ← askList xs ask
      pure (v :: vs)

/-- If every step of an `askList` simulates to a pure value, the whole `askList` collapses to the
corresponding pure `List.map`. -/
theorem simulateQ_askList {ιq ιq' : Type} {spec : OracleSpec ιq} {spec' : OracleSpec ιq'}
    (so : QueryImpl spec (OracleComp spec')) {β γ : Type}
    (xs : List β) (ask : β → OracleComp spec γ) (ans : β → γ)
    (hstep : ∀ b, simulateQ so (ask b) = pure (ans b)) :
    simulateQ so (askList xs ask) = pure (xs.map ans) := by
  induction xs with
  | nil => simp [askList]
  | cons y ys ih =>
      rw [askList, simulateQ_bind, hstep, pure_bind, simulateQ_bind, ih, pure_bind,
        simulateQ_pure, List.map_cons]

/-- The honest answer of the input-codeword oracle (ascribed at `F`). -/
noncomputable def inputAns (oStmt : ∀ i, OracleStatement ι F i) (x : ι) : F :=
  OracleInterface.answer (oStmt ()) x

/-- The honest answer of a message oracle (ascribed at `F`). -/
noncomputable def msgAns {M : ℕ}
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) : F :=
  OracleInterface.answer (msgs j) k

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ)

open scoped Classical in
/-- **The checking computation** of the multi-round STIR verifier: round-0 fold-query check
against the input codeword, per-round out/shift consistency checks between consecutive folded
oracles, and the final full-read low-degree check. -/
noncomputable def checkingComp (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)) Bool := do
  -- (1) round-0 fold-query check: g₁ agrees with (the fold of) the input codeword at the
  -- point derived from the first out-challenge
  let x0 := queryPoint φ (chalFE chals (outChalIdx M 0))
  let vIn ← askInput M x0
  let v0 ← askMsg M (msgIdx M 0) (msgPos M (msgIdx M 0) x0)
  -- (2) per-round consistency checks: consecutive folded oracles agree at the points derived
  -- from the round's out- and shift-challenges
  let consist ← askList (List.finRange M) (fun j => do
      let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
      let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
      let va ← askMsg M (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
      let vb ← askMsg M (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
      let vc ← askMsg M (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
      let vd ← askMsg M (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
      pure (decide (va = vb) && decide (vc = vd)))
  -- (3) final low-degree check: read the final message (the final polynomial, in the clear)
  -- in full and check membership in the Reed-Solomon code
  let finalVals ← askList (List.finRange (Fintype.card ι)) (fun k =>
      askMsg M (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
  pure (decide (vIn = v0) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg))

open scoped Classical in
/-- **The pure value of the checking computation** under the honest oracle implementation
(`simOracle2` over the input oracle statement and the transcript messages). -/
noncomputable def checkingBool (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) : Bool :=
  let x0 := queryPoint φ (chalFE chals (outChalIdx M 0))
  let vIn := inputAns oStmt x0
  let v0 := msgAns msgs (msgIdx M 0) (msgPos M (msgIdx M 0) x0)
  let consist := (List.finRange M).map (fun j =>
      let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
      let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
      let va := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
      let vb := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
      let vc := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
      let vd := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
      decide (va = vb) && decide (vc = vd))
  let finalVals := (List.finRange (Fintype.card ι)).map (fun k =>
      msgAns msgs (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
  decide (vIn = v0) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg)

/-- `simulateQ` collapse for the input-oracle query. -/
theorem simulateQ_askInput (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j) (x : ι) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askInput M x)
      = (pure (inputAns oStmt x) : OracleComp []ₒ F) := rfl

/-- `simulateQ` collapse for a message-oracle query. -/
theorem simulateQ_askMsg (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askMsg M j k)
      = (pure (msgAns msgs j k) : OracleComp []ₒ F) := rfl

/-- **Central collapse**: under the honest oracle implementation, the checking computation is a
pure computation of `checkingBool`. (Holds for ARBITRARY oracle/message values; this single
lemma powers both the safety and the correctness branches of completeness.) -/
theorem simulateQ_checkingComp (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (checkingComp M φ deg chals)
      = pure (checkingBool M φ deg oStmt msgs chals) := by
  unfold checkingComp checkingBool
  rw [simulateQ_bind, simulateQ_askInput]
  simp only [pure_bind]
  rw [simulateQ_bind, simulateQ_askMsg]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun j =>
      let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
      let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
      let va := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
      let vb := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
      let vc := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
      let vd := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
      decide (va = vb) && decide (vc = vd))
      (fun j => by
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind, simulateQ_pure])]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun k =>
      msgAns msgs (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
      (fun k => simulateQ_askMsg M oStmt msgs _ _)]
  simp only [pure_bind, simulateQ_pure]

/-- **The checking multi-round STIR verifier.** Forwards no oracles (IOP shape); its `verify` is
the genuine checking computation. -/
noncomputable def stirCheckingVerifier :
    OracleVerifier []ₒ Unit (OracleStatement ι F) Bool (fun _ : Empty => Unit)
      ((stirMultiVSpec M ι).toProtocolSpec F) where
  verify := fun _ chals => OptionT.lift (checkingComp M φ deg chals)
  embed := ⟨fun i => i.elim, fun i => i.elim⟩
  hEq := fun i => i.elim

/-- **The checking (M+1)-round STIR Vector IOPP**: the landed honest folding prover together
with the checking verifier. -/
noncomputable def stirCheckingIOP :
    VectorIOP Unit (OracleStatement ι F) Unit (stirMultiVSpec M ι) F where
  prover := stirMultiRoundProver M φ deg
  verifier := stirCheckingVerifier M φ deg

end CheckingVerifier

/-! ### The honest prover's run-support invariant -/

section Invariant

variable [Nonempty ι]

/-- The honest packed message value at message round `iv` (`iv % 3 = 1`): the packed fold of the
input codeword, which by `combine_single_self` is the packed input codeword itself. -/
noncomputable def honestMsg (M : ℕ) (f : ι → F) (iv : ℕ) (h : iv < 3 * M + 3)
    (hdir : iv % 3 = 1) : Vector F ((stirMultiVSpec M ι).length ⟨iv, h⟩) :=
  Vector.cast (stirMultiVSpec_length_msg (ι := ι) (F := F) (M := M)
    ⟨⟨iv, h⟩, by
      show (stirMultiVSpec M ι).dir _ = .P_to_V
      rw [stirVSpec_dir_eq_msg_iff]; exact hdir⟩)
    (packFiniteFunction ι f)

/-- **Run-support invariant of the honest multi-round STIR prover** (symbolic `M`, any round
`k`): on the support of `runToRound k`, (i) the prover's carried context is the input context
(it only updates its stored fold challenge), and (ii) every message entry of the partial
transcript is the honest packed fold of the input codeword — which, since `Combine.combine` of
a single codeword at its own degree is the identity, is the packed input codeword. -/
theorem stirMultiRoundProver_runToRound_invariant (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (k : Fin (3 * M + 3 + 1)) :
    ∀ ts ∈ _root_.support
      ((stirMultiRoundProver M φ deg).runToRound k stmtIn witIn),
      ts.2.1 = (stmtIn, witIn) ∧
      ∀ (iv : ℕ) (hik : iv < k.val) (hdir : iv % 3 = 1),
        ts.1 ⟨iv, hik⟩ = honestMsg M (stmtIn.2 ()) iv
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
            if h : 0 < (stirMultiVSpec M ι).length ⟨(j : ℕ), j.isLt⟩
            then r.get ⟨0, h⟩ else 0) := by
          dsimp only [stirMultiRoundProver] at hfch
          simpa only [support_pure, Set.mem_singleton_iff] using hfch
        refine ⟨by rw [hfch']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpec M ι).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
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
        have hms' : msg = Vector.cast (stirMultiVSpec_length_msg ⟨j, hDir⟩)
            (packFiniteFunction ι
              (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ())
                (fun _ : Fin 1 => deg))) ∧ st' = st := by
          dsimp only [stirMultiRoundProver] at hms
          simp only [liftM_pure, liftComp_pure, support_pure] at hms
          exact Prod.ext_iff.mp (Set.mem_singleton_iff.mp hms)
        obtain ⟨hmsg, hst'⟩ := hms'
        refine ⟨by rw [hst']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpec M ι).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.castSucc ⟨iv, hlt⟩) = _
          rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          letI : DecidableEq ι := Classical.decEq ι
          show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpec M ι).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.last (j : ℕ)) = _
          rw [Fin.snoc_last, hmsg, ihSt]
          show Vector.cast _ (packFiniteFunction ι
            (Combine.combine φ deg st.2 (fun _ : Fin 1 => stmtIn.2 ())
              (fun _ : Fin 1 => deg))) = _
          rw [Round.combine_single_self]
          rfl

end Invariant

/-! ### The honest checks pass -/

section HonestChecks

variable [Nonempty ι]

/-- Zero relative distance from a nonempty code forces membership (the `δ = 0` instance of the
`stirRelation` is genuine code membership). -/
theorem mem_of_relDistFromCode_le_zero {f : ι → F} {C : Set (ι → F)}
    (hne : C.Nonempty) (h : Code.relDistFromCode f C ≤ 0) : f ∈ C := by
  haveI : Nonempty C := hne.to_subtype
  obtain ⟨v, hv, hdist⟩ := Code.exists_relClosest_codeword_of_Nonempty_Code C f
  have h0 : (Code.relHammingDist f v : ENNReal) = 0 :=
    hdist.trans (le_antisymm h (zero_le _))
  have h1 : Code.relHammingDist f v = 0 := by
    rw [NNRat.cast, NNRatCast.nnratCast, ENNReal.instNNRatCast] at h0
    simp only [ENNReal.coe_eq_zero] at h0
    exact_mod_cast h0
  have hcard : (Fintype.card ι : ℚ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have h2 : hammingDist f v = 0 := by
    have := (div_eq_zero_iff.mp h1).resolve_right hcard
    exact_mod_cast this
  rwa [hammingDist_eq_zero.mp h2]

/-- The input-codeword oracle answers with the function value. -/
theorem inputAns_apply (oStmt : ∀ i, OracleStatement ι F i) (x : ι) :
    inputAns oStmt x = oStmt () x := rfl

/-- Answer of the honest packed message oracle: reading position `k` returns the function value
at the `k`-th enumeration point of the domain. -/
theorem answer_honest_pack (M : ℕ) (f : ι → F)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    OracleInterface.answer
      ((Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι f)
        : Vector F ((stirMultiVSpec M ι).length j.1))
        : ((stirMultiVSpec M ι).toProtocolSpec F).Message j) k
      = f ((Fintype.equivFin ι).symm ⟨(k : ℕ),
          lt_of_lt_of_eq k.isLt (stirMultiVSpec_length_msg j).symm⟩) := by
  show (Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι f))[(k : ℕ)] = _
  rw [Vector.getElem_cast, packFiniteFunction, Vector.getElem_ofFn]

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ)

open scoped Classical in
/-- **The honest prover passes every check**: if the input oracle is a genuine codeword and
every transcript message is its honest packed fold (= the packed input codeword), then the
checking verifier's decision bit is `true`, for every challenge vector. -/
theorem checkingBool_honest (f : ι → F) (hmem : f ∈ ReedSolomon.code φ deg)
    (oStmt : ∀ i, OracleStatement ι F i) (hOStmt : oStmt () = f)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (hmsgs : ∀ j, msgs j
      = Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι f))
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    checkingBool M φ deg oStmt msgs chals = true := by
  -- the uniform honest-message evaluation at a domain point
  have hans : ∀ (j) (x : ι), msgAns msgs j (msgPos M j x) = f x := by
    intro j x
    rw [msgAns, hmsgs j, answer_honest_pack]
    -- the packed index is (by `Fin` eta) the enumeration index of `x`
    show f ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)) = f x
    rw [Equiv.symm_apply_apply]
  -- the honest final-message evaluation at an enumeration index
  have hfin : ∀ k : Fin (Fintype.card ι),
      msgAns msgs (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k)
      = f ((Fintype.equivFin ι).symm k) := by
    intro k
    rw [msgAns, hmsgs _, answer_honest_pack]
    rfl
  unfold checkingBool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- round-0 fold-query check
    rw [inputAns_apply, hOStmt, hans]
  · -- per-round consistency checks
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨j, -, rfl⟩ := hb
    simp only [hans, Bool.and_eq_true, decide_eq_true_eq, and_self]
  · -- final low-degree check
    have hfun : (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAns msgs (msgIdx M (Fin.last M))
            (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0)) = f := by
      funext x
      rw [List.getD_eq_getElem _ _ (by
        simp only [List.length_map, List.length_finRange]
        exact (Fintype.equivFin ι x).isLt)]
      rw [List.getElem_map, List.getElem_finRange, hfin]
      simp only [Fin.cast_mk, Fin.eta, Equiv.symm_apply_apply]
    rw [hfun]
    exact hmem

/-! #### Non-vacuousness: the checks genuinely constrain the prover -/

variable {M : ℕ} {φ : ι ↪ F} {deg : ℕ}

open scoped Classical in
/-- An accepting decision **forces the round-0 fold-query check**: the first folded oracle must
agree with the input codeword at the sampled point (so `verify = pure true` is genuinely false
for the checking verifier, unlike the forwarding shell). -/
theorem checkingBool_true_implies_fold_check
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (h : checkingBool M φ deg oStmt msgs chals = true) :
    inputAns oStmt (queryPoint φ (chalFE chals (outChalIdx M 0)))
      = msgAns msgs (msgIdx M 0)
          (msgPos M (msgIdx M 0) (queryPoint φ (chalFE chals (outChalIdx M 0)))) := by
  unfold checkingBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

open scoped Classical in
/-- An accepting decision forces every sampled inter-round consistency check. For each shifted
round `j`, the verifier has compared the `j`-th and `(j+1)`-st prover messages at both sampled
points: the out challenge for the next message and the shift challenge between the messages. -/
theorem checkingBool_true_implies_round_consistency
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (h : checkingBool M φ deg oStmt msgs chals = true)
    (j : Fin M) :
    (msgAns msgs (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE chals (outChalIdx M j.succ))))
      = msgAns msgs (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE chals (outChalIdx M j.succ))))) ∧
    (msgAns msgs (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE chals (shiftChalIdx M j))))
      = msgAns msgs (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE chals (shiftChalIdx M j))))) := by
  unfold checkingBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hall := h.1.2
  let b :=
    (let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
     let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
     let va := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
     let vb := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
     let vc := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
     let vd := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
     decide (va = vb) && decide (vc = vd))
  have hb : b = true := by
    apply (List.all_eq_true.mp hall)
    simp only [List.mem_map]
    exact ⟨j, List.mem_finRange j, rfl⟩
  dsimp [b] at hb
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb

open scoped Classical in
/-- Out-challenge projection of `checkingBool_true_implies_round_consistency`. -/
theorem checkingBool_true_implies_out_consistency
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (h : checkingBool M φ deg oStmt msgs chals = true)
    (j : Fin M) :
    msgAns msgs (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE chals (outChalIdx M j.succ))))
      = msgAns msgs (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE chals (outChalIdx M j.succ)))) :=
  (checkingBool_true_implies_round_consistency
    (M := M) (φ := φ) (deg := deg) oStmt msgs chals h j).1

open scoped Classical in
/-- Shift-challenge projection of `checkingBool_true_implies_round_consistency`. -/
theorem checkingBool_true_implies_shift_consistency
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (h : checkingBool M φ deg oStmt msgs chals = true)
    (j : Fin M) :
    msgAns msgs (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE chals (shiftChalIdx M j))))
      = msgAns msgs (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE chals (shiftChalIdx M j)))) :=
  (checkingBool_true_implies_round_consistency
    (M := M) (φ := φ) (deg := deg) oStmt msgs chals h j).2

open scoped Classical in
/-- An accepting decision **forces the final low-degree check**: the function read off the
final prover message must be a Reed-Solomon codeword. -/
theorem checkingBool_true_implies_final_in_code
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (h : checkingBool M φ deg oStmt msgs chals = true) :
    (fun x : ι =>
      (((List.finRange (Fintype.card ι)).map (fun k =>
        msgAns msgs (msgIdx M (Fin.last M))
          (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
        ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0))
      ∈ ReedSolomon.code φ deg := by
  unfold checkingBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

open scoped Classical in
/-- Exact decomposition of the checking predicate into its mathematical checks: the initial
fold query agrees, every sampled adjacent-round pair agrees at the out and shift challenges, and
the final message is a Reed-Solomon codeword. -/
theorem checkingBool_eq_true_iff
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    checkingBool M φ deg oStmt msgs chals = true ↔
      inputAns oStmt (queryPoint φ (chalFE chals (outChalIdx M 0)))
        = msgAns msgs (msgIdx M 0)
            (msgPos M (msgIdx M 0) (queryPoint φ (chalFE chals (outChalIdx M 0)))) ∧
      (∀ j : Fin M,
        (msgAns msgs (msgIdx M j.castSucc)
            (msgPos M (msgIdx M j.castSucc)
              (queryPoint φ (chalFE chals (outChalIdx M j.succ))))
          = msgAns msgs (msgIdx M j.succ)
            (msgPos M (msgIdx M j.succ)
              (queryPoint φ (chalFE chals (outChalIdx M j.succ))))) ∧
        (msgAns msgs (msgIdx M j.castSucc)
            (msgPos M (msgIdx M j.castSucc)
              (queryPoint φ (chalFE chals (shiftChalIdx M j))))
          = msgAns msgs (msgIdx M j.succ)
            (msgPos M (msgIdx M j.succ)
              (queryPoint φ (chalFE chals (shiftChalIdx M j)))))) ∧
      (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAns msgs (msgIdx M (Fin.last M))
            (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0))
        ∈ ReedSolomon.code φ deg := by
  constructor
  · intro h
    exact ⟨checkingBool_true_implies_fold_check
        (M := M) (φ := φ) (deg := deg) oStmt msgs chals h,
      ⟨fun j => checkingBool_true_implies_round_consistency
        (M := M) (φ := φ) (deg := deg) oStmt msgs chals h j,
      checkingBool_true_implies_final_in_code
        (M := M) (φ := φ) (deg := deg) oStmt msgs chals h⟩⟩
  · intro h
    unfold checkingBool
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h.1, ?_⟩, h.2.2⟩
    apply List.all_eq_true.mpr
    intro b hb
    simp only [List.mem_map] at hb
    rcases hb with ⟨j, _hj, rfl⟩
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h.2.1 j

end HonestChecks

/-! ### Completeness of the checking IOP -/

section Completeness

open OracleReduction

variable [Nonempty ι]

/-- `simulateQ` collapse of the checking verifier's core computation at the `OptionT` layer:
under the honest oracle implementation the whole lifted computation is a `pure` of the
decision bit. (Holds for arbitrary message/oracle values.) -/
theorem simulateQ_lift_checkingComp (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (OptionT.lift (checkingComp M φ deg chals)) : OptionT (OracleComp []ₒ) Bool)
      = pure (checkingBool M φ deg oStmt msgs chals) := by
  show (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (checkingComp M φ deg chals >>= fun b => (pure (some b) : OracleComp _ (Option Bool)))
      : OracleComp []ₒ (Option Bool))
    = pure (some (checkingBool M φ deg oStmt msgs chals))
  rw [simulateQ_bind, simulateQ_checkingComp]
  simp

/-- Running the spec-lifted `OptionT` `pure` is the `pure` of `some` (the underlying collapse
consumed by both the safety and correctness branches of the completeness proof). -/
theorem OptionT_run_liftComp_pure {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)] {α : Type} (xv : α) :
    OptionT.run (liftComp (pure xv : OptionT (OracleComp spec₁) α) spec₂)
      = (pure (some xv) : OracleComp spec₂ (Option α)) := by
  show liftComp (pure (some xv) : OracleComp spec₁ (Option α)) spec₂ = _
  rw [liftComp_pure]

/-- **Pure form of the checking verifier's non-oracle run**: `toVerifier.verify` is the `pure`
of the decision bit (paired with the empty output-oracle family), for every transcript. -/
theorem checkingVerifier_toVerifier_verify (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F)) :
    (stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr
      = pure (checkingBool M φ deg stmtIn.2 tr.messages tr.challenges,
          fun i : Empty => i.elim) := by
  dsimp only [OracleVerifier.toVerifier, stirCheckingVerifier]
  erw [simulateQ_lift_checkingComp, pure_bind]

open scoped Classical in
/-- Exact support characterization of the checking verifier: for a fixed transcript, the verifier
has one deterministic output, whose Boolean component is precisely `checkingBool`. -/
theorem checkingVerifier_support_iff
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit)) :
    out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr) ↔
      out = (checkingBool M φ deg stmtIn.2 tr.messages tr.challenges,
        fun i : Empty => i.elim) := by
  rw [checkingVerifier_toVerifier_verify]
  simp only [support_pure, Set.mem_singleton_iff]

open scoped Classical in
/-- On the support of the deterministic checking verifier, accepting is equivalent to the raw
checking predicate being true. -/
theorem checkingVerifier_acceptance_iff_checkingBool
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr)) :
    out.1 = true ↔ checkingBool M φ deg stmtIn.2 tr.messages tr.challenges = true := by
  have hout_eq := (checkingVerifier_support_iff M φ deg stmtIn tr out).mp hout
  constructor
  · intro hacc
    rw [hout_eq] at hacc
    simpa using hacc
  · intro hbool
    rw [hout_eq]
    simpa using hbool

open scoped Classical in
/-- If a value in the support of `toVerifier.verify` is accepting, then the transcript's
raw checking predicate is true. This is the verifier-level form consumed by soundness
arguments, as opposed to the lower-level `checkingBool` statement. -/
theorem checkingVerifier_acceptance_implies_checkingBool
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr))
    (hacc : out.1 = true) :
    checkingBool M φ deg stmtIn.2 tr.messages tr.challenges = true := by
  exact (checkingVerifier_acceptance_iff_checkingBool M φ deg stmtIn tr out hout).mp hacc

open scoped Classical in
/-- Verifier-level accepting transcripts force the round-0 fold-query check. -/
theorem checkingVerifier_acceptance_implies_fold_check
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr))
    (hacc : out.1 = true) :
    inputAns stmtIn.2 (queryPoint φ (chalFE tr.challenges (outChalIdx M 0)))
      = msgAns tr.messages (msgIdx M 0)
          (msgPos M (msgIdx M 0) (queryPoint φ (chalFE tr.challenges (outChalIdx M 0)))) := by
  exact checkingBool_true_implies_fold_check (M := M) (φ := φ) (deg := deg)
    stmtIn.2 tr.messages tr.challenges
    (checkingVerifier_acceptance_implies_checkingBool M φ deg stmtIn tr out hout hacc)

open scoped Classical in
/-- Verifier-level accepting transcripts force every sampled inter-round consistency check. -/
theorem checkingVerifier_acceptance_implies_round_consistency
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr))
    (hacc : out.1 = true)
    (j : Fin M) :
    (msgAns tr.messages (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE tr.challenges (outChalIdx M j.succ))))
      = msgAns tr.messages (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE tr.challenges (outChalIdx M j.succ))))) ∧
    (msgAns tr.messages (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE tr.challenges (shiftChalIdx M j))))
      = msgAns tr.messages (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE tr.challenges (shiftChalIdx M j))))) := by
  exact checkingBool_true_implies_round_consistency (M := M) (φ := φ) (deg := deg)
    stmtIn.2 tr.messages tr.challenges
    (checkingVerifier_acceptance_implies_checkingBool M φ deg stmtIn tr out hout hacc) j

open scoped Classical in
/-- Out-challenge projection of `checkingVerifier_acceptance_implies_round_consistency`. -/
theorem checkingVerifier_acceptance_implies_out_consistency
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr))
    (hacc : out.1 = true)
    (j : Fin M) :
    msgAns tr.messages (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE tr.challenges (outChalIdx M j.succ))))
      = msgAns tr.messages (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE tr.challenges (outChalIdx M j.succ)))) := by
  exact checkingBool_true_implies_out_consistency (M := M) (φ := φ) (deg := deg)
    stmtIn.2 tr.messages tr.challenges
    (checkingVerifier_acceptance_implies_checkingBool M φ deg stmtIn tr out hout hacc) j

open scoped Classical in
/-- Shift-challenge projection of `checkingVerifier_acceptance_implies_round_consistency`. -/
theorem checkingVerifier_acceptance_implies_shift_consistency
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr))
    (hacc : out.1 = true)
    (j : Fin M) :
    msgAns tr.messages (msgIdx M j.castSucc)
        (msgPos M (msgIdx M j.castSucc)
          (queryPoint φ (chalFE tr.challenges (shiftChalIdx M j))))
      = msgAns tr.messages (msgIdx M j.succ)
        (msgPos M (msgIdx M j.succ)
          (queryPoint φ (chalFE tr.challenges (shiftChalIdx M j)))) := by
  exact checkingBool_true_implies_shift_consistency (M := M) (φ := φ) (deg := deg)
    stmtIn.2 tr.messages tr.challenges
    (checkingVerifier_acceptance_implies_checkingBool M φ deg stmtIn tr out hout hacc) j

open scoped Classical in
/-- Verifier-level accepting transcripts force the final low-degree check. -/
theorem checkingVerifier_acceptance_implies_final_in_code
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F))
    (out : Bool × (∀ _ : Empty, Unit))
    (hout : out ∈ _root_.support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr))
    (hacc : out.1 = true) :
    (fun x : ι =>
      (((List.finRange (Fintype.card ι)).map (fun k =>
        msgAns tr.messages (msgIdx M (Fin.last M))
          (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
        ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0))
      ∈ ReedSolomon.code φ deg := by
  exact checkingBool_true_implies_final_in_code (M := M) (φ := φ) (deg := deg)
    stmtIn.2 tr.messages tr.challenges
    (checkingVerifier_acceptance_implies_checkingBool M φ deg stmtIn tr out hout hacc)

set_option maxHeartbeats 1600000 in
/-- **Perfect completeness of the checking (M+1)-round STIR Vector IOPP**, for arbitrary
symbolic depth `M`, against the genuine perfect-completeness relation `stirRelation deg φ 0`:
on the honest run every transcript message is the packed genuine fold of the input codeword
(the run-support invariant), so every consistency check compares equal values and the final
full-read low-degree check sees exactly the input codeword, which the `δ = 0` input relation
forces into the code. -/
theorem stirCheckingIOP_perfectCompleteness (M : ℕ) (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction.perfectCompleteness (pure ()) isEmptyElim
      (stirRelation deg φ 0) acceptRejectOracleRel (stirCheckingIOP M φ deg) := by
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness
    (reduction := stirCheckingIOP M φ deg) (stirRelation deg φ 0) acceptRejectOracleRel
    (pure ()) isEmptyElim inferInstance
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- the δ = 0 input relation is genuine code membership
  have hmem : oStmtIn () ∈ ReedSolomon.code φ deg := by
    have h0 : Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg)
        ≤ ((0 : ℝ≥0) : ENNReal) := h_relIn
    exact mem_of_relDistFromCode_le_zero ⟨0, Submodule.zero_mem _⟩ (by simpa using h0)
  dsimp only [stirCheckingIOP, stirMultiRoundProver]
  simp only [checkingVerifier_toVerifier_verify]
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
        ((stirMultiRoundProver M φ deg).runToRound (Fin.last (3 * M + 3))
          (stmtIn, oStmtIn) witIn) := by
      simpa only [OptionT.support_liftM] using hα
    have hinv := stirMultiRoundProver_runToRound_invariant M φ deg (stmtIn, oStmtIn) witIn
      (Fin.last (3 * M + 3)) α hα'
    have hmsgs : ∀ j, FullTranscript.messages (pSpec := (stirMultiVSpec M ι).toProtocolSpec F)
        α.1 j
        = Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι (oStmtIn ())) := by
      intro j
      have hdir : ((j.1 : Fin (3 * M + 3)) : ℕ) % 3 = 1 :=
        (stirVSpec_dir_eq_msg_iff (M := M) (msgLen := fun _ => Fintype.card ι)
          (chalLen := 1)).mp j.2
      exact hinv.2 j.1.val j.1.isLt hdir
    have hbool : checkingBool M φ deg oStmtIn
        (FullTranscript.messages (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) α.1)
        (FullTranscript.challenges (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) α.1)
        = true :=
      checkingBool_honest M φ deg (oStmtIn ()) hmem oStmtIn rfl _ hmsgs _
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_map, support_map, Set.mem_image] at hx
    erw [OptionT_run_liftComp_pure] at hx
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, Option.map_some,
      Option.some.injEq] at hx
    subst hx
    have hfn : ∀ (f g : ∀ _ : Empty, Unit), f = g := fun _ _ => funext fun i => i.elim
    refine ⟨?_, ?_, hfn _ _⟩
    · simp only [acceptRejectOracleRel, Set.mem_singleton_iff, Prod.mk.injEq, hbool]
    · show (true : Bool) = checkingBool M φ deg oStmtIn _ _
      rw [hbool]

end Completeness

/-! ### Soundness: the honestly-named residuals (Johnson-CA-gated) -/

section Soundness

open VectorIOP ArkLib.ProofSystem.Stir.ErrorAccumulation

variable [Nonempty ι]

/-- **The named open residual (soundness leg for the CHECKING verifier)**: round-by-round
knowledge soundness of `stirCheckingVerifier` with respect to the δ-far soundness relation.
Unlike the shell-verifier residual (`stirMultiRoundRbrSoundnessResidual`, which is
likely-false since the shell accepts everything), this is the genuine open obligation of
#301: the checking verifier rejects provers caught inconsistent at the sampled points or
whose final message is not a codeword, and bounding its flip probability is exactly the
per-round proximity-gap analysis. NOT proven here; consumed as a hypothesis. -/
def stirCheckingRbrSoundnessResidual (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0) : Prop :=
  OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
    (stirRelation deg φ δ) (stirCheckingIOP M φ deg).verifier ε_rbr

/-- **The CA bridge residual**: the implication from the EXISTING Johnson-regime
correlated-agreement residuals to rbr knowledge soundness of the checking verifier —

* `ProximityGap.StrictCoeffPolysResidual` (`BCIKS20/Curves.lean`): the strict Johnson §5
  list-decoding extraction behind the BCIKS20 correlated-agreement theorem (the in-tree
  producer for `Combine.combine_theorem` / `STIR.proximity_gap` in the `1 − √ρ` regime),
  consumed at every positive batching width `k`;
* `ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap`: the named keystone
  equating the accounting per-round errors with the BCIKS20 proximity-gap error bounds.

This implication (CA ⟹ per-round flip-probability bounds for the fold/out/shift/fin checks
⟹ rbr soundness) is the genuine open protocol-soundness mathematics of #301. It is isolated
here as a named `Prop` and consumed as a hypothesis below — NOT fabricated. -/
def stirCheckingCABridge (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (e ProxGapBound : Fin (M + 1) → ℝ≥0) : Prop :=
  (∀ k : ℕ, 0 < k →
    ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
      (k := k) (deg := deg) (domain := φ) (δ := δ)) →
  PerRoundProximityGap e ProxGapBound →
  stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr

/-- rbr knowledge soundness of the checking verifier, from the named CA residuals through the
named bridge (modus ponens; the open content lives entirely in the named hypotheses). -/
theorem stirCheckingRbrSoundness_of_CA (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (e ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr e ProxGapBound)
    (hCA : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ))
    (hPR : PerRoundProximityGap e ProxGapBound) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr :=
  hBridge hCA hPR

omit [SampleableType F] in
/-- All strict coefficient-polynomial residuals needed by the checking bridge are discharged in
the vacuous small-field regime `|F| ≤ |ι|`. For any positive curve width `k`, this implies
`|F| ≤ k * |ι|`, so the existing BCIKS20 small-field theorem
`strictCoeffPolysResidual_of_card_le` applies. -/
theorem strictCoeffPolys_all_of_card_le [DecidableEq ι]
    (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (hq : (Fintype.card F : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0)) :
    ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ) := by
  intro k hk
  refine ProximityGap.strictCoeffPolysResidual_of_card_le
    (k := k) (deg := deg) (domain := φ) (δ := δ)
    (Nat.pos_of_ne_zero (NeZero.ne deg)) hδ ?_
  have hk1_nat : 1 ≤ k := Nat.succ_le_iff.mpr hk
  have hk1 : (1 : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast hk1_nat
  have hmul : (Fintype.card ι : ℝ≥0) * 1 ≤ (Fintype.card ι : ℝ≥0) * k :=
    mul_le_mul_right hk1 (Fintype.card ι : ℝ≥0)
  exact le_trans hq (by simpa [one_mul, mul_comm] using hmul)

omit [SampleableType F] in
/-- The sharp vacuous-regime counterpart of `strictCoeffPolys_all_of_card_le`: if
`|F| ≤ deg^2 * 10^7`, then for every positive curve width `k` we have
`|F| ≤ k * deg^2 * 10^7`, so `strictCoeffPolysResidual_of_card_le_e7` discharges the full
positive-width strict coefficient-polynomial residual family. -/
theorem strictCoeffPolys_all_of_card_le_e7 [DecidableEq ι]
    (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ) := by
  intro k hk
  refine ProximityGap.strictCoeffPolysResidual_of_card_le_e7
    (k := k) (deg := deg) (domain := φ) (δ := δ) ?_
  have hk1_nat : 1 ≤ k := Nat.succ_le_iff.mpr hk
  have hk1 : (1 : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast hk1_nat
  have hmul :
      (((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0) * 1) ≤
        (((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0) * k) :=
    mul_le_mul_right hk1 (((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0))
  exact le_trans hq (by simpa [one_mul, mul_comm] using hmul)

omit [SampleableType F] in
/-- The #304-aligned conversion: if every positive-width instance of the honest large-sector
residual is available, then the full strict coefficient-polynomial residual family needed by
the checking bridge is available.  The small-good-set sector is exactly the Lagrange
interpolation case proven in `StrictCoeffLargeReduction`. -/
theorem strictCoeffPolys_all_of_large [DecidableEq ι]
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hLarge : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysLargeResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ)) :
    ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ) := by
  intro k hk
  exact ProximityGap.strictCoeffPolysResidual_of_large (hLarge k hk)

/-- RBR knowledge soundness of the checking verifier in the small-field regime, conditional only
on the protocol-level CA bridge. The BCIKS20 strict-coefficient residual family is discharged by
`strictCoeffPolys_all_of_card_le`; the per-round equality keystone is reflexive by choosing
the accounting errors to be the proximity-gap bounds. -/
theorem stirCheckingRbrSoundness_of_card_le [DecidableEq ι]
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (hq : (Fintype.card F : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0)) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr :=
  stirCheckingRbrSoundness_of_CA M φ deg δ ε_rbr ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_card_le φ deg δ hδ hq)
    (PerRoundProximityGap.refl ProxGapBound)

/-- RBR knowledge soundness of the checking verifier in the sharp vacuous regime
`|F| ≤ deg^2 * 10^7`, conditional only on the protocol-level CA bridge. -/
theorem stirCheckingRbrSoundness_of_card_le_e7 [DecidableEq ι]
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr :=
  stirCheckingRbrSoundness_of_CA M φ deg δ ε_rbr ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_card_le_e7 φ deg δ hq)
    (PerRoundProximityGap.refl ProxGapBound)

/-- RBR knowledge soundness of the checking verifier from the #304 large-sector residual family,
conditional only on the protocol-level checking bridge. -/
theorem stirCheckingRbrSoundness_of_large [DecidableEq ι]
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hLarge : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysLargeResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ)) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr :=
  stirCheckingRbrSoundness_of_CA M φ deg δ ε_rbr ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_large φ deg δ hLarge)
    (PerRoundProximityGap.refl ProxGapBound)

/-- **Vacuity gate for the checking rbr-soundness residual**: rbr knowledge soundness of the
checking verifier holds outright for ANY error budget that allots ≥ 1 to the round-0 (fold)
challenge. The knowledge state function is the canonical "δ-close at the root" function —
false on the empty transcript for δ-far inputs and true afterwards; the only false→true
crossing happens at the round-0 challenge (round 0 is a verifier challenge since prover
messages sit at rounds `3j + 1` by `stirVSpec_dir_eq_msg_iff`), where the unit budget absorbs
the whole probability mass (`probEvent_le_one`). All other challenge rounds have crossing
probability `0`. HONESTY: this is the vacuous-budget regime — it carries no security content
for budgets below 1, where the genuine open bridge (`stirCheckingCABridge`) remains the open
math of #301. -/
theorem stirCheckingRbrSoundness_of_one_le_first
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (h1 : ∀ i : (stirMultiVSpec M ι).ChallengeIdx, (i.1 : ℕ) = 0 → 1 ≤ ε_rbr i) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr := by
  refine ⟨fun _ => Unit,
    { eqIn := rfl
      extractMid := fun _ _ _ _ => ()
      extractOut := fun _ _ _ => () },
    { toFun := fun m stmtIn _ _ => (m : ℕ) = 0 → (stmtIn, ()) ∈ stirRelation deg φ δ
      toFun_empty := fun stmtIn witMid => by
        constructor
        · intro h _; exact h
        · intro h; exact h (by simp)
      toFun_next := fun m hdir stmtIn tr msg witMid h => by
        intro hc0
        exfalso
        rw [show ((stirMultiVSpec M ι).toProtocolSpec F).dir m = (stirMultiVSpec M ι).dir m
          from rfl, stirVSpec_dir_eq_msg_iff] at hdir
        have hm0 : (m : ℕ) = 0 := by simpa using hc0
        omega
      toFun_full := fun stmtIn tr witOut _ => by
        intro hlast
        exfalso
        simp only [Fin.val_last] at hlast
        omega }, ?_⟩
  intro stmtIn witIn prover i
  by_cases h0 : (i.1 : ℕ) = 0
  · refine le_trans probEvent_le_one ?_
    exact_mod_cast h1 i h0
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro ⟨tr, chal, lg⟩ _ hp
    obtain ⟨w, hno, -⟩ := hp
    exact hno fun hc => absurd (by simpa using hc) h0

/-- **The STIR proximity error is ≥ 1 in the small-field regime** `|F| ≤ (m−1)·|ι|` (the
regime where `STIR.proximity_gap_of_card_le` is unconditional), in the unique-decoding branch
`δ ≤ (1 − ρ)/2`: there `err⋆ = (m−1)·d/(ρ·|F|)`, and `ρ·|F| ≤ (d/|ι|)·(m−1)·|ι| = (m−1)·d`
since `ρ·|ι| = min d |ι| ≤ d` (`rateOfLinearCode_eq_min_div`). -/
theorem one_le_proximityError_of_card_le {deg m : ℕ} [NeZero deg] (φ : ι ↪ F) (δ : ℝ≥0)
    (hδ : δ ≤ (1 - (LinearCode.rate (code φ deg) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0)) :
    1 ≤ proximityError F deg (LinearCode.rate (code φ deg)) δ m := by
  have hcardι : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hcardF : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  -- the rate in ℝ≥0: `min deg |ι| / |ι|`
  have hrate : (LinearCode.rate (code φ deg) : ℝ≥0)
      = ((min deg (Fintype.card ι) : ℕ) : ℝ≥0) / ((Fintype.card ι : ℕ) : ℝ≥0) := by
    rw [ReedSolomon.rateOfLinearCode_eq_min_div]
    push_cast
    norm_num
  have hρpos : (0 : ℝ≥0) < (LinearCode.rate (code φ deg) : ℝ≥0) := by
    rw [hrate]
    apply div_pos _ hcardι
    have : 0 < min deg (Fintype.card ι) :=
      lt_min (Nat.pos_of_ne_zero (NeZero.ne deg)) Fintype.card_pos
    exact_mod_cast this
  -- the key product bound: `ρ · |ι| ≤ deg`
  have hρι : (LinearCode.rate (code φ deg) : ℝ≥0) * (Fintype.card ι : ℝ≥0) ≤ (deg : ℝ≥0) := by
    rw [hrate, div_mul_cancel₀ _ (ne_of_gt hcardι)]
    exact_mod_cast min_le_left _ _
  -- hence `ρ · |F| ≤ (m−1)·deg`
  have hkey : (LinearCode.rate (code φ deg) : ℝ≥0) * (Fintype.card F : ℝ≥0)
      ≤ ((m : ℝ≥0) - 1) * (deg : ℝ≥0) := by
    calc (LinearCode.rate (code φ deg) : ℝ≥0) * (Fintype.card F : ℝ≥0)
        ≤ (LinearCode.rate (code φ deg) : ℝ≥0)
            * (((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0)) := by
          exact mul_le_mul_right hq _
      _ = ((m : ℝ≥0) - 1) * ((LinearCode.rate (code φ deg) : ℝ≥0)
            * (Fintype.card ι : ℝ≥0)) := by ring
      _ ≤ ((m : ℝ≥0) - 1) * (deg : ℝ≥0) := mul_le_mul_right hρι _
  rw [proximityError, if_pos hδ]
  rw [le_div_iff₀ (mul_pos hρpos hcardF)]
  simpa using hkey

/-- **Small-field discharge of the checking rbr-soundness residual** (#301 Part B): in the
regime `|F| ≤ (m−1)·|ι|` (where `STIR.proximity_gap_of_card_le` is unconditional) and the
unique-decoding branch `δ ≤ (1−ρ)/2`, the rbr knowledge soundness of the checking verifier
holds for any budget dominating the prescribed STIR proximity error `err⋆(deg, ρ, δ, m)` at
the fold challenge — with NO correlated-agreement residuals and NO bridge hypothesis: the
regime forces `err⋆ ≥ 1`, which absorbs the fold-challenge crossing probability outright. -/
theorem stirCheckingRbrSoundness_of_small_field
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0) {m : ℕ}
    (hδ : δ ≤ (1 - (LinearCode.rate (code φ deg) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hε : ∀ i : (stirMultiVSpec M ι).ChallengeIdx, (i.1 : ℕ) = 0 →
      proximityError F deg (LinearCode.rate (code φ deg)) δ m ≤ ε_rbr i) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr :=
  stirCheckingRbrSoundness_of_one_le_first M φ deg δ ε_rbr
    (fun i hi => le_trans (one_le_proximityError_of_card_le φ δ hδ hq) (hε i hi))

/-- **The protocol-level CA bridge residual is DISCHARGED in the small-field regime**: its
conclusion (`stirCheckingRbrSoundnessResidual`) holds outright there, so the implication is
trivially true. In the general (large-field, sub-1 budget) regime the bridge remains the
genuine open math of #301. -/
theorem stirCheckingCABridge_of_small_field
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0) {m : ℕ}
    (hδ : δ ≤ (1 - (LinearCode.rate (code φ deg) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hε : ∀ i : (stirMultiVSpec M ι).ChallengeIdx, (i.1 : ℕ) = 0 →
      proximityError F deg (LinearCode.rate (code φ deg)) δ m ≤ ε_rbr i)
    (e ProxGapBound : Fin (M + 1) → ℝ≥0) :
    stirCheckingCABridge M φ deg δ ε_rbr e ProxGapBound :=
  fun _ _ => stirCheckingRbrSoundness_of_small_field M φ deg δ hδ hq ε_rbr hε

/-- **The checking IOPP is `IsSecureWithGap`**, with the completeness leg PROVEN
(`stirCheckingIOP_perfectCompleteness`) and the soundness leg consumed as the named
checking-verifier residual. -/
theorem stirCheckingIOP_isSecureWithGap (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hSound : stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirCheckingIOP M φ deg) where
  is_complete := stirCheckingIOP_perfectCompleteness M φ deg
  is_rbr_knowledge_sound := hSound

/-- `IsSecureWithGap` for the checking IOPP from the named CA residuals + bridge. -/
theorem stirCheckingIOP_isSecureWithGap_of_CA (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (e ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr e ProxGapBound)
    (hCA : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ))
    (hPR : PerRoundProximityGap e ProxGapBound) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirCheckingIOP M φ deg) :=
  stirCheckingIOP_isSecureWithGap M φ deg δ ε_rbr
    (stirCheckingRbrSoundness_of_CA M φ deg δ ε_rbr e ProxGapBound hBridge hCA hPR)

/-- `IsSecureWithGap` for the checking IOPP in the small-field regime, with the BCIKS20
strict-coefficient residual family discharged. The only remaining soundness hypothesis is the
protocol-level checking bridge. -/
theorem stirCheckingIOP_isSecureWithGap_of_card_le [DecidableEq ι]
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (hq : (Fintype.card F : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0)) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirCheckingIOP M φ deg) :=
  stirCheckingIOP_isSecureWithGap M φ deg δ ε_rbr
    (stirCheckingRbrSoundness_of_card_le M φ deg δ ε_rbr ProxGapBound hBridge hδ hq)

/-- `IsSecureWithGap` for the checking IOPP in the sharp vacuous regime
`|F| ≤ deg^2 * 10^7`, with the BCIKS20 strict-coefficient residual family discharged. -/
theorem stirCheckingIOP_isSecureWithGap_of_card_le_e7 [DecidableEq ι]
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirCheckingIOP M φ deg) :=
  stirCheckingIOP_isSecureWithGap M φ deg δ ε_rbr
    (stirCheckingRbrSoundness_of_card_le_e7 M φ deg δ ε_rbr ProxGapBound hBridge hq)

/-- `IsSecureWithGap` for the checking IOPP from the #304 large-sector residual family. -/
theorem stirCheckingIOP_isSecureWithGap_of_large [DecidableEq ι]
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hLarge : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysLargeResidual (ι := ι) (F := F)
        (k := k) (deg := deg) (domain := φ) (δ := δ)) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirCheckingIOP M φ deg) :=
  stirCheckingIOP_isSecureWithGap M φ deg δ ε_rbr
    (stirCheckingRbrSoundness_of_large M φ deg δ ε_rbr ProxGapBound hBridge hLarge)

/-- **`IsSecureWithGap` for the checking IOPP in the small-field regime `|F| ≤ (m−1)·|ι|`,
with NO residual hypotheses** (#301 Part B): completeness is the landed
`stirCheckingIOP_perfectCompleteness`; soundness is the small-field discharge
(`stirCheckingRbrSoundness_of_small_field`) — no CA family, no bridge, no per-round-gap
keystone. -/
theorem stirCheckingIOP_isSecureWithGap_small_field
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) [NeZero deg] (δ : ℝ≥0) {m : ℕ}
    (hδ : δ ≤ (1 - (LinearCode.rate (code φ deg) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hε : ∀ i : (stirMultiVSpec M ι).ChallengeIdx, (i.1 : ℕ) = 0 →
      proximityError F deg (LinearCode.rate (code φ deg)) δ m ≤ ε_rbr i) :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ) ε_rbr
      (stirCheckingIOP M φ deg) :=
  stirCheckingIOP_isSecureWithGap M φ deg δ ε_rbr
    (stirCheckingRbrSoundness_of_small_field M φ deg δ hδ hq ε_rbr hε)

end Soundness

end MultiRound

section CheckingFrontDoors

open MultiRound VectorIOP LinearCode ReedSolomon STIR NNReal Finset
open ArkLib.ProofSystem.Stir.ErrorAccumulation

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- **Lemma 5.4 through the CHECKING IOPP**: `stir_rbr_soundness` discharged with
`π := stirCheckingIOP` via the landed `stir_rbr_soundness_of_secure_vectorIOP` wiring. The
completeness leg is PROVEN; the soundness leg is consumed via the named CA residuals
(`StrictCoeffPolysResidual` + `PerRoundProximityGap`) through the named bridge
(`stirCheckingCABridge`); the per-round error legs (`hfold`/`hrest`) are free-parameter
constraints of the statement. -/
theorem stir_rbr_soundness_of_checkingIOP_CA
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
    (e ProxGapBound : Fin (M + 1) → ℝ≥0)
    -- the named open CA-bridge residual for the checking verifier
    (hBridge : stirCheckingCABridge M (P.φ 0) (degree ι P 0) (Dist.δ 0)
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
      e ProxGapBound)
    -- the EXISTING named Johnson-CA residual (BCIKS20 §5 strict extraction)
    (hCA : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysResidual (ι := ι 0) (F := F)
        (k := k) (deg := degree ι P 0) (domain := P.φ 0) (δ := Dist.δ 0))
    -- the EXISTING named per-round accounting keystone
    (hPR : PerRoundProximityGap e ProxGapBound)
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
    (stirCheckingIOP M (P.φ 0) (degree ι P 0))
    (stirCheckingIOP_isSecureWithGap_of_CA M (P.φ 0) (degree ι P 0) (Dist.δ 0) _
      e ProxGapBound hBridge hCA hPR)
    hfold hrest

/-- **Lemma 5.4 through the CHECKING IOPP, small-field CA discharge**: the same checking front
door as `stir_rbr_soundness_of_checkingIOP_CA`, but the BCIKS20 strict-coefficient residual family
is discharged by `strictCoeffPolys_all_of_card_le` under `|F| ≤ |ι₀|`. The remaining
soundness hypothesis is the protocol-level checking bridge. -/
theorem stir_rbr_soundness_of_checkingIOP_card_le
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    [DecidableEq (ι 0)]
    {s : ℕ} {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι P Dist} [NeZero (degree ι P 0)]
    (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) P.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j)))))
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M (P.φ 0) (degree ι P 0) (Dist.δ 0)
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
      ProxGapBound ProxGapBound)
    (hδsqrt : Dist.δ 0 < 1 - ReedSolomon.sqrtRate (degree ι P 0) (P.φ 0))
    (hq : (Fintype.card F : ℝ≥0) ≤ (Fintype.card (ι 0) : ℝ≥0))
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
  stir_rbr_soundness_of_checkingIOP_CA (hParams := hParams) (Codes := Codes)
    ι hδ₀ hδᵢ ε_fold ε_out ε_shift ε_fin
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_card_le (P.φ 0) (degree ι P 0) (Dist.δ 0)
      hδsqrt hq)
    (PerRoundProximityGap.refl ProxGapBound)
    hfold hrest

/-- **Lemma 5.4 through the CHECKING IOPP, sharp vacuous CA discharge**: as
`stir_rbr_soundness_of_checkingIOP_card_le`, but using the `|F| ≤ deg₀² * 10⁷` BCIKS discharge. -/
theorem stir_rbr_soundness_of_checkingIOP_card_le_e7
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    [DecidableEq (ι 0)]
    {s : ℕ} {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι P Dist} [NeZero (degree ι P 0)]
    (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) P.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j)))))
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M (P.φ 0) (degree ι P 0) (Dist.δ 0)
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
      ProxGapBound ProxGapBound)
    (hq : (Fintype.card F : ℝ≥0) ≤ (((degree ι P 0) ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0))
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
  stir_rbr_soundness_of_checkingIOP_CA (hParams := hParams) (Codes := Codes)
    ι hδ₀ hδᵢ ε_fold ε_out ε_shift ε_fin
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_card_le_e7 (P.φ 0) (degree ι P 0) (Dist.δ 0) hq)
    (PerRoundProximityGap.refl ProxGapBound)
    hfold hrest

/-- **Lemma 5.4 through the CHECKING IOPP, large-sector CA discharge**: as
`stir_rbr_soundness_of_checkingIOP_CA`, but the BCIKS20 input is the #304 honest
large-good-set residual family. -/
theorem stir_rbr_soundness_of_checkingIOP_large
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    [DecidableEq (ι 0)]
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
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M (P.φ 0) (degree ι P 0) (Dist.δ 0)
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
      ProxGapBound ProxGapBound)
    (hLarge : ∀ k : ℕ, 0 < k →
      ProximityGap.StrictCoeffPolysLargeResidual (ι := ι 0) (F := F)
        (k := k) (deg := degree ι P 0) (domain := P.φ 0) (δ := Dist.δ 0))
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
  stir_rbr_soundness_of_checkingIOP_CA (hParams := hParams) (Codes := Codes)
    ι hδ₀ hδᵢ ε_fold ε_out ε_shift ε_fin
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_large (P.φ 0) (degree ι P 0) (Dist.δ 0) hLarge)
    (PerRoundProximityGap.refl ProxGapBound)
    hfold hrest

/-- **Lemma 5.4 through the CHECKING IOPP, small-field UNCONDITIONAL soundness discharge**
(#301 Part B): `stir_rbr_soundness` discharged through `π := stirCheckingIOP` in the regime
`|F| ≤ (m−1)·|ι₀|` and the unique-decoding branch `δ₀ ≤ (1−ρ₀)/2`, with NO
correlated-agreement residual, NO checking bridge, and NO per-round-gap keystone. The lower-bound
hypothesis `hεlb` says the fold-round error budget dominates the vacuous `err⋆ ≥ 1` threshold;
the usual `hfold`/`hrest` hypotheses are still the statement's advertised per-round upper
bounds. -/
theorem stir_rbr_soundness_of_checkingIOP_small_field
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    {s : ℕ} {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι P Dist} [NeZero (degree ι P 0)]
    (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) P.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j)))))
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    {m : ℕ}
    (hδudr : Dist.δ 0 ≤
      (1 - (LinearCode.rate (code (P.φ 0) (degree ι P 0)) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card (ι 0) : ℝ≥0))
    (hεlb :
      proximityError F (degree ι P 0)
        (LinearCode.rate (code (P.φ 0) (degree ι P 0))) (Dist.δ 0) m ≤ ε_fold)
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
    (stirCheckingIOP M (P.φ 0) (degree ι P 0))
    (stirCheckingIOP_isSecureWithGap_small_field M (P.φ 0) (degree ι P 0) (Dist.δ 0)
      hδudr hq
      (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
      (fun i _hi => le_trans hεlb (Finset.le_max' _ _ (by simp))))
    hfold hrest

/-- **Theorem 5.1 through the CHECKING IOPP**: `stir_main` discharged with
`π := stirCheckingIOP` via the landed `stir_main_of_secure_vectorIOP` wiring. The
completeness leg is PROVEN; the soundness leg is consumed via the named CA residuals through
the named bridge; the rbr error bound (`hε`) and the complexity claims (`hM`/`hLen`/`hQin`/
`hQpf`) are free-parameter constraints of the statement. -/
theorem stir_main_of_checkingIOP_CA
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
    (e ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr e ProxGapBound)
    (hCA : ∀ k' : ℕ, 0 < k' →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k') (deg := degree) (domain := φ) (δ := δ))
    (hPR : PerRoundProximityGap e ProxGapBound)
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
    (stirCheckingIOP M φ degree)
    (stirCheckingIOP_isSecureWithGap_of_CA M φ degree δ ε_rbr
      e ProxGapBound hBridge hCA hPR)
    hε hM hLen hQin hQpf

/-- **Theorem 5.1 through the CHECKING IOPP, small-field CA discharge**: `stir_main` through
`π := stirCheckingIOP`, with the strict BCIKS20 coefficient residual family discharged under
`|F| ≤ |ι|`. The remaining soundness hypothesis is the protocol-level checking bridge. -/
theorem stir_main_of_checkingIOP_card_le
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ] [NeZero degree]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr ProxGapBound ProxGapBound)
    (hδsqrt : δ < 1 - ReedSolomon.sqrtRate degree φ)
    (hq : (Fintype.card F : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0))
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_CA secpar hk hkGe δ hδub hF ε_rbr
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_card_le φ degree δ hδsqrt hq)
    (PerRoundProximityGap.refl ProxGapBound)
    hε hM hLen hQin hQpf

/-- **Theorem 5.1 through the CHECKING IOPP, sharp vacuous CA discharge**: as
`stir_main_of_checkingIOP_card_le`, but using the `|F| ≤ degree² * 10⁷` BCIKS discharge. -/
theorem stir_main_of_checkingIOP_card_le_e7
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ] [NeZero degree]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr ProxGapBound ProxGapBound)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((degree ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0))
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_CA secpar hk hkGe δ hδub hF ε_rbr
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_card_le_e7 φ degree δ hq)
    (PerRoundProximityGap.refl ProxGapBound)
    hε hM hLen hQin hQpf

/-- **Theorem 5.1 through the CHECKING IOPP, large-sector CA discharge**: as
`stir_main_of_checkingIOP_CA`, but consuming the #304 honest large-sector residual family
instead of the full strict coefficient residual family. -/
theorem stir_main_of_checkingIOP_large
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr ProxGapBound ProxGapBound)
    (hLarge : ∀ k' : ℕ, 0 < k' →
      ProximityGap.StrictCoeffPolysLargeResidual (ι := ι) (F := F)
        (k := k') (deg := degree) (domain := φ) (δ := δ))
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_CA secpar hk hkGe δ hδub hF ε_rbr
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_large φ degree δ hLarge)
    (PerRoundProximityGap.refl ProxGapBound)
    hε hM hLen hQin hQpf

/-- **Theorem 5.1 through the CHECKING IOPP, small-field UNCONDITIONAL soundness discharge**
(#301 Part B): `stir_main` discharged through `π := stirCheckingIOP` in the regime
`|F| ≤ (m−1)·|ι|` and the unique-decoding branch `δ ≤ (1−ρ)/2`, with NO
correlated-agreement residual, NO checking bridge, and NO per-round-gap keystone: the
soundness leg is PROVEN outright (the regime forces the prescribed `err⋆ ≥ 1`, the same
vacuity that makes `STIR.proximity_gap_of_card_le` unconditional). The remaining hypotheses
(`hε`/`hM`/`hLen`/`hQin`/`hQpf`) are exactly `stir_main`'s own free-parameter legs.
HONESTY: in this regime `hε` together with `hεlb` pins `secpar = 0`, since
`ε_rbr ≥ err⋆ ≥ 1 > 2^{-secpar}` for `secpar > 0` — the faithful formal statement that STIR
offers no security over a field this small. The general (large-field) regime stays
conditional on the #304 capture-kernel stream through the named bridge. -/
theorem stir_main_of_checkingIOP_small_field
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ] [NeZero degree]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    {m : ℕ}
    (hδudr : δ ≤ (1 - (LinearCode.rate (code φ degree) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hεlb : ∀ i : (stirMultiVSpec M ι).ChallengeIdx, (i.1 : ℕ) = 0 →
      proximityError F degree (LinearCode.rate (code φ degree)) δ m ≤ ε_rbr i)
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
    (stirCheckingIOP M φ degree)
    (stirCheckingIOP_isSecureWithGap_small_field M φ degree δ hδudr hq ε_rbr hεlb)
    hε hM hLen hQin hQpf

end CheckingFrontDoors

end StirIOP

#print axioms StirIOP.MultiRound.simulateQ_checkingComp
#print axioms StirIOP.MultiRound.stirCheckingVerifier
#print axioms StirIOP.MultiRound.stirCheckingIOP
#print axioms StirIOP.MultiRound.stirMultiRoundProver_runToRound_invariant
#print axioms StirIOP.MultiRound.mem_of_relDistFromCode_le_zero
#print axioms StirIOP.MultiRound.checkingBool_honest
#print axioms StirIOP.MultiRound.checkingBool_true_implies_fold_check
#print axioms StirIOP.MultiRound.checkingBool_true_implies_round_consistency
#print axioms StirIOP.MultiRound.checkingBool_true_implies_out_consistency
#print axioms StirIOP.MultiRound.checkingBool_true_implies_shift_consistency
#print axioms StirIOP.MultiRound.checkingBool_true_implies_final_in_code
#print axioms StirIOP.MultiRound.checkingBool_eq_true_iff
#print axioms StirIOP.MultiRound.checkingVerifier_toVerifier_verify
#print axioms StirIOP.MultiRound.checkingVerifier_support_iff
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_iff_checkingBool
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_implies_checkingBool
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_implies_fold_check
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_implies_round_consistency
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_implies_out_consistency
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_implies_shift_consistency
#print axioms StirIOP.MultiRound.checkingVerifier_acceptance_implies_final_in_code
#print axioms StirIOP.MultiRound.stirCheckingIOP_perfectCompleteness
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_CA
#print axioms StirIOP.MultiRound.strictCoeffPolys_all_of_card_le
#print axioms StirIOP.MultiRound.strictCoeffPolys_all_of_card_le_e7
#print axioms StirIOP.MultiRound.strictCoeffPolys_all_of_large
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_card_le
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_card_le_e7
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_large
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap_of_CA
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap_of_card_le
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap_of_card_le_e7
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap_of_large
#print axioms StirIOP.stir_rbr_soundness_of_checkingIOP_CA
#print axioms StirIOP.stir_rbr_soundness_of_checkingIOP_card_le
#print axioms StirIOP.stir_rbr_soundness_of_checkingIOP_card_le_e7
#print axioms StirIOP.stir_rbr_soundness_of_checkingIOP_large
#print axioms StirIOP.stir_rbr_soundness_of_checkingIOP_small_field
#print axioms StirIOP.stir_main_of_checkingIOP_CA
#print axioms StirIOP.stir_main_of_checkingIOP_card_le
#print axioms StirIOP.stir_main_of_checkingIOP_card_le_e7
#print axioms StirIOP.stir_main_of_checkingIOP_large
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_one_le_first
#print axioms StirIOP.MultiRound.one_le_proximityError_of_card_le
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_small_field
#print axioms StirIOP.MultiRound.stirCheckingCABridge_of_small_field
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap_small_field
#print axioms StirIOP.stir_main_of_checkingIOP_small_field
