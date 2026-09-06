/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ToMathlib.OracleCompEvalDistBindComm
import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

/-!
# Sequential append run distributions and verifier routing

Distributional factoring and message/challenge seam proofs for appended provers,
with the verifier routing identities used by sequential composition.
-/

section


/-!
# Distributional (`evalDist`-level) run-factoring for the appended prover

The syntactic run-factoring keystone `Prover.append_run` is proven *conditional* on
`Prover.appendRunRightResidual`, a **syntactic** `OracleComp` equality between the appended run and
the sequential `P₁.run ≫ P₂.run`. That syntactic residual is **false** when the first `pSpec₂` round
is a challenge: the appended prover samples the seam `getChallenge` *before* consuming `P₁.output`
(see `Prover.append_continueFromTo_seam_step_challenge`), whereas the factored form runs `P₁.output`
*first*. The two are different free-monad trees, hence unequal syntactically — but **equal as
distributions**, because `getChallenge` (a uniform sample) is independent of `P₁.output` (a
computation in `oSpec`), and `SPMF` is commutative (`OracleComp.evalDist_bind_comm`).

This section states the residual and the keystone at the `evalDist` level, the form actually consumed
by completeness/soundness proofs (which only ever compare `evalDist`s). `appendRunRightDistResidual`
is the distribution-level residual; it is **dischargeable** (unlike its syntactic counterpart) by
assembling the proven left-block / message-seam / interior pieces together with
`evalDist_bind_comm` at the challenge seam. `append_run_evalDist` reduces the appended run to the
sequential composition, conditional on that residual, via the *same* seam-split backbone as the
syntactic `append_run`.

## Message-seam discharge (unconditional)

When the seam round (`pSpec₂`'s round 0) is a **prover message** (`pSpec₂.dir 0 = .P_to_V`), the
*syntactic* residual already holds (`Prover.appendRunRightResidual_holds_msg`), so the
distributional one follows by `congrArg evalDist`. This makes `append_run_evalDist` **unconditional**
for the message-seam case (`append_run_evalDist_msg`) — exactly the case that arises in LogUp
Protocol 2, whose embedded sumcheck phase opens with a prover message (the round polynomial). The
genuinely distributional content (`evalDist_bind_comm`) is needed only for the challenge-seam case.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- **Distribution-level right-block residual of `append_run`.** The `evalDist` analogue of
`appendRunRightResidual`: after the seam-split, the appended run-distribution equals the sequential
`P₁.run ≫ P₂.run` distribution. Unlike the syntactic residual, this holds even when the seam round
is a challenge, since the `getChallenge`/`P₁.output` reordering at the seam is a *distributional*
commutation (`OracleComp.evalDist_bind_comm`), not a syntactic one. -/
def appendRunRightDistResidual [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) : Prop :=
  evalDist
      (((do
          let ⟨transcript, state⟩ ←
            (Prover.runToRound (⟨m, by omega⟩ : Fin (m + n + 1)) stmt wit (P₁.append P₂)
              >>= (P₁.append P₂).continueFromTo stmt wit ⟨m, by omega⟩ (Fin.last (m + n)))
          let output ← @liftM (OracleComp oSpec)
            (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
            (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
              (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
            (Stmt₃ × Wit₃) ((P₁.append P₂).output state)
          pure (transcript, output)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)))
    = evalDist
      ((do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃))

/-- **Distributional run-factoring keystone.** Running the appended prover `P₁.append P₂` equals, as
a distribution, running `P₁` then `P₂` sequentially. Proven by the same seam-split backbone as the
syntactic `append_run` (`run_eq_runToRound_last` then `runToRound_eq_bind_continueFromTo` at the seam
round `⟨m⟩`), reducing to the distribution-level residual `appendRunRightDistResidual`. This is the
form the completeness/soundness proofs consume; it sidesteps the syntactic
`getChallenge`/`P₁.output` non-commutation that blocks the syntactic `appendRunRightResidual`. -/
theorem append_run_evalDist [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁)
    (hRight : appendRunRightDistResidual (P₁ := P₁) (P₂ := P₂) stmt wit) :
      evalDist ((P₁.append P₂).run stmt wit)
        = evalDist ((do
          let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
          let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
          return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)) := by
  rw [run_eq_runToRound_last,
      runToRound_eq_bind_continueFromTo (P₁.append P₂) stmt wit
        (⟨m, by omega⟩ : Fin (m + n + 1)) (Fin.last (m + n)) (by
          simp only [Fin.le_def, Fin.val_last]; omega)]
  simpa [appendRunRightDistResidual] using hRight

/-- **Message-seam discharge of the distributional residual (unconditional).** When the seam round
is a prover message, the *syntactic* residual `appendRunRightResidual` already holds
(`appendRunRightResidual_holds_msg`), so its `evalDist` image — the distributional residual — holds
by `congrArg evalDist`. No distributional commutation is needed in this case. -/
theorem appendRunRightDistResidual_holds_msg
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    appendRunRightDistResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  unfold appendRunRightDistResidual
  exact congrArg evalDist (appendRunRightResidual_holds_msg stmt wit hn hDir hDir₂)

/-- **Sequential-composition run-factoring at `evalDist`, for a message-first `P₂` (UNCONDITIONAL).**
Combines the conditional `append_run_evalDist` with the message-seam discharge
`appendRunRightDistResidual_holds_msg`. This is the distribution-level keystone the LogUp
completeness/soundness composition consumes (LogUp's embedded sumcheck opens with a prover message,
so its seam is a message seam). No residual hypothesis required. -/
theorem append_run_evalDist_msg
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
      evalDist ((P₁.append P₂).run stmt wit)
        = evalDist ((do
          let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
          let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
          return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)) :=
  append_run_evalDist stmt wit (appendRunRightDistResidual_holds_msg stmt wit hn hDir hDir₂)

#print axioms append_run_evalDist
#print axioms appendRunRightDistResidual_holds_msg
#print axioms append_run_evalDist_msg

end Prover

end

section


/-!
# Challenge-seam discharge of the distributional run-factoring residual

The syntactic residual `Prover.appendRunRightResidual` is **false** at a challenge seam: the appended
prover samples the seam `getChallenge` *before* consuming `P₁.output`
(`Prover.append_continueFromTo_seam_start_challenge_split`), whereas the factored form `P₁.run ≫
P₂.run` runs `P₁.output` *first* (`P₂` only begins after `P₁`).  Those are different free-monad
trees.  They are, however, equal **as distributions**, because the seam `getChallenge` is a uniform
sample independent of the `oSpec` computation `P₁.output`, and `SPMF` is commutative
(`OracleComp.evalDist_bind_comm`).

This section discharges the *distributional* residual `Prover.appendRunRightDistResidual` for the
challenge seam (`pSpec₂.dir 0 = .V_to_P`), the analogue of the message-seam discharge
`Prover.appendRunRightDistResidual_holds_msg` above. The single genuinely
distributional step is one application of `evalDist_bind_comm` swapping the seam `getChallenge` with
`P₁.output`; everything else reuses the proven syntactic challenge-seam machinery
(`append_continueFromTo_seam_start_challenge_split`, `append_continueFromTo_right_interior`,
`processRound_zero_continueFromTo_eq_runToRound_last`, the transcript/state reconciliation lemmas)
under `congrArg evalDist`.

Combined with `append_run_evalDist`, this yields `append_run_evalDist_challenge`: the appended run
factors (distributionally) as `P₁.run ≫ P₂.run` for a challenge-first `P₂` — the inter-phase Spartan
composition case where a phase opens with a verifier challenge.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- **Distributional msg-shaping of the challenge seam start.**  The appended prover's seam-round
continuation at a *challenge* seam — which samples the seam `getChallenge` *before* replaying
`P₁.output` (`append_continueFromTo_seam_start_challenge_split`) — has the same `evalDist` as the
canonical "message-shaped" boundary that runs `P₁.output` *first* and then `P₂.processRound 0`
(itself a `getChallenge`/`receiveChallenge` for a `V_to_P` round 0).  The reorder is the lone
distributional step, discharged by `OracleComp.evalDist_bind_comm`.  This is the challenge analogue
of `append_continueFromTo_seam_start_message_processRound`, stated at `evalDist`. -/
theorem append_continueFromTo_seam_start_challenge_evalDist
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    evalDist (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      = evalDist
        ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctxIn₂ =>
        (liftM
          (P₂.processRound (⟨0, hn⟩ : Fin n)
            (pure
              ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ ×
              P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) >>= fun p =>
        (pure
          (Transcript.appendRight T₁ p.1,
            cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))) := by
  -- Step 1: rewrite the LHS seam continuation to the proven challenge-first split form.
  rw [eq_of_heq (append_continueFromTo_seam_start_challenge_split
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT)]
  -- Step 2: on the RHS, fold `liftM (P₂.processRound 0 …) >>= pure(appendRight, cast)` into the
  -- challenge-first inner shape (`getChallenge >>= receiveChallenge >>= pure`) via the proven
  -- syntactic `liftComp_processRound_zero_challenge_appendRight` (after `liftComp = liftM`).
  conv_rhs =>
    enter [1, 2, ctxIn₂]
    rw [show (liftM (P₂.processRound (⟨0, hn⟩ : Fin n)
              (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = OracleComp.liftComp (P₂.processRound (⟨0, hn⟩ : Fin n)
              (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂)))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) from
          (OracleComp.liftComp_eq_liftM _).symm]
    rw [liftComp_processRound_zero_challenge_appendRight
      (P₁ := P₁) (P₂ := P₂) hn hDir₂ T₁ ctxIn₂]
  -- Now both sides are `... >>= getChallenge >>= P₁.output …` vs `getChallenge >>= P₁.output …`
  -- differing only in the order of the outer `getChallenge` and `liftComp (P₁.output)` binds.  The
  -- statement's `liftM (P₁.output)` (composed instance) is `liftComp (P₁.output) (full spec)` via
  -- `liftM_via_leftChallenge_eq_liftComp`; normalize the RHS bound to that so both sides share the
  -- exact `liftComp (P₁.output) (full spec)` term, then commute distributionally.
  rw [liftM_via_leftChallenge_eq_liftComp
    (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    (X := P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2))]
  exact (OracleComp.evalDist_bind_comm
    (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩))
    (OracleComp.liftComp (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2))
      (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂))
    (fun challenge ctxIn₂ =>
      OracleComp.liftComp
        (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun f =>
      (pure
        (Transcript.appendRight T₁
            (Transcript.concat challenge
              (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
          cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm
            (f challenge)))))

/-- **Interior fold from the msg-shaped seam boundary (direction-agnostic, syntactic).**  Binding the
msg-shaped seam boundary `B = P₁.output >>= P₂.processRound 0 >>= pure(appendRight, cast)` with the
appended interior continuation `continueFromTo ⟨m+1⟩ last` collapses (heterogeneously) to `P₁.output`
threaded into `P₂.runToRound (last n)`, transported via `appendRight`.  This is exactly the
post-seam-start portion of `append_continueFromTo_right_msg`'s proof, which never inspects the seam
direction (it only uses the *shape* of `B`); factoring it lets the challenge branch reuse the same
fold after the `evalDist`-level seam-start commute. -/
theorem append_right_block_from_seam_boundary_heq (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq
      (((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctxIn₂ =>
        (liftM
          (P₂.processRound (⟨0, hn⟩ : Fin n)
            (pure
              ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ ×
              P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) >>= fun p =>
        (pure
          (Transcript.appendRight T₁ p.1,
            cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))
        >>= (P₁.append P₂).continueFromTo stmt wit (⟨m, by omega⟩ : Fin (m + n)).succ
              (Fin.last (m + n)))
      ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
        ((fun p => (Transcript.appendRight T₁ p.1,
            cast (append_PrvState_last (P₁ := P₁) (P₂ := P₂) hn).symm p.2)) <$>
          liftComp (P₂.runToRound (Fin.last n) ctx.1 ctx.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
              × (P₁.append P₂).PrvState (Fin.last (m + n))))) := by
  simp only [bind_assoc, pure_bind]
  refine bind_heq_congr rfl rfl HEq.rfl (fun ctx ctx' hc => ?_)
  obtain rfl := eq_of_heq hc
  obtain ⟨c1, c2⟩ := ctx
  rw [← processRound_zero_continueFromTo_eq_runToRound_last hn P₂ c1 c2,
    OracleComp.liftComp_bind, map_bind, ← OracleComp.liftComp_eq_liftM]
  refine bind_heq_congr rfl rfl HEq.rfl (fun p p' hp => ?_)
  obtain rfl := eq_of_heq hp
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    have hL : (Fin.last (m + 1) : Fin (m + 1 + 1)) = (⟨m, by omega⟩ : Fin (m + 1)).succ := by
      apply Fin.ext; simp [Fin.val_last, Fin.val_succ]
    refine HEq.trans (continueFromTo_heq_target hL (P₁.append P₂) stmt wit _) ?_
    rw [continueFromTo_self]
    have hRHS : (P₂.continueFromTo c1 c2 (⟨0, hn⟩ : Fin 1).succ (Fin.last 1) p
        : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _) = pure p :=
      continueFromTo_self _ _ _ _ _
    rw [hRHS]
    rfl
  · have hint := append_continueFromTo_right_interior (P₁ := P₁) (P₂ := P₂)
      (stmt := stmt) (wit := wit) (stmt₂ := c1) (wit₂ := c2)
      T₁ (⟨1, hge⟩ : Fin n) (by simp only [Fin.val_mk]; omega) (n - 1)
      (by simp only [Fin.val_mk]; omega) p
    rw [bind_pure_comp] at hint
    have eL : (Fin.last (m + n) : Fin (m + n + 1))
        = ⟨m + ((⟨1, hge⟩ : Fin n).val + (n - 1)), by simp only [Fin.val_mk]; omega⟩ := by
      apply Fin.ext; simp only [Fin.val_last, Fin.val_mk]; omega
    refine HEq.trans (continueFromTo_heq_target eL (P₁.append P₂) stmt wit
      (Transcript.appendRight T₁ p.1, cast (append_PrvState_seam_succ hn).symm p.2)) ?_
    refine HEq.trans hint ?_
    have eR : (⟨(⟨1, hge⟩ : Fin n).val + (n - 1), by simp only [Fin.val_mk]; omega⟩ : Fin (n + 1))
        = Fin.last n := by apply Fin.ext; simp only [Fin.val_last, Fin.val_mk]; omega
    have eRapp : (⟨m + ((⟨1, hge⟩ : Fin n).val + (n - 1)), by simp only [Fin.val_mk]; omega⟩
        : Fin (m + n + 1)) = Fin.last (m + n) := by
      apply Fin.ext; simp only [Fin.val_last, Fin.val_mk]; omega
    congr 1
    · rw [eR]
    · rw [eRapp]
    · have happ : ∀ {j₁ j₂ : Fin (n + 1)} (hj : j₁ = j₂) {u : pSpec₂.Transcript j₁}
          {u' : pSpec₂.Transcript j₂}, HEq u u' →
          HEq (Transcript.appendRight T₁ u) (Transcript.appendRight T₁ u') := by
        intro j₁ j₂ hj u u' hu; subst hj; rw [eq_of_heq hu]
      refine Function.hfunext (by rw [eR]) fun a a' ha => ?_
      obtain ⟨t, s⟩ := a
      obtain ⟨t', s'⟩ := a'
      obtain ⟨ht, hs⟩ := prod_heq_split (by rw [eR]) (by rw [eR]) ha
      exact prodMk_heq (by rw [eRapp]) (by rw [eRapp]) (happ eR ht)
        ((cast_heq _ _).trans (hs.trans (cast_heq _ _).symm))
    · exact liftComp_continueFromTo_heq_target eR P₂ c1 c2 p

/-- **Right-block run characterization at a challenge seam, distributional.**  The `evalDist`-level
analogue of `append_continueFromTo_right_msg`: the appended prover's continuation over the whole
right block (seam round `⟨m⟩` to the last round) has the same distribution as `P₁`'s output threaded
into `P₂`'s full run-to-round, transported into the appended transcript via `appendRight`.  The
genuine distributional content is the seam `getChallenge`/`P₁.output` reorder, isolated in
`append_continueFromTo_seam_start_challenge_evalDist`; the rest mirrors `append_continueFromTo_right_msg`
under `congrArg evalDist`. -/
theorem append_continueFromTo_right_challenge_evalDist
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 = Transcript.appendRight T₁
      (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    evalDist (Prover.continueFromTo (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (Fin.last (m + n)) rSeam)
      = evalDist
        ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
          ((fun p => (Transcript.appendRight T₁ p.1,
              cast (append_PrvState_last (P₁ := P₁) (P₂ := P₂) hn).symm p.2)) <$>
            liftComp (P₂.runToRound (Fin.last n) ctx.1 ctx.2)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
                × (P₁.append P₂).PrvState (Fin.last (m + n))))) := by
  -- Split the right block at the seam successor `⟨m+1⟩` (`continueFromTo_trans`), then rewrite the
  -- seam factor via the `evalDist`-level seam start; the interior/output assembly is the proven,
  -- direction-agnostic `append_right_block_from_seam_boundary_heq`.
  rw [continueFromTo_trans (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
    (⟨m, by omega⟩ : Fin (m + n)).succ (Fin.last (m + n))
    (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    (by rw [Fin.le_def, Fin.val_succ, Fin.val_last]; omega) rSeam]
  -- Push `evalDist` through the seam/interior bind, swap the seam factor for the msg-shaped boundary
  -- `B` (the one distributional step), then re-fuse the bind and fold via the syntactic helper.
  rw [evalDist_bind,
    append_continueFromTo_seam_start_challenge_evalDist stmt wit hn hDir hDir₂ T₁ rSeam hT,
    ← evalDist_bind]
  exact congrArg evalDist (eq_of_heq
    (append_right_block_from_seam_boundary_heq stmt wit hn T₁ rSeam))

/-- **Challenge-seam discharge of the distributional residual.**  When the seam round (`pSpec₂`'s
round 0) is a verifier challenge, the *distributional* residual `appendRunRightDistResidual` holds.
The analogue of `appendRunRightDistResidual_holds_msg`; the syntactic `appendRunRightResidual` is
*false* here, so this genuinely needs `evalDist_bind_comm` (inside
`append_continueFromTo_right_challenge_evalDist`). -/
theorem appendRunRightDistResidual_holds_challenge
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
    appendRunRightDistResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  unfold appendRunRightDistResidual
  rw [bind_assoc]
  rw [show (⟨m, by omega⟩ : Fin (m + n + 1))
      = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp]
  -- After `bind_assoc` the seam-split LHS is `runToRound ⟨m⟩.castSucc >>= fun rSeam =>
  --   continueFromTo ⟨m⟩.castSucc last rSeam >>= K`.  Replace, *per seam value* and at the
  -- `evalDist` level, the inner right-block continuation by its msg-shaped form (one bind commute
  -- each, via `append_continueFromTo_right_challenge_evalDist`).  This rewrites the appended LHS into
  -- the exact shape the message discharge produces.
  conv_lhs =>
    rw [evalDist_bind]
    enter [2, rSeam]
    rw [evalDist_bind,
      append_continueFromTo_right_challenge_evalDist stmt wit hn hDir hDir₂
        (cast (append_Transcript_seam_castSucc hn) rSeam.1) rSeam
        (seam_transcript_appendRight hn rSeam.1),
      ← evalDist_bind]
  rw [← evalDist_bind]
  -- The appended LHS is now the message-discharge LHS; close by `congrArg evalDist` of the same
  -- syntactic factoring used by `appendRunRightResidual_holds_msg`.
  refine congrArg evalDist ?_
  apply eq_of_heq
  have hseam : HEq ((P₁.append P₂).runToRound (⟨m, by omega⟩ : Fin (m + n)).castSucc stmt wit)
      (liftM (P₁.runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
    have := append_runToRound_seam (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit)
    rwa [show ((Fin.last m).castLE (by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  simp only [run_eq_runToRound_last, liftM_bind, bind_assoc, liftM_pure, pure_bind,
    bind_map_left]
  refine bind_heq_congr
    (by rw [append_Transcript_seam_castSucc hn, append_PrvState_seam_castSucc hn]; rfl) rfl
    hseam (fun rSeam x hr => ?_)
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_seam_castSucc hn)
    (append_PrvState_seam_castSucc hn) hr
  have hc2 : cast (append_PrvState_seam_castSucc hn) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  have hc1 : cast (append_Transcript_seam_castSucc hn) rSeam.1 = x.1 :=
    eq_of_heq ((cast_heq _ _).trans ht)
  rw [hc2, hc1]
  apply heq_of_eq
  simp only [OracleComp.liftComp_eq_liftM, append_output_last hn, Transcript.appendRight_full,
    cast_cast, cast_eq]
  refine bind_congr fun x_1 => bind_congr fun a => ?_
  simp only [← OracleComp.liftComp_eq_liftM]
  rw [Prover.liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]

/-- **Sequential-composition run-factoring at `evalDist`, for a challenge-first `P₂`.**  Combines the
conditional `append_run_evalDist` with the challenge-seam discharge
`appendRunRightDistResidual_holds_challenge`.  This is the distribution-level keystone for inter-phase
Spartan composition where a phase opens with a verifier challenge. -/
theorem append_run_evalDist_challenge
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
      evalDist ((P₁.append P₂).run stmt wit)
        = evalDist ((do
          let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
          let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
          return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)) :=
  append_run_evalDist stmt wit (appendRunRightDistResidual_holds_challenge stmt wit hn hDir hDir₂)

/-- **Seam-agnostic discharge of the distributional run-factoring residual.** Total case split:
empty trailing protocol (the syntactic residual holds, `appendRunRightResidual_holds_empty`,
and `evalDist` is `congrArg`), message seam (`appendRunRightDistResidual_holds_msg`), or
challenge seam (`appendRunRightDistResidual_holds_challenge`). With this, the named
distributional residual holds for *every* pair of provers — the syntactic
`appendRunRightResidual` remains genuinely FALSE at challenge seams (see the challenge
discharge's docstring), so the distributional form is the honest live statement. -/
theorem appendRunRightDistResidual_holds
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) :
    appendRunRightDistResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact congrArg evalDist (appendRunRightResidual_holds_empty (P₁ := P₁) (P₂ := P₂) stmt wit)
  · have hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
        = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
      rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from by ext; simp,
        Prover.append_dir_natAdd]
    cases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with
    | V_to_P => exact appendRunRightDistResidual_holds_challenge stmt wit hn (hDir.trans hd) hd
    | P_to_V => exact appendRunRightDistResidual_holds_msg stmt wit hn (hDir.trans hd) hd

end Prover


-- Axiom audit (seam-agnostic total): only [propext, Classical.choice, Quot.sound].
#print axioms Prover.appendRunRightDistResidual_holds

end

section


/-!
# Verifier-fusion building blocks for the sequential-composition keystone

The oracle-level append perfect-completeness keystone reduces (see
`OracleReduction.verifier_append_eq_iff_verify`) to showing, per input/transcript, that the appended
oracle-verifier's `toVerifier.verify` — one `simulateQ` over the joint `simOracle2` running
`OracleVerifier.Append.verify` (a `router₁`/`router₂`-routed two-stage run) — equals the two-stage
composite `V₂.toVerifier ∘ V₁.toVerifier`. With the universal-fold fusion law
`simulateQ_simulateQ`, that collapses to two per-router handler equalities
`(fun q => simulateQ S (routerᵢ q)) = simOracle2 …`.

This section proves the **first** of those (`router₁_handler_eq`) outright, together with the per-query
routing facts it rests on: simulating the `emitMessageQuery` / `emitOStmtQuery{Inl}` routers through
`simOracle2` yields the corresponding in-the-clear oracle answer. The message case uses the
transcript seam-split `ProtocolSpec.messages_inl`.
-/

open OracleComp OracleSpec ProtocolSpec OracleVerifier.Append

namespace OracleVerifier.Append

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]

/-- Simulating `emitMessageQuery` through `simOracle2` yields the message answer: `subst` the type
and instance equalities, after which the emitted query is answered directly by `simOracle2`'s
message half. -/
lemma simulateQ_emitMessageQuery
    {T₁ : Type} (O₁ : OracleInterface T₁)
    (j : (pSpec₁ ++ₚ pSpec₂).MessageIdx)
    (hMsg : (pSpec₁ ++ₚ pSpec₂).Message j = T₁)
    (hO : O₁ = cast (congrArg OracleInterface hMsg)
      (instOracleInterfaceMessageAppend j))
    (q : O₁.Query)
    (oStmt : ∀ i, OStmt₁ i) (msgs : ∀ j, (pSpec₁ ++ₚ pSpec₂).Message j) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        (emitMessageQuery (oSpec := oSpec) (OStmt₁ := OStmt₁) O₁ j hMsg hO q)
      = (pure (O₁.answer (hMsg ▸ msgs j) q) : OracleComp oSpec _) := by
  subst hMsg
  subst hO
  simp only [emitMessageQuery, simulateQ_spec_query, OracleInterface.simOracle2,
    OracleInterface.simOracle0, QueryImpl.add, QueryImpl.addLift, QueryImpl.liftTarget,
    QueryImpl.id]
  rfl

/-- Simulating `emitOStmtQueryInl` through `simOracle2` yields the `OStmt₁`-answer (the query is
routed straight into `[OStmt₁]ₒ` at index `k`). -/
lemma simulateQ_emitOStmtQueryInl
    {T : Type} (O : OracleInterface T) (k : ιₛ₁) (hSt : OStmt₁ k = T)
    (hO : O = cast (congrArg OracleInterface hSt) (Oₛ₁ k)) (q : O.Query)
    (oStmt : ∀ i, OStmt₁ i) (msgs : ∀ j, (pSpec₁ ++ₚ pSpec₂).Message j) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        (emitOStmtQueryInl (oSpec := oSpec) (pSpec₂ := pSpec₂) O k hSt hO q)
      = (pure (O.answer (hSt ▸ oStmt k) q) : OracleComp oSpec _) := by
  subst hSt
  subst hO
  simp only [emitOStmtQueryInl, simulateQ_spec_query, OracleInterface.simOracle2,
    OracleInterface.simOracle0, QueryImpl.add, QueryImpl.addLift, QueryImpl.liftTarget,
    QueryImpl.id]
  rfl

/-- **router₁ handler equality.** Routing `V₁`'s queries via `router₁` and answering through the
joint-transcript `simOracle2` (which knows the appended messages) equals answering directly through
the first-half `simOracle2`. The `oSpec` and `[OStmt₁]ₒ` cases are passthrough; the message case
routes to `MessageIdx.inl` and is reconciled by the seam-split `ProtocolSpec.messages_inl`. -/
theorem router₁_handler_eq (oStmt : ∀ i, OStmt₁ i)
    (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) :
    (fun q => simulateQ (OracleInterface.simOracle2 oSpec oStmt T.messages)
        (router₁ (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₂ := pSpec₂) q))
      = OracleInterface.simOracle2 oSpec oStmt T.fst.messages := by
  funext q
  rcases q with t | t
  · simp [router₁, OracleInterface.simOracle2]
  · rcases t with t | ⟨i, qq⟩
    · simp [router₁, OracleInterface.simOracle2, QueryImpl.add]
    · change simulateQ _ (emitMessageInl i qq) = _
      rw [emitMessageInl, simulateQ_emitMessageQuery]
      simp only [OracleInterface.simOracle2, OracleInterface.simOracle0, QueryImpl.add,
        QueryImpl.addLift, QueryImpl.liftTarget, QueryImpl.id]
      congr 1

end OracleVerifier.Append

end

section


/-!
# Verifier-fusion bedrock: `simulateQ` of the V₂-side oracle-statement router

This section supplies the per-query obligation at the heart of the oracle-level append
perfect-completeness keystone: simulating the appended verifier's `emitOStmt₂Query` (which routes a
query to one of `V₁`'s output oracle statements `OStmt₂ i`) under the combined `simOracle2` answers
exactly from the reconstructed oracle statement `mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst i`.

The single subtlety is that `emitOStmt₂Query` is *tactic-built* (`by cases h : V₁.embed i …`), so a
naive `split` does not fire on its elaborated `Sum.casesOn`; the proof must mirror the definition with
`cases h : V₁.embed i`, then discharge each branch via the proven per-query simulators
(`emitOStmtQueryInl_simulateQ` / `emitOStmtQueryInr_simulateQ`) and the `mkVerifierOStmtOut`
characterizations, with the residual dependent casts collapsed by `eq_of_heq` over `eqRec_heq`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleVerifier.Append

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {Stmt₁ Stmt₂ : Type}

/-- **The V₂-side per-query routing simulates to the reconstructed oracle statement.** -/
theorem simulateQ_emitOStmt₂Query_core
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [coh : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (oStmt : ∀ i, OStmt₁ i) (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂))
    (i : ιₛ₂) (q : (Oₛ₂ i).Query) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages) (emitOStmt₂Query V₁ i q)
      = pure ((Oₛ₂ i).answer (mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst i) q) :=
  -- The `cases h : V₁.embed i` route fails (`generalize` on the tactic-built `Sum.casesOn` motive);
  -- delegate to the `split`-based proof in `Append.lean`.
  simulateQ_emitOStmt₂Query V₁ oStmt tr i q

end OracleVerifier.Append

end
