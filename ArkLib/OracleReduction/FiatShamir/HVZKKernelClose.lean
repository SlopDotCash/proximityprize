/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKKernelInfra

/-!
# Closing the basic Fiat-Shamir HVZK coupling (#116)

Proves `Reduction.canonicalFSPerStateEagerCoupling` — the last residual of the basic
Fiat-Shamir HVZK transfer — and welds it through the existing canonical reductions, so the
perfect-HVZK transfer `fiatShamir_hvzkTransferResidual_canonical_proved` holds unconditionally
for the canonical lazy-random-oracle implementation.

The proof: explicit per-round runs (`fsRun`/`intRun`/`fsDerive`), a dependent-Fin prefix layer
(take/derive commutation, so the verifier re-reads exactly the prover's keys), per-round run
characterizations, the analytic step `vstep_core` (swap the table past `receiveChallenge` via
`evalDist_bind_comm`, then backward dependent marginalization at the round's fresh key), the
per-round `Fin.induction` invariant with an update-invariant continuation, and the capstone
OptionT flattening of `fiatShamirHonestExecution`/`Reduction.run`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace Reduction

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]

/-- The table-derived partial transcript at the full length of the bundle. -/
noncomputable def fsDerive
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (stmt : StmtIn) (j : Fin (n + 1)) (msgs : pSpec.MessagesUpTo j) :
    pSpec.Transcript j :=
  derivedTranscriptAux g stmt j msgs (Fin.last j.val)

/-- Explicit FS-side per-round run: statement stripped, challenges read deterministically from
the table `g`, `oSpec` queries routed through `impl`. -/
noncomputable def fsRun (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (st0 : P.PrvState 0) (a : σ) (j : Fin (n + 1)) :
    ProbComp ((pSpec.MessagesUpTo j × P.PrvState j) × σ) :=
  Fin.induction (motive := fun j => ProbComp ((pSpec.MessagesUpTo j × P.PrvState j) × σ))
    (pure ((default, st0), a))
    (fun i ih => ih >>= fun r =>
      match hDir : pSpec.dir i with
      | .V_to_P => (simulateQ impl (P.receiveChallenge ⟨i, hDir⟩ r.1.2)).run r.2 >>= fun f =>
          pure ((r.1.1.extend hDir, f.1 (g ⟨⟨i, hDir⟩, (stmt, r.1.1)⟩)), f.2)
      | .P_to_V => (simulateQ impl (P.sendMessage ⟨i, hDir⟩ r.1.2)).run r.2 >>= fun ms =>
          pure ((r.1.1.concat hDir ms.1.1, ms.1.2), ms.2))
    j

/-- Explicit interactive per-round run: challenges drawn fresh-uniform, `oSpec` queries routed
through `impl`. -/
noncomputable def intRun (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (st0 : P.PrvState 0) (a : σ) (j : Fin (n + 1)) :
    ProbComp ((pSpec.Transcript j × P.PrvState j) × σ) :=
  Fin.induction (motive := fun j => ProbComp ((pSpec.Transcript j × P.PrvState j) × σ))
    (pure ((default, st0), a))
    (fun i ih => ih >>= fun r =>
      match hDir : pSpec.dir i with
      | .V_to_P => ($ᵗ (pSpec.Challenge ⟨i, hDir⟩)) >>= fun ch =>
          (simulateQ impl (P.receiveChallenge ⟨i, hDir⟩ r.1.2)).run r.2 >>= fun f =>
          pure ((r.1.1.concat ch, f.1 ch), f.2)
      | .P_to_V => (simulateQ impl (P.sendMessage ⟨i, hDir⟩ r.1.2)).run r.2 >>= fun ms =>
          pure ((r.1.1.concat ms.1.1, ms.1.2), ms.2))
    j

section RunEquations

variable (impl : QueryImpl oSpec (StateT σ ProbComp))
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)
  (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
    (fsChallengeOracle StmtIn pSpec).Range q)
  (st0 : P.PrvState 0) (a : σ)

@[simp] theorem fsRun_zero : fsRun impl P stmt g st0 a 0 = pure ((default, st0), a) := rfl

@[simp] theorem intRun_zero : intRun impl P st0 a 0 = pure ((default, st0), a) := rfl

theorem fsRun_succ_PtoV (j : Fin n) (hj : pSpec.dir j = .P_to_V) :
    fsRun impl P stmt g st0 a j.succ
      = fsRun impl P stmt g st0 a j.castSucc >>= fun r =>
          (simulateQ impl (P.sendMessage ⟨j, hj⟩ r.1.2)).run r.2 >>= fun ms =>
          pure ((r.1.1.concat hj ms.1.1, ms.1.2), ms.2) := by
  unfold fsRun
  rw [Fin.induction_succ]
  congr 1
  funext r
  split
  · next hDir => exact absurd (hDir.symm.trans hj) (by simp)
  · next => rfl

theorem fsRun_succ_VtoP (j : Fin n) (hj : pSpec.dir j = .V_to_P) :
    fsRun impl P stmt g st0 a j.succ
      = fsRun impl P stmt g st0 a j.castSucc >>= fun r =>
          (simulateQ impl (P.receiveChallenge ⟨j, hj⟩ r.1.2)).run r.2 >>= fun f =>
          pure ((r.1.1.extend hj, f.1 (g ⟨⟨j, hj⟩, (stmt, r.1.1)⟩)), f.2) := by
  unfold fsRun
  rw [Fin.induction_succ]
  congr 1
  funext r
  split
  · next => rfl
  · next hDir => exact absurd (hDir.symm.trans hj) (by simp)

theorem intRun_succ_PtoV (j : Fin n) (hj : pSpec.dir j = .P_to_V) :
    intRun impl P st0 a j.succ
      = intRun impl P st0 a j.castSucc >>= fun r =>
          (simulateQ impl (P.sendMessage ⟨j, hj⟩ r.1.2)).run r.2 >>= fun ms =>
          pure ((r.1.1.concat ms.1.1, ms.1.2), ms.2) := by
  unfold intRun
  rw [Fin.induction_succ]
  congr 1
  funext r
  split
  · next hDir => exact absurd (hDir.symm.trans hj) (by simp)
  · next => rfl

theorem intRun_succ_VtoP (j : Fin n) (hj : pSpec.dir j = .V_to_P) :
    intRun impl P st0 a j.succ
      = intRun impl P st0 a j.castSucc >>= fun r =>
          ($ᵗ (pSpec.Challenge ⟨j, hj⟩)) >>= fun ch =>
          (simulateQ impl (P.receiveChallenge ⟨j, hj⟩ r.1.2)).run r.2 >>= fun f =>
          pure ((r.1.1.concat ch, f.1 ch), f.2) := by
  unfold intRun
  rw [Fin.induction_succ]
  congr 1
  funext r
  split
  · next => rfl
  · next hDir => exact absurd (hDir.symm.trans hj) (by simp)

end RunEquations

/-! ## Take-prefix lemmas (generalizing `take_extend_self`/`take_concat_self`) -/

section TakeLemmas

/-- General prefix form of `take_extend_self`: any proper-prefix `take` of an extended bundle is
the corresponding `take` of the original bundle. -/
theorem take_extend_of_le {k : Fin n}
    (m : pSpec.MessagesUpTo k.castSucc) (h : pSpec.dir k = .V_to_P)
    (j : Fin (k.val + 1)) :
    (m.extend h).take (Fin.castLE (by simp only [Fin.val_succ]; omega) j) = m.take j := by
  funext idx
  obtain ⟨i, hi⟩ := idx
  simp only [MessagesUpTo.take, MessagesUpTo.extend, MessagesUpTo.concat']
  exact congrFun (Fin.dconcat_castSucc
    (motive := fun x : Fin (k.val + 1) =>
      pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
        pSpec.«Type» (Fin.castLE (by omega) x))
    (fun i hi => m ⟨i, hi⟩) _ ⟨i.val, by simp only [Fin.val_castLE] at hi ⊢; omega⟩) _

/-- General prefix form of `take_concat_self`. -/
theorem take_concat_of_le {k : Fin n}
    (m : pSpec.MessagesUpTo k.castSucc) (h : pSpec.dir k = .P_to_V)
    (msg : pSpec.Message ⟨k, h⟩) (j : Fin (k.val + 1)) :
    (m.concat h msg).take (Fin.castLE (by simp only [Fin.val_succ]; omega) j) = m.take j := by
  funext idx
  obtain ⟨i, hi⟩ := idx
  simp only [MessagesUpTo.take, MessagesUpTo.concat, MessagesUpTo.concat']
  exact congrFun (Fin.dconcat_castSucc
    (motive := fun x : Fin (k.val + 1) =>
      pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
        pSpec.«Type» (Fin.castLE (by omega) x))
    (fun i hi => m ⟨i, hi⟩) _ ⟨i.val, by simp only [Fin.val_castLE] at hi ⊢; omega⟩) _

/-- `take` at the full length is the identity. -/
theorem take_last_self {K : Fin (n + 1)} (m : pSpec.MessagesUpTo K) :
    m.take (Fin.last K.val) = m := rfl

/-- `take` one step further across a challenge round is `extend` of the shorter `take`. -/
theorem take_succ_extend {K : Fin (n + 1)} (m : pSpec.MessagesUpTo K) (i : Fin K.val)
    (hd : pSpec.dir (⟨i.val, by omega⟩ : Fin n) = .V_to_P) :
    m.take i.succ
      = MessagesUpTo.extend (k := ⟨i.val, by omega⟩) (m.take i.castSucc) hd := by
  funext idx
  obtain ⟨i', hi'⟩ := idx
  induction i' using Fin.lastCases with
  | last => exact absurd (hd.symm.trans hi') (by simp)
  | cast k' =>
    simp only [MessagesUpTo.take, MessagesUpTo.extend, MessagesUpTo.concat']
    exact (congrFun (Fin.dconcat_castSucc
      (motive := fun x : Fin (i.val + 1) =>
        pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
          pSpec.«Type» (Fin.castLE (by omega) x))
      (fun x hx => m ⟨Fin.castLE (by omega) x, hx⟩) _ k') _).symm

/-- `take` one step further across a message round is `concat` of the shorter `take`. -/
theorem take_succ_concat {K : Fin (n + 1)} (m : pSpec.MessagesUpTo K) (i : Fin K.val)
    (hd : pSpec.dir (⟨i.val, by omega⟩ : Fin n) = .P_to_V) :
    m.take i.succ
      = MessagesUpTo.concat (k := ⟨i.val, by omega⟩) (m.take i.castSucc) hd
          (m ⟨⟨i.val, by omega⟩, hd⟩) := by
  funext idx
  obtain ⟨i', hi'⟩ := idx
  induction i' using Fin.lastCases with
  | last =>
    simp only [MessagesUpTo.take, MessagesUpTo.concat, MessagesUpTo.concat']
    exact (congrFun (Fin.dconcat_last
      (motive := fun x : Fin (i.val + 1) =>
        pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
          pSpec.«Type» (Fin.castLE (by omega) x))
      (fun x hx => m ⟨Fin.castLE (by omega) x, hx⟩)
      (fun _ => m ⟨⟨i.val, by omega⟩, hd⟩)) _).symm
  | cast k' =>
    simp only [MessagesUpTo.take, MessagesUpTo.concat, MessagesUpTo.concat']
    exact (congrFun (Fin.dconcat_castSucc
      (motive := fun x : Fin (i.val + 1) =>
        pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
          pSpec.«Type» (Fin.castLE (by omega) x))
      (fun x hx => m ⟨Fin.castLE (by omega) x, hx⟩) _ k') _).symm

end TakeLemmas

/-! ## Derived-transcript step lemmas -/

section DeriveLemmas

variable (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
    (fsChallengeOracle StmtIn pSpec).Range q) (stmt : StmtIn)

/-- Unfolding of `derivedTranscriptAux` at a successor index. -/
theorem derivedTranscriptAux_succ (K : Fin (n + 1)) (M : pSpec.MessagesUpTo K)
    (i : Fin K.val) :
    derivedTranscriptAux g stmt K M i.succ
      = (match hDir : pSpec.dir (i.castLE (by omega)) with
        | .V_to_P => (derivedTranscriptAux g stmt K M i.castSucc).concat
            (g ⟨⟨i.castLE (by omega), hDir⟩, (stmt, M.take i.castSucc)⟩)
        | .P_to_V => (derivedTranscriptAux g stmt K M i.castSucc).concat (M ⟨i, hDir⟩)) := by
  unfold derivedTranscriptAux
  rw [Fin.induction_succ]
  rfl

/-- Prefix stability of the derived transcript under `extend` across a challenge round
(ℕ-valued index form). -/
theorem derivedTranscriptAux_extend_stab {k : Fin n} (h : pSpec.dir k = .V_to_P)
    (msgs : pSpec.MessagesUpTo k.castSucc) (v : ℕ) (hv : v ≤ k.val) :
    derivedTranscriptAux g stmt k.succ (msgs.extend h)
        (⟨v, by omega⟩ : Fin (k.val + 1 + 1))
      = derivedTranscriptAux g stmt k.castSucc msgs
          (⟨v, by omega⟩ : Fin (k.val + 1)) := by
  induction v with
  | zero => rfl
  | succ v ihv =>
    have hvk : v ≤ k.val := by omega
    show derivedTranscriptAux g stmt k.succ (msgs.extend h)
        (Fin.succ (⟨v, by omega⟩ : Fin (k.val + 1)))
      = derivedTranscriptAux g stmt k.castSucc msgs
          (Fin.succ (⟨v, by omega⟩ : Fin k.val))
    rw [derivedTranscriptAux_succ, derivedTranscriptAux_succ]
    have hT : derivedTranscriptAux g stmt k.succ (msgs.extend h)
          (Fin.castSucc (⟨v, by omega⟩ : Fin (k.val + 1)))
        = derivedTranscriptAux g stmt k.castSucc msgs
            (Fin.castSucc (⟨v, by omega⟩ : Fin k.val)) := ihv hvk
    have htake : (msgs.extend h).take
          (Fin.castSucc (⟨v, by omega⟩ : Fin (k.val + 1)))
        = msgs.take (Fin.castSucc (⟨v, by omega⟩ : Fin k.val)) :=
      take_extend_of_le msgs h ⟨v, by omega⟩
    split
    · next hDir =>
      split
      · next hDir' => rw [hT, htake]; rfl
      · next hDir' => exact absurd (hDir.symm.trans hDir') (by simp)
    · next hDir =>
      split
      · next hDir' => exact absurd (hDir.symm.trans hDir') (by simp)
      · next hDir' =>
        have hval : (msgs.extend h)
              ⟨(⟨v, by omega⟩ : Fin (k.val + 1)), hDir⟩
            = msgs ⟨(⟨v, by omega⟩ : Fin k.val), hDir'⟩ :=
          congrFun (Fin.dconcat_castSucc
            (motive := fun x : Fin (k.val + 1) =>
              pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
                pSpec.«Type» (Fin.castLE (by omega) x))
            (fun x hx => msgs ⟨x, hx⟩) _ ⟨v, by omega⟩) hDir
        rw [hT, hval]; rfl

/-- Prefix stability of the derived transcript under `concat` across a message round
(ℕ-valued index form). -/
theorem derivedTranscriptAux_concat_stab {k : Fin n} (h : pSpec.dir k = .P_to_V)
    (msgs : pSpec.MessagesUpTo k.castSucc) (msg : pSpec.Message ⟨k, h⟩)
    (v : ℕ) (hv : v ≤ k.val) :
    derivedTranscriptAux g stmt k.succ (msgs.concat h msg)
        (⟨v, by omega⟩ : Fin (k.val + 1 + 1))
      = derivedTranscriptAux g stmt k.castSucc msgs
          (⟨v, by omega⟩ : Fin (k.val + 1)) := by
  induction v with
  | zero => rfl
  | succ v ihv =>
    have hvk : v ≤ k.val := by omega
    show derivedTranscriptAux g stmt k.succ (msgs.concat h msg)
        (Fin.succ (⟨v, by omega⟩ : Fin (k.val + 1)))
      = derivedTranscriptAux g stmt k.castSucc msgs
          (Fin.succ (⟨v, by omega⟩ : Fin k.val))
    rw [derivedTranscriptAux_succ, derivedTranscriptAux_succ]
    have hT : derivedTranscriptAux g stmt k.succ (msgs.concat h msg)
          (Fin.castSucc (⟨v, by omega⟩ : Fin (k.val + 1)))
        = derivedTranscriptAux g stmt k.castSucc msgs
            (Fin.castSucc (⟨v, by omega⟩ : Fin k.val)) := ihv hvk
    have htake : (msgs.concat h msg).take
          (Fin.castSucc (⟨v, by omega⟩ : Fin (k.val + 1)))
        = msgs.take (Fin.castSucc (⟨v, by omega⟩ : Fin k.val)) :=
      take_concat_of_le msgs h msg ⟨v, by omega⟩
    split
    · next hDir =>
      split
      · next hDir' => rw [hT, htake]; rfl
      · next hDir' => exact absurd (hDir.symm.trans hDir') (by simp)
    · next hDir =>
      split
      · next hDir' => exact absurd (hDir.symm.trans hDir') (by simp)
      · next hDir' =>
        have hval : (msgs.concat h msg)
              ⟨(⟨v, by omega⟩ : Fin (k.val + 1)), hDir⟩
            = msgs ⟨(⟨v, by omega⟩ : Fin k.val), hDir'⟩ :=
          congrFun (Fin.dconcat_castSucc
            (motive := fun x : Fin (k.val + 1) =>
              pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
                pSpec.«Type» (Fin.castLE (by omega) x))
            (fun x hx => msgs ⟨x, hx⟩) _ ⟨v, by omega⟩) hDir
        rw [hT, hval]; rfl

/-- **C2.** The table-derived transcript of an `extend`ed bundle is the table-derived transcript
of the original bundle extended by the table read at the prover's round key. -/
theorem fsDerive_extend {k : Fin n} (h : pSpec.dir k = .V_to_P)
    (msgs : pSpec.MessagesUpTo k.castSucc) :
    fsDerive g stmt k.succ (msgs.extend h)
      = Transcript.concat (g ⟨⟨k, h⟩, (stmt, msgs)⟩) (fsDerive g stmt k.castSucc msgs) := by
  show derivedTranscriptAux g stmt k.succ (msgs.extend h)
      (Fin.succ (⟨k.val, by omega⟩ : Fin (k.val + 1))) = _
  rw [derivedTranscriptAux_succ]
  split
  · next hDir =>
    have hT : derivedTranscriptAux g stmt k.succ (msgs.extend h)
          (Fin.castSucc (⟨k.val, by omega⟩ : Fin (k.val + 1)))
        = fsDerive g stmt k.castSucc msgs :=
      derivedTranscriptAux_extend_stab g stmt h msgs k.val le_rfl
    have htake : (msgs.extend h).take
          (Fin.castSucc (⟨k.val, by omega⟩ : Fin (k.val + 1))) = msgs :=
      MessagesUpTo.take_extend_self msgs h
    rw [hT, htake]
    rfl
  · next hDir => exact absurd (h.symm.trans hDir) (by simp)

/-- **C1.** The table-derived transcript of a `concat`ed bundle is the table-derived transcript
of the original bundle extended by the new message. -/
theorem fsDerive_concat {k : Fin n} (h : pSpec.dir k = .P_to_V)
    (msgs : pSpec.MessagesUpTo k.castSucc) (msg : pSpec.Message ⟨k, h⟩) :
    fsDerive g stmt k.succ (msgs.concat h msg)
      = Transcript.concat msg (fsDerive g stmt k.castSucc msgs) := by
  show derivedTranscriptAux g stmt k.succ (msgs.concat h msg)
      (Fin.succ (⟨k.val, by omega⟩ : Fin (k.val + 1))) = _
  rw [derivedTranscriptAux_succ]
  split
  · next hDir => exact absurd (h.symm.trans hDir) (by simp)
  · next hDir =>
    have hT : derivedTranscriptAux g stmt k.succ (msgs.concat h msg)
          (Fin.castSucc (⟨k.val, by omega⟩ : Fin (k.val + 1)))
        = fsDerive g stmt k.castSucc msgs :=
      derivedTranscriptAux_concat_stab g stmt h msgs msg k.val le_rfl
    have hlast : (msgs.concat h msg)
          ⟨(⟨k.val, by omega⟩ : Fin (k.val + 1)), hDir⟩ = msg :=
      congrFun (Fin.dconcat_last
        (motive := fun x : Fin (k.val + 1) =>
          pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
            pSpec.«Type» (Fin.castLE (by omega) x))
        (fun x hx => msgs ⟨x, hx⟩) (fun _ => msg)) hDir
    rw [hT, hlast]
    rfl

/-- **D (aux).** The message bundle of the table-derived partial transcript is the `take` of the
original bundle. -/
theorem toMessagesUpTo_derivedTranscriptAux (K : Fin (n + 1)) (M : pSpec.MessagesUpTo K)
    (v : ℕ) (hv : v ≤ K.val) :
    (derivedTranscriptAux g stmt K M (⟨v, by omega⟩ : Fin (K.val + 1))).toMessagesUpTo
      = M.take (⟨v, by omega⟩ : Fin (K.val + 1)) := by
  induction v with
  | zero =>
    funext idx
    obtain ⟨i, hi⟩ := idx
    exact i.elim0
  | succ v ihv =>
    have hvk : v ≤ K.val := by omega
    show (derivedTranscriptAux g stmt K M
        (Fin.succ (⟨v, by omega⟩ : Fin K.val))).toMessagesUpTo = _
    rw [derivedTranscriptAux_succ]
    split
    · next hDir =>
      have hd : pSpec.dir (⟨v, by omega⟩ : Fin n) = .V_to_P := hDir
      refine Eq.trans (ProtocolSpec.toMessagesUpTo_extend (m := ⟨v, by omega⟩) hd _ _) ?_
      refine Eq.trans (congrArg
        (fun X => MessagesUpTo.extend (k := ⟨v, by omega⟩) X hd) (ihv hvk)) ?_
      exact (take_succ_extend M ⟨v, by omega⟩ hd).symm
    · next hDir =>
      have hd : pSpec.dir (⟨v, by omega⟩ : Fin n) = .P_to_V := hDir
      refine Eq.trans (ProtocolSpec.toMessagesUpTo_concat (m := ⟨v, by omega⟩) hd _ _) ?_
      refine Eq.trans (congrArg
        (fun X => MessagesUpTo.concat (k := ⟨v, by omega⟩) X hd
          (M ⟨⟨v, by omega⟩, hd⟩)) (ihv hvk)) ?_
      exact (take_succ_concat M ⟨v, by omega⟩ hd).symm

/-- **D.** The message bundle of the table-derived transcript is the original bundle. -/
theorem toMessagesUpTo_fsDerive (K : Fin (n + 1)) (M : pSpec.MessagesUpTo K) :
    (fsDerive g stmt K M).toMessagesUpTo = M :=
  toMessagesUpTo_derivedTranscriptAux g stmt K M K.val le_rfl

end DeriveLemmas

/-! ## Routing helpers and run characterizations -/

section RunChar

variable (impl : QueryImpl oSpec (StateT σ ProbComp))
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
  (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
    (fsChallengeOracle StmtIn pSpec).Range q)

/-- Routing: an `oSpec` computation lifted into the FS sum spec simulates through the left
implementation. -/
theorem simulateQ_add_fsTableImpl_liftM {α : Type} (oa : OracleComp oSpec α) :
    simulateQ (impl + fsTableImpl (σ := σ) g)
        (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α)
      = simulateQ impl oa := by
  rw [← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left]

/-- Routing: an `oSpec` computation lifted into the interactive sum spec simulates through the
left implementation. -/
theorem simulateQ_addLift_cqi_liftM {α : Type} (oa : OracleComp oSpec α) :
    simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
      = simulateQ impl oa :=
  simulateQ_addLift_liftM impl oa

/-- The lifted interactive `getChallenge` is the lifted sum-spec query. -/
theorem liftM_getChallenge_eq (i : pSpec.ChallengeIdx) :
    (liftM (pSpec.getChallenge i) : OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i))
      = liftM ((oSpec + [pSpec.Challenge]ₒ).query (Sum.inr ⟨i, ()⟩)) := rfl

/-- A fresh interactive challenge through the combined implementation, in run form. -/
theorem simulateQ_addLift_cqi_getChallenge_run (i : pSpec.ChallengeIdx) (a : σ) :
    (simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (liftM (pSpec.getChallenge i))).run a
      = ($ᵗ (pSpec.Challenge i)) >>= fun u => pure (u, a) := by
  rw [liftM_getChallenge_eq]
  erw [simulateQ_spec_query]
  exact addLift_challengeQueryImpl_run_inr impl ⟨i, ()⟩ a

/-- `processRoundFS` on a `V_to_P` round: receive-challenge closure, then the Fiat-Shamir
challenge query at the in-flight key. -/
theorem processRoundFS_of_VtoP (j : Fin n) (hj : pSpec.dir j = .V_to_P)
    (cur : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × P.PrvState j.castSucc)) :
    P.processRoundFS j cur =
      (do
        let x ← cur
        let f ← liftM (P.receiveChallenge ⟨j, hj⟩ x.2.2)
        let challenge ← query (spec := fsChallengeOracle StmtIn pSpec)
          (m := OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) ⟨⟨j, hj⟩, (x.2.1, x.1)⟩
        return (x.1.extend hj, x.2.1, f challenge)) := by
  unfold Prover.processRoundFS
  congr 1
  funext x
  obtain ⟨messages, stmtIn, state⟩ := x
  dsimp only
  split
  · next => rfl
  · next hd => exact Direction.noConfusion (hd.symm.trans hj)

/-- **B-FS.** The simulated Fiat-Shamir prover run is the explicit `fsRun` chain (with the
constant statement re-attached). -/
theorem simulateQ_fsTable_runToRoundFS (j : Fin (n + 1)) (a : σ) :
    (simulateQ (impl + fsTableImpl (σ := σ) g)
        (P.runToRoundFS j stmt (P.input (stmt, wit)))).run a
      = fsRun impl P stmt g (P.input (stmt, wit)) a j >>= fun r =>
          pure ((r.1.1, stmt, r.1.2), r.2) := by
  induction j using Fin.induction generalizing a with
  | zero =>
    rw [show P.runToRoundFS 0 stmt (P.input (stmt, wit))
        = (pure (default, stmt, P.input (stmt, wit))
          : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) _) from rfl]
    rw [simulateQ_pure, fsRun_zero, pure_bind]
    rfl
  | succ i ih =>
    have hstep : P.runToRoundFS i.succ stmt (P.input (stmt, wit))
        = P.processRoundFS i (P.runToRoundFS i.castSucc stmt (P.input (stmt, wit))) := by
      simp only [Prover.runToRoundFS, Fin.induction_succ]
    rw [hstep]
    rcases hdir : pSpec.dir i with _ | _
    · -- P_to_V
      rw [processRoundFS_of_PtoV P i hdir]
      rw [simulateQ_bind, StateT.run_bind]
      rw [ih a]
      rw [fsRun_succ_PtoV impl P stmt g _ a i hdir]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      rw [simulateQ_bind, StateT.run_bind, simulateQ_add_fsTableImpl_liftM]
      try simp only [bind_assoc, pure_bind]
      refine bind_congr fun ms => ?_
      obtain ⟨⟨msg, st'⟩, a''⟩ := ms
      rw [simulateQ_pure]
      rfl
    · -- V_to_P
      rw [processRoundFS_of_VtoP P i hdir]
      rw [simulateQ_bind, StateT.run_bind]
      rw [ih a]
      rw [fsRun_succ_VtoP impl P stmt g _ a i hdir]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      rw [simulateQ_bind, StateT.run_bind, simulateQ_add_fsTableImpl_liftM]
      try simp only [bind_assoc, pure_bind]
      refine bind_congr fun f => ?_
      rw [simulateQ_bind, StateT.run_bind, simulateQ_add_fsTableImpl_query_run]
      simp only [pure_bind]
      rw [simulateQ_pure]
      rfl

/-- **B-Int.** The simulated interactive prover run is the explicit `intRun` chain. -/
theorem simulateQ_addLift_runToRound (j : Fin (n + 1)) (a : σ) :
    (simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (P.runToRound j stmt wit)).run a
      = intRun impl P (P.input (stmt, wit)) a j := by
  induction j using Fin.induction generalizing a with
  | zero =>
    rw [show P.runToRound 0 stmt wit
        = (pure (default, P.input (stmt, wit))
          : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) from rfl]
    rw [simulateQ_pure, intRun_zero]
    rfl
  | succ i ih =>
    rw [Prover.run_succ]
    rcases hdir : pSpec.dir i with _ | _
    · -- P_to_V
      rw [Prover.processRound_P_to_V i hdir]
      rw [simulateQ_bind, StateT.run_bind]
      rw [ih a]
      rw [intRun_succ_PtoV impl P _ a i hdir]
      refine bind_congr fun r => ?_
      rw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_cqi_liftM]
      refine bind_congr fun ms => ?_
      obtain ⟨⟨msg, st'⟩, a''⟩ := ms
      rw [simulateQ_pure]
      rfl
    · -- V_to_P
      rw [Prover.processRound_V_to_P i hdir]
      rw [simulateQ_bind, StateT.run_bind]
      rw [ih a]
      rw [intRun_succ_VtoP impl P _ a i hdir]
      refine bind_congr fun r => ?_
      rw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_cqi_getChallenge_run]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ch => ?_
      rw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_cqi_liftM]
      try simp only [bind_assoc, pure_bind]
      refine bind_congr fun f => ?_
      rw [simulateQ_pure]
      rfl

end RunChar

/-! ## The V_to_P analytic core: swap, marginalize the fresh-key table read, swap back -/

section VStepCore

variable (impl : QueryImpl oSpec (StateT σ ProbComp))
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)

/-- **Per-round marginalization.** With the previous-round data fixed, the round-`i` table read
(at the fresh round-`i` key) averaged over the uniform table is a fresh uniform challenge draw,
and the receive-challenge step commutes across it. -/
theorem vstep_core (i : Fin n) (hdir : pSpec.dir i = .V_to_P) {β : Type}
    (Φ : ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q) →
      pSpec.Transcript i.succ → P.PrvState i.succ → σ → ProbComp β)
    (hΦ : ∀ (t : (fsChallengeOracle StmtIn pSpec).Domain)
      (u : (fsChallengeOracle StmtIn pSpec).Range t)
      (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q)
      (T : pSpec.Transcript i.succ) (st : P.PrvState i.succ) (a' : σ),
      (t.1.1.val : ℕ) < (i.succ).val → Φ (Function.update g t u) T st a' = Φ g T st a')
    (T : pSpec.Transcript i.castSucc) (st : P.PrvState i.castSucc) (a' : σ) :
    𝒟[do
      let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q)
      let f ← (simulateQ impl (P.receiveChallenge ⟨i, hdir⟩ st)).run a'
      Φ g (Transcript.concat (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩) T)
        (f.1 (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩)) f.2]
    = 𝒟[do
        let ch ← $ᵗ (pSpec.Challenge ⟨i, hdir⟩)
        let f ← (simulateQ impl (P.receiveChallenge ⟨i, hdir⟩ st)).run a'
        let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
          (fsChallengeOracle StmtIn pSpec).Range q)
        Φ g (Transcript.concat ch T) (f.1 ch) f.2] := by
  classical
  haveI : Nonempty ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := ⟨fun q => Classical.arbitrary _⟩
  -- step 1: swap the table sample past the receive-challenge step
  refine Eq.trans (OracleComp.evalDist_bind_comm _ _
    (fun g (f : (pSpec.Challenge ⟨i, hdir⟩ → P.PrvState i.succ) × σ) =>
      Φ g (Transcript.concat (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩) T)
        (f.1 (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩)) f.2)) ?_
  -- step 2: per receive-challenge outcome, marginalize the round-i table read
  refine Eq.trans ?_ ((OracleComp.evalDist_bind_comm
    ($ᵗ (pSpec.Challenge ⟨i, hdir⟩)) _
    (fun ch (f : (pSpec.Challenge ⟨i, hdir⟩ → P.PrvState i.succ) × σ) => (do
      let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q)
      Φ g (Transcript.concat ch T) (f.1 ch) f.2))).symm)
  rw [evalDist_bind, evalDist_bind]
  refine congrArg _ (funext fun f => ?_)
  refine Eq.trans (evalDist_uniformSample_bind_update_bind_dep
    (ι' := (fsChallengeOracle StmtIn pSpec).Domain)
    (R := (fsChallengeOracle StmtIn pSpec).Range)
    (⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩ : (fsChallengeOracle StmtIn pSpec).Domain)
    (fun g => Φ g (Transcript.concat (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩) T)
      (f.1 (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩)) f.2)).symm ?_
  refine congrArg evalDist (bind_congr fun u => bind_congr fun g => ?_)
  rw [Function.update_self]
  exact hΦ _ u g _ _ _ (Nat.lt_succ_self i.val)

end VStepCore

/-! ## The per-round eager coupling invariant -/

section Invariant

variable (impl : QueryImpl oSpec (StateT σ ProbComp))
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)

set_option maxHeartbeats 4000000 in
/-- **Per-round eager coupling invariant.** For any continuation `Φ` reading the table only at
rounds `≥ j`, the table-averaged FS run (with its derived transcript) agrees with the
interactive run (with the table sampled independently afterwards). -/
theorem eager_coupling_invariant (a : σ) (j : Fin (n + 1)) {β : Type}
    (Φ : ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q) →
      pSpec.Transcript j → P.PrvState j → σ → ProbComp β)
    (hΦ : ∀ (t : (fsChallengeOracle StmtIn pSpec).Domain)
      (u : (fsChallengeOracle StmtIn pSpec).Range t)
      (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q)
      (T : pSpec.Transcript j) (st : P.PrvState j) (a' : σ),
      (t.1.1.val : ℕ) < j.val → Φ (Function.update g t u) T st a' = Φ g T st a') :
    𝒟[do
      let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q)
      let r ← fsRun impl P stmt g (P.input (stmt, wit)) a j
      Φ g (fsDerive g stmt j r.1.1) r.1.2 r.2]
    = 𝒟[do
        let r ← intRun impl P (P.input (stmt, wit)) a j
        let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
          (fsChallengeOracle StmtIn pSpec).Range q)
        Φ g r.1.1 r.1.2 r.2] := by
  induction j using Fin.induction with
  | zero =>
    simp only [fsRun_zero, intRun_zero, pure_bind]
    refine congrArg evalDist (bind_congr fun g => ?_)
    congr 1
  | succ i ih =>
    rcases hdir : pSpec.dir i with _ | _
    · -- P_to_V round
      have h1 : (do
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            let r ← fsRun impl P stmt g (P.input (stmt, wit)) a i.succ
            Φ g (fsDerive g stmt i.succ r.1.1) r.1.2 r.2)
          = (do
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            let r ← fsRun impl P stmt g (P.input (stmt, wit)) a i.castSucc
            let ms ← (simulateQ impl (P.sendMessage ⟨i, hdir⟩ r.1.2)).run r.2
            Φ g (Transcript.concat ms.1.1 (fsDerive g stmt i.castSucc r.1.1))
              ms.1.2 ms.2) := by
        refine bind_congr fun g => ?_
        rw [fsRun_succ_PtoV impl P stmt g _ a i hdir]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun r => bind_congr fun ms => ?_
        rw [fsDerive_concat g stmt hdir r.1.1 ms.1.1]
      rw [h1]
      refine Eq.trans (ih (fun g T st a' =>
          (simulateQ impl (P.sendMessage ⟨i, hdir⟩ st)).run a' >>= fun ms =>
            Φ g (Transcript.concat ms.1.1 T) ms.1.2 ms.2)
        (fun t u g T st a' hlt => bind_congr fun ms =>
          hΦ t u g _ _ _ (by
            simp only [Fin.val_castSucc] at hlt
            simp only [Fin.val_succ]
            omega))) ?_
      have h2 : (do
            let r ← intRun impl P (P.input (stmt, wit)) a i.succ
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            Φ g r.1.1 r.1.2 r.2)
          = (do
            let r ← intRun impl P (P.input (stmt, wit)) a i.castSucc
            let ms ← (simulateQ impl (P.sendMessage ⟨i, hdir⟩ r.1.2)).run r.2
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            Φ g (Transcript.concat ms.1.1 r.1.1) ms.1.2 ms.2) := by
        rw [intRun_succ_PtoV impl P _ a i hdir]
        simp only [bind_assoc, pure_bind]
      rw [h2]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg _ (funext fun r => ?_)
      exact OracleComp.evalDist_bind_comm _ _ (fun g
        (ms : (pSpec.Message ⟨i, hdir⟩ × P.PrvState i.succ) × σ) =>
          Φ g (Transcript.concat ms.1.1 r.1.1) ms.1.2 ms.2)
    · -- V_to_P round
      have h1 : (do
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            let r ← fsRun impl P stmt g (P.input (stmt, wit)) a i.succ
            Φ g (fsDerive g stmt i.succ r.1.1) r.1.2 r.2)
          = (do
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            let r ← fsRun impl P stmt g (P.input (stmt, wit)) a i.castSucc
            let f ← (simulateQ impl (P.receiveChallenge ⟨i, hdir⟩ r.1.2)).run r.2
            Φ g (Transcript.concat
                (g ⟨⟨i, hdir⟩, (stmt,
                  (fsDerive g stmt i.castSucc r.1.1).toMessagesUpTo)⟩)
                (fsDerive g stmt i.castSucc r.1.1))
              (f.1 (g ⟨⟨i, hdir⟩, (stmt,
                  (fsDerive g stmt i.castSucc r.1.1).toMessagesUpTo)⟩)) f.2) := by
        refine bind_congr fun g => ?_
        rw [fsRun_succ_VtoP impl P stmt g _ a i hdir]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun r => bind_congr fun f => ?_
        rw [fsDerive_extend g stmt hdir r.1.1]
        have hgk : (g ⟨⟨i, hdir⟩, (stmt,
              (fsDerive g stmt i.castSucc r.1.1).toMessagesUpTo)⟩
              : pSpec.Challenge ⟨i, hdir⟩)
            = g ⟨⟨i, hdir⟩, (stmt, r.1.1)⟩ :=
          @congrArg (pSpec.MessagesUpTo i.castSucc) (pSpec.Challenge ⟨i, hdir⟩)
            ((fsDerive g stmt i.castSucc r.1.1).toMessagesUpTo) (r.1.1)
            (fun M => g ⟨⟨i, hdir⟩, (stmt, M)⟩)
            (toMessagesUpTo_fsDerive g stmt i.castSucc r.1.1)
        rw [← hgk]
      rw [h1]
      refine Eq.trans (ih (fun g T st a' =>
          (simulateQ impl (P.receiveChallenge ⟨i, hdir⟩ st)).run a' >>= fun f =>
            Φ g (Transcript.concat (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩) T)
              (f.1 (g ⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩)) f.2)
        (fun t u g T st a' hlt => by
          have hne : (⟨⟨i, hdir⟩, (stmt, T.toMessagesUpTo)⟩
              : (fsChallengeOracle StmtIn pSpec).Domain) ≠ t := by
            intro hEq
            exact (fsKey_ne_of_round_lt (i := t.1) (j := ⟨i, hdir⟩)
              (by simpa using hlt) t.2 (stmt, T.toMessagesUpTo))
              (by rw [hEq])
          refine bind_congr fun f => ?_
          rw [Function.update_of_ne hne]
          exact hΦ t u g _ _ _ (by
            simp only [Fin.val_castSucc] at hlt
            simp only [Fin.val_succ]
            omega))) ?_
      have h2 : (do
            let r ← intRun impl P (P.input (stmt, wit)) a i.succ
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            Φ g r.1.1 r.1.2 r.2)
          = (do
            let r ← intRun impl P (P.input (stmt, wit)) a i.castSucc
            let ch ← $ᵗ (pSpec.Challenge ⟨i, hdir⟩)
            let f ← (simulateQ impl (P.receiveChallenge ⟨i, hdir⟩ r.1.2)).run r.2
            let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
              (fsChallengeOracle StmtIn pSpec).Range q)
            Φ g (Transcript.concat ch r.1.1) (f.1 ch) f.2) := by
        rw [intRun_succ_VtoP impl P _ a i hdir]
        simp only [bind_assoc, pure_bind]
      rw [h2]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg _ (funext fun r => ?_)
      exact vstep_core impl P stmt i hdir Φ hΦ r.1.1 r.1.2 r.2

end Invariant

/-! ## OptionT-run flattening of the two honest executions -/

section RunFlatten

set_option linter.unusedSimpArgs false

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)

/-- `OptionT.run` of the same-spec lift. -/
theorem optRun_liftM_inner {ι' : Type} {spec' : OracleSpec ι'} {α : Type}
    (x : OracleComp spec' α) :
    (liftM x : OptionT (OracleComp spec') α).run = x >>= fun a => pure (some a) := rfl

/-- `OptionT.run` of the cross-spec composite lift. -/
theorem optRun_liftM_cross {ι₂ : Type} {spec₂ : OracleSpec ι₂} {α : Type}
    (x : OracleComp oSpec α) :
    (liftM x : OptionT (OracleComp (oSpec + spec₂)) α).run
      = (x.liftComp (oSpec + spec₂)) >>= fun a => pure (some a) := by
  have h : (liftM x : OptionT (OracleComp (oSpec + spec₂)) α).run
      = simulateQ (fun t => (liftM (oSpec.query t)
          : OracleComp (oSpec + spec₂) _))
        (x >>= fun a => pure (some a)) := rfl
  rw [h, simulateQ_bind, OracleComp.liftComp_def]
  simp only [simulateQ_pure]

/-- `OptionT.run` of a mapped `Option.getM`. -/
theorem optRun_map_getM {ι' : Type} {spec' : OracleSpec ι'} {α β : Type}
    (o : Option α) (f : α → β) :
    ((f <$> (o.getM : OptionT (OracleComp spec') α)).run)
      = pure (Option.map f o) := by
  cases o <;> rfl

/-- `Prover.run` as an explicit chain. -/
theorem prover_run_eq (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    P.run stmt wit
      = P.runToRound (Fin.last n) stmt wit >>= fun x =>
        (liftM (P.output x.2) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) >>= fun c =>
        pure (x.1, c) := rfl

/-- **FS honest execution, flattened.** -/
theorem honestExecution_run_eq :
    (R.fiatShamirHonestExecution stmt wit).run
      = (R.prover.runToRoundFS (Fin.last n) stmt (R.prover.input (stmt, wit))) >>= fun x =>
        ((R.prover.output x.2.2).liftComp (oSpec + fsChallengeOracle StmtIn pSpec)) >>=
          fun ctxOut =>
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmt x.1) >>= fun transcript =>
        ((R.verifier.verify stmt transcript).run.liftComp
          (oSpec + fsChallengeOracle StmtIn pSpec)) >>= fun o =>
        pure (Option.map (fun s =>
          ((((fun y => match y with
            | ⟨0, _⟩ => x.1) : FiatShamirProofTranscript (pSpec := pSpec)), ctxOut), s)) o) := by
  unfold Reduction.fiatShamirHonestExecution Verifier.fiatShamir
  simp only [Verifier.run, OptionT.run_bind, Option.elimM,
    optRun_liftM_inner, optRun_liftM_cross, optRun_map_getM,
    bind_assoc, pure_bind, Option.elim_some, map_bind, bind_pure_comp, bind_map_left]
  rfl

/-- **Interactive run, flattened.** -/
theorem reduction_run_eq :
    (R.run stmt wit).run
      = R.prover.runToRound (Fin.last n) stmt wit >>= fun x =>
        (liftM (R.prover.output x.2) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) >>= fun c =>
        ((R.verifier.verify stmt x.1).run.liftComp (oSpec + [pSpec.Challenge]ₒ)) >>= fun o =>
        pure (Option.map (fun s => ((x.1, c), s)) o) := by
  unfold Reduction.run
  simp only [Verifier.run, OptionT.run_bind, Option.elimM,
    optRun_liftM_inner, optRun_liftM_cross, optRun_map_getM,
    bind_assoc, pure_bind, Option.elim_some, map_bind, bind_pure_comp, bind_map_left,
    prover_run_eq]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  erw [bind_map_left]
  rfl

end RunFlatten

/-! ## Simulated capstone chains -/

section CapChains

variable (impl : QueryImpl oSpec (StateT σ ProbComp))
  (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
  (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
    (fsChallengeOracle StmtIn pSpec).Range q)

/-- The one-message Fiat-Shamir proof determined by a message bundle. -/
def mkFSProof (M : pSpec.MessagesUpTo (Fin.last n)) :
    FiatShamirProofTranscript (pSpec := pSpec) :=
  fun y => match y with | ⟨0, _⟩ => M

/-- Routing: a `liftComp`ed `oSpec` computation through the interactive combined
implementation. -/
theorem simulateQ_addLift_cqi_liftComp {α : Type} (x : OracleComp oSpec α) :
    simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (x.liftComp (oSpec + [pSpec.Challenge]ₒ))
      = simulateQ impl x := by
  rw [OracleComp.liftComp_eq_liftM]
  exact simulateQ_addLift_liftM impl x

/-- **B-Cap-FS.** The simulated FS honest execution is the `fsRun` chain followed by the
prover output, the verifier on the table-derived transcript, and the assembled marginal. -/
theorem simulateQ_fsTable_honest_run (a : σ) :
    (simulateQ (impl + fsTableImpl (σ := σ) g)
        (R.fiatShamirHonestExecution stmt wit).run).run a
      = fsRun impl R.prover stmt g (R.prover.input (stmt, wit)) a (Fin.last n) >>= fun r =>
        (simulateQ impl (R.prover.output r.1.2)).run r.2 >>= fun po =>
        (simulateQ impl (R.verifier.verify stmt
            (fsDerive g stmt (Fin.last n) r.1.1)).run).run po.2 >>= fun vo =>
        pure ((Option.map (fun s => ((mkFSProof r.1.1, po.1), s)) vo.1), vo.2) := by
  rw [honestExecution_run_eq]
  rw [simulateQ_bind, StateT.run_bind,
    simulateQ_fsTable_runToRoundFS impl R.prover stmt wit g (Fin.last n) a]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_liftComp_left]
  refine bind_congr fun po => ?_
  rw [simulateQ_bind, StateT.run_bind, simulateQ_add_fsTableImpl_deriveTranscriptFS_run]
  erw [pure_bind]
  rw [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_liftComp_left]
  refine bind_congr fun vo => ?_
  rw [simulateQ_pure]
  rfl

/-- **B-Cap-Int.** The simulated interactive run is the `intRun` chain followed by the prover
output, the verifier on the interactive transcript, and the assembled marginal. -/
theorem simulateQ_addLift_reduction_run (a : σ) :
    (simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (R.run stmt wit).run).run a
      = intRun impl R.prover (R.prover.input (stmt, wit)) a (Fin.last n) >>= fun r =>
        (simulateQ impl (R.prover.output r.1.2)).run r.2 >>= fun po =>
        (simulateQ impl (R.verifier.verify stmt r.1.1).run).run po.2 >>= fun vo =>
        pure ((Option.map (fun s => ((r.1.1, po.1), s)) vo.1), vo.2) := by
  rw [reduction_run_eq]
  erw [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_addLift_runToRound impl R.prover stmt wit (Fin.last n) a]
  refine bind_congr fun r => ?_
  erw [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_addLift_cqi_liftM]
  refine bind_congr fun po => ?_
  erw [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_addLift_cqi_liftComp]
  refine bind_congr fun vo => ?_
  erw [simulateQ_pure]
  rfl

end CapChains

/-! ## Marginal massage to the invariant shape -/

section Marginal

variable (impl : QueryImpl oSpec (StateT σ ProbComp))
  (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)

/-- Commute an output map past `StateT.run'`. -/
theorem stateT_run'_map' {σ' α β : Type} (f : α → β) (M : StateT σ' ProbComp α) (s : σ') :
    (f <$> M).run' s = f <$> M.run' s := by
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- Binding a fresh uniform table and ignoring it is distribution-preserving. -/
theorem evalDist_table_bind_const {β : Type} (k : ProbComp β) :
    𝒟[($ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q)) >>= fun _ => k] = 𝒟[k] := by
  classical
  haveI : Nonempty ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := ⟨fun q => Classical.arbitrary _⟩
  refine evalDist_ext fun z => ?_
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
    tsum_probOutput_eq_one' (by simp), one_mul]

/-- **hL.** The FS side of the eager coupling, in invariant shape. -/
theorem fs_marginal_eq (a : σ) :
    (Option.map (fun r : (FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
          StmtOut => r.1.1) <$>
        (do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          (simulateQ (impl + fsTableImpl (σ := σ) g)
            (R.fiatShamirHonestExecution stmt wit).run).run' a))
      = (do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          let r ← fsRun impl R.prover stmt g (R.prover.input (stmt, wit)) a (Fin.last n)
          (simulateQ impl (R.prover.output r.1.2)).run r.2 >>= fun po =>
          (simulateQ impl (R.verifier.verify stmt
              (fsDerive g stmt (Fin.last n) r.1.1)).run).run po.2 >>= fun vo =>
          pure (Option.map (Function.const StmtOut
            (mkFSProof (fsDerive g stmt (Fin.last n) r.1.1).toMessagesUpTo)) vo.1)) := by
  rw [map_bind]
  refine bind_congr fun g => ?_
  rw [StateT.run'_eq, Functor.map_map]
  rw [simulateQ_fsTable_honest_run impl R stmt wit g a]
  rw [map_bind]
  refine bind_congr fun r => ?_
  rw [map_bind]
  refine bind_congr fun po => ?_
  rw [map_bind]
  refine bind_congr fun vo => ?_
  rw [map_pure]
  rw [show mkFSProof (pSpec := pSpec)
        ((fsDerive g stmt (Fin.last n) r.1.1).toMessagesUpTo) = mkFSProof r.1.1 from
    congrArg _ (toMessagesUpTo_fsDerive g stmt (Fin.last n) r.1.1)]
  obtain ⟨ovo, s'⟩ := vo
  cases ovo <;> rfl

/-- **hR.** The interactive side of the eager coupling, in invariant shape (no table). -/
theorem int_marginal_eq (a : σ) :
    (Option.map (msgProjFS (pSpec := pSpec)) <$>
        StateT.run'
          (simulateQ (impl.addLift challengeQueryImpl)
            ((Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
                result.1.1)) <$> (R.run stmt wit).run)
            : StateT σ ProbComp (Option (FullTranscript pSpec))) a)
      = (do
          let r ← intRun impl R.prover (R.prover.input (stmt, wit)) a (Fin.last n)
          (simulateQ impl (R.prover.output r.1.2)).run r.2 >>= fun po =>
          (simulateQ impl (R.verifier.verify stmt r.1.1).run).run po.2 >>= fun vo =>
          pure (Option.map (Function.const StmtOut
            (mkFSProof (Transcript.toMessagesUpTo r.1.1))) vo.1)) := by
  erw [simulateQ_map]
  rw [stateT_run'_map', Functor.map_map, StateT.run'_eq, Functor.map_map]
  rw [simulateQ_addLift_reduction_run impl R stmt wit a]
  erw [map_bind]
  refine bind_congr fun r => ?_
  erw [map_bind]
  refine bind_congr fun po => ?_
  erw [map_bind]
  refine bind_congr fun vo => ?_
  erw [map_pure]
  obtain ⟨ovo, s'⟩ := vo
  cases ovo <;> rfl

end Marginal

/-! ## The capstone: the eager coupling residual holds -/

set_option maxHeartbeats 4000000 in
/-- **`Reduction.canonicalFSPerStateEagerCoupling` holds** — the cache-free eager coupling
residual of the basic Fiat-Shamir HVZK transfer (#116). -/
theorem canonicalFSPerStateEagerCoupling_proved
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    canonicalFSPerStateEagerCoupling impl R stmt wit := by
  unfold canonicalFSPerStateEagerCoupling
  intro a
  refine Eq.trans (congrArg evalDist (fs_marginal_eq impl R stmt wit a))
    (Eq.trans ?_ (congrArg evalDist (int_marginal_eq impl R stmt wit a)).symm)
  refine Eq.trans (eager_coupling_invariant impl R.prover stmt wit a (Fin.last n)
    (fun _g T st a' =>
      (simulateQ impl (R.prover.output st)).run a' >>= fun po =>
      (simulateQ impl (R.verifier.verify stmt T).run).run po.2 >>= fun vo =>
      pure (Option.map (Function.const StmtOut
        (mkFSProof (Transcript.toMessagesUpTo T))) vo.1))
    (fun _ _ _ _ _ _ _ => rfl)) ?_
  rw [evalDist_bind, evalDist_bind]
  refine congrArg _ (funext fun r => ?_)
  exact evalDist_table_bind_const _

#print axioms canonicalFSPerStateEagerCoupling_proved

/-! ## Downstream: the per-state coupling kernel and the full HVZK transfer -/

/-- The per-`oSpec`-state lazy-vs-eager coupling kernel of #116 holds. -/
theorem canonicalFSPerStateCoupling_proved
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    canonicalFSPerStateCoupling impl R stmt wit :=
  canonicalFSPerStateCoupling_of_eagerCoupling impl R stmt wit
    (canonicalFSPerStateEagerCoupling_proved impl R stmt wit)

/-- The canonical Fiat-Shamir HVZK coupling kernel holds unconditionally. -/
theorem canonicalFSCouplingKernel_proved
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    canonicalFSCouplingKernel init impl rel R :=
  canonicalFSCouplingKernel_of_perStateCoupling init impl rel R
    (fun stmt wit _ => canonicalFSPerStateCoupling_proved impl R stmt wit)

/-- **The basic Fiat-Shamir HVZK transfer residual holds unconditionally** for the canonical
lazy random-oracle challenge implementation: perfect HVZK of `R` transfers to `R.fiatShamir`. -/
theorem fiatShamir_hvzkTransferResidual_canonical_proved
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    fiatShamir_hvzkTransferResidual init impl
      (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
      (canonicalFSImpl (StmtIn := StmtIn) impl) rel R :=
  fiatShamir_hvzkTransferResidual_canonical init impl rel R
    (canonicalFSCouplingKernel_proved init impl rel R)

#print axioms eager_coupling_invariant
#print axioms canonicalFSPerStateCoupling_proved
#print axioms canonicalFSCouplingKernel_proved
#print axioms fiatShamir_hvzkTransferResidual_canonical_proved

end Reduction
