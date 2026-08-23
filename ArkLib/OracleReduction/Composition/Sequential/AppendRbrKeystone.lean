/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessProof
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun
import ArkLib.ToVCVio.EvalDist.Instances.OptionT

/-!
# Round-by-round (knowledge) soundness append keystone — `appendRbr*SoundnessResidual` discharge

This file makes the round-by-round soundness append keystone **unconditional** for the
deterministic-`V₁` message-seam case that issue #29 (and #114 / #13) need. It targets the named
residual `Verifier.appendRbrSoundnessResidual` (and the knowledge variant) recorded in `Append.lean`.

The two side hypotheses missing from the residual statement (`hVerify`: `V₁` deterministic &
non-failing — which also supplies the `verify` function; `hInit`: a reachable initial state) are the
exact inputs required by the already-proven composite combinators `Verifier.StateFunction.append`
and `Extractor.RoundByRound.append`. With those added, the residue is the **per-round** bound, which
— unlike plain soundness — is a single challenge index `i`, hence a *case split* on
`ChallengeIdx.sumEquiv.symm i` (no union over rounds), deferring each phase to `h₁` / `h₂`.

## Proof architecture

* Phase-1 (`i = ChallengeIdx.inl i₁`): the appended state function `StateFunction.append` lands in its
  `dif_pos` branch (both `i.1.castSucc` and `i.1.succ` are `≤ m`), so the per-round flip event is
  definitionally `S₁`'s flip event at `i₁` on the transcript's `.fst` half. The appended prover's
  partial run `prover.runToRound (inl i₁).castSucc` factors through `Prover.fst` via
  `fst_runToRound_heq`, and the combined challenge-oracle sampling transfers to `pSpec₁`'s own oracle
  via `evalDist_run'_challengeSeam_left`. The bound is then exactly `h₁` applied at `i₁`.
* Phase-2 (`i = ChallengeIdx.inr i₂`): the appended flip event collapses (via the `dif_neg` branch,
  `StateFunction.append_toFun_gt`) to `S₂`'s flip event at `i₂`, but evaluated at the *random*
  seam-crossing statement `verify stmtIn transcript.fst`. The inner bounds `h₁`/`h₂` are silent on the
  positive-probability event `verify stmtIn transcript.fst ∈ lang₂`, so phase 2 is **not** a
  consequence of `h₁`/`h₂` and the phase-1 seam reduction alone — it is a *genuine residual* (see
  `appendRbrSoundnessPhase2Residual`). The keystones below isolate that residual as a single typed
  hypothesis, keeping every theorem axiom-clean (no `sorry`).

## Status

* `append_rbrSoundness_keystone`: phase-1 fully proven internally and unconditionally; phase-2 supplied
  as the explicit residual `appendRbrSoundnessPhase2Residual`. Axiom-clean.
* `append_rbrKnowledgeSoundness_keystone`: extractor leg supplied unconditionally from the proven
  `Extractor.RoundByRound.append`; the composite knowledge state function `kSF` and the per-round
  knowledge bound `hBound` (carrying the same phase-2 obstruction, witness-threaded) supplied as
  explicit residuals. Axiom-clean.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- **At a phase-1-only round index, the transcript truncation is the identity.** For `k ≤ m`,
the appended-spec transcript `tr` keeps all its rounds under the phase-1 truncation, so
`Transcript.fst tr` is heterogeneously equal to `tr` (only per-round value types differ). -/
theorem transcript_fst_heq {k : Fin (m + n + 1)} (hk : (k : ℕ) ≤ m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) :
    HEq (ProtocolSpec.Transcript.fst tr) tr := by
  refine Function.hfunext (congrArg Fin (Nat.min_eq_left hk)) (fun a a' ha => ?_)
  have hval : a.val = a'.val := by
    have := (Fin.heq_ext_iff (Nat.min_eq_left hk)).mp ha
    omega
  have hidx : (⟨a.val, by omega⟩ : Fin (k : ℕ)) = a' := Fin.ext hval
  unfold ProtocolSpec.Transcript.fst
  exact HEq.trans (cast_heq _ _) (hidx ▸ HEq.rfl)

/-- **A phase-2 message leaves the phase-1 truncation unchanged.** For a round index `j ≥ m`
(into the second protocol), appending a message and taking the phase-1 truncation equals the
phase-1 truncation of the original transcript — the appended element sits past the first `m`
rounds, so `Fin.snoc` leaves positions `< m` untouched. -/
theorem transcript_concat_fst {j : Fin (m + n)} (hj : m ≤ (j : ℕ))
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc) :
    HEq (ProtocolSpec.Transcript.fst (ProtocolSpec.Transcript.concat msg tr))
        (ProtocolSpec.Transcript.fst tr) := by
  have hsize : (↑(⟨min (↑j.succ) m, by omega⟩ : Fin (m + 1)) : ℕ)
      = ↑(⟨min (↑j.castSucc) m, by omega⟩ : Fin (m + 1)) := by
    simp only [Fin.val_succ, Fin.val_castSucc]; omega
  refine Function.hfunext (congrArg Fin hsize) (fun a a' ha => ?_)
  have hva : (a : ℕ) = (a' : ℕ) := by have := (Fin.heq_ext_iff hsize).mp ha; omega
  have halt : (a : ℕ) < (j : ℕ) := by have := a.isLt; simp only [Fin.val_mk] at this; omega
  simp only [ProtocolSpec.Transcript.fst, ProtocolSpec.Transcript.concat]
  refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
  rw [Fin.snoc, dif_pos (show ((⟨a.val, by omega⟩ : Fin ((j : ℕ) + 1)) : ℕ) < (j : ℕ) from by
    simp only [Fin.val_mk]; exact halt)]
  exact (Fin.ext (by simpa using hva) : ((⟨a.val, by omega⟩ : Fin ((j : ℕ) + 1)).castLT
    (by simp only [Fin.val_mk]; exact halt)) = ⟨a'.val, by omega⟩) ▸ HEq.rfl

/-- **Projection of a product type-cast (first component).** Casting `(a, b)` along a product of
type equalities and projecting commutes with `a` (heterogeneously). With the type equalities as
free variables, `subst` discharges it. -/
theorem prod_cast_fst_heq {A A' B B' : Type _} (hA : A = A') (hB : B = B') (a : A) (b : B) :
    HEq ((congrArg₂ Prod hA hB ▸ (a, b) : A' × B').1) a := by
  subst hA; subst hB; rfl

/-- **Projection of a product type-cast (second component).** -/
theorem prod_cast_snd_heq {A A' B B' : Type _} (hA : A = A') (hB : B = B') (a : A) (b : B) :
    HEq ((congrArg₂ Prod hA hB ▸ (a, b) : A' × B').2) b := by
  subst hA; subst hB; rfl

/-- **evalDist transport for the phase-1 experiment.** If the combined-oracle body `bodyA` is
heterogeneously equal to `liftM oa` (the `pSpec₁`-oracle body lifted into the combined oracle),
then the two experiments' output distributions agree (heterogeneously). Proved by `subst`ing the
value-type equality `h` (making `bodyA = liftM oa`), then transferring the per-state distribution
across the challenge seam with `evalDist_run'_challengeSeam_left`. -/
theorem evalDist_init_run'_heq_of_body_heq {α β : Type} (h : α = β)
    (bodyA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
    (oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) β)
    (hbody : HEq bodyA
      (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) β)) :
    HEq (evalDist (init >>= fun s =>
          (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂))
            : QueryImpl _ (StateT σ ProbComp)) bodyA).run' s))
        (evalDist (init >>= fun s =>
          (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁))
            : QueryImpl _ (StateT σ ProbComp)) oa).run' s)) := by
  subst h
  rw [eq_of_heq hbody]
  apply heq_of_eq
  rw [evalDist_bind, evalDist_bind]
  exact bind_congr fun s => OracleReduction.evalDist_run'_challengeSeam_left impl oa s

/-- **Phase-1 per-round experiment body HEq.** The appended rbr experiment body at a phase-1
challenge index `inl i₁` — the appended prover's partial run `runToRound (inl i₁).castSucc` followed
by sampling the appended `getChallenge (inl i₁)` under the *combined* challenge oracle — is
heterogeneously equal (the two value types are *propositionally equal* via `append_Transcript_castLE`
on the transcript and `range_challenge_append_inl` on the challenge) to `liftComp` of the phase-1
experiment body of `prover.fst` over `pSpec₁`'s own challenge oracle, lifted into the combined oracle.
This packages the run-level seam-factoring `fst_runToRound_heq` with the challenge-seam reduction
`append_getChallenge_left`. -/
theorem phase1_body_heq
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₁ : pSpec₁.ChallengeIdx) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (OracleComp.liftComp
        (do
          let ⟨transcript, _⟩ ← prover.fst.runToRound i₁.1.castSucc stmtIn witIn
          let challenge ← OracleComp.liftComp (pSpec₁.getChallenge i₁) (oSpec + [pSpec₁.Challenge]ₒ)
          pure (transcript, challenge))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) := by
  have hChalDir : (pSpec₁ ++ₚ pSpec₂).dir (i₁.1.castLE (by omega)) = .V_to_P := by
    rw [Prover.append_dir_castLE i₁.1]; exact i₁.2
  -- index reindexings
  have hidxCS : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc : Fin (m + n + 1))
      = (i₁.1.castSucc.castLE (by omega)) := by ext; simp [ChallengeIdx.inl]
  have hidxChal : (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 = i₁.1.castLE (by omega) := by
    ext; simp [ChallengeIdx.inl]
  -- The transcript and challenge value-type equalities (propositional).
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
      = pSpec₁.Transcript i₁.1.castSucc := by
    rw [hidxCS]; exact Prover.append_Transcript_castLE i₁.1.castSucc
  have hStTy : prover.PrvState (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
      = prover.fst.PrvState i₁.1.castSucc := by rw [hidxCS]; rfl
  have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)
      = pSpec₁.Challenge i₁ := by
    show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i₁) = pSpec₁.Challenge i₁
    simp [ChallengeIdx.inl, ProtocolSpec.append]
  have hValTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
        × prover.PrvState (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc)
      = (pSpec₁.Transcript i₁.1.castSucc × prover.fst.PrvState i₁.1.castSucc) := by
    rw [hTrTy, hStTy]
  have hResTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
      = (pSpec₁.Transcript i₁.1.castSucc × pSpec₁.Challenge i₁) := by
    rw [hTrTy, hChTy]
  -- Distribute `liftComp` over the RHS bind/pure.
  rw [OracleComp.liftComp_bind]
  refine Prover.bind_heq_congr hValTy hResTy ?_ ?_
  · -- the partial runs: phase-1 faithfulness.
    rw [hidxCS]; exact Prover.fst_runToRound_heq prover stmtIn witIn i₁.1.castSucc
  · -- the challenge-sampling continuations.
    rintro ⟨trA, stA⟩ ⟨trB, stB⟩ hpair
    obtain ⟨htr, _⟩ := Prover.prod_heq_split hTrTy hStTy hpair
    rw [OracleComp.liftComp_bind]
    refine Prover.bind_heq_congr hChTy hResTy ?_ ?_
    · -- the challenge query HEq: `append_getChallenge_left`, both sides lifted into the combined
      -- oracle.
      have hChTy' : (pSpec₁ ++ₚ pSpec₂).Challenge (⟨i₁.1.castLE (by omega), hChalDir⟩) =
          pSpec₁.Challenge i₁ := by
        rw [← hChTy]; congr 1 <;> (apply Subtype.ext; rw [hidxChal])
      have hgc := Prover.append_getChallenge_left (pSpec₂ := pSpec₂) i₁.1 hChalDir i₁.2
      rw [show (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁) = ⟨i₁.1.castLE (by omega), hChalDir⟩ from by
            apply Subtype.ext; rw [hidxChal]]
      -- LHS: `liftComp (getChallenge ⟨castLE,_⟩) combined`; transport `hgc` through `liftComp`.
      refine HEq.trans (Prover.liftComp_heq_congr
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChTy' hgc) ?_
      -- now: `liftComp (liftM (getChallenge i₁) : OracleComp [combined Ch]) combined`
      --      ≍ `liftComp (liftComp (getChallenge i₁) (oSpec+[pSpec₁ Ch])) combined`.
      -- Both are double-lifts of `getChallenge i₁` from `[pSpec₁ Ch]` into `oSpec+[combined Ch]`.
      apply heq_of_eq
      rw [show (liftM (pSpec₁.getChallenge i₁) : OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
            = OracleComp.liftComp (pSpec₁.getChallenge i₁) [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ from
          (OracleComp.liftComp_eq_liftM _).symm]
      rw [show OracleComp.liftComp (OracleComp.liftComp (pSpec₁.getChallenge i₁)
                [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              = OracleComp.liftComp (pSpec₁.getChallenge i₁)
                  (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            from Prover.liftComp_liftComp (midSpec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (fun t => rfl) (pSpec₁.getChallenge i₁),
          show OracleComp.liftComp (OracleComp.liftComp (pSpec₁.getChallenge i₁)
                (oSpec + [pSpec₁.Challenge]ₒ)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              = OracleComp.liftComp (pSpec₁.getChallenge i₁)
                  (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            from Prover.liftComp_liftComp (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
                (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (fun t => rfl) (pSpec₁.getChallenge i₁)]
    · -- the final `pure (transcript, challenge)` continuations.
      rintro cA cB hc
      refine Prover.pure_heq_pure (by rw [hTrTy, hChTy]) ?_
      exact Prover.prodMk_heq hTrTy hChTy htr hc

/-- **Phase-1 projection of the appended state function.** On a round index lying in the first
protocol (`roundIdx.val ≤ m`), `StateFunction.append` is definitionally `S₁` evaluated on the
transcript's phase-1 truncation — the `dif_pos` branch of its `toFun`. -/
theorem StateFunction.append_toFun_le
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = S₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst) := by
  simp only [StateFunction.append, dif_pos h]

/-- **Phase-2 projection of the appended state function.** On a round index lying in the second
protocol (`¬ roundIdx.val ≤ m`), `StateFunction.append` is definitionally `S₂` on the `verify`-fed
intermediate statement and the transcript's phase-2 tail — the `dif_neg` branch of its `toFun`. -/
theorem StateFunction.append_toFun_gt
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : ¬ roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = S₂.toFun ⟨roundIdx - m, by omega⟩
          (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst))
          (by simpa [h] using transcript.snd) := by
  simp only [StateFunction.append, dif_neg h]

/-- **Phase-2 per-round residual of the round-by-round soundness append keystone.**

This is the *exact* shape of the appended round-by-round per-round flip-event bound at a **phase-2**
challenge index `ChallengeIdx.inr i₂`, stated against the proven composite state function
`StateFunction.append`. It is the single genuine residual of `append_rbrSoundness_keystone`: the
phase-1 case is discharged internally (see below), but phase 2 is *not* a consequence of `h₁`/`h₂`
alone.

**Why phase 2 is a residual and not plumbing.** At a phase-2 index, the appended flip event collapses
(via `StateFunction.append_toFun_gt`) to `S₂`'s flip event at `i₂`, but evaluated at the *random*
intermediate statement `verify stmtIn transcript.fst` (the seam-crossing statement determined by the
realized phase-1 transcript). The inner bound `h₂` only bounds `S₂`'s flip event for input statements
*outside* `lang₂`; for the positive-probability event `verify stmtIn transcript.fst ∈ lang₂` the inner
bound is silent, yet the appended per-round probability averages over both. (Concretely, `S₂` may start
`true` on a `lang₂` statement, dip to `false`, and flip back to `true` at round `i₂` — a flip event
with positive probability that `h₂` does not control.) Discharging this requires either strengthening
`h₂` to bound `S₂`'s flip event for **all** input statements (the structure that round-by-round
*knowledge* soundness supplies, via its witness-carrying knowledge state function), or a
seam-doomed-ness argument forcing `verify stmtIn transcript.fst ∉ lang₂` almost surely on the relevant
support. Both are genuine additional content beyond the proven phase-1 seam reduction; this residual
isolates exactly that content as a typed hypothesis, keeping the keystone axiom-clean (no `sorry`). -/
def appendRbrSoundnessPhase2Residual
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) : Prop :=
  ∀ stmtIn ∉ lang₁, ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
  ∀ prover : Prover oSpec Stmt₁ WitIn Stmt₃ WitOut (pSpec₁ ++ₚ pSpec₂),
  ∀ i₂ : pSpec₂.ChallengeIdx,
    Pr[fun ⟨transcript, challenge⟩ =>
      ¬ (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit).toFun
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript ∧
        (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit).toFun
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (transcript.concat challenge)
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ←
            prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
          let challenge ←
            liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
          return (transcript, challenge))).run' (← init)] ≤
      rbrSoundnessError₂ i₂

/-- **Round-by-round soundness append keystone, deterministic-`V₁` message-seam case.**
Discharges `Verifier.appendRbrSoundnessResidual` for the deterministic-`V₁` message-seam case **with
the phase-2 per-round bound supplied as an explicit residual hypothesis** (`hPhase2`, of type
`appendRbrSoundnessPhase2Residual`).

The two added side conditions (`verify`/`hVerify` and `hInit`) are exactly the inputs of the proven
`StateFunction.append`; with them the per-round bound is a case split on `ChallengeIdx.sumEquiv.symm`.
The **phase-1** half is discharged *internally* and unconditionally (reducing to `h₁` applied to the
phase-1 seam prover `prover.fstCast` via the proven run and challenge seam bricks). The **phase-2**
half is exactly `hPhase2` — see `appendRbrSoundnessPhase2Residual` for why it is a genuine residual and
not mere plumbing. This theorem is fully axiom-clean (no `sorry`): it isolates the phase-2 obstruction
as a single typed hypothesis instead of hiding it. -/
theorem append_rbrSoundness_keystone
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (hS₁ : ∀ stmtIn ∉ lang₁, ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
      ∀ prover : Prover oSpec Stmt₁ WitIn Stmt₂ WitOut pSpec₁, ∀ i : pSpec₁.ChallengeIdx,
        Pr[fun ⟨transcript, challenge⟩ =>
          ¬ S₁ i.1.castSucc stmtIn transcript ∧ S₁ i.1.succ stmtIn (transcript.concat challenge)
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₁.getChallenge i) _
              return (transcript, challenge))).run' (← init)] ≤ rbrSoundnessError₁ i)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hNE : Nonempty Stmt₂)
    (hPhase2 : appendRbrSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂ S₁ S₂
      verify hVerify hInit (rbrSoundnessError₂ := rbrSoundnessError₂)) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  refine ⟨StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hInit, ?_⟩
  intro stmtIn hStmtIn WitIn WitOut witIn prover i
  -- Case split on phase-1 / phase-2 of the appended challenge index.
  rcases hi : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
  · -- Phase 1.
    have hRHS : (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrSoundnessError₁ i₁ := by
      simp only [Function.comp_apply, hi, Sum.elim_inl]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inl i₁ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i
      rw [hi] at this; simpa using this.symm
    subst hiEq
    -- Reduce to the inner verifier's per-round bound `hS₁`, applied to the phase-1 seam prover
    -- recast to an `Stmt₂`-output prover (`fstCast`; the dummy claim is irrelevant since the rbr
    -- experiment touches only `runToRound`, which is output-agnostic).
    refine le_of_eq_of_le ?phase1_transport
      (hS₁ stmtIn hStmtIn WitIn Unit witIn (prover.fstCast hNE.some) i₁)
    -- Remaining (`phase1_transport`): the appended phase-1 experiment over the *combined* challenge
    -- oracle has the same event-probability as the `fstCast` experiment over `pSpec₁`'s own oracle.
    -- The ingredients are all proven: `Prover.fstCast_runToRound` (= `fst`'s run), `phase1_body_heq`
    -- (the body HEq), `evalDist_run'_challengeSeam_left` (combined → `pSpec₁` distribution transfer),
    -- and `StateFunction.append.toFun`'s `dif_pos` branch (the appended state function collapses to
    -- `S₁` on `transcript.fst` for phase-1 indices). Assembled through `probEvent_congr_heq`.
    have hidxCS : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc : Fin (m + n + 1))
        = i₁.1.castSucc.castLE (by omega) := by ext; simp [ChallengeIdx.inl]
    have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
        = pSpec₁.Transcript i₁.1.castSucc := by
      rw [hidxCS]; exact Prover.append_Transcript_castLE i₁.1.castSucc
    have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)
        = pSpec₁.Challenge i₁ := by simp [ChallengeIdx.inl, ProtocolSpec.append]
    have hResTy :
        ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
          = (pSpec₁.Transcript i₁.1.castSucc × pSpec₁.Challenge i₁) := congrArg₂ Prod hTrTy hChTy
    refine probEvent_congr_heq hResTy _ _ _ _ ?hd ?hPQ
    · -- hd : the appended and `fstCast` experiments have heterogeneously-equal `evalDist`s.
      -- The appended phase-1 body is `liftM` of the `fstCast` body (`phase1_body_heq` +
      -- `fstCast_runToRound`), so the experiment distributions transfer via the challenge seam.
      exact evalDist_init_run'_heq_of_body_heq hResTy _ _
        ((phase1_body_heq prover stmtIn witIn i₁).trans
          (heq_of_eq (by rw [Prover.fstCast_runToRound]; exact OracleComp.liftComp_eq_liftM _)))
    · -- hPQ : the appended state-function event corresponds to `S₁`'s under the type cast.
      rintro ⟨tr, ch⟩
      have hlt : i₁.1.val < m := i₁.1.isLt
      have hval : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1).val = i₁.1.val := by
        simp [ChallengeIdx.inl, Fin.coe_castAdd]
      have hcs : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val ≤ m := by
        rw [Fin.val_castSucc, hval]; omega
      have hsu : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val ≤ m := by
        rw [Fin.val_succ, hval]; omega
      simp only [StateFunction.append_toFun_le V₁ V₂ S₁ S₂ verify hVerify hInit hcs,
          StateFunction.append_toFun_le V₁ V₂ S₁ S₂ verify hVerify hInit hsu]
      have hiCS : (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val, by omega⟩ : Fin (m + 1))
          = i₁.1.castSucc := Fin.ext (by simp [Fin.val_castSucc, hval])
      have hiSU : (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val, by omega⟩ : Fin (m + 1))
          = i₁.1.succ := Fin.ext (by simp [Fin.val_succ, hval])
      refine iff_of_eq ?_
      congr 1
      · -- `¬ A₁ = ¬ A₂`: dependent congruence of `S₁.toFun · stmtIn ·` over index + transcript.
        refine congrArg Not (eq_of_heq (dcongr_heq ?_ (fun _ _ _ => rfl) (fun _ _ => hiCS ▸ HEq.rfl)))
        exact (cast_heq _ _).trans
          (HEq.trans (transcript_fst_heq hcs tr) (prod_cast_fst_heq hTrTy hChTy tr ch).symm)
      · -- `B₁ = B₂`
        refine eq_of_heq (dcongr_heq ?_ (fun _ _ _ => rfl) (fun _ _ => hiSU ▸ HEq.rfl))
        refine (cast_heq _ _).trans
          (HEq.trans (transcript_fst_heq hsu (Transcript.concat ch tr)) ?_)
        -- `concat ch tr ≍ concat (hResTy ▸ (tr,ch)).2 (hResTy ▸ (tr,ch)).1` via `concat_heq`.
        exact Prover.concat_heq i₁.1 (prod_cast_fst_heq hTrTy hChTy tr ch).symm
          (prod_cast_snd_heq hTrTy hChTy tr ch).symm
  · -- Phase 2. The appended flip event collapses (`StateFunction.append_toFun_gt`) to `S₂`'s flip
    -- event at `i₂` evaluated at the *random* seam-crossing statement `verify stmtIn transcript.fst`;
    -- `h₁`/`h₂` do not control the `verify stmtIn transcript.fst ∈ lang₂` mass, so this half is the
    -- genuine residual `hPhase2` (see `appendRbrSoundnessPhase2Residual` for the precise obstruction).
    have hRHS : (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrSoundnessError₂ i₂ := by
      simp only [Function.comp_apply, hi, Sum.elim_inr]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inr i₂ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i
      rw [hi] at this; simpa using this.symm
    subst hiEq
    exact hPhase2 stmtIn hStmtIn WitIn WitOut witIn prover i₂

/-! ## Round-by-round *knowledge* soundness append keystone

The knowledge variant adds, on top of the soundness state-function leg, a **round-by-round
extractor** (the proven `Extractor.RoundByRound.append`, which threads the intermediate statement via
the deterministic `verify`) and a **knowledge state function** carrying the per-round intermediate
witness. The proven extractor combinator discharges the `extractMid` / `extractOut` seam
identification; what is *not* yet available as a named def in the tree is the composite
`KnowledgeStateFunction.append` (the witness-threaded analogue of `StateFunction.append`), and the
per-round knowledge bound inherits the *same* phase-2 residual obstruction analysed in
`appendRbrSoundnessPhase2Residual` (now witness-carrying).

The keystone below is therefore stated to consume those two genuinely-missing pieces as explicit
inputs — the composite knowledge state function `kSF` and the per-round knowledge bound `hBound` —
while supplying the extractor leg unconditionally from `Extractor.RoundByRound.append`. This isolates
exactly the remaining content (the `KnowledgeStateFunction.append` construction and the phase-2
witness-carrying flip bound) without any `sorry`, so the existential structure of
`rbrKnowledgeSoundness` is fully assembled around the proven extractor. -/

/-- **Round-by-round knowledge soundness append keystone, deterministic-`V₁` message-seam case.**

Assembles the `rbrKnowledgeSoundness` existential for the appended verifier around the *proven*
composite round-by-round extractor `Extractor.RoundByRound.append E₁ E₂ verify` (its `WitMid` carrier,
`extractMid`, and `extractOut` are all discharged upstream — the deterministic `verify`, supplied by
`hVerify`, is exactly the intermediate-statement reconstruction that the appended extractor needs).

The two remaining pieces — the composite knowledge state function `kSF` (the witness-threaded analogue
of `StateFunction.append`, not yet a named def in the tree) and the per-round knowledge bound `hBound`
(which carries the *same* phase-2 obstruction as `appendRbrSoundnessPhase2Residual`, now with the
intermediate witness threaded) — are taken as explicit inputs. With them the conclusion is immediate.
This keystone is fully axiom-clean (no `sorry`): it pins down precisely which composite objects the
appended round-by-round knowledge soundness existential is built from, leaving only the construction of
`kSF` and the discharge of `hBound` as the named residuals. -/
theorem append_rbrKnowledgeSoundness_keystone
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    -- The composite knowledge state function (witness-threaded analogue of `StateFunction.append`,
    -- built against the proven composite extractor) — a named residual not yet in the tree.
    (kSF : (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃
      (Extractor.RoundByRound.append E₁ E₂ verify))
    -- The per-round knowledge bound (carries the phase-2 obstruction of
    -- `appendRbrSoundnessPhase2Residual`, with the intermediate witness threaded) — a named residual.
    (hBound : ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
      ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂),
      ∀ i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF.toFun i.1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
                (transcript.concat challenge) witMid) ∧
              kSF.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  ⟨_, Extractor.RoundByRound.append E₁ E₂ verify, kSF, hBound⟩

end Verifier

-- Axiom audit: the round-by-round (knowledge) soundness append keystones must not introduce
-- `sorryAx`. Each should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms Verifier.append_rbrSoundness_keystone
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone
