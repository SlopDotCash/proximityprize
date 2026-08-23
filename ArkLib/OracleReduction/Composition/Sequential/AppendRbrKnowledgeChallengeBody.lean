/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunPartialChallenge

/-!
# Challenge-seam phase-2 experiment body factoring (#114 rbr chain)

`phase2_body_heq_challenge`: the `V_to_P`-seam analogue of `phase2_body_heq` for phase-2 challenge
indices strictly past the seam (`hpos`), via the proven challenge-seam split-prover factoring
`snd_runToRound_natAdd_seam_challenge`. At a challenge seam the positivity of the phase-2 index is a
*hypothesis* (the seam challenge itself, `i₂ = 0`, is handled separately) rather than a consequence
of the seam direction.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

theorem phase2_body_heq_challenge
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₂ : pSpec₂.ChallengeIdx) (hn : 0 < n) (hpos : 0 < ((i₂.1 : Fin n) : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
        let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (Transcript.appendRight transcript₁ r.1, challenge)) := by
  classical
  have hk0 : 0 < ((i₂.1.castSucc : Fin (n + 1)) : ℕ) := by simpa using hpos
  -- The phase-2 index identity: `(inr i₂).castSucc = ⟨m + (i₂.castSucc).val, _⟩`.
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr]
  -- Transcript/state value-type equalities induced by the index identity.
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (pSpec₁ ++ₚ pSpec₂).Transcript
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  have hStTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  -- The seam-index transcript/state types, and `prover`'s own state type there (via the merge).
  have hidx2 : (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = (Fin.natAdd m i₂.1).castSucc := by ext; simp
  have hStTy' : ((Prover.fst prover).append (Prover.snd prover)).PrvState
      (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    rw [hidx2]; exact Prover.merge_PrvState_natAdd_castSucc prover i₂.1 hpos
  have hPrvTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) :=
    hStTy.trans hStTy'.symm
  -- STEP 1: the bound HEq — appended `runToRound (inr i₂).castSucc` ≍ the seam-factored run (the RHS
  -- of `snd_runToRound_natAdd_seam`), via the index transport.
  have hRunHeq := HEq.trans (Prover.runToRound_heq_index hidx prover stmtIn witIn)
    (Prover.snd_runToRound_natAdd_seam_challenge (P := prover) hn hDir hDir₂ (i₂.1.castSucc) hk0 stmtIn witIn)
  -- The challenge-sampling continuation on the seam-index value type, used as the explicit `f'`.
  let K' : ((pSpec₁ ++ₚ pSpec₂).Transcript
        (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      × ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)))
      → OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript
              (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    fun p => do
      let challenge ← OracleComp.liftComp
        ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      pure (p.1, challenge)
  -- STEP 2: bind congruence over the top-level bind into `(seam-run) >>= K'`, then collapse the
  -- inner `do`-block by `bind_assoc` to the stated RHS.  `K'` reads only the transcript component, so
  -- the (discarded) trailing state cast in the seam run is irrelevant.
  refine HEq.trans (Prover.bind_heq_congr (congrArg₂ Prod hTrTy hPrvTy)
    (by rw [hTrTy]) (f' := K') hRunHeq (fun ⟨trA, stA⟩ ⟨trB, stB⟩ hpair => ?_)) (heq_of_eq ?_)
  · -- continuation HEq: same combined `getChallenge`, then `pure (·, challenge)` on HEq transcripts.
    obtain ⟨htr, _⟩ := Prover.prod_heq_split hTrTy hPrvTy hpair
    refine Prover.bind_heq_congr rfl (by rw [hTrTy]) HEq.rfl ?_
    rintro cA cB hc
    exact Prover.pure_heq_pure (by rw [hTrTy]) (Prover.prodMk_heq hTrTy rfl htr hc)
  · -- the inner-block collapse: `(seam-run) >>= K' = stated RHS`.
    show _ >>= K' = _
    simp only [K', bind_assoc, pure_bind]

theorem phase2_body_heq_challenge_zero
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₂ : pSpec₂.ChallengeIdx) (hn : 0 < n) (hz : ((i₂.1 : Fin n) : ℕ) = 0)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
        let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (Transcript.appendRight transcript₁ r.1, challenge)) := by
  classical
  -- Index transports at `i₂.val = 0`: the appended index is the seam `⟨m⟩` (= castLE of `last m`),
  -- and the phase-2 index is `0`.
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i₂.1⟩
  have hcs0 : (i₂.1.castSucc : Fin (n + 1)) = 0 := by
    ext; simp [hz]
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = ((Fin.last m).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr, hz]
  -- LHS prover run ~ `fst`'s full partial run (seam factoring, no right block at the seam).
  have hseam : HEq
      (prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn)
      (liftM ((Prover.fst prover).runToRound (Fin.last m) stmtIn witIn) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
    refine HEq.trans (Prover.runToRound_heq_index hidx prover stmtIn witIn) ?_
    refine HEq.trans (Prover.merge_runToRound prover stmtIn witIn _).symm ?_
    exact Prover.append_runToRound_seam (P₁ := Prover.fst prover) (P₂ := Prover.snd prover)
      (stmt := stmtIn) (wit := witIn)
  -- RHS: `fst.run = runToRound last >>= pure`-pack; `snd.runToRound 0 = pure`.
  have hsnd : ∀ (c : prover.PrvState ((Fin.last m).castLE
      (show m + 1 ≤ m + n + 1 by omega)) × Unit), HEq
      ((Prover.snd prover).runToRound i₂.1.castSucc c.1 c.2)
      (pure ((default : pSpec₂.Transcript 0),
        (Prover.snd prover).input (c.1, c.2)) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _) := by
    intro c
    refine HEq.trans (Prover.runToRound_heq_index hcs0 (Prover.snd prover) c.1 c.2) ?_
    rfl
  -- Unfold `fst.run` (pure output) and collapse `snd.runToRound 0` on the RHS.
  conv_rhs => rw [Prover.run_eq_runToRound_last]
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]
  -- Both sides now head with the phase-1 partial run; reduce along `hseam`.
  refine Prover.bind_heq_congr ?_ ?_ hseam (fun x x' hx => ?_)
  · rw [hidx, Prover.append_Transcript_castLE (Fin.last m)]
    rfl
  · rw [show (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
        = (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc from by
      ext; simp [ChallengeIdx.inr]]
  · -- Collapse the (pure) `fst.output`, exposing the `snd.runToRound 0` bind.
    simp only [show prover.fst.output x'.2 = pure (x'.2, ()) from rfl, liftM_pure, pure_bind]
    -- Collapse `snd.runToRound (castSucc i₂ = 0)` definitionally after the index rewrite.
    rw [show (i₂.1.castSucc : Fin (n + 1)) = 0 from hcs0]
    simp only [liftM_pure, pure_bind,
      show ∀ (a) (b), Prover.runToRound (0 : Fin (n + 1)) a b prover.snd
        = pure (default, prover.snd.input (a, b)) from fun _ _ => rfl]
    -- Both sides: `challenge ≫ pure`; the transcript components match via the seam transport.
    have hidxm : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        = ((⟨m, by omega⟩ : Fin (m + n)).castSucc : Fin (m + n + 1)) := by
      ext; simp [ChallengeIdx.inr, hz]
    refine Prover.bind_heq_congr rfl ?_ HEq.rfl (fun c c' hc => ?_)
    · rw [show (⟨m + ((0 : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
          = (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc from by
        ext; simp [ChallengeIdx.inr, hz]]
    · obtain rfl := eq_of_heq hc
      refine Prover.pure_heq_pure (by
        rw [show (⟨m + ((0 : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            = (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc from by
          ext; simp [ChallengeIdx.inr, hz]]) ?_
      refine Prover.prodMk_heq (by
        rw [show (⟨m + ((0 : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            = (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc from by
          ext; simp [ChallengeIdx.inr, hz]]) rfl ?_ HEq.rfl
      -- the transcript component: `x.1 ≍ appendRight x'.1 default` via the seam transport
      obtain ⟨ht, hs⟩ := Prover.prod_heq_split
        (by rw [hidx, Prover.append_Transcript_castLE (Fin.last m)])
        (by rw [hidx]; rfl) hx
      -- transport `x.1` to the `⟨m⟩.castSucc` index and apply the free-`hT` seam decomposition
      have hx1m : HEq x.1 (cast (congrArg ((pSpec₁ ++ₚ pSpec₂).Transcript) hidxm) x.1) :=
        (cast_heq _ _).symm
      have hseamT := Prover.seam_transcript_appendRight (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        hn (cast (congrArg ((pSpec₁ ++ₚ pSpec₂).Transcript) hidxm) x.1)
      refine HEq.trans hx1m ?_
      rw [hseamT]
      -- `appendRight (cast …) default ≍ appendRight x'.1 default`: the casts compose to `ht`
      have hcc : cast (Prover.append_Transcript_seam_castSucc hn)
          (cast (congrArg ((pSpec₁ ++ₚ pSpec₂).Transcript) hidxm) x.1) = x'.1 := by
        apply eq_of_heq
        exact ((cast_heq _ _).trans (cast_heq _ _)).trans ht
      rw [hcc]
      exact HEq.rfl

end Verifier
