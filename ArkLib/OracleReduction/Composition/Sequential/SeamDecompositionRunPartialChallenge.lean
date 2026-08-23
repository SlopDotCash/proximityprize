/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunPartial

/-!
# Challenge-seam phase-2 partial run factoring (#114 rbr chain)

The `V_to_P`-seam analogues of `append_continueFromTo_right_msg_partial` and
`snd_runToRound_natAdd_seam`, under **purity of `P₁.output`** — which holds *definitionally* for the
split prover (`Prover.fst P` has `output = fun st => pure (st, ())`). At a challenge seam the
appended prover samples the seam challenge before the phase-1 output is consumed; for a *pure*
output the two commute **syntactically** (`pure_bind`), so — unlike the honest-prover completeness
factoring, which is genuinely distributional — the split-prover factoring is a plain `HEq`,
proven by welding the challenge-first seam split (`append_continueFromTo_seam_start_challenge_split`)
to the (direction-agnostic) interior fold via the reversed challenge refold
(`liftComp_processRound_zero_challenge_appendRight`).

These are the direction-specific bricks for the challenge-seam rbr knowledge-soundness append
keystone (`phase2_body_heq_challenge` and onward).
-/

open OracleComp ProtocolSpec OracleVerifier.Append

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
  {stmt : Stmt₁} {wit : Wit₁}

/-- Challenge-seam analogue of `append_continueFromTo_right_msg_partial`, under the **purity of
`P₁.output`** (the split-prover case `P₁ = Prover.fst P`): the seam `getChallenge` commutes with a
pure output syntactically, so the same right-block factoring holds at a `V_to_P` seam. -/
theorem append_continueFromTo_right_challenge_partial (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (out₁ : P₁.PrvState (Fin.last m) → Stmt₂ × Wit₂)
    (hOut : ∀ s, P₁.output s = pure (out₁ s))
    (k : Fin (n + 1)) (hk : 0 < (k : ℕ))
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 = Transcript.appendRight T₁
      (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)) rSeam)
      ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
        ((fun p => (Transcript.appendRight T₁ p.1,
            cast (by
              have h1 : (k : Fin (n + 1)) = (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ := by
                ext; simp; omega
              have h2 : (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
                  = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) := by
                ext; simp; omega
              rw [h2]
              exact (congrArg P₂.PrvState h1).trans
                (append_PrvState_natAdd_succ (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).symm
              : P₂.PrvState k = (P₁.append P₂).PrvState ⟨m + (k : ℕ), by omega⟩) p.2)) <$>
          liftComp (P₂.runToRound k ctx.1 ctx.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
              × (P₁.append P₂).PrvState (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))))) := by
  -- 1. Split the right block at the seam-successor.
  rw [continueFromTo_trans (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
    (⟨m, by omega⟩ : Fin (m + n)).succ (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
    (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    (by rw [Fin.le_def, Fin.val_succ]; simp only [Fin.val_mk]; omega) rSeam]
  -- 2. Seam factor via the proven challenge-first split.
  rw [eq_of_heq (append_continueFromTo_seam_start_challenge_split
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT)]
  -- 3. Collapse the pure output on both sides (`hOut`), then refold the RHS seam round to the
  -- challenge-first shape via `liftComp_processRound_zero_challenge_appendRight`.
  simp only [hOut, OracleComp.liftComp_pure, liftM_pure, pure_bind]
  -- 4. RHS: factor `P₂.runToRound k` at the seam successor and expose its round-0 challenge step.
  have hP2run : (P₂.runToRound k (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).1
        (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).2 :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
      = P₂.runToRound (⟨0, hn⟩ : Fin n).succ _ _ >>=
          P₂.continueFromTo _ _ (⟨0, hn⟩ : Fin n).succ k :=
    runToRound_eq_bind_continueFromTo P₂ _ _ (⟨0, hn⟩ : Fin n).succ k
      (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_mk]; omega)
  rw [hP2run]
  rw [← processRound_zero_pure_eq_runToRound hn P₂ _ _]
  -- 5. Fold the LHS seam head back to `processRound 0` shape (reversed challenge fold; the
  -- direction-specific content ends here).
  rw [← liftComp_processRound_zero_challenge_appendRight (P₁ := P₁) (P₂ := P₂) hn hDir₂ T₁
    (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2))]
  -- 6. Align both sides as `liftComp (processRound 0 X) >>= …` and reduce to the interior.
  rw [OracleComp.liftComp_bind, ← bind_pure_comp, bind_assoc, bind_assoc]
  refine bind_heq_congr rfl rfl HEq.rfl (fun p p' hp => ?_)
  obtain rfl := eq_of_heq hp
  simp only [pure_bind]
  rw [bind_pure_comp]
  rcases Nat.lt_or_ge (k : ℕ) 2 with hlt | hge
  · -- k = 1 (incl. the `n = 1` boundary): no interior rounds; both sides `pure (bridge p)`.
    -- `subst` the concrete index `k = ⟨0,hn⟩.succ` (handles all `k`-dependent casts definitionally).
    have hkeq : (k : Fin (n + 1)) = (⟨0, hn⟩ : Fin n).succ := by ext; simp; omega
    subst hkeq
    have hLtgt : ((⟨m, by omega⟩ : Fin (m + n)).succ : Fin (m + n + 1))
        = (⟨m + ((⟨0, hn⟩ : Fin n).succ : ℕ), by omega⟩ : Fin (m + n + 1)) := by ext; simp
    -- LHS: `continueFromTo (⟨m⟩.succ) (⟨m+1⟩) = continueFromTo (⟨m⟩.succ) (⟨m⟩.succ) = pure rk`.
    refine HEq.trans (continueFromTo_heq_target hLtgt.symm (P₁.append P₂) stmt wit _) ?_
    rw [continueFromTo_self]
    -- RHS: `P₂.continueFromTo 0.succ 0.succ p = pure p`.
    rw [continueFromTo_self]
    apply heq_of_eq
    simp only [OracleComp.liftComp_pure, map_pure]
    refine congrArg pure (Prod.ext rfl (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)))
  · -- k ≥ 2 (so n ≥ 2): fold the `k-1` interior rounds via `append_continueFromTo_right_interior`.
    have eStart : ((⟨m, by omega⟩ : Fin (m + n)).succ : Fin (m + n + 1))
        = (Fin.natAdd m (⟨1, by omega⟩ : Fin n)).castSucc := by ext; simp
    have eTgt : (⟨m + ((1 : ℕ) + ((k : ℕ) - 1)), by omega⟩ : Fin (m + n + 1))
        = (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)) := by ext; simp only [Fin.val_mk]; omega
    have eR : (⟨(1 : ℕ) + ((k : ℕ) - 1), by omega⟩ : Fin (n + 1)) = k := by
      ext; simp only [Fin.val_mk]; omega
    -- LHS: transport the start index `⟨m⟩.succ = (natAdd m ⟨1⟩).castSucc` (HEq, not `rw`).  The target
    -- start matches `hint`'s input shape `(appendRight T₁ p.1, cast (natAdd_castSucc).symm p.2)`.
    refine HEq.trans (continueFromTo_heq_start (j := (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)))
      eStart (P₁.append P₂) stmt wit
      (Transcript.appendRight T₁ p.1, cast (append_PrvState_seam_succ hn).symm p.2)
      (Transcript.appendRight T₁ p.1,
        cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) (⟨1, by omega⟩ : Fin n)
          (by simp)).symm p.2)
      (prodMk_heq (by rw [eStart]) (by rw [eStart]) HEq.rfl
        ((cast_heq _ _).trans (cast_heq _ _).symm))) ?_
    refine HEq.trans (continueFromTo_heq_target eTgt.symm (P₁.append P₂) stmt wit
      (Transcript.appendRight T₁ p.1,
        cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) (⟨1, by omega⟩ : Fin n)
          (by simp)).symm p.2)) ?_
    have hint := append_continueFromTo_right_interior (P₁ := P₁) (P₂ := P₂)
      (stmt := stmt) (wit := wit) (stmt₂ := (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).1) (wit₂ := (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).2)
      T₁ (⟨1, by omega⟩ : Fin n) (by simp) ((k : ℕ) - 1)
      (by simp only [Fin.val_mk]; omega) p
    rw [bind_pure_comp] at hint
    refine HEq.trans hint ?_
    -- RHS reconciliation: align the `P₂.continueFromTo` target index `1+(k-1) = k` and start `1 = 0.succ`.
    have happ : ∀ {j₁ j₂ : Fin (n + 1)} (hj : j₁ = j₂) {u : pSpec₂.Transcript j₁}
        {u' : pSpec₂.Transcript j₂}, HEq u u' →
        HEq (Transcript.appendRight T₁ u) (Transcript.appendRight T₁ u') := by
      intro j₁ j₂ hj u u' hu; subst hj; rw [eq_of_heq hu]
    refine map_heq_congr (by rw [eR]) (by rw [eTgt]) (fun a a' ha => ?_)
      (HEq.trans (liftComp_continueFromTo_heq_target eR P₂ (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).1 (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).2 p)
        (liftComp_continueFromTo_heq_start
          (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (show (⟨1, by omega⟩ : Fin n).castSucc = (⟨0, hn⟩ : Fin n).succ from by ext; simp)
          P₂ (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).1 (out₁ (cast (append_PrvState_seam_castSucc hn) rSeam.2)).2 _ p HEq.rfl))
    obtain ⟨t, s⟩ := a
    obtain ⟨t', s'⟩ := a'
    obtain ⟨ht, hs⟩ := prod_heq_split (by rw [eR]) (by rw [eR]) ha
    refine prodMk_heq (by rw [eTgt]) (by rw [eTgt]) (happ eR ht)
      ((cast_heq _ _).trans (hs.trans (cast_heq _ _).symm))

variable {P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)}

theorem snd_runToRound_natAdd_seam_challenge (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (k : Fin (n + 1)) (hk : 0 < (k : ℕ)) (stmt : Stmt₁) (wit : Wit₁) :
    HEq (P.runToRound (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)) stmt wit)
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst P).run stmt wit)
        let r ← liftM ((Prover.snd P).runToRound k ctxIn₂.1 ctxIn₂.2)
        (pure (Transcript.appendRight transcript₁ r.1,
            cast (by
              have h1 : (k : Fin (n + 1)) = (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ := by
                ext; simp; omega
              have h2 : (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
                  = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) := by
                ext; simp; omega
              rw [h2]
              exact (congrArg (Prover.snd P).PrvState h1).trans
                (append_PrvState_natAdd_succ (P₁ := Prover.fst P) (P₂ := Prover.snd P)
                  (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).symm
              : (Prover.snd P).PrvState k
                = ((Prover.fst P).append (Prover.snd P)).PrvState
                    (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))) r.2)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
                × ((Prover.fst P).append (Prover.snd P)).PrvState
                    (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))))) := by
  -- Weld onto `P` via the run-merge, then work with the append-of-restrictions.
  refine HEq.trans (merge_runToRound P stmt wit (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))).symm ?_
  -- Seam-split the append-of-restrictions run at `k = ⟨m⟩`.
  rw [runToRound_eq_bind_continueFromTo ((Prover.fst P).append (Prover.snd P)) stmt wit
        (⟨m, by omega⟩ : Fin (m + n + 1)) (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
        (by simp only [Fin.le_def, Fin.val_mk]; omega)]
  rw [show (⟨m, by omega⟩ : Fin (m + n + 1)) = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by
        ext; simp]
  -- The seam state: `runToRound ⟨m⟩` of the append is `fst`'s run-to-`last m`.
  have hidx : ((Fin.last m).castLE (by omega) : Fin (m + n + 1))
      = (⟨m, by omega⟩ : Fin (m + n)).castSucc := by ext; simp
  have hseam : HEq (((Prover.fst P).append (Prover.snd P)).runToRound
        (⟨m, by omega⟩ : Fin (m + n)).castSucc stmt wit)
      (liftM ((Prover.fst P).runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :=
    HEq.trans
      (runToRound_heq_index hidx.symm ((Prover.fst P).append (Prover.snd P)) stmt wit)
      (append_runToRound_seam (P₁ := Prover.fst P) (P₂ := Prover.snd P) (stmt := stmt) (wit := wit))
  -- Rewrite the appended-seam continuation per realized seam state via the partial characterization
  -- (mirrors `appendRunRightResidual_holds_msg`).
  conv_lhs =>
    enter [2, rSeam]
    rw [eq_of_heq (append_continueFromTo_right_challenge_partial (P₁ := Prover.fst P) (P₂ := Prover.snd P)
      (stmt := stmt) (wit := wit) hn hDir hDir₂ (fun st => (st, ())) (fun _ => rfl) k hk
      (cast (append_Transcript_seam_castSucc hn) rSeam.1) rSeam
      (seam_transcript_appendRight hn rSeam.1))]
  -- Expand the target `liftM (fst.run) = liftM (runToRound (last m) >>= output)`, normalize lifts
  -- (directly on the `HEq` goal, since the seam-runToRound parts differ in type).
  simp only [run_eq_runToRound_last, liftM_bind, bind_assoc, liftM_pure, pure_bind,
    bind_map_left, Function.comp, OracleComp.liftComp_eq_liftM]
  -- Bind over the seam: appended-seam-runToRound ≍ `liftM (fst.runToRound last)` via `hseam`.
  refine bind_heq_congr
    (by rw [append_Transcript_seam_castSucc hn, append_PrvState_seam_castSucc hn]; rfl) rfl
    hseam (fun rSeam x hr => ?_)
  -- per-seam-state continuation equality (collapse the seam `cast`s à la `appendRunRightResidual_holds_msg`).
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_seam_castSucc hn)
    (append_PrvState_seam_castSucc hn) hr
  have hc2 : cast (append_PrvState_seam_castSucc hn) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  have hc1 : cast (append_Transcript_seam_castSucc hn) rSeam.1 = x.1 :=
    eq_of_heq ((cast_heq _ _).trans ht)
  rw [hc2, hc1]
  apply heq_of_eq
  refine bind_congr (fun ctx => ?_)
  -- `bridge <$> liftM (snd.runToRound k ctx) = liftM (snd.runToRound k ctx) >>= pure ∘ bridge`.
  rw [bind_pure_comp]

end Prover
