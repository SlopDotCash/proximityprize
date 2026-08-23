/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.RBRSoundnessCheckedBridge

/-!
# The WHIR paper-transcript challenge-cardinality pin, computed exactly (issue #302)

`whir_rbr_soundness_of_checkedVectorIOP_rbr` (`RBRSoundnessCheckedBridge.lean`) carries the
structural gate `hChallengeCard : card ChallengeIdx = 2M + 2`. Its docstring claimed the count is
`foldingParam 0 + 2M + ∑_{i<M} foldingParam (i+1)` ("= 2M+2 iff the folding parameters sum to
2") — **that count omits the `finalRandomness` slot**, which is `V_to_P`
(`paperTranscriptSlotDirection`, `WhirBricksConstruction.lean`). This file computes the
cardinality exactly:

  `card ChallengeIdx = (∑ i, foldingParam i) + 2M + 1`,

so the pin `= 2M + 2` holds **iff `∑ foldingParam = 1`**, which under the bridge's own
`[∀ i, Fact (0 < foldingParam i)]` (over `M + 1` rounds) forces **`M = 0` and
`foldingParam 0 = 1`** — the single-iteration unit-fold WHIR instance. The general-`M` form of
the bridge therefore needs either an aggregated-vector-challenge transcript shape or a
restatement of the pin; until then the honest reading of `hChallengeCard` is the unit-fold case.
-/

open ProtocolSpec

namespace Whir302Checked

open WhirIOP WhirIOP.Construction NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-- The `V_to_P` (challenge) slots of the faithful WHIR Construction 5.1 transcript, enumerated:
initial sumcheck challenges (`Fin (foldingParam 0)`), out-of-domain challenges (`Fin M`), shift
challenges (`Fin M`), main sumcheck challenges (`Σ i : Fin M, Fin (foldingParam i.succ)`), and the
single `finalRandomness` slot (`Unit`) — the slot the original bridge docstring's count missed. -/
def paperChallengeSlotEquiv (P : Params ιs F) :
    {s : PaperTranscriptSlot P // paperTranscriptSlotDirection s = .V_to_P} ≃
      (Fin (P.foldingParam 0) ⊕ Fin M ⊕ Fin M ⊕
        ((i : Fin M) × Fin (P.foldingParam i.succ)) ⊕ Unit) where
  toFun := fun ⟨s, hdir⟩ =>
    match s, hdir with
    | .initialSumcheckChallenge j, _ => Sum.inl j
    | .mainOutOfDomainChallenge i, _ => Sum.inr (Sum.inl i)
    | .mainShiftChallenge i, _ => Sum.inr (Sum.inr (Sum.inl i))
    | .mainSumcheckChallenge i j, _ => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩)))
    | .finalRandomness, _ => Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))
  invFun := fun x =>
    match x with
    | Sum.inl j => ⟨.initialSumcheckChallenge j, rfl⟩
    | Sum.inr (Sum.inl i) => ⟨.mainOutOfDomainChallenge i, rfl⟩
    | Sum.inr (Sum.inr (Sum.inl i)) => ⟨.mainShiftChallenge i, rfl⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩))) => ⟨.mainSumcheckChallenge i j, rfl⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))) => ⟨.finalRandomness, rfl⟩
  left_inv := fun ⟨s, hdir⟩ => by
    cases s <;> first
      | rfl
      | exact absurd hdir (by simp [paperTranscriptSlotDirection])
  right_inv := fun x => by
    rcases x with j | i | i | ⟨i, j⟩ | ⟨⟩ <;> rfl

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- **The exact challenge count of the faithful WHIR paper transcript:**
`(∑ i, foldingParam i) + 2M + 1`. The `+1` is the `finalRandomness` slot. -/
theorem card_challengeIdx_whirPaperTranscriptVectorSpec (P : Params ιs F) (d : ℕ) :
    Fintype.card ((whirPaperTranscriptVectorSpec P d).ChallengeIdx) =
      (∑ i, P.foldingParam i) + 2 * M + 1 := by
  have e1 : ((whirPaperTranscriptVectorSpec P d).ChallengeIdx) ≃
      {s : PaperTranscriptSlot P // paperTranscriptSlotDirection s = .V_to_P} :=
    Equiv.subtypeEquiv (Fintype.equivFin (PaperTranscriptSlot P)).symm (fun _ => Iff.rfl)
  rw [Fintype.card_congr (e1.trans (paperChallengeSlotEquiv P))]
  have hsum : (∑ i, P.foldingParam i) =
      P.foldingParam 0 + ∑ i : Fin M, P.foldingParam i.succ := Fin.sum_univ_succ _
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, Fintype.card_unit]
  omega

/-- The bridge's structural gate `card = 2M + 2` holds **iff the folding parameters sum to 1**
(not 2 — the original docstring's count missed `finalRandomness`). -/
theorem whirPaper_challengeCard_eq_iff (P : Params ιs F) (d : ℕ) :
    Fintype.card ((whirPaperTranscriptVectorSpec P d).ChallengeIdx) = 2 * M + 2 ↔
      (∑ i, P.foldingParam i) = 1 := by
  rw [card_challengeIdx_whirPaperTranscriptVectorSpec]
  omega

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [(i : Fin (M + 1)) → Fintype (ιs i)] in
/-- Under the bridge's own positivity instances, `∑ foldingParam = 1` forces the single-iteration
unit-fold instance: `M = 0` (and hence `foldingParam 0 = 1`). -/
theorem M_eq_zero_of_paramsSum_eq_one (P : Params ιs F)
    [hpos : ∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (hSum : (∑ i, P.foldingParam i) = 1) : M = 0 := by
  by_contra hM
  have h2 : 2 ≤ ∑ i, P.foldingParam i := by
    calc 2 ≤ M + 1 := by omega
    _ = ∑ _i : Fin (M + 1), 1 := by simp
    _ ≤ ∑ i, P.foldingParam i :=
        Finset.sum_le_sum (fun i _ => (hpos i).out)
  omega


/-- **The bridge at its honest gate**: `whir_rbr_soundness_of_checkedVectorIOP_rbr` with the
challenge-cardinality pin replaced by its exact characterization `∑ foldingParam = 1` (the
unit-fold instance — see `whirPaper_challengeCard_eq_iff`). Hypotheses are verbatim those of the
bridge; only the structural gate is restated in its true form. The sole remaining gate is
`hSound` (the genuine open soundness mathematics). -/
theorem whir_rbr_soundness_of_checkedVectorIOP_rbr_unitFold
    {d dstar : ℕ}
    {P : Params ιs F} {S : ∀ i : Fin (M + 1), Finset (ιs i)}
    {hParams : ParamConditions ιs P} {h : GenMutualCorrParams ιs P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)]
    [∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (h_fold_0 :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
        ∀ j : Fin ((P.foldingParam 0) + 1),
          let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤ ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ))
    (h_out :
        ∀ i : Fin (M + 1),
          ε_out i ≤
            2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F))
    (h_shift :
        ∀ i : Fin M,
          ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F)
    (h_fold_i :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
        ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ)
    (h_fin :
        ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)))
    (d' : ℕ)
    (hSum : (∑ i, P.foldingParam i) = 1)
    (hSound : OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
      (whirRelation m_0 (P.φ 0) (h.δ 0))
      (paperTranscriptOracleVerifier P d' (whirVerifyChecked P d'))
      (fun _ =>
        (Finset.univ.image
            (fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i))
          ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪ Finset.univ.image ε_shift).max'
          (by simp))) :
    whir_rbr_soundness (F := F) (M := M) ιs (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin :=
  whir_rbr_soundness_of_checkedVectorIOP_rbr hm_0
    ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin d'
    ((whirPaper_challengeCard_eq_iff P d').mpr hSum) hSound

end Whir302Checked

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Whir302Checked.paperChallengeSlotEquiv
#print axioms Whir302Checked.card_challengeIdx_whirPaperTranscriptVectorSpec
#print axioms Whir302Checked.whirPaper_challengeCard_eq_iff
#print axioms Whir302Checked.M_eq_zero_of_paramsSum_eq_one
#print axioms Whir302Checked.whir_rbr_soundness_of_checkedVectorIOP_rbr_unitFold
