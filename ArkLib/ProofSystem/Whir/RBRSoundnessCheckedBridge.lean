/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.AveragedRbr.Security.RoundByRound
import ArkLib.ProofSystem.Whir.CheckedVerifier

/-!
# WHIR Theorem 5.2 front door, instantiated with the CHECKED verifier

`WhirIOP.whir_rbr_soundness` (`Whir/RBRSoundness.lean`, WHIR Theorem 5.2) is a
statement about an explicitly supplied `VectorIOP` `π`: a `2 * M + 2` challenge-count
pin and `IsSecureWithGapAveraged` at a per-round budget that dominates the Theorem 5.2 bounds.
Its packaging theorems (`whir_rbr_soundness_of_secure_gap`,
`whir_vector_iop_breakthrough`) consume an **abstract** `π` together with its full
`IsSecureWithGapAveraged` proof — both completeness and soundness as hypotheses.

This file instantiates the statement with the **checked construction**
`Whir302Checked.whirCheckedVectorIOP` (real over-the-wire sumcheck-consistency and
final-zero-sum checks; perfect completeness PROVEN —
`whirCheckedVectorIOP_perfectCompleteness`). This construction does **not** implement
Construction 5.1: its verifier never queries the input oracle, and
`CheckedObliviousness.lean` proves that all-zero prover messages pass every one of its
checks on every statement and challenge draw (`whirCheckingBool_allZero`). So the result
below does not certify WHIR. The completeness leg of `IsSecureWithGapAveraged` is discharged,
leaving two named gates. The fixed-prefix sibling uses the same gates and takes its own
fixed-prefix soundness hypothesis:

* `hChallengeCard` — the challenge-cardinality pin
  `card ((whirPaperTranscriptVectorSpec P d').ChallengeIdx) = 2 * M + 2`.
  HONESTY (count corrected 2026-06-10, machine-checked in `ChallengeCardPin.lean`): the
  paper-faithful transcript shape *unbundles* the per-round sumcheck challenges, and its
  exact challenge count is `(∑ i, foldingParam i) + 2 * M + 1`
  (`card_challengeIdx_whirPaperTranscriptVectorSpec` — an earlier version of this note
  omitted the `finalRandomness` slot). Hence the pin holds **iff `∑ foldingParam = 1`**
  (`whirPaper_challengeCard_eq_iff`), which under `[∀ i, Fact (0 < foldingParam i)]`
  forces the single-iteration unit-fold instance `M = 0`, `foldingParam 0 = 1`
  (`M_eq_zero_of_paramsSum_eq_one`) — NOT "params summing to 2". The front door's
  `2 * M + 2` pin reflects the aggregated vector-challenge reading of Construction 5.1;
  this hypothesis records the mismatch *as a named obligation* rather than papering over
  it, and the general-`M` reconciliation requires an aggregated-vector-challenge
  transcript construction or a pin restatement.
* `hSound` — round-by-round knowledge soundness of the checked verifier at the WHIR
  budget. This is not open mathematics for the verifier as it stands: as recorded in
  `CheckedObliviousness.lean`, the all-zero attack means `hSound` cannot hold when a
  δ-far input exists and the per-challenge budgets sum to less than one. A sub-unit
  discharge first needs input/fold-binding checks in the verifier (cf. the local port
  `whirVerifyCheckedWithInitialInputBindingAt`, not used by `whirVerifyChecked`) and a
  matching honest prover; only then would the MCA Cor 4.11 / folding L4.20–4.23 chain
  (conditional today on `mca_johnson_bound_CONJECTURE` in the `√ρ` regime, or the UDR
  window via `mca_rsc_pair_holds`) be the remaining mathematics.

No fabrication: both gates are consumed as hypotheses, and the construction plus its
completeness are the previously landed, axiom-clean theorems.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

set_option linter.unusedVariables false

namespace Whir302Checked

open WhirIOP WhirIOP.Construction NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-- **`whir_rbr_soundness` for the checked construction**: the statement holds for
`π = whirCheckedVectorIOP P d'` given (i) the challenge-cardinality pin for the
paper-transcript wire shape and (ii) rbr knowledge soundness of the CHECKED verifier at
the WHIR per-round budget. Perfect completeness of `π` is PROVEN. This does not certify
WHIR: the checked verifier is input-oblivious, so (ii) cannot hold at a sub-unit total
budget against δ-far inputs, and (i) forces `M = 0` and `foldingParam 0 = 1`
(`ChallengeCardPin.lean`); see the module docstring. -/
private theorem whirRbrSoundnessOfCheckedWith (fixedPrefix : Bool)
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
          Fintype (BlockRelDistance.Generic.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Nonempty (BlockRelDistance.Generic.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
        let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ) ≤ ε_fold 0 j)
    (h_out :
        ∀ i : Fin M,
          2^(P.varCount i.succ) * (h.dist i.succ 0)^2 / (2 * Fintype.card F) ≤ ε_out i.succ)
    (h_shift :
        ∀ i : Fin M,
          (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + (h.dist i.succ 0) * (P.repeatParam i.castSucc + 1) / Fintype.card F ≤ ε_shift i)
    (h_fold_i :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (BlockRelDistance.Generic.indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (BlockRelDistance.Generic.indexPowT (S i) (P.φ i) j) := h.inst2
        let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin M, ∀ j : Fin (P.foldingParam i.succ),
          d * (h.dist i.succ j.castSucc) / Fintype.card F + errStar i.succ j.succ
            ≤ ε_fold i.succ j)
    (h_fin :
        (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)) ≤ ε_fin)
    (d' : ℕ)
    (hChallengeCard :
      Fintype.card ((whirPaperTranscriptVectorSpec P d').ChallengeIdx) = 2 * M + 2)
    (hSound :
      let relation := whirRelation m_0 (P.φ 0) (h.δ 0)
      let verifier := paperTranscriptOracleVerifier P d' (whirVerifyChecked P d')
      let budget : (whirPaperTranscriptVectorSpec P d').ChallengeIdx → ℝ≥0 :=
        fun _ => whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin
      if fixedPrefix then
        OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim relation verifier budget
      else
        OracleProof.rbrKnowledgeSoundnessAveraged (pure ()) isEmptyElim relation verifier budget) :
    whirRbrSoundnessWith (F := F) (M := M) ιs fixedPrefix (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin
      (whirPaperTranscriptVectorSpec P d') (whirCheckedVectorIOP P d') := by
  refine ⟨hChallengeCard, ?_⟩
  cases fixedPrefix
  · exact whirCheckedVectorIOP_isSecureWithGap_of_rbr P d' (m0 := m_0) (h.δ 0) _ hSound
  · exact whirCheckedVectorIOP_isSecureWithGap_fixedPrefix_of_rbr
      P d' (m0 := m_0) (h.δ 0) _ hSound

/-- The checked construction at the historical prover-averaged contract, given the challenge
pin and its prover-averaged bound. The checked construction is input-oblivious. -/
theorem whir_rbr_soundness_of_checkedVectorIOP_rbr :
    type_of% (@whirRbrSoundnessOfCheckedWith F _ _ _ _ M ιs _ false) :=
  @whirRbrSoundnessOfCheckedWith F _ _ _ _ M ιs _ false

/-- The checked construction at the fixed-prefix contract, given the challenge pin and a
fixed-prefix bound for this verifier. The checked construction is input-oblivious. -/
theorem whir_rbr_soundness_fixedPrefix_of_checkedVectorIOP_rbr :
    type_of% (@whirRbrSoundnessOfCheckedWith F _ _ _ _ M ιs _ true) :=
  @whirRbrSoundnessOfCheckedWith F _ _ _ _ M ιs _ true

end Whir302Checked

/-! ## Axiom audit — kernel-clean. -/
#print axioms Whir302Checked.whir_rbr_soundness_of_checkedVectorIOP_rbr
#print axioms Whir302Checked.whir_rbr_soundness_fixedPrefix_of_checkedVectorIOP_rbr
