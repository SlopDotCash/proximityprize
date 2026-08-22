/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.CheckedVerifier

/-!
# WHIR Theorem 5.2 front door, instantiated with the CHECKED verifier

`WhirIOP.whir_rbr_soundness` (`Whir/RBRSoundness.lean`, WHIR Theorem 5.2) is an
existential front door: it demands *some* `VectorIOP` `π` with `2 * M + 2` challenge
slots that `IsSecureWithGap` at the WHIR per-round budget. Until now its only
dischargers (`whir_rbr_soundness_of_secure_gap`, `whir_vector_iop_breakthrough`)
consumed an **abstract** `π` together with its full `IsSecureWithGap` proof — both
completeness and soundness as hypotheses.

This file instantiates the existential with the **concrete checked WHIR construction**
`Whir302Checked.whirCheckedVectorIOP` (real over-the-wire sumcheck-consistency and
final-zero-sum checks; perfect completeness PROVEN —
`whirCheckedVectorIOP_perfectCompleteness`). The completeness leg of `IsSecureWithGap`
is therefore discharged, and the front door reduces to exactly two named gates:

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
  budget. This is the genuine open soundness mathematics (the MCA Cor 4.11 / folding
  L4.20–4.23 chain, conditional today on `mca_johnson_bound_CONJECTURE` in the `√ρ`
  regime, or the UDR window via `mca_rsc_pair_holds`).

No fabrication: both gates are consumed as hypotheses, and the construction plus its
completeness are the previously landed, axiom-clean theorems.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

set_option linter.unusedVariables false

namespace Whir302Checked

open WhirIOP WhirIOP.Construction NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-- **WHIR Theorem 5.2 from the checked construction**: `whir_rbr_soundness` holds given
(i) the challenge-cardinality pin for the paper-transcript wire shape and (ii) rbr
knowledge soundness of the CHECKED verifier at the WHIR per-round budget. The witness
`π` is the concrete `whirCheckedVectorIOP P d'`, whose perfect completeness is PROVEN;
only the two named gates remain (see the module docstring for their honest status). -/
theorem whir_rbr_soundness_of_checkedVectorIOP_rbr
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
    (hChallengeCard :
      Fintype.card ((whirPaperTranscriptVectorSpec P d').ChallengeIdx) = 2 * M + 2)
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
  whir_rbr_soundness_of_secure_gap (ι := Unit)
    hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
    ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin
    hChallengeCard (whirCheckedVectorIOP P d')
    (whirCheckedVectorIOP_isSecureWithGap_of_rbr P d' (m0 := m_0) (h.δ 0) _ hSound)

end Whir302Checked

/-! ## Axiom audit — kernel-clean. -/
#print axioms Whir302Checked.whir_rbr_soundness_of_checkedVectorIOP_rbr
