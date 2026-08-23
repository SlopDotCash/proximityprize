/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Master Cryptographer
-/
import ArkLib.ProofSystem.Whir.RBRSoundness
import ArkLib.ToMathlib.WhirBricksConstruction

/-!
# WHIR Vector IOP Resolution (Issue #113)

This file records the residual checkpoint for the `whir_vector_iop_residual`
mathematics.  The hard WHIR work is still the concrete Vector IOP construction,
its `IsSecureWithGap` proof, and the fold/OOD/shift/final budget inequalities.
This standalone surface only assembles those residuals through the existing
`whir_rbr_soundness_of_whirVectorSpec_secure_gap` theorem.
-/

namespace WhirIOPP

open scoped NNReal ProbabilityTheory

/-- **Issue #113 checkpoint:** WHIR RBR soundness from the concrete residual witnesses. -/
theorem whir_vector_iop_breakthrough
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    {d dstar : ℕ} {P : WhirIOP.Params ι F} {S : ∀ i : Fin (M + 1), Finset (ι i)}
    {hParams : WhirIOP.ParamConditions ι P} {h : WhirIOP.GenMutualCorrParams ι P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ι 0)]
    [∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (h_fold_0 :
      let maxDeg := (Finset.univ : Finset (Fin m_0)).sup
        (fun i => wPoly₀.degreeOf (Fin.succ i))
      let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
      ∀ _ : Fin ((P.foldingParam 0) + 1),
        let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
      ∀ j : Fin (P.foldingParam 0),
        ε_fold 0 j ≤
          ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ))
    (h_out :
      ∀ i : Fin (M + 1),
        ε_out i ≤
          2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F))
    (h_shift :
      ∀ i : Fin M,
        ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
          + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F)
    (h_fold_i :
      let maxDeg := (Finset.univ : Finset (Fin m_0)).sup
        (fun i => wPoly₀.degreeOf (Fin.succ i))
      let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
      let d := max dstar 3
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
      ∀ i : Fin (M + 1), ∀ _ : Fin ((P.foldingParam i) + 1),
        let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
      ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
        ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ)
    (h_fin :
      ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)))
    (π : VectorIOP Unit (WhirIOP.OracleStatement (ι 0) F) Unit
      (WhirIOP.Construction.whirVectorSpec M) F)
    (hSecure :
      let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : (WhirIOP.Construction.whirVectorSpec M).ChallengeIdx → ℝ≥0 :=
        fun _ => (Finset.univ.image max_ε_folds ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪
          Finset.univ.image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (WhirIOP.whirRelation m_0 (P.φ 0) 0)
        (WhirIOP.whirRelation m_0 (P.φ 0) (h.δ 0)) ε_rbr π) :
    WhirIOP.whir_rbr_soundness (F := F) (M := M) ι (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h) hm_0 (σ₀ := σ₀)
      (wPoly₀ := wPoly₀) (δ := δ) ε_fold ε_out ε_shift ε_fin
      h_fold_0 h_out h_shift h_fold_i h_fin :=
  WhirIOP.Construction.whir_rbr_soundness_of_whirVectorSpec_secure_gap
    (F := F) (M := M) (ιs := ι) (d := d) (dstar := dstar)
    (P := P) (S := S) (hParams := hParams) (h := h) hm_0
    (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
    ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin π hSecure

#print axioms WhirIOPP.whir_vector_iop_breakthrough

end WhirIOPP
