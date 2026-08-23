/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffPolysExceptional
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellStrictExtraction

/-!
# BCIKS20 §5 — share-form (Prop-5.5-faithful) strict coefficient-polynomial residual

`StrictCoeffPolysResidual` (`Curves.lean`) demands ONE coefficient family `B` matching the
decoded family at EVERY good parameter; `StrictCoeffPolysExcResidual b`
(`StrictCoeffPolysExceptional.lean`) relaxes this by a CONSTANT exceptional budget `b`.
Neither matches what BCIKS20 §5 actually produces: Proposition 5.5 pins the decoded family
to one curve only on a subset of PROPORTIONAL size (`|S′| ≥ |S|/2D_Y` on one curve) — the
surviving set is a `1/ℓ` SHARE of the good set (up to a degenerate-cell budget `T`), not
the good set minus a constant.

The cell machinery delivers exactly this shape:
`BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_heavy_cell` produces a factor cell
`G′` with `|good| ≤ T + ℓ·|G′|` carrying the full coefficient family (`ℓ` = number of
factor cells of the GS interpolant, `T` = the degenerate-cell budget).

This file builds the matching honest residual surface and its consumer chain down to the
correlated-agreement keystone:

* `StrictCoeffPolysShareResidual ℓ T` — verbatim `StrictCoeffPolysResidual`, except the
  coefficient identity is only required on a subset `G′ ⊆ good` with
  `|good| ≤ T + ℓ·|G′|` (the Prop-5.5 share shape; `ℓ = 1, T = 0` forces `G′` to exhaust
  the good set up to nothing and recovers the counting power of the original).
* `strictCoeffPolysShareResidual_of_strictCoeffPolysResidual` /
  `strictCoeffPolysShareResidual_of_exc` — the weld lattice: the original residual and the
  constant-budget exceptional residual both land in the share surface.
* `RS_jointAgreement_of_prob_gt_share` — the §6 consumer: a probability threshold whose
  mass dominates `ℓ·(n+1)·k + T` parameters still yields `jointAgreement`, by running the
  single-family subset counting core on `S′ = G′` (the share subset beats both counting
  thresholds once the good set beats `ℓ·threshold + T`).
* `RS_jointAgreement_of_prob_gt_strict_johnson_share` — the strict-Johnson instantiation
  at the explicit threshold `k · (errorBound + (ℓ·(n+1)·k + T)/|F|)`.
* `correlatedAgreement_affine_curves_of_strict_coeff_polys_share` /
  `correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_share` — the keystone:
  Theorem 1.5 from the share residual, at the adjusted proximity error
  `ε = errorBound + (ℓ·(n+1)·k + T)/|F|`; the strict-interior front door carries no
  boundary residual.

Honest accounting: the share surface costs `(ℓ·(n+1)·k + T)/|F|` of proximity error where
the constant-budget surface costs `b/|F|`.  For the BCIKS20 parameter regime
(`|F| ≫ n·k·ℓ`) both are vanishing; the share form is the one the §5 cell machinery can
actually discharge.
-/

namespace ProximityGap

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate
open NNReal Finset Function ProbabilityTheory
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section ShareResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Share-form (Prop-5.5-faithful) strict Johnson extraction residual.**  Verbatim
`StrictCoeffPolysResidual`, except the coefficient-polynomial identity is required only on
a subset `G′` of the good set of proportional size: `|good| ≤ T + ℓ·|G′|` (`ℓ` = number of
factor cells, `T` = degenerate-cell budget).  This is the conclusion shape of BCIKS20
Proposition 5.5 and the exact output shape of the cell extraction
(`strict_coeffPolys_of_heavy_cell`). -/
def StrictCoeffPolysShareResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (ℓ T : ℕ) : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F, ∃ G' : Finset F,
          G' ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ∧
          (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≤
            T + ℓ * G'.card ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ G', ∀ j < deg, (P z).coeff j = (B j).eval z

/-- **Cell-decomposition supplier for the share residual.**  The SK2 cell theorem
`strict_coeffPolys_of_heavy_cell` is exactly a producer for `StrictCoeffPolysShareResidual`:
when the good set is larger than the degenerate budget `T`, the supplied section-linked
cell decomposition gives the share subset; when it is not, the empty subset already satisfies
the share inequality. -/
theorem strictCoeffPolysShareResidual_of_cell_decomposition
    {n k deg : ℕ} [NeZero n] {domain : Fin n ↪ F} {δ : ℝ≥0} {ℓ T : ℕ}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) (Fin n)),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
        T < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
        ∃ (Idx : Type) (_ : DecidableEq Idx)
          (Index : Finset (Option Idx)) (Ecell : Option Idx → Finset F)
          (Rof : Idx → (F[X])[X][Y]) (wof : Idx → F[X][Y]) (Bw : ℕ)
          (Tset : Idx → Finset (Fin n)) (Sset : Idx → Fin n → Finset F),
          Index.card ≤ ℓ + 1 ∧
            none ∈ Index ∧
            RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ⊆
              Index.biUnion Ecell ∧
            Index.biUnion Ecell ⊆
              RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ∧
            (Ecell none).card ≤ T ∧
            (∀ R, some R ∈ Index → Irreducible (Rof R)) ∧
            (∀ R, some R ∈ Index → ∀ γ ∈ Ecell (some R),
              (Polynomial.X - Polynomial.C (P γ)) ∣
                (Rof R).map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) ∧
            (∀ R, some R ∈ Index →
              (Polynomial.X - Polynomial.C (wof R)) ∣ Rof R) ∧
            (∀ R, some R ∈ Index → ∀ i, ((wof R).coeff i).natDegree ≤ Bw) ∧
            (∀ R, some R ∈ Index → (wof R).natDegree < (Tset R).card) ∧
            (∀ R, some R ∈ Index → ∀ t ∈ Tset R, Sset R t ⊆ Ecell (some R)) ∧
            (∀ R, some R ∈ Index → ∀ t ∈ Tset R, max Bw k < (Sset R t).card) ∧
            ∀ R, some R ∈ Index → ∀ t ∈ Tset R, ∀ z ∈ Sset R t,
              (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
      ℓ T := by
  classical
  intro hk u hprob hJ hsqrt P hP
  set G : Finset F := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ
    with hG
  by_cases hbig : T < G.card
  · obtain ⟨Idx, hIdxDec, Index, Ecell, Rof, wof, Bw, Tset, Sset, hIndexCard, hnone,
      hcover, hcellsGood, hnoneCard, hRirr, hdvdP, hwdvd, hB, hT, hSE, hScard,
      hagree⟩ := hInput hk u hprob hJ hsqrt P hP (by simpa [hG] using hbig)
    letI : DecidableEq Idx := hIdxDec
    have hcoverG : G ⊆ Index.biUnion Ecell := by
      simpa [hG] using hcover
    have hcellsGoodG : Index.biUnion Ecell ⊆ G := by
      simpa [hG] using hcellsGood
    have hLk : k + 1 - 1 ≤ k := by omega
    obtain ⟨G', hcount, hG'cells, B, hBdeg, hBid⟩ :=
      BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_heavy_cell
        (domain := domain) (u := u) (G := G) (Index := Index) (Ecell := Ecell)
        (P := P) (hIdx := hIndexCard) (hnone := hnone) (hcover := hcoverG)
        (hnoneCard := hnoneCard) (hbig := hbig) (Rof := Rof) (hRirr := hRirr)
        (hdvdP := hdvdP) (wof := wof) (hLk := hLk)
        (hwdvd := hwdvd) (hB := hB) (Tset := Tset) (hT := hT)
        (Sset := Sset) (hSE := hSE) (hScard := hScard) (hagree := hagree)
    refine ⟨B, G', ?_, hcount, (fun j _ => hBdeg j), ?_⟩
    · intro z hz
      exact hcellsGoodG (hG'cells hz)
    · intro z hz j _
      exact hBid z hz j
  · refine ⟨fun _ => (0 : Polynomial F), (∅ : Finset F), ?_, ?_, ?_, ?_⟩
    · exact Finset.empty_subset G
    · have hle : G.card ≤ T := Nat.le_of_not_lt hbig
      simpa using hle
    · intro j _
      simp
    · intro z hz
      cases hz

/-- The original (full-good-set) residual implies the share residual at every positive
share `ℓ` and every budget `T`, with `G′ = good`. -/
theorem strictCoeffPolysShareResidual_of_strictCoeffPolysResidual
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} {ℓ T : ℕ} (hℓ : 0 < ℓ)
    (h : StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
      ℓ T := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨B, hBdeg, hBid⟩ := h hk u hprob hJ hsqrt P hP
  refine ⟨B, RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    Finset.Subset.refl _, ?_, hBdeg, fun z hz j hj => hBid z hz j hj⟩
  have hmul := Nat.le_mul_of_pos_left
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card hℓ
  omega

/-- The constant-budget exceptional residual implies the share residual at share `1` and
budget `b`, with `G′ = good \ E`. -/
theorem strictCoeffPolysShareResidual_of_exc
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} {b : ℕ}
    (h : StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) b) :
    StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
      1 b := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨B, E, hEcard, hBdeg, hBid⟩ := h hk u hprob hJ hsqrt P hP
  refine ⟨B, RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ \ E,
    Finset.sdiff_subset, ?_, hBdeg, ?_⟩
  · have hsd := Finset.le_card_sdiff E
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    omega
  · intro z hz j hj
    have hz' := Finset.mem_sdiff.mp hz
    exact hBid z hz'.1 hz'.2 j hj

/-- **§6 consumer for the share residual.**  A probability threshold `η` whose mass
dominates `ℓ·(n+1)·k + T` parameters (`hη`) makes the good set large enough that the share
subset `G′` beats both counting thresholds of the single-family subset core
(`ℓ·|G′| ≥ |good| − T > ℓ·(n+1)·k`), and `jointAgreement` follows at `S′ = G′`. -/
theorem RS_jointAgreement_of_prob_gt_share
    {k deg : ℕ} {domain : ι ↪ F} {δ η : ℝ≥0} [NeZero deg]
    (ℓ T : ℕ)
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal))
    (hη :
      ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ENNReal) ≤
        (η : ENNReal) * (Fintype.card F : ENNReal))
    (hcoeffPolyShare : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F, ∃ G' : Finset F,
          G' ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ∧
          (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≤
            T + ℓ * G'.card ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ G', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  have hxη :
      (η : ENNReal) * (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) :=
    goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
      (k := k) (deg := deg) (domain := domain) (δ := δ) (η := η) u hprob
  have hgood : ℓ * ((Fintype.card ι + 1) * k) + T <
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card := by
    have h := lt_of_le_of_lt hη hxη
    exact_mod_cast h
  obtain ⟨P, hP⟩ :=
    exists_decoded_polynomial_family_of_subset_goodCoeffsCurve
      (k := k) (deg := deg) (domain := domain) (δ := δ) u
      (S' := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
      (fun _ hz => hz)
  obtain ⟨B, G', hG'sub, hcount, hBdeg, hBid⟩ := hcoeffPolyShare P hP
  have hG' : (Fintype.card ι + 1) * k < G'.card := by
    have h2 : ℓ * ((Fintype.card ι + 1) * k) < ℓ * G'.card := by omega
    exact Nat.lt_of_mul_lt_mul_left h2
  have hki : k ≤ (Fintype.card ι + 1) * k :=
    Nat.le_mul_of_pos_left k (Nat.succ_pos _)
  refine subset_single_decoded_family_coeff_polys_implies_jointAgreement_of_pos
    (deg := deg) (domain := domain) (δ := δ) hk
    (S' := G') (by omega) (by omega) P ?_ B hBdeg hBid
  intro z hz
  exact hP z (hG'sub hz)

/-- Strict-Johnson front door for the share residual, at the explicit threshold
`k · (errorBound + (ℓ·(n+1)·k + T) / |F|)`.  The extra probability mass converts to
`k·(ℓ·(n+1)·k + T) ≥ ℓ·(n+1)·k + T` surplus good parameters, which pays for the share
counting. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_share
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (ℓ T : ℕ)
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) *
          ((errorBound δ deg domain +
            ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
              (Fintype.card F : ℝ≥0) : ℝ≥0) :
            ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hcoeffPolyShare : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F, ∃ G' : Finset F,
          G' ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ∧
          (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≤
            T + ℓ * G'.card ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ G', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  set S : ℕ := ℓ * ((Fintype.card ι + 1) * k) + T with hSdef
  set qn : ℝ≥0 := (Fintype.card F : ℝ≥0) with hqn
  have hqn0 : qn ≠ 0 := by
    simp [hqn, Fintype.card_ne_zero]
  set η : ℝ≥0 := (k : ℝ≥0) * (errorBound δ deg domain + (S : ℝ≥0) / qn) with hηdef
  have hprob' :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal) := by
    simpa [hηdef, ENNReal.coe_mul, ENNReal.coe_natCast] using hprob
  have hk1 : (1 : ℝ≥0) ≤ (k : ℝ≥0) := by
    exact_mod_cast hk
  have hη_nn : (S : ℝ≥0) ≤ η * qn := by
    have hbq : (S : ℝ≥0) / qn * qn = (S : ℝ≥0) := div_mul_cancel₀ _ hqn0
    have hkey : η * qn =
        (k : ℝ≥0) * errorBound δ deg domain * qn + (k : ℝ≥0) * (S : ℝ≥0) := by
      calc η * qn
          = (k : ℝ≥0) *
              (errorBound δ deg domain * qn + (S : ℝ≥0) / qn * qn) := by
            rw [hηdef]; ring
        _ = (k : ℝ≥0) * (errorBound δ deg domain * qn + (S : ℝ≥0)) := by
            rw [hbq]
        _ = (k : ℝ≥0) * errorBound δ deg domain * qn + (k : ℝ≥0) * (S : ℝ≥0) := by
            ring
    rw [hkey]
    calc (S : ℝ≥0) ≤ (k : ℝ≥0) * (S : ℝ≥0) :=
          le_mul_of_one_le_left (zero_le _) hk1
      _ ≤ (k : ℝ≥0) * errorBound δ deg domain * qn + (k : ℝ≥0) * (S : ℝ≥0) :=
          le_add_self
  have hη :
      ((S : ℕ) : ENNReal) ≤ (η : ENNReal) * (Fintype.card F : ENNReal) := by
    have hcast := ENNReal.coe_le_coe.mpr hη_nn
    simpa [hqn, ENNReal.coe_mul, ENNReal.coe_natCast] using hcast
  exact RS_jointAgreement_of_prob_gt_share
    (deg := deg) (domain := domain) (δ := δ) (η := η)
    ℓ T hk u hprob' (by rw [hSdef] at hη; exact hη) hcoeffPolyShare

/-- **Theorem 1.5 from the share residual** ([BCIKS20], Prop-5.5-faithful conclusion
shape).  Identical to `correlatedAgreement_affine_curves_of_strict_coeff_polys_exc` except
that the strict Johnson branch consumes `StrictCoeffPolysShareResidual ℓ T` and the
proximity error pays for the share counting:
`ε = errorBound + (ℓ·(n+1)·k + T) / |F|`. -/
theorem correlatedAgreement_affine_curves_of_strict_coeff_polys_share {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (ℓ T : ℕ)
    (_hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hShare :
      StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
        ℓ T)
    (hBoundary :
      BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := errorBound δ deg domain +
        ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
          (Fintype.card F : ℝ≥0)) := by
  classical
  have hmono :
      errorBound δ deg domain ≤
        errorBound δ deg domain +
          ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
            (Fintype.card F : ℝ≥0) :=
    le_self_add
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact δ_ε_correlatedAgreementCurves_mono_error hmono
      (RS_correlatedAgreement_curves_k_zero (deg := deg) (domain := domain) (δ := δ))
  · by_cases hUDR : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code domain deg)
    · exact δ_ε_correlatedAgreementCurves_mono_error hmono
        (RS_correlatedAgreement_curves_uniqueDecodingRegime hkpos hUDR)
    · unfold δ_ε_correlatedAgreementCurves
      intro u hprob
      have hprob_weak :
          Pr_{
            let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) := by
        refine lt_of_le_of_lt ?_ hprob
        exact mul_le_mul_right (ENNReal.coe_le_coe.mpr hmono) _
      by_cases hJ :
          (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ
      · by_cases hsqrt : δ < 1 - ReedSolomon.sqrtRate deg domain
        · exact RS_jointAgreement_of_prob_gt_strict_johnson_share
            (deg := deg) (domain := domain) (δ := δ) ℓ T hkpos u hprob hJ hsqrt
            (hShare hkpos u hprob_weak hJ hsqrt)
        · exact hBoundary hkpos u hprob_weak hJ hsqrt
      · push Not at hJ
        exact False.elim (hUDR
          (RS_le_relativeUniqueDecodingRadius_of_le_rate_half
            (deg := deg) (domain := domain) (δ := δ) hJ))

/-- **Strict-interior share front door.**  In the open Johnson regime
`δ < 1 - sqrtRate`, the boundary branch is unreachable, so the share residual gives the
curve correlated-agreement theorem without any `BoundaryProbabilityResidual` assumption. -/
theorem correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_share {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (ℓ T : ℕ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hShare :
      StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
        ℓ T) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := errorBound δ deg domain +
        ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
          (Fintype.card F : ℝ≥0)) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys_share
    (k := k) (deg := deg) (domain := domain) (δ := δ) ℓ T hδ.le hShare
    (fun _hk _u _hprob _hJ hnot => absurd hδ hnot)

end ShareResidual

end ProximityGap

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ProximityGap.StrictCoeffPolysShareResidual
#print axioms ProximityGap.strictCoeffPolysShareResidual_of_cell_decomposition
#print axioms ProximityGap.strictCoeffPolysShareResidual_of_strictCoeffPolysResidual
#print axioms ProximityGap.strictCoeffPolysShareResidual_of_exc
#print axioms ProximityGap.RS_jointAgreement_of_prob_gt_share
#print axioms ProximityGap.RS_jointAgreement_of_prob_gt_strict_johnson_share
#print axioms ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_share
#print axioms ProximityGap.correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_share
