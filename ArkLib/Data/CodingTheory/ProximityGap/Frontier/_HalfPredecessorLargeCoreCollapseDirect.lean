/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCorePacking

/-!
# Direct large-core collapse at the half predecessor

This standalone module proves the family-level large-line branch of the rate-`1/16`
half-predecessor argument using only the bad-event rich-point bridge and the local line-core
packing facts. It defines the exact maximal subfamily on a given polynomial line. If that line
has a sufficiently large joint core, every selected point outside it lies on one second secant
line, and the two packing bounds give a total of at most the coordinate count.
-/

set_option autoImplicit false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapseDirect

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A large joint core makes a hypothetical more-than-`2h` family collapse onto
two polynomial lines. Exact line-core packing then bounds both lines by `h`.

The inequality `h + 4d < 2z + 3`, with `d=k-1`, is the subtraction-free
form of `2z > h + 4d - 3`. -/
theorem card_le_two_mul_of_large_core
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (a r : F[X])
    (hn : Fintype.card ι = 2 * h) (hk : 1 ≤ k) (hd : k - 1 ≤ h)
    (ha : a.natDegree < k) (hr : r.natDegree < k)
    (hrich : ∀ gamma ∈ family.G,
      h + 1 ≤ (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    (hcore : h + 4 * (k - 1) <
      2 * (jointCore dom (u 0) (u 1) a r).card + 3) :
    family.G.card ≤ 2 * h := by
  classical
  have hh : 1 ≤ h := by
    have hcardPos : 0 < Fintype.card ι := Fintype.card_pos
    rw [hn] at hcardPos
    omega
  let d : ℕ := k - 1
  let D : Finset ι := jointCore dom (u 0) (u 1) a r
  let Gline : Finset F :=
    family.G.filter fun gamma => family.q gamma = a + C gamma * r
  have hGline : Gline ⊆ family.G := by
    exact Finset.filter_subset _ _
  have hline : ∀ gamma ∈ Gline, family.q gamma = a + C gamma * r := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hlineLarge : ∀ gamma ∈ Gline,
      h + 1 ≤ (fullAgreement dom (u 0) (u 1) gamma
        (a + C gamma * r)).card := by
    intro gamma hgamma
    rw [← hline gamma hgamma]
    exact hrich gamma (hGline hgamma)
  have hlineProper : ∀ gamma ∈ Gline,
      ¬ fullAgreement dom (u 0) (u 1) gamma (a + C gamma * r) ⊆ D := by
    simpa only [D] using
      (family.line_hproper a r Gline ha hr hGline hline)
  have hpackLine : Gline.card * max 1 (h + 1 - D.card) + D.card ≤ 2 * h := by
    have hp := line_card_mul_max_add_core_le dom (u 0) (u 1) a r Gline (h + 1)
      hlineLarge hlineProper
    simpa only [D, hn] using hp
  have hGlineCard : Gline.card ≤ h :=
    line_card_le_half_of_packing hpackLine

  by_contra hbad
  have hGlarge : 2 * h + 1 ≤ family.G.card := by omega
  let Gout : Finset F := family.G \ Gline
  have hsplit : Gout.card + Gline.card = family.G.card := by
    exact Finset.card_sdiff_add_card_eq_card hGline
  have hGoutCard : h + 1 ≤ Gout.card := by omega
  have hGout : Gout ⊆ family.G := Finset.sdiff_subset
  have hnotLine : ∀ gamma ∈ Gout,
      family.q gamma ≠ a + C gamma * r := by
    intro gamma hgamma heq
    have hgammaG : gamma ∈ family.G := hGout hgamma
    have hgammaLine : gamma ∈ Gline := by
      exact Finset.mem_filter.mpr ⟨hgammaG, heq⟩
    exact (Finset.mem_sdiff.mp hgamma).2 hgammaLine
  have hfreshLarge : ∀ gamma ∈ Gout,
      h + 1 - d ≤
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \ D).card := by
    intro gamma hgamma
    have hdeg := family.degree_lt gamma (hGout hgamma)
    have hcap :
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩ D).card ≤ d := by
      simpa only [D, d] using
        (fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
          hdeg ha hr (hnotLine gamma hgamma))
    rw [Finset.card_sdiff, Finset.inter_comm D]
    have hbig := hrich gamma (hGout hgamma)
    omega

  have htwo : 1 < Gout.card := by omega
  obtain ⟨beta, hbeta, theta, htheta, hbetatheta⟩ :=
    Finset.one_lt_card.mp htwo
  have hbetaG : beta ∈ family.G := hGout hbeta
  have hthetaG : theta ∈ family.G := hGout htheta
  have hqbeta : (family.q beta).natDegree < k :=
    family.degree_lt beta hbetaG
  have hqtheta : (family.q theta).natDegree < k :=
    family.degree_lt theta hthetaG
  let r₂ : F[X] := slopePolynomial beta theta (family.q beta) (family.q theta)
  let a₂ : F[X] := family.q beta - C beta * r₂
  have hr₂ : r₂.natDegree < k := by
    simpa only [r₂] using slopePolynomial_natDegree_lt hqbeta hqtheta
  have ha₂ : a₂.natDegree < k := by
    have hCr : (C beta * r₂).natDegree ≤ r₂.natDegree :=
      natDegree_C_mul_le beta r₂
    exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt hqbeta (lt_of_le_of_lt hCr hr₂))

  have hsecondLine : ∀ gamma ∈ Gout,
      family.q gamma = a₂ + C gamma * r₂ := by
    intro gamma hgamma
    by_cases hgb : gamma = beta
    · subst gamma
      simp only [a₂]
      ring
    by_cases hgt : gamma = theta
    · subst gamma
      simpa only [a₂, r₂] using
        (second_point_on_secant_line hbetatheta (family.q beta) (family.q theta))
    have hqgamma : (family.q gamma).natDegree < k :=
      family.degree_lt gamma (hGout hgamma)
    let V : Finset ι := Finset.univ \ D
    let X : Finset ι :=
      fullAgreement dom (u 0) (u 1) beta (family.q beta) \ D
    let Y : Finset ι :=
      fullAgreement dom (u 0) (u 1) theta (family.q theta) \ D
    let Z : Finset ι :=
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \ D
    have hXV : X ⊆ V := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
    have hYV : Y ⊆ V := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
    have hZV : Z ⊆ V := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
    have hXcard : h + 1 - d ≤ X.card := by
      change h + 1 - d ≤
        (fullAgreement dom (u 0) (u 1) beta (family.q beta) \ D).card
      exact hfreshLarge beta hbeta
    have hYcard : h + 1 - d ≤ Y.card := by
      change h + 1 - d ≤
        (fullAgreement dom (u 0) (u 1) theta (family.q theta) \ D).card
      exact hfreshLarge theta htheta
    have hZcard : h + 1 - d ≤ Z.card := by
      change h + 1 - d ≤
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \ D).card
      exact hfreshLarge gamma hgamma
    have hVcard : V.card = 2 * h - D.card := by
      simp only [V, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn]
    have hd' : d ≤ h := by simpa only [d] using hd
    have hcore' : h + 4 * d < 2 * D.card + 3 := by
      simpa only [d, D] using hcore
    have hgap : 2 * V.card + d < 3 * (h + 1 - d) := by
      rw [hVcard]
      omega
    have hinter : d < (X ∩ Y ∩ Z).card :=
      three_set_inter_card_gt V X Y Z (h + 1 - d) d
        hXV hYV hZV hXcard hYcard hZcard hgap
    have hsubset : X ∩ Y ∩ Z ⊆
        (fullAgreement dom (u 0) (u 1) beta (family.q beta) ∩
          fullAgreement dom (u 0) (u 1) theta (family.q theta)) ∩
            fullAgreement dom (u 0) (u 1) gamma (family.q gamma) := by
      intro i hi
      simp only [Finset.mem_inter, X, Y, Z, Finset.mem_sdiff] at hi ⊢
      exact ⟨⟨hi.1.1.1, hi.1.2.1⟩, hi.2.1⟩
    have hfull : d <
        ((fullAgreement dom (u 0) (u 1) beta (family.q beta) ∩
          fullAgreement dom (u 0) (u 1) theta (family.q theta)) ∩
            fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card :=
      lt_of_lt_of_le hinter (Finset.card_le_card hsubset)
    have hslope : slopePolynomial beta gamma (family.q beta) (family.q gamma) =
        slopePolynomial beta theta (family.q beta) (family.q theta) := by
      by_contra hslope
      have hle := triple_fullAgreement_card_le_pred_of_slope_ne
        dom (u 0) (u 1) hk
        (gamma₁ := beta) (gamma₂ := theta) (gamma₃ := gamma)
        (q₁ := family.q beta) (q₂ := family.q theta) (q₃ := family.q gamma)
        hbetatheta (Ne.symm hgb) hqbeta hqtheta hqgamma (Ne.symm hslope)
      have hle' :
          ((fullAgreement dom (u 0) (u 1) beta (family.q beta) ∩
            fullAgreement dom (u 0) (u 1) theta (family.q theta)) ∩
              fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card ≤ d := by
        simpa only [d] using hle
      exact (not_le_of_gt hfull) hle'
    have hthird := third_point_on_secant_line_of_slope_eq
      (gamma := beta) (beta := theta) (theta := gamma)
      (q := family.q beta) (p := family.q theta) (s := family.q gamma)
      (Ne.symm hgb) hslope
    simpa only [a₂, r₂] using hthird

  have hsecondLarge : ∀ gamma ∈ Gout,
      h + 1 ≤ (fullAgreement dom (u 0) (u 1) gamma
        (a₂ + C gamma * r₂)).card := by
    intro gamma hgamma
    rw [← hsecondLine gamma hgamma]
    exact hrich gamma (hGout hgamma)
  have hsecondProper : ∀ gamma ∈ Gout,
      ¬ fullAgreement dom (u 0) (u 1) gamma (a₂ + C gamma * r₂) ⊆
        jointCore dom (u 0) (u 1) a₂ r₂ := by
    exact family.line_hproper a₂ r₂ Gout ha₂ hr₂ hGout hsecondLine
  have hpackSecond :
      Gout.card * max 1
          (h + 1 - (jointCore dom (u 0) (u 1) a₂ r₂).card) +
        (jointCore dom (u 0) (u 1) a₂ r₂).card ≤ 2 * h := by
    have hp := line_card_mul_max_add_core_le dom (u 0) (u 1) a₂ r₂ Gout (h + 1)
      hsecondLarge hsecondProper
    simpa only [hn] using hp
  have hGoutLe : Gout.card ≤ h :=
    line_card_le_half_of_packing hpackSecond
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapseDirect

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapseDirect.card_le_two_mul_of_large_core
