/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCorePacking

/-!
# Polynomial-line cores for the half-predecessor incidence argument

This file formalizes the local Reed--Solomon geometry used by the rate-`1/16`
half-predecessor proof.  A selected lifted point is a pair `(gamma,q)` and its
full agreement set records where `q(alpha_i)=u0_i+gamma*u1_i`.

For points on one nonvertical polynomial line `q=a+gamma*r`:

* two distinct full agreement sets intersect exactly in the joint core where
  `(a,r)` agrees with `(u0,u1)`;
* their fresh parts outside that core are disjoint;
* a point off the polynomial line meets its core in at most `k-1` coordinates.

These are field- and domain-independent consequences of the root bound.  They
are the geometric inputs behind the line-richness dichotomy, not named residuals.
-/

set_option autoImplicit false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Full agreement of a polynomial with one affine point of the received line. -/
def fullAgreement (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (gamma : F) (q : F[X]) : Finset ι :=
  Finset.univ.filter fun i => q.eval (dom i) = u₀ i + gamma * u₁ i

/-- The coordinates jointly explained by the polynomial line `(a,r)`. -/
def jointCore (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (a r : F[X]) : Finset ι :=
  Finset.univ.filter fun i =>
    a.eval (dom i) = u₀ i ∧ r.eval (dom i) = u₁ i

/-- Every point of a polynomial line agrees on its joint core. -/
theorem jointCore_subset_fullAgreement
    (dom : ι ↪ F) (u₀ u₁ : ι → F) (a r : F[X]) (gamma : F) :
    jointCore dom u₀ u₁ a r ⊆
      fullAgreement dom u₀ u₁ gamma (a + C gamma * r) := by
  intro i hi
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ, true_and,
    eval_add, eval_mul, eval_C]
  rw [hi.1, hi.2]

/-- **Exact line-core identity.**  Distinct points of one nonvertical polynomial
line have full agreement intersection equal to the joint core. -/
theorem fullAgreement_inter_eq_jointCore
    (dom : ι ↪ F) (u₀ u₁ : ι → F) (a r : F[X])
    {gamma beta : F} (hne : gamma ≠ beta) :
    fullAgreement dom u₀ u₁ gamma (a + C gamma * r) ∩
        fullAgreement dom u₀ u₁ beta (a + C beta * r) =
      jointCore dom u₀ u₁ a r := by
  ext i
  simp only [fullAgreement, jointCore, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and, eval_add, eval_mul, eval_C]
  constructor
  · rintro ⟨hgamma, hbeta⟩
    have hmul : (gamma - beta) * (r.eval (dom i) - u₁ i) = 0 := by
      linear_combination hgamma - hbeta
    have hdiff : gamma - beta ≠ 0 := sub_ne_zero.mpr hne
    have hr : r.eval (dom i) = u₁ i := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hdiff)
    have ha : a.eval (dom i) = u₀ i := by
      rw [hr] at hgamma
      exact add_right_cancel hgamma
    exact ⟨ha, hr⟩
  · rintro ⟨ha, hr⟩
    constructor <;> rw [ha, hr]

/-- The fresh agreement fibres of two distinct points on a polynomial line are
disjoint after deleting the joint core. -/
theorem freshAgreement_disjoint
    (dom : ι ↪ F) (u₀ u₁ : ι → F) (a r : F[X])
    {gamma beta : F} (hne : gamma ≠ beta) :
    Disjoint
      (fullAgreement dom u₀ u₁ gamma (a + C gamma * r) \
        jointCore dom u₀ u₁ a r)
      (fullAgreement dom u₀ u₁ beta (a + C beta * r) \
        jointCore dom u₀ u₁ a r) := by
  rw [Finset.disjoint_left]
  intro i hiGamma hiBeta
  simp only [Finset.mem_sdiff] at hiGamma hiBeta
  apply hiGamma.2
  rw [← fullAgreement_inter_eq_jointCore dom u₀ u₁ a r hne]
  exact Finset.mem_inter.mpr ⟨hiGamma.1, hiBeta.1⟩

/-- **Line fresh-fibre packing.**  If every selected point on a polynomial line
has at least `t` full agreements and is not jointly explained by the line core,
then its fresh fibres pack disjointly outside the core.  This is `(L2)` in the
rate-`1/16` argument. -/
theorem line_card_mul_max_add_core_le
    (dom : ι ↪ F) (u₀ u₁ : ι → F) (a r : F[X])
    (G : Finset F) (t : ℕ)
    (hlarge : ∀ gamma ∈ G,
      t ≤ (fullAgreement dom u₀ u₁ gamma (a + C gamma * r)).card)
    (hproper : ∀ gamma ∈ G,
      ¬ fullAgreement dom u₀ u₁ gamma (a + C gamma * r) ⊆
        jointCore dom u₀ u₁ a r) :
    G.card * max 1 (t - (jointCore dom u₀ u₁ a r).card) +
        (jointCore dom u₀ u₁ a r).card ≤ Fintype.card ι := by
  classical
  apply lineCore_packing G
    (fun gamma => fullAgreement dom u₀ u₁ gamma (a + C gamma * r))
    (jointCore dom u₀ u₁ a r) t
  · intro gamma _hgamma
    exact jointCore_subset_fullAgreement dom u₀ u₁ a r gamma
  · intro gamma _hgamma beta _hbeta hne
    exact freshAgreement_disjoint dom u₀ u₁ a r hne
  · exact hlarge
  · intro gamma hgamma _hcoreLarge
    exact Finset.sdiff_nonempty.mpr (hproper gamma hgamma)

/-- Any polynomial line at agreement threshold `h+1` inside `2h` coordinates
contains at most `h` selected points.  This is the numerical consequence of
the exact fresh-fibre packing law, including cores of size at least `h+1`. -/
theorem line_card_le_half_of_packing
    {h z L : ℕ} (hpacking : L * max 1 (h + 1 - z) + z ≤ 2 * h) :
    L ≤ h := by
  by_cases hzh : z ≤ h
  · have hmax : h + 1 - z ≤ max 1 (h + 1 - z) := le_max_right _ _
    have hmul : L * (h + 1 - z) ≤ L * max 1 (h + 1 - z) :=
      Nat.mul_le_mul_left L hmax
    by_contra hL
    have hL' : h + 1 ≤ L := by omega
    have hpos : 1 ≤ h + 1 - z := by omega
    have hsum : h + 1 - z + z = h + 1 := Nat.sub_add_cancel (by omega)
    have hhMul : h ≤ h * (h + 1 - z) := by
      simpa only [mul_one] using Nat.mul_le_mul_left h hpos
    have hbase : h + (h + 1 - z) ≤ (h + 1) * (h + 1 - z) := by
      rw [add_mul, one_mul]
      exact Nat.add_le_add_right hhMul _
    have hprod : (h + 1) * (h + 1 - z) ≤ L * (h + 1 - z) :=
      Nat.mul_le_mul_right _ hL'
    omega
  · have hone : 1 ≤ max 1 (h + 1 - z) := le_max_left _ _
    have hmul : L ≤ L * max 1 (h + 1 - z) := by
      simpa only [mul_one] using Nat.mul_le_mul_left L hone
    omega

/-- A nonzero degree-`<k` polynomial vanishes on at most `k-1` evaluation
coordinates. -/
theorem domain_root_card_le_pred
    (dom : ι ↪ F) {k : ℕ} (hk : 1 ≤ k) (p : F[X])
    (hp0 : p ≠ 0) (hpdeg : p.natDegree < k) :
    (Finset.univ.filter fun i => p.eval (dom i) = 0).card ≤ k - 1 := by
  exact le_trans (ArkLib.CS25.card_domain_roots_le dom p hp0) (by omega)

/-- **Off-line core cap.**  A selected polynomial point not lying on `(a,r)`
meets that line's joint core in at most `k-1` coordinates. -/
theorem fullAgreement_inter_jointCore_card_le
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {gamma : F} {q a r : F[X]}
    (hqdeg : q.natDegree < k) (hadeg : a.natDegree < k)
    (hrdeg : r.natDegree < k) (hoff : q ≠ a + C gamma * r) :
    (fullAgreement dom u₀ u₁ gamma q ∩ jointCore dom u₀ u₁ a r).card ≤ k - 1 := by
  let p : F[X] := q - (a + C gamma * r)
  have hp0 : p ≠ 0 := sub_ne_zero.mpr hoff
  have hCr : (C gamma * r).natDegree ≤ r.natDegree := natDegree_C_mul_le gamma r
  have hlineDeg : (a + C gamma * r).natDegree < k :=
    lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt hadeg (lt_of_le_of_lt hCr hrdeg))
  have hpdeg : p.natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hqdeg hlineDeg)
  have hsub :
      fullAgreement dom u₀ u₁ gamma q ∩ jointCore dom u₀ u₁ a r ⊆
        Finset.univ.filter (fun i => p.eval (dom i) = 0) := by
    intro i hi
    simp only [Finset.mem_inter, fullAgreement, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, eval_sub,
      eval_add, eval_mul, eval_C]
    rw [hi.2.1, hi.2.2, hi.1]
    ring
  exact le_trans (Finset.card_le_card hsub)
    (domain_root_card_le_pred dom hk p hp0 hpdeg)

/-- The slope polynomial between two lifted points. -/
noncomputable def slopePolynomial (gamma beta : F) (q p : F[X]) : F[X] :=
  C (gamma - beta)⁻¹ * (q - p)

/-- A secant slope reconstructs the polynomial difference exactly. -/
theorem C_sub_mul_slopePolynomial
    {gamma beta : F} (hne : gamma ≠ beta) (q p : F[X]) :
    C (gamma - beta) * slopePolynomial gamma beta q p = q - p := by
  simp only [slopePolynomial, ← mul_assoc, ← C_mul]
  rw [mul_inv_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]

/-- The second lifted point lies on the polynomial secant through the first. -/
theorem second_point_on_secant_line
    {gamma beta : F} (hne : gamma ≠ beta) (q p : F[X]) :
    let r := slopePolynomial gamma beta q p
    let a := q - C gamma * r
    p = a + C beta * r := by
  dsimp only
  have hdiff := C_sub_mul_slopePolynomial hne q p
  calc
    p = q - (q - p) := by abel
    _ = q - C (gamma - beta) * slopePolynomial gamma beta q p := by rw [hdiff]
    _ = q - C gamma * slopePolynomial gamma beta q p +
        C beta * slopePolynomial gamma beta q p := by rw [C_sub]; ring

/-- Equality of slopes from one base point places the third point on the same
nonvertical polynomial line. -/
theorem third_point_on_secant_line_of_slope_eq
    {gamma beta theta : F} {q p s : F[X]}
    (hgt : gamma ≠ theta)
    (hslope : slopePolynomial gamma theta q s =
      slopePolynomial gamma beta q p) :
    let r := slopePolynomial gamma beta q p
    let a := q - C gamma * r
    s = a + C theta * r := by
  dsimp only
  have hline := second_point_on_secant_line hgt q s
  dsimp only at hline
  rw [hslope] at hline
  exact hline

/-- On the intersection of two distinct full agreement sets, their slope
polynomial evaluates to the received direction row. -/
theorem slopePolynomial_eval_eq_direction
    (dom : ι ↪ F) (u₀ u₁ : ι → F)
    {gamma beta : F} (hne : gamma ≠ beta) {q p : F[X]} {i : ι}
    (hiGamma : i ∈ fullAgreement dom u₀ u₁ gamma q)
    (hiBeta : i ∈ fullAgreement dom u₀ u₁ beta p) :
    (slopePolynomial gamma beta q p).eval (dom i) = u₁ i := by
  simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ, true_and] at hiGamma hiBeta
  simp only [slopePolynomial, eval_mul, eval_C, eval_sub]
  have hkey : q.eval (dom i) - p.eval (dom i) =
      (gamma - beta) * u₁ i := by
    linear_combination hiGamma - hiBeta
  rw [hkey, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_mul]

/-- Slope polynomials between degree-`<k` points still have degree `<k`. -/
theorem slopePolynomial_natDegree_lt
    {k : ℕ} {gamma beta : F} {q p : F[X]}
    (hq : q.natDegree < k) (hp : p.natDegree < k) :
    (slopePolynomial gamma beta q p).natDegree < k := by
  exact lt_of_le_of_lt (natDegree_C_mul_le _ _)
    (lt_of_le_of_lt (natDegree_sub_le q p) (max_lt hq hp))

/-- **Noncollinear triple codegree cap.**  If the slopes from the first lifted
point to the other two are distinct, their three full agreement sets meet in
at most `k-1` coordinates.  Distinct slopes are exactly noncollinearity in the
nonvertical affine chart. -/
theorem triple_fullAgreement_card_le_pred_of_slope_ne
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {gamma₁ gamma₂ gamma₃ : F} {q₁ q₂ q₃ : F[X]}
    (h12 : gamma₁ ≠ gamma₂) (h13 : gamma₁ ≠ gamma₃)
    (hq₁ : q₁.natDegree < k) (hq₂ : q₂.natDegree < k)
    (hq₃ : q₃.natDegree < k)
    (hslope : slopePolynomial gamma₁ gamma₂ q₁ q₂ ≠
      slopePolynomial gamma₁ gamma₃ q₁ q₃) :
    ((fullAgreement dom u₀ u₁ gamma₁ q₁ ∩
        fullAgreement dom u₀ u₁ gamma₂ q₂) ∩
      fullAgreement dom u₀ u₁ gamma₃ q₃).card ≤ k - 1 := by
  let s12 := slopePolynomial gamma₁ gamma₂ q₁ q₂
  let s13 := slopePolynomial gamma₁ gamma₃ q₁ q₃
  let diff := s12 - s13
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr hslope
  have hs12deg : s12.natDegree < k :=
    slopePolynomial_natDegree_lt hq₁ hq₂
  have hs13deg : s13.natDegree < k :=
    slopePolynomial_natDegree_lt hq₁ hq₃
  have hdiffdeg : diff.natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hs12deg hs13deg)
  have hsub :
      (fullAgreement dom u₀ u₁ gamma₁ q₁ ∩
          fullAgreement dom u₀ u₁ gamma₂ q₂) ∩
        fullAgreement dom u₀ u₁ gamma₃ q₃ ⊆
      Finset.univ.filter (fun i => diff.eval (dom i) = 0) := by
    intro i hi
    rw [Finset.mem_inter, Finset.mem_inter] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [diff, eval_sub, sub_eq_zero]
    rw [slopePolynomial_eval_eq_direction dom u₀ u₁ h12 hi.1.1 hi.1.2,
      slopePolynomial_eval_eq_direction dom u₀ u₁ h13 hi.1.1 hi.2]
  exact le_trans (Finset.card_le_card hsub)
    (domain_root_card_le_pred dom hk diff hdiff hdiffdeg)

end ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry.fullAgreement_inter_eq_jointCore
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry.freshAgreement_disjoint
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry.fullAgreement_inter_jointCore_card_le
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry.line_card_mul_max_add_core_le
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry.triple_fullAgreement_card_le_pred_of_slope_ne
