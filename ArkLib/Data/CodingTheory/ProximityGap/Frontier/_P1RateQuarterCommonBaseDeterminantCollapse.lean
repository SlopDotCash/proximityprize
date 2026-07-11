/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines

/-!
# Common-base secants collapse without a counting threshold

Every canonical secant through the same lifted point `(gamma0,q gamma0)` has
parameter `(q gamma0 - gamma0*r, r)`.  Consequently all such polynomial
parameter pairs lie on one affine line, and every three-line Pluecker
determinant vanishes identically.  Unlike the multiplicity consumer, this
collapse costs no core-cardinality budget.
-/

set_option autoImplicit false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines
open HalfPredecessorRateQuarterDeterminantCollapse

/-! ## Exact finite-set factor split -/

/-- The three-set weighted overlap splits exactly into the reference-pair
intersection and the union of the two external intersections.  Triple points
are counted once in each summand, matching the two determinant factors. -/
theorem weightedOverlap_eq_referenceInter_add_externalInterUnion
    {U : Type} [Fintype U] [DecidableEq U]
    (D0 D1 E : Finset U) :
    ((D0 ∩ D1) ∪ (D0 ∩ E) ∪ (D1 ∩ E)).card +
        ((D0 ∩ D1) ∩ E).card =
      (D0 ∩ D1).card +
        ((D0 ∩ E) ∪ (D1 ∩ E)).card := by
  let R := D0 ∩ D1
  let Q := (D0 ∩ E) ∪ (D1 ∩ E)
  have hinter : R ∩ Q = (D0 ∩ D1) ∩ E := by
    ext x
    simp only [R, Q, Finset.mem_inter, Finset.mem_union]
    tauto
  have hunion : R ∪ Q = (D0 ∩ D1) ∪ (D0 ∩ E) ∪ (D1 ∩ E) := by
    ext x
    simp only [R, Q, Finset.mem_inter, Finset.mem_union]
    tauto
  have hbook := Finset.card_union_add_card_inter R Q
  rw [hinter, hunion] at hbook
  exact hbook

/-- Polynomial-line form: determinant weighted overlap is exactly the sum of
the root supports assigned to the reference-direction factor and to the
external common-lift defect factor. -/
theorem pairOverlap_add_tripleOverlap_eq_twoFactorSupports
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 external : PolynomialLine F) :
    (pairOverlap dom u0 u1 line0 line1 external).card +
        (tripleOverlap dom u0 u1 line0 line1 external).card =
      (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line1.1 line1.2).card +
        ((jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 external.1 external.2) ∪
          (jointCore dom u0 u1 line1.1 line1.2 ∩
            jointCore dom u0 u1 external.1 external.2)).card := by
  simpa only [pairOverlap, tripleOverlap] using
    weightedOverlap_eq_referenceInter_add_externalInterUnion
      (jointCore dom u0 u1 line0.1 line0.2)
      (jointCore dom u0 u1 line1.1 line1.2)
      (jointCore dom u0 u1 external.1 external.2)

/-- A nonzero degree-`<k` polynomial carrying a certified `k-1`-element
domain-root support has degree exactly `k-1`. -/
theorem natDegree_eq_pred_of_rootSupport_card_eq_pred
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) {k : Nat} (hk : 1 ≤ k)
    (p : F[X]) (hp0 : p ≠ 0) (hpdeg : p.natDegree < k)
    (roots : Finset iota)
    (hroots : roots ⊆ Finset.univ.filter fun i => p.eval (dom i) = 0)
    (hcard : roots.card = k - 1) :
    p.natDegree = k - 1 := by
  have hlower : k - 1 ≤ p.natDegree := by
    rw [← hcard]
    exact (Finset.card_le_card hroots).trans
      (ArkLib.CS25.card_domain_roots_le dom p hp0)
  omega

/-- Locator polynomial of a finite evaluation-coordinate set. -/
noncomputable def domainLocator
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) : F[X] :=
  ∏ i ∈ S, (X - C (dom i))

theorem domainLocator_ne_zero
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) :
    domainLocator dom S ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (dom i)

theorem domainLocator_natDegree
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) :
    (domainLocator dom S).natDegree = S.card := by
  rw [domainLocator, Polynomial.natDegree_prod _ _
    (fun i _ => X_sub_C_ne_zero (dom i))]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  simp

/-- Locator inclusion--exclusion: overlap coordinates occur in both factors
and therefore contribute the double-root locator. -/
theorem domainLocator_union_mul_inter
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (R Q : Finset iota) :
    domainLocator dom (R ∪ Q) * domainLocator dom (R ∩ Q) =
      domainLocator dom R * domainLocator dom Q := by
  simpa only [domainLocator] using
    (Finset.prod_union_inter
      (s₁ := R) (s₂ := Q) (f := fun i => X - C (dom i)))

/-- The union of the two factor supports is precisely the pair-overlap set. -/
theorem twoFactorSupport_union_eq_pairOverlap
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 external : PolynomialLine F) :
    (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line1.1 line1.2) ∪
        ((jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 external.1 external.2) ∪
          (jointCore dom u0 u1 line1.1 line1.2 ∩
            jointCore dom u0 u1 external.1 external.2)) =
      pairOverlap dom u0 u1 line0 line1 external := by
  ext i
  simp only [pairOverlap, Finset.mem_union, Finset.mem_inter]
  tauto

/-- The intersection of the factor supports is precisely the triple core. -/
theorem twoFactorSupport_inter_eq_tripleOverlap
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 external : PolynomialLine F) :
    (jointCore dom u0 u1 line0.1 line0.2 ∩
        jointCore dom u0 u1 line1.1 line1.2) ∩
      ((jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 external.1 external.2) ∪
        (jointCore dom u0 u1 line1.1 line1.2 ∩
          jointCore dom u0 u1 external.1 external.2)) =
      tripleOverlap dom u0 u1 line0 line1 external := by
  ext i
  simp only [tripleOverlap, Finset.mem_inter, Finset.mem_union]
  tauto

/-- Every polynomial vanishing on `S` is divisible by its domain locator. -/
theorem domainLocator_dvd_of_eval_eq_zero
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) (p : F[X])
    (hroot : ∀ i ∈ S, p.eval (dom i) = 0) :
    domainLocator dom S ∣ p := by
  rw [domainLocator]
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact Polynomial.pairwise_coprime_X_sub_C dom.injective hij
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot]
    exact hroot i hi

/-- **Maximal root support normal form.**  A nonzero polynomial whose degree
equals the size of a certified domain-root set is a nonzero scalar multiple
of that set's locator polynomial. -/
theorem eq_C_mul_domainLocator_of_natDegree_eq_card
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) (p : F[X])
    (hp0 : p ≠ 0) (hpdeg : p.natDegree = S.card)
    (hroot : ∀ i ∈ S, p.eval (dom i) = 0) :
    ∃ c : F, c ≠ 0 ∧ p = C c * domainLocator dom S := by
  have hdvd := domainLocator_dvd_of_eval_eq_zero dom S p hroot
  obtain ⟨q, hq⟩ := hdvd
  have hL0 := domainLocator_ne_zero dom S
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact hp0 hq
  have hmuldeg := Polynomial.natDegree_mul hL0 hq0
  have hqdeg : q.natDegree = 0 := by
    rw [← hq, domainLocator_natDegree, hpdeg] at hmuldeg
    omega
  let c := q.coeff 0
  have hqC : q = C c := by
    exact Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have hc : c ≠ 0 := by
    intro hc0
    apply hq0
    rw [hqC, hc0, C_0]
  refine ⟨c, hc, ?_⟩
  rw [hq, hqC]
  ring

/-- Any three polynomial-line parameters passing through the same scalar
lifted polynomial point have zero line determinant. -/
theorem lineDeterminant_eq_zero_of_common_lift
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line1 line2 line3 : PolynomialLine F)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hline2 : q0 = line2.1 + C gamma0 * line2.2)
    (hline3 : q0 = line3.1 + C gamma0 * line3.2) :
    lineDeterminant line1 line2 line3 = 0 := by
  have ha1 : line1.1 = q0 - C gamma0 * line1.2 := by
    linear_combination -hline1
  have ha2 : line2.1 = q0 - C gamma0 * line2.2 := by
    linear_combination -hline2
  have ha3 : line3.1 = q0 - C gamma0 * line3.2 := by
    linear_combination -hline3
  rw [lineDeterminant, ha1, ha2, ha3]
  ring

/-- **Threshold-free common-base collapse.**  Three canonical secants sharing
their first endpoint have identically zero determinant, for arbitrary other
endpoints (no distinctness or agreement-size assumptions are needed). -/
theorem three_commonBase_secants_lineDeterminant_eq_zero
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma0 beta1 beta2 beta3 : F) :
    lineDeterminant
        (secantParameter family gamma0 beta1)
        (secantParameter family gamma0 beta2)
        (secantParameter family gamma0 beta3) = 0 := by
  apply lineDeterminant_eq_zero_of_common_lift gamma0 (family.q gamma0)
  all_goals simp only [secantParameter]
  all_goals ring

/-- All canonical secants through one base endpoint form a collapsed cluster
relative to any two fixed members of that common-base family. -/
theorem commonBase_secants_form_collapsed_cluster
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma0 beta0 beta1 : F) :
    ∀ beta : F,
      lineDeterminant
          (secantParameter family gamma0 beta0)
          (secantParameter family gamma0 beta1)
          (secantParameter family gamma0 beta) = 0 := by
  intro beta
  exact three_commonBase_secants_lineDeterminant_eq_zero
    family gamma0 beta0 beta1 beta

/-! ## Pointwise transversality -/

/-- **Common-base secant slopes separate at a base mismatch.**  If two
partner polynomials agree with their respective received affine combinations
at `x`, while the shared base polynomial misses there, then their canonical
common-base secant slopes have different evaluations at `x`. -/
theorem commonBase_secantSlope_eval_ne_of_baseMismatch
    {F : Type} [Field F]
    {gamma0 beta beta' : F}
    (hbeta : gamma0 ≠ beta) (hbeta' : gamma0 ≠ beta')
    (hbb' : beta ≠ beta')
    (q0 q q' : F[X]) (u0 u1 x : F)
    (hq : q.eval x = u0 + beta * u1)
    (hq' : q'.eval x = u0 + beta' * u1)
    (hmiss : q0.eval x ≠ u0 + gamma0 * u1) :
    (slopePolynomial gamma0 beta q0 q).eval x ≠
      (slopePolynomial gamma0 beta' q0 q').eval x := by
  intro heq
  simp only [slopePolynomial, eval_mul, eval_C, eval_sub] at heq
  rw [hq, hq'] at heq
  have hd : q0.eval x - (u0 + gamma0 * u1) ≠ 0 :=
    sub_ne_zero.mpr hmiss
  have hb : gamma0 - beta ≠ 0 := sub_ne_zero.mpr hbeta
  have hb' : gamma0 - beta' ≠ 0 := sub_ne_zero.mpr hbeta'
  have hfactor :
      (beta - beta') * (q0.eval x - (u0 + gamma0 * u1)) = 0 := by
    field_simp [hb, hb'] at heq
    linear_combination heq
  exact (mul_ne_zero (sub_ne_zero.mpr hbb') hd) hfactor

/-- Family-facing `href` adapter for the collapsed-cluster injection.  Two
distinct common-base canonical secants are pointwise transverse at every
coordinate where both partner codewords agree and the base codeword misses. -/
theorem commonBase_secantDirection_sub_eval_ne_zero
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma0 beta beta' : F}
    (hbeta : gamma0 ≠ beta) (hbeta' : gamma0 ≠ beta')
    (hbb' : beta ≠ beta') (i : iota)
    (hagree : (family.q beta).eval (dom i) = u 0 i + beta * u 1 i)
    (hagree' : (family.q beta').eval (dom i) = u 0 i + beta' * u 1 i)
    (hmiss : (family.q gamma0).eval (dom i) ≠
      u 0 i + gamma0 * u 1 i) :
    (((secantParameter family gamma0 beta).2 -
        (secantParameter family gamma0 beta').2).eval (dom i)) ≠ 0 := by
  rw [eval_sub, sub_ne_zero]
  simpa only [secantParameter] using
    commonBase_secantSlope_eval_ne_of_baseMismatch
      hbeta hbeta' hbb' (family.q gamma0) (family.q beta)
        (family.q beta') (u 0 i) (u 1 i) (dom i) hagree hagree' hmiss

/-! ## Degenerate-cluster injection no-go -/

/-- In a common-lift cluster, a pair equation for a scalar different from the
common base forces the two line directions to agree at that coordinate.  Thus
the transverse-petal premise of the generic collapsed-cluster injection is
incompatible with using two common-base lines as source and target for a
nonbase scalar. -/
theorem commonLift_pairEquation_forces_direction_eval_eq
    {F : Type} [Field F]
    (gamma0 gamma x : F) (q0 : F[X])
    (source target : PolynomialLine F)
    (hgamma : gamma ≠ gamma0)
    (hsource : q0 = source.1 + C gamma0 * source.2)
    (htarget : q0 = target.1 + C gamma0 * target.2)
    (hequation :
      (source.1 - target.1).eval x +
        gamma * (source.2 - target.2).eval x = 0) :
    (source.2 - target.2).eval x = 0 := by
  have ha : source.1 - target.1 =
      -C gamma0 * (source.2 - target.2) := by
    linear_combination -hsource + htarget
  rw [ha, eval_mul, eval_neg, eval_C] at hequation
  have hfactor : (gamma - gamma0) *
      (source.2 - target.2).eval x = 0 := by
    linear_combination hequation
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hgamma)

/-- Explicit contradiction form: no nonbase scalar can have a transverse pair
equation between two members of one common-base collapsed cluster. -/
theorem commonLift_no_transverse_pairEquation
    {F : Type} [Field F]
    (gamma0 gamma x : F) (q0 : F[X])
    (source target : PolynomialLine F)
    (hgamma : gamma ≠ gamma0)
    (hsource : q0 = source.1 + C gamma0 * source.2)
    (htarget : q0 = target.1 + C gamma0 * target.2)
    (htrans : (source.2 - target.2).eval x ≠ 0) :
    (source.1 - target.1).eval x +
        gamma * (source.2 - target.2).eval x ≠ 0 := by
  intro hequation
  exact htrans (commonLift_pairEquation_forces_direction_eval_eq
    gamma0 gamma x q0 source target hgamma hsource htarget hequation)

/-! ## Direct Möbius-label charge no-go -/

/-- Direction value carried at one common-base mismatch coordinate. -/
noncomputable def mobiusDirectionValue
    {F : Type} [Field F] (gamma0 u1 mismatch gamma : F) : F :=
  u1 + (gamma - gamma0)⁻¹ * mismatch

/-- At a nonzero base mismatch, the direction value at one fixed coordinate
is injective in the nonbase rider.  Consequently a coordinate can carry many
different riders with distinct direction labels; forgetting the label cannot
give a coordinate-only injection. -/
theorem mobiusDirectionValue_injOn_nonbase
    {F : Type} [Field F] (gamma0 u1 mismatch : F)
    (hmismatch : mismatch ≠ 0) :
    Set.InjOn (mobiusDirectionValue gamma0 u1 mismatch)
      {gamma : F | gamma ≠ gamma0} := by
  intro gamma hgamma beta hbeta heq
  simp only [Set.mem_setOf_eq] at hgamma hbeta
  simp only [mobiusDirectionValue] at heq
  have hinv : (gamma - gamma0)⁻¹ = (beta - gamma0)⁻¹ := by
    apply mul_right_cancel₀ hmismatch
    linear_combination heq
  have hsub : gamma - gamma0 = beta - gamma0 := inv_injective hinv
  linear_combination hsub

/-! ## External-line determinant factorization -/

/-- **External defect factorization.**  Relative to two lines through the
same lifted point `(gamma0,q0)`, the three-line determinant is the product of
their direction difference and the polynomial defect measuring whether the
external line also passes through that lifted point. -/
theorem lineDeterminant_commonLift_factorization
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2) :
    lineDeterminant line0 line1 external =
      (line1.2 - line0.2) *
        (q0 - (external.1 + C gamma0 * external.2)) := by
  have ha0 : line0.1 = q0 - C gamma0 * line0.2 := by
    linear_combination -hline0
  have ha1 : line1.1 = q0 - C gamma0 * line1.2 := by
    linear_combination -hline1
  rw [lineDeterminant, ha0, ha1]
  ring

/-- Two distinct lines through one lifted point necessarily have distinct
direction polynomials. -/
theorem direction_ne_of_commonLift_line_ne
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1) : line1.2 ≠ line0.2 := by
  intro hdir
  apply hne
  apply Prod.ext
  · linear_combination -hline0 + hline1 + C gamma0 * hdir
  · exact hdir.symm

/-- Distinct degree-`<k` common-lift lines have joint cores intersecting in at
most `k-1` coordinates, witnessed by their nonzero direction difference. -/
theorem distinct_commonLift_coreInter_card_le_pred
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hr0 : line0.2.natDegree < k)
    (hr1 : line1.2.natDegree < k) :
    (jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 line1.1 line1.2).card ≤ k - 1 := by
  let p := line1.2 - line0.2
  have hp0 : p ≠ 0 := sub_ne_zero.mpr
    (direction_ne_of_commonLift_line_ne
      gamma0 q0 line0 line1 hline0 hline1 hne)
  have hpdeg : p.natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hr1 hr0)
  have hsub :
      jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line1.1 line1.2 ⊆
        Finset.univ.filter fun i => p.eval (dom i) = 0 := by
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi ⊢
    simp only [p, eval_sub, hi.2.2, hi.1.2, sub_self]
  exact (Finset.card_le_card hsub).trans
    (domain_root_card_le_pred dom hk p hp0 hpdeg)

/-- **Maximality of a nondegenerate common-lift cluster.**  If the two
reference directions are distinct, an external line determinant-collapses
with them exactly only if it passes through the same lifted base point. -/
theorem external_commonLift_of_lineDeterminant_eq_zero
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hdirection : line1.2 ≠ line0.2)
    (hdet : lineDeterminant line0 line1 external = 0) :
    q0 = external.1 + C gamma0 * external.2 := by
  rw [lineDeterminant_commonLift_factorization
    gamma0 q0 line0 line1 external hline0 hline1] at hdet
  have hdir : line1.2 - line0.2 ≠ 0 := sub_ne_zero.mpr hdirection
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hdir)

/-- Distinct-reference form of common-lift maximality. -/
theorem external_commonLift_of_distinct_commonLift_determinant_zero
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hdet : lineDeterminant line0 line1 external = 0) :
    q0 = external.1 + C gamma0 * external.2 := by
  exact external_commonLift_of_lineDeterminant_eq_zero
    gamma0 q0 line0 line1 external hline0 hline1
      (direction_ne_of_commonLift_line_ne
        gamma0 q0 line0 line1 hline0 hline1 hne) hdet

/-- The external common-lift defect retains the original degree bound `<k`;
the factorization therefore exposes two separate one-degree budgets rather
than one opaque determinant budget of size `2(k-1)`. -/
theorem commonLift_externalDefect_natDegree_lt
    {F : Type} [Field F] {k : Nat}
    (gamma0 : F) (q0 : F[X]) (external : PolynomialLine F)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k) :
    (q0 - (external.1 + C gamma0 * external.2)).natDegree < k := by
  have hCmul : (C gamma0 * external.2).natDegree ≤
      external.2.natDegree := by
    calc
      _ ≤ (C gamma0).natDegree + external.2.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ external.2.natDegree := by simp
  have hadd : (external.1 + C gamma0 * external.2).natDegree < k := by
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      (max_lt ha (hCmul.trans_lt hr))
  exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    (max_lt hq0 hadd)

/-- **External defect root-count consumer.**  If the base polynomial's full
agreement and an external line core meet in at least `k` coordinates, the
degree-`<k` external defect vanishes identically, so the external line joins
the common-lift cluster. -/
theorem external_commonLift_of_k_le_baseAgreement_inter_jointCore
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (external : PolynomialLine F)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hlarge : k ≤
      (fullAgreement dom u0 u1 gamma0 q0 ∩
        jointCore dom u0 u1 external.1 external.2).card) :
    q0 = external.1 + C gamma0 * external.2 := by
  by_contra hoff
  have hcap := fullAgreement_inter_jointCore_card_le
    dom u0 u1 hk hq0 ha hr hoff
  omega

/-- A common-lift line core is contained in the full agreement set of the
shared lifted base polynomial. -/
theorem commonLift_jointCore_subset_baseAgreement
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (gamma0 : F) (q0 : F[X]) (line : PolynomialLine F)
    (hline : q0 = line.1 + C gamma0 * line.2) :
    jointCore dom u0 u1 line.1 line.2 ⊆
      fullAgreement dom u0 u1 gamma0 q0 := by
  intro i hi
  simp only [jointCore, fullAgreement, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi ⊢
  rw [hline, eval_add, eval_mul, eval_C, hi.1, hi.2]

/-- **Two-reference external-overlap cap.**  For a genuinely external line,
all coordinates where its core meets either of two common-lift reference cores
are roots of the *single* external-defect polynomial.  Their union therefore
has size at most `k-1`, rather than requiring an opaque determinant budget. -/
theorem two_commonLift_coreInter_external_union_card_le_pred
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hexternal : q0 ≠ external.1 + C gamma0 * external.2) :
    ((jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 external.1 external.2) ∪
        (jointCore dom u0 u1 line1.1 line1.2 ∩
          jointCore dom u0 u1 external.1 external.2)).card ≤ k - 1 := by
  let B := fullAgreement dom u0 u1 gamma0 q0
  let E := jointCore dom u0 u1 external.1 external.2
  have hsub :
      (jointCore dom u0 u1 line0.1 line0.2 ∩ E) ∪
          (jointCore dom u0 u1 line1.1 line1.2 ∩ E) ⊆ B ∩ E := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_inter] at hi ⊢
    rcases hi with hi | hi
    · exact ⟨commonLift_jointCore_subset_baseAgreement
        dom u0 u1 gamma0 q0 line0 hline0 hi.1, hi.2⟩
    · exact ⟨commonLift_jointCore_subset_baseAgreement
        dom u0 u1 gamma0 q0 line1 hline1 hi.1, hi.2⟩
  have hcap := fullAgreement_inter_jointCore_card_le
    dom u0 u1 hk hq0 ha hr hexternal
  exact (Finset.card_le_card hsub).trans (by simpa only [B, E] using hcap)

/-- **Arbitrary common-lift cluster overlap cap.**  Adding any number of
common-lift cores does not enlarge the external overlap budget: their whole
union still meets a genuinely external core in at most `k-1` coordinates. -/
theorem commonLift_coreUnion_inter_external_card_le_pred
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (lines : Finset (PolynomialLine F)) (external : PolynomialLine F)
    (hlines : ∀ line ∈ lines,
      q0 = line.1 + C gamma0 * line.2)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hexternal : q0 ≠ external.1 + C gamma0 * external.2) :
    ((lines.biUnion fun line =>
        jointCore dom u0 u1 line.1 line.2) ∩
      jointCore dom u0 u1 external.1 external.2).card ≤ k - 1 := by
  let B := fullAgreement dom u0 u1 gamma0 q0
  let E := jointCore dom u0 u1 external.1 external.2
  have hsub :
      (lines.biUnion fun line => jointCore dom u0 u1 line.1 line.2) ∩ E ⊆
        B ∩ E := by
    intro i hi
    simp only [Finset.mem_inter, Finset.mem_biUnion] at hi ⊢
    obtain ⟨line, hline, hiLine⟩ := hi.1
    exact ⟨commonLift_jointCore_subset_baseAgreement
      dom u0 u1 gamma0 q0 line (hlines line hline) hiLine, hi.2⟩
  have hcap := fullAgreement_inter_jointCore_card_le
    dom u0 u1 hk hq0 ha hr hexternal
  exact (Finset.card_le_card hsub).trans (by simpa only [B, E] using hcap)

/-- **Cluster-union closure criterion.**  If the common-lift core union and an
external core have combined size at least `|iota|+k`, their forced overlap has
`k` coordinates, so the external line must join the cluster. -/
theorem external_commonLift_of_coreUnion_add_core_ge_domain_add_k
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (lines : Finset (PolynomialLine F)) (external : PolynomialLine F)
    (hlines : ∀ line ∈ lines,
      q0 = line.1 + C gamma0 * line.2)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hlarge : Fintype.card iota + k ≤
      (lines.biUnion fun line => jointCore dom u0 u1 line.1 line.2).card +
        (jointCore dom u0 u1 external.1 external.2).card) :
    q0 = external.1 + C gamma0 * external.2 := by
  by_contra hexternal
  have hcap := commonLift_coreUnion_inter_external_card_le_pred
    dom u0 u1 hk gamma0 q0 lines external hlines hq0 ha hr hexternal
  have hunion := Finset.card_union_add_card_inter
    (lines.biUnion fun line => jointCore dom u0 u1 line.1 line.2)
    (jointCore dom u0 u1 external.1 external.2)
  have hunionLe :
      ((lines.biUnion fun line => jointCore dom u0 u1 line.1 line.2) ∪
        jointCore dom u0 u1 external.1 external.2).card ≤
          Fintype.card iota := Finset.card_le_univ _
  omega

/-- **Three-core mass closure with identified factors.**  Two common-lift
reference cores spend at most one `k-1` budget on their mutual overlap, while
a genuinely external core spends at most one `k-1` budget meeting their
union.  Total core mass above `|iota|+2(k-1)` therefore forces the third line
to join the common-lift cluster. -/
theorem external_commonLift_of_twoReference_coreMass_gt
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hrefInter :
      (jointCore dom u0 u1 line0.1 line0.2 ∩
        jointCore dom u0 u1 line1.1 line1.2).card ≤ k - 1)
    (hlarge : Fintype.card iota + 2 * (k - 1) <
      (jointCore dom u0 u1 line0.1 line0.2).card +
        (jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 external.1 external.2).card) :
    q0 = external.1 + C gamma0 * external.2 := by
  by_contra hexternal
  let D0 := jointCore dom u0 u1 line0.1 line0.2
  let D1 := jointCore dom u0 u1 line1.1 line1.2
  let E := jointCore dom u0 u1 external.1 external.2
  let A := D0 ∪ D1
  have hExtCap : (A ∩ E).card ≤ k - 1 := by
    simpa only [A, D0, D1, E, Finset.union_inter_distrib_right] using
      two_commonLift_coreInter_external_union_card_le_pred
        dom u0 u1 hk gamma0 q0 line0 line1 external
          hline0 hline1 hq0 ha hr hexternal
  have hbookRef := Finset.card_union_add_card_inter D0 D1
  have hbookExt := Finset.card_union_add_card_inter A E
  have hunionLe : (A ∪ E).card ≤ Fintype.card iota :=
    Finset.card_le_univ _
  change A.card + (D0 ∩ D1).card = D0.card + D1.card at hbookRef
  change (A ∪ E).card + (A ∩ E).card = A.card + E.card at hbookExt
  change (D0 ∩ D1).card ≤ k - 1 at hrefInter
  change Fintype.card iota + 2 * (k - 1) < D0.card + D1.card + E.card at hlarge
  omega

/-- Degree-facing form of the three-core mass closure: the reference-core
intersection budget is discharged automatically from distinctness. -/
theorem external_commonLift_of_distinct_twoReference_coreMass_gt
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hq0 : q0.natDegree < k)
    (hr0 : line0.2.natDegree < k)
    (hr1 : line1.2.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hlarge : Fintype.card iota + 2 * (k - 1) <
      (jointCore dom u0 u1 line0.1 line0.2).card +
        (jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 external.1 external.2).card) :
    q0 = external.1 + C gamma0 * external.2 := by
  apply external_commonLift_of_twoReference_coreMass_gt
    dom u0 u1 hk gamma0 q0 line0 line1 external
      hline0 hline1 hq0 ha hr
  · exact distinct_commonLift_coreInter_card_le_pred
      dom u0 u1 hk gamma0 q0 line0 line1 hline0 hline1 hne hr0 hr1
  · exact hlarge

/-! ## Noncollapsed heavy triples are near-covers -/

/-- A noncollapsed degree-`<k` triple with each core of size at least `h`
must have core union of size at least `3h-2(k-1)`.  This is the exact
weighted-overlap identity combined with the determinant multiplicity cap. -/
theorem threeCoreUnion_card_ge_of_determinant_ne_zero
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k h : Nat} (hk : 1 ≤ k)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hdet : lineDeterminant line0 line1 line2 ≠ 0)
    (hcore0 : h ≤ (jointCore dom u0 u1 line0.1 line0.2).card)
    (hcore1 : h ≤ (jointCore dom u0 u1 line1.1 line1.2).card)
    (hcore2 : h ≤ (jointCore dom u0 u1 line2.1 line2.2).card) :
    3 * h - 2 * (k - 1) ≤
      (coreUnion dom u0 u1 line0 line1 line2).card := by
  have hcap := pairOverlap_card_add_tripleOverlap_card_le_two_mul_pred
    hk dom u0 u1 line0 line1 line2 hdeg hdet
  have hid := pairOverlap_card_add_tripleOverlap_card_add_coreUnion_card
    dom u0 u1 line0 line1 line2
  omega

/-- **Two-factor support saturation.**  For distinct common-lift references
and a genuinely external line, full weighted-overlap saturation forces both
the reference-direction root support and the external-defect root support to
have exactly `k-1` coordinates. -/
theorem twoFactorSupports_eq_pred_of_weightedOverlap_eq_fullBudget
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hq0 : q0.natDegree < k)
    (hr0 : line0.2.natDegree < k)
    (hr1 : line1.2.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hexternal : q0 ≠ external.1 + C gamma0 * external.2)
    (hsaturated :
      (pairOverlap dom u0 u1 line0 line1 external).card +
        (tripleOverlap dom u0 u1 line0 line1 external).card =
          2 * (k - 1)) :
    (jointCore dom u0 u1 line0.1 line0.2 ∩
        jointCore dom u0 u1 line1.1 line1.2).card = k - 1 ∧
      ((jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 external.1 external.2) ∪
        (jointCore dom u0 u1 line1.1 line1.2 ∩
          jointCore dom u0 u1 external.1 external.2)).card = k - 1 := by
  have hrefCap := distinct_commonLift_coreInter_card_le_pred
    dom u0 u1 hk gamma0 q0 line0 line1 hline0 hline1 hne hr0 hr1
  have hextCap := two_commonLift_coreInter_external_union_card_le_pred
    dom u0 u1 hk gamma0 q0 line0 line1 external
      hline0 hline1 hq0 ha hr hexternal
  have hsplit := pairOverlap_add_tripleOverlap_eq_twoFactorSupports
    dom u0 u1 line0 line1 external
  omega

/-- **Concrete two-locator normal form.**  Under full two-factor support
saturation, both determinant factors are nonzero scalar multiples of the
locators of their exact coordinate supports. -/
theorem twoFactor_eq_scalar_mul_domainLocators_of_fullBudget
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hq0 : q0.natDegree < k)
    (hr0 : line0.2.natDegree < k)
    (hr1 : line1.2.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hexternal : q0 ≠ external.1 + C gamma0 * external.2)
    (hsaturated :
      (pairOverlap dom u0 u1 line0 line1 external).card +
        (tripleOverlap dom u0 u1 line0 line1 external).card =
          2 * (k - 1)) :
    let R := jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 line1.1 line1.2
    let Q := (jointCore dom u0 u1 line0.1 line0.2 ∩
        jointCore dom u0 u1 external.1 external.2) ∪
      (jointCore dom u0 u1 line1.1 line1.2 ∩
        jointCore dom u0 u1 external.1 external.2)
    ∃ cRef cDef : F, cRef ≠ 0 ∧ cDef ≠ 0 ∧
      line1.2 - line0.2 = C cRef * domainLocator dom R ∧
      q0 - (external.1 + C gamma0 * external.2) =
        C cDef * domainLocator dom Q := by
  dsimp only
  let R := jointCore dom u0 u1 line0.1 line0.2 ∩
    jointCore dom u0 u1 line1.1 line1.2
  let Q := (jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 external.1 external.2) ∪
    (jointCore dom u0 u1 line1.1 line1.2 ∩
      jointCore dom u0 u1 external.1 external.2)
  let pRef := line1.2 - line0.2
  let pDef := q0 - (external.1 + C gamma0 * external.2)
  have hcards := twoFactorSupports_eq_pred_of_weightedOverlap_eq_fullBudget
    dom u0 u1 hk gamma0 q0 line0 line1 external hline0 hline1 hne
      hq0 hr0 hr1 ha hr hexternal hsaturated
  change R.card = k - 1 ∧ Q.card = k - 1 at hcards
  have hpRef0 : pRef ≠ 0 := sub_ne_zero.mpr
    (direction_ne_of_commonLift_line_ne
      gamma0 q0 line0 line1 hline0 hline1 hne)
  have hpDef0 : pDef ≠ 0 := sub_ne_zero.mpr hexternal
  have hpRefLt : pRef.natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hr1 hr0)
  have hpDefLt : pDef.natDegree < k := by
    exact commonLift_externalDefect_natDegree_lt gamma0 q0 external hq0 ha hr
  have hrootRef : ∀ i ∈ R, pRef.eval (dom i) = 0 := by
    intro i hi
    simp only [R, Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [pRef, eval_sub, hi.2.2, hi.1.2, sub_self]
  have hrootDef : ∀ i ∈ Q, pDef.eval (dom i) = 0 := by
    intro i hi
    simp only [Q, Finset.mem_union, Finset.mem_inter] at hi
    rcases hi with hi | hi
    · have hbase := commonLift_jointCore_subset_baseAgreement
        dom u0 u1 gamma0 q0 line0 hline0 hi.1
      simp only [fullAgreement, jointCore, Finset.mem_filter,
        Finset.mem_univ, true_and] at hbase hi
      simp only [pDef, eval_sub, eval_add, eval_mul, eval_C,
        hbase, hi.2.1, hi.2.2]
      ring
    · have hbase := commonLift_jointCore_subset_baseAgreement
        dom u0 u1 gamma0 q0 line1 hline1 hi.1
      simp only [fullAgreement, jointCore, Finset.mem_filter,
        Finset.mem_univ, true_and] at hbase hi
      simp only [pDef, eval_sub, eval_add, eval_mul, eval_C,
        hbase, hi.2.1, hi.2.2]
      ring
  have hpRefDeg : pRef.natDegree = R.card := by
    rw [hcards.1]
    exact natDegree_eq_pred_of_rootSupport_card_eq_pred
      dom hk pRef hpRef0 hpRefLt R (by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hrootRef i hi) hcards.1
  have hpDefDeg : pDef.natDegree = Q.card := by
    rw [hcards.2]
    exact natDegree_eq_pred_of_rootSupport_card_eq_pred
      dom hk pDef hpDef0 hpDefLt Q (by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hrootDef i hi) hcards.2
  obtain ⟨cRef, hcRef, hRef⟩ :=
    eq_C_mul_domainLocator_of_natDegree_eq_card
      dom R pRef hpRef0 hpRefDeg hrootRef
  obtain ⟨cDef, hcDef, hDef⟩ :=
    eq_C_mul_domainLocator_of_natDegree_eq_card
      dom Q pDef hpDef0 hpDefDeg hrootDef
  exact ⟨cRef, cDef, hcRef, hcDef, hRef, hDef⟩

/-- **Saturated determinant locator product.**  In the full-budget case the
entire three-line determinant is a nonzero scalar times the product of the
reference and external support locators. -/
theorem lineDeterminant_eq_scalar_mul_two_domainLocators_of_fullBudget
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    {k : Nat} (hk : 1 ≤ k) (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hq0 : q0.natDegree < k)
    (hr0 : line0.2.natDegree < k)
    (hr1 : line1.2.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k)
    (hexternal : q0 ≠ external.1 + C gamma0 * external.2)
    (hsaturated :
      (pairOverlap dom u0 u1 line0 line1 external).card +
        (tripleOverlap dom u0 u1 line0 line1 external).card =
          2 * (k - 1)) :
    let R := jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 line1.1 line1.2
    let Q := (jointCore dom u0 u1 line0.1 line0.2 ∩
        jointCore dom u0 u1 external.1 external.2) ∪
      (jointCore dom u0 u1 line1.1 line1.2 ∩
        jointCore dom u0 u1 external.1 external.2)
    ∃ c : F, c ≠ 0 ∧
      lineDeterminant line0 line1 external =
        C c * domainLocator dom R * domainLocator dom Q := by
  dsimp only
  obtain ⟨cRef, cDef, hcRef, hcDef, hRef, hDef⟩ :=
    twoFactor_eq_scalar_mul_domainLocators_of_fullBudget
      dom u0 u1 hk gamma0 q0 line0 line1 external hline0 hline1 hne
        hq0 hr0 hr1 ha hr hexternal hsaturated
  refine ⟨cRef * cDef, mul_ne_zero hcRef hcDef, ?_⟩
  rw [lineDeterminant_commonLift_factorization
    gamma0 q0 line0 line1 external hline0 hline1, hRef, hDef, C_mul]
  ring

/-- Repackage a two-factor locator form as the canonical simple-root
`pairOverlap` locator times the extra-multiplicity `tripleOverlap` locator. -/
theorem twoFactor_locatorForm_eq_pairOverlap_mul_tripleOverlap
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 external : PolynomialLine F) (c : F)
    (hform :
      let R := jointCore dom u0 u1 line0.1 line0.2 ∩
        jointCore dom u0 u1 line1.1 line1.2
      let Q := (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 external.1 external.2) ∪
        (jointCore dom u0 u1 line1.1 line1.2 ∩
          jointCore dom u0 u1 external.1 external.2)
      lineDeterminant line0 line1 external =
        C c * domainLocator dom R * domainLocator dom Q) :
    lineDeterminant line0 line1 external =
      C c * domainLocator dom (pairOverlap dom u0 u1 line0 line1 external) *
        domainLocator dom (tripleOverlap dom u0 u1 line0 line1 external) := by
  dsimp only at hform
  let R := jointCore dom u0 u1 line0.1 line0.2 ∩
    jointCore dom u0 u1 line1.1 line1.2
  let Q := (jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 external.1 external.2) ∪
    (jointCore dom u0 u1 line1.1 line1.2 ∩
      jointCore dom u0 u1 external.1 external.2)
  have hU := twoFactorSupport_union_eq_pairOverlap
    dom u0 u1 line0 line1 external
  have hI := twoFactorSupport_inter_eq_tripleOverlap
    dom u0 u1 line0 line1 external
  change R ∪ Q = pairOverlap dom u0 u1 line0 line1 external at hU
  change R ∩ Q = tripleOverlap dom u0 u1 line0 line1 external at hI
  have hloc := domainLocator_union_mul_inter dom R Q
  rw [hU, hI] at hloc
  rw [hform]
  calc
    C c * domainLocator dom R * domainLocator dom Q =
        C c * (domainLocator dom R * domainLocator dom Q) := by ring
    _ = C c * (domainLocator dom
          (pairOverlap dom u0 u1 line0 line1 external) *
        domainLocator dom
          (tripleOverlap dom u0 u1 line0 line1 external)) := by rw [hloc]
    _ = _ := by ring

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

#print axioms weightedOverlap_eq_referenceInter_add_externalInterUnion
#print axioms pairOverlap_add_tripleOverlap_eq_twoFactorSupports
#print axioms natDegree_eq_pred_of_rootSupport_card_eq_pred
#print axioms domainLocator_ne_zero
#print axioms domainLocator_natDegree
#print axioms domainLocator_union_mul_inter
#print axioms twoFactorSupport_union_eq_pairOverlap
#print axioms twoFactorSupport_inter_eq_tripleOverlap
#print axioms domainLocator_dvd_of_eval_eq_zero
#print axioms eq_C_mul_domainLocator_of_natDegree_eq_card
#print axioms lineDeterminant_eq_zero_of_common_lift
#print axioms three_commonBase_secants_lineDeterminant_eq_zero
#print axioms commonBase_secants_form_collapsed_cluster
#print axioms commonBase_secantSlope_eval_ne_of_baseMismatch
#print axioms commonBase_secantDirection_sub_eval_ne_zero
#print axioms commonLift_pairEquation_forces_direction_eval_eq
#print axioms commonLift_no_transverse_pairEquation
#print axioms mobiusDirectionValue_injOn_nonbase
#print axioms lineDeterminant_commonLift_factorization
#print axioms direction_ne_of_commonLift_line_ne
#print axioms distinct_commonLift_coreInter_card_le_pred
#print axioms external_commonLift_of_lineDeterminant_eq_zero
#print axioms external_commonLift_of_distinct_commonLift_determinant_zero
#print axioms commonLift_externalDefect_natDegree_lt
#print axioms external_commonLift_of_k_le_baseAgreement_inter_jointCore
#print axioms commonLift_jointCore_subset_baseAgreement
#print axioms two_commonLift_coreInter_external_union_card_le_pred
#print axioms commonLift_coreUnion_inter_external_card_le_pred
#print axioms external_commonLift_of_coreUnion_add_core_ge_domain_add_k
#print axioms external_commonLift_of_twoReference_coreMass_gt
#print axioms external_commonLift_of_distinct_twoReference_coreMass_gt
#print axioms threeCoreUnion_card_ge_of_determinant_ne_zero
#print axioms twoFactorSupports_eq_pred_of_weightedOverlap_eq_fullBudget
#print axioms twoFactor_eq_scalar_mul_domainLocators_of_fullBudget
#print axioms lineDeterminant_eq_scalar_mul_two_domainLocators_of_fullBudget
#print axioms twoFactor_locatorForm_eq_pairOverlap_mul_tripleOverlap
