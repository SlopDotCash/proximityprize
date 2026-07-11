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

/-- If every pair is related by one of two equivalence relations, then one of
the relations is universal.  Applied to the two cancellation outcomes below,
this says that a rider family with no `Q`-charged pair lies in one polynomial
pencil through one of the two base lifts. -/
theorem one_universal_of_pair_covered_by_two_equivalences
    {V : Type} [Nonempty V] (R S : V → V → Prop)
    (hRsymm : ∀ {x y}, R x y → R y x)
    (hRtrans : ∀ {x y z}, R x y → R y z → R x z)
    (hSsymm : ∀ {x y}, S x y → S y x)
    (hStrans : ∀ {x y z}, S x y → S y z → S x z)
    (hcover : ∀ x y, R x y ∨ S x y) :
    (∀ x y, R x y) ∨ ∀ x y, S x y := by
  by_cases hRuniv : ∀ x y, R x y
  · exact Or.inl hRuniv
  · apply Or.inr
    push_neg at hRuniv
    obtain ⟨x, y, hxy⟩ := hRuniv
    have hSxy : S x y := (hcover x y).resolve_left hxy
    have hAllSx : ∀ z, S z x := by
      intro z
      by_contra hSzx
      have hRzx : R z x := (hcover z x).resolve_right hSzx
      have hSzy : ¬ S z y := by
        intro hzy
        exact hSzx (hStrans hzy (hSsymm hSxy))
      have hRzy : R z y := (hcover z y).resolve_right hSzy
      exact hxy (hRtrans (hRsymm hRzx) hRzy)
    intro z w
    exact hStrans (hAllSx z) (hSsymm (hAllSx w))

/-- Normalized polynomial slope from a lifted base point. -/
noncomputable def normalizedPolynomialSlope
    {F : Type} [Field F] (gamma0 : F) (q0 : F[X])
    (gamma : F) (p : F[X]) : F[X] :=
  C ((gamma - gamma0)⁻¹) * (p - q0)

/-- The denominator-cleared common-base collinearity equation is exactly
equality of normalized polynomial slopes away from the base rider. -/
theorem commonBase_collinear_iff_normalizedPolynomialSlope_eq
    {F : Type} [Field F]
    (gamma0 gamma delta : F) (q0 pGamma pDelta : F[X])
    (hgamma : gamma ≠ gamma0) (hdelta : delta ≠ gamma0) :
    C (delta - gamma0) * pGamma -
          C (gamma - gamma0) * pDelta = C (delta - gamma) * q0 ↔
      normalizedPolynomialSlope gamma0 q0 gamma pGamma =
        normalizedPolynomialSlope gamma0 q0 delta pDelta := by
  let alpha := gamma - gamma0
  let beta := delta - gamma0
  have halpha : alpha ≠ 0 := sub_ne_zero.mpr hgamma
  have hbeta : beta ≠ 0 := sub_ne_zero.mpr hdelta
  have hCalpha : C alpha ≠ (0 : F[X]) := C_ne_zero.mpr halpha
  have hCbeta : C beta ≠ (0 : F[X]) := C_ne_zero.mpr hbeta
  have hcoefAlpha : C alpha * C beta * C alpha⁻¹ = (C beta : F[X]) := by
    rw [← C_mul, ← C_mul]
    field_simp
  have hcoefBeta : C alpha * C beta * C beta⁻¹ = (C alpha : F[X]) := by
    rw [← C_mul, ← C_mul]
    field_simp
  have hcross :
      C (delta - gamma0) * pGamma -
            C (gamma - gamma0) * pDelta = C (delta - gamma) * q0 ↔
        C beta * (pGamma - q0) = C alpha * (pDelta - q0) := by
    simp only [alpha, beta, map_sub]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  constructor
  · intro h
    apply mul_left_cancel₀ (mul_ne_zero hCalpha hCbeta)
    change (C alpha * C beta) *
        (C alpha⁻¹ * (pGamma - q0)) =
      (C alpha * C beta) * (C beta⁻¹ * (pDelta - q0))
    rw [← mul_assoc, hcoefAlpha, ← mul_assoc, hcoefBeta]
    exact hcross.mp h
  · intro h
    have hm := congrArg
      (fun p : F[X] => (C alpha * C beta) * p) h
    apply hcross.mpr
    change (C alpha * C beta) *
        (C alpha⁻¹ * (pGamma - q0)) =
      (C alpha * C beta) * (C beta⁻¹ * (pDelta - q0)) at hm
    rwa [← mul_assoc, hcoefAlpha, ← mul_assoc, hcoefBeta] at hm

/-- **Global two-pencil collapse.**  If every rider pair is polynomially
collinear through one of two fixed lifted base polynomials, then the entire
family lies in one of those two pencils.  This is the global consumer for a
trichotomy family with no `Q`-charged edge. -/
theorem family_universal_pencil_of_pair_covered_by_two_baseCollinearities
    {V F : Type} [Nonempty V] [Field F]
    (gamma0 : F) (qA qB : F[X])
    (gamma : V → F) (p : V → F[X])
    (hnonbase : ∀ x, gamma x ≠ gamma0)
    (hcover : ∀ x y,
      (C (gamma y - gamma0) * p x -
          C (gamma x - gamma0) * p y = C (gamma y - gamma x) * qA) ∨
      (C (gamma y - gamma0) * p x -
          C (gamma x - gamma0) * p y = C (gamma y - gamma x) * qB)) :
    (∀ x y,
      normalizedPolynomialSlope gamma0 qA (gamma x) (p x) =
        normalizedPolynomialSlope gamma0 qA (gamma y) (p y)) ∨
      ∀ x y,
        normalizedPolynomialSlope gamma0 qB (gamma x) (p x) =
          normalizedPolynomialSlope gamma0 qB (gamma y) (p y) := by
  let R : V → V → Prop := fun x y =>
    normalizedPolynomialSlope gamma0 qA (gamma x) (p x) =
      normalizedPolynomialSlope gamma0 qA (gamma y) (p y)
  let S : V → V → Prop := fun x y =>
    normalizedPolynomialSlope gamma0 qB (gamma x) (p x) =
      normalizedPolynomialSlope gamma0 qB (gamma y) (p y)
  have hpair : ∀ x y, R x y ∨ S x y := by
    intro x y
    rcases hcover x y with hA | hB
    · exact Or.inl
        ((commonBase_collinear_iff_normalizedPolynomialSlope_eq
          gamma0 (gamma x) (gamma y) qA (p x) (p y)
            (hnonbase x) (hnonbase y)).mp hA)
    · exact Or.inr
        ((commonBase_collinear_iff_normalizedPolynomialSlope_eq
          gamma0 (gamma x) (gamma y) qB (p x) (p y)
            (hnonbase x) (hnonbase y)).mp hB)
  have hout := one_universal_of_pair_covered_by_two_equivalences R S
    (fun h => h.symm) (fun hxy hyz => hxy.trans hyz)
    (fun h => h.symm) (fun hxy hyz => hxy.trans hyz) hpair
  simpa only [R, S] using hout

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

/-- Split a locator into the coordinates shared with `T` and the remaining
coordinates.  This is the polynomial gcd factorization used to reduce
varying-bin two-rider Padé identities. -/
theorem domainLocator_eq_inter_mul_sdiff
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S T : Finset iota) :
    domainLocator dom S =
      domainLocator dom (S ∩ T) * domainLocator dom (S \ T) := by
  rw [domainLocator, domainLocator, domainLocator]
  calc
    ∏ i ∈ S, (X - C (dom i)) =
        (∏ i ∈ S \ (S ∩ T), (X - C (dom i))) *
          ∏ i ∈ S ∩ T, (X - C (dom i)) :=
      (Finset.prod_sdiff
        (Finset.inter_subset_left : S ∩ T ⊆ S)).symm
    _ = (∏ i ∈ S ∩ T, (X - C (dom i))) *
        ∏ i ∈ S \ T, (X - C (dom i)) := by
      rw [mul_comm]
      congr 2
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto

/-- Absorbing the nonshared part of a locator into a quotient preserves the
original strict degree budget, with the shared intersection becoming the new
outer locator. -/
theorem interLocator_sdiffQuotient_degree_budget
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S T : Finset iota) (c : F) (p : F[X]) {k : Nat}
    (hdeg : S.card + p.natDegree < k) :
    (S ∩ T).card +
        (C c * domainLocator dom (S \ T) * p).natDegree < k := by
  have hpolydeg :
      (C c * domainLocator dom (S \ T) * p).natDegree ≤
        (S \ T).card + p.natDegree := by
    calc
      _ ≤ (C c).natDegree +
          (domainLocator dom (S \ T)).natDegree + p.natDegree := by
        exact (Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add_right Polynomial.natDegree_mul_le _))
      _ ≤ (S \ T).card + p.natDegree := by
        rw [domainLocator_natDegree]
        simp
  have hcard := Finset.card_inter_add_card_sdiff S T
  omega

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

/-- **Sequential locator quotient.**  If a nonzero degree-`<k` polynomial
vanishes on a coordinate bin `S`, factoring its locator leaves a nonzero
quotient whose degree plus `|S|` is still `<k`.  This is the first step of the
one-hole CRT/Padé attack. -/
theorem exists_lowDegree_quotient_of_rootSupport
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) (p : F[X]) {k : Nat}
    (hp0 : p ≠ 0) (hpdeg : p.natDegree < k)
    (hroot : ∀ i ∈ S, p.eval (dom i) = 0) :
    ∃ q : F[X], q ≠ 0 ∧ p = domainLocator dom S * q ∧
      S.card + q.natDegree < k := by
  obtain ⟨q, hq⟩ := domainLocator_dvd_of_eval_eq_zero dom S p hroot
  have hL0 := domainLocator_ne_zero dom S
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact hp0 hq
  have hmuldeg := Polynomial.natDegree_mul hL0 hq0
  have hdeg : S.card + q.natDegree < k := by
    rw [← hq, domainLocator_natDegree] at hmuldeg
    omega
  exact ⟨q, hq0, hq, hdeg⟩

/-- A domain locator is nonzero at every domain coordinate outside its
defining support. -/
theorem domainLocator_eval_ne_zero_of_not_mem
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) {i : iota} (hi : i ∉ S) :
    (domainLocator dom S).eval (dom i) ≠ 0 := by
  rw [domainLocator, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro heq
  apply hi
  exact dom.injective heq.symm ▸ hj

/-- **Second-bin quotient evaluation.**  Once `p` is factored by the first-bin
locator, every outside evaluation of `p` determines the low-degree quotient
by division by the nonzero locator value. -/
theorem quotient_eval_eq_div_of_locator_factorization
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) (p q : F[X])
    (hfactor : p = domainLocator dom S * q)
    {i : iota} (hi : i ∉ S) (value : F)
    (heval : p.eval (dom i) = value) :
    q.eval (dom i) = value / (domainLocator dom S).eval (dom i) := by
  have hL := domainLocator_eval_ne_zero_of_not_mem dom S hi
  have hprod := congrArg (fun f : F[X] => f.eval (dom i)) hfactor
  simp only [eval_mul] at hprod
  rw [heval] at hprod
  apply (eq_div_iff hL).mpr
  rw [mul_comm]
  exact hprod.symm

/-- **External affine-difference decomposition.**  Relative to a line through
`(gamma0,q0)`, the external line at rider `gamma` differs by its direction
difference scaled by `gamma-gamma0`, minus the external common-lift defect. -/
theorem external_affineDifference_eq_directionDiff_sub_defect
    {F : Type} [Field F]
    (gamma0 gamma : F) (q0 : F[X])
    (line0 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2) :
    (external.1 + C gamma * external.2) -
        (line0.1 + C gamma * line0.2) =
      C (gamma - gamma0) * (external.2 - line0.2) -
        (q0 - (external.1 + C gamma0 * external.2)) := by
  have ha0 : line0.1 = q0 - C gamma0 * line0.2 := by
    linear_combination -hline0
  rw [ha0, C_sub]
  ring

/-- **Two-rider external-defect elimination.**  Cross-multiplying the affine
differences at two riders cancels the unknown external direction exactly and
leaves a scalar multiple of the canonical common-lift defect.  This is the
correct route by which the saturated external support `Q` enters a
multiwitness Padé argument; unlike the reference support, it is not generally
the zero set of a single non-base affine target. -/
theorem twoRider_externalAffineDifference_eliminates_direction
    {F : Type} [Field F]
    (gamma0 gamma delta : F) (q0 : F[X])
    (line0 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2) :
    C (delta - gamma0) *
          ((external.1 + C gamma * external.2) -
            (line0.1 + C gamma * line0.2)) -
        C (gamma - gamma0) *
          ((external.1 + C delta * external.2) -
            (line0.1 + C delta * line0.2)) =
      C (gamma - delta) *
        (q0 - (external.1 + C gamma0 * external.2)) := by
  rw [external_affineDifference_eq_directionDiff_sub_defect
      gamma0 gamma q0 line0 external hline0,
    external_affineDifference_eq_directionDiff_sub_defect
      gamma0 delta q0 line0 external hline0,
    C_sub]
  simp only [map_sub]
  ring

/-- **Three-rider eliminant cocycle.**  The denominator-cleared pair
eliminants around a triangle satisfy this weighted sum identically, for
arbitrary polynomials.  Hence merely summing the three pairwise Padé
eliminations produces no new triangle constraint; a successful charged-cycle
argument must use locator support or quotient-degree structure before this
tautological cancellation. -/
theorem threeRider_scaledResidual_eliminant_cocycle
    {F : Type} [Field F]
    (gamma0 gamma1 gamma2 gamma3 : F)
    (p1 p2 p3 : F[X]) :
    C (gamma3 - gamma0) *
          (C (gamma2 - gamma0) * p1 - C (gamma1 - gamma0) * p2) +
        C (gamma1 - gamma0) *
          (C (gamma3 - gamma0) * p2 - C (gamma2 - gamma0) * p3) +
        C (gamma2 - gamma0) *
          (C (gamma1 - gamma0) * p3 - C (gamma3 - gamma0) * p1) = 0 := by
  simp only [map_sub]
  ring

/-- Locator-factored form of the same triangle cocycle.  It holds for
completely unrelated supports and quotients, confirming that the raw
three-edge identity itself cannot force a common locator. -/
theorem threeRider_locatorResidual_eliminant_cocycle
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S1 S2 S3 : Finset iota)
    (gamma0 gamma1 gamma2 gamma3 : F)
    (q1 q2 q3 : F[X]) :
    C (gamma3 - gamma0) *
          (C (gamma2 - gamma0) * (domainLocator dom S1 * q1) -
            C (gamma1 - gamma0) * (domainLocator dom S2 * q2)) +
        C (gamma1 - gamma0) *
          (C (gamma3 - gamma0) * (domainLocator dom S2 * q2) -
            C (gamma2 - gamma0) * (domainLocator dom S3 * q3)) +
        C (gamma2 - gamma0) *
          (C (gamma1 - gamma0) * (domainLocator dom S3 * q3) -
            C (gamma3 - gamma0) * (domainLocator dom S1 * q1)) = 0 := by
  exact threeRider_scaledResidual_eliminant_cocycle gamma0 gamma1 gamma2 gamma3
    (domainLocator dom S1 * q1) (domainLocator dom S2 * q2)
    (domainLocator dom S3 * q3)

/-- For two common-lift lines, the affine difference has no defect term. -/
theorem commonLift_affineDifference_eq_smul_directionDiff
    {F : Type} [Field F]
    (gamma0 gamma : F) (q0 : F[X])
    (line0 line1 : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2) :
    (line1.1 + C gamma * line1.2) -
        (line0.1 + C gamma * line0.2) =
      C (gamma - gamma0) * (line1.2 - line0.2) := by
  have ha0 : line0.1 = q0 - C gamma0 * line0.2 := by
    linear_combination -hline0
  have ha1 : line1.1 = q0 - C gamma0 * line1.2 := by
    linear_combination -hline1
  rw [ha0, ha1, C_sub]
  ring

/-- **Two-bin locator Padé identity.**  If `p` vanishes on a first coordinate
bin and agrees with a polynomial target `g` on a second bin, then factoring
the two bin locators yields `L₀*q - L₁*h = g`; the first quotient retains the
sharp degree budget inherited from `p`. -/
theorem exists_twoBin_locator_pade
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S0 S1 : Finset iota)
    (p g : F[X]) {k : Nat}
    (hp0 : p ≠ 0) (hpdeg : p.natDegree < k)
    (hzero0 : ∀ i ∈ S0, p.eval (dom i) = 0)
    (hagree1 : ∀ i ∈ S1, p.eval (dom i) = g.eval (dom i)) :
    ∃ q h : F[X], q ≠ 0 ∧
      p = domainLocator dom S0 * q ∧
      p - g = domainLocator dom S1 * h ∧
      domainLocator dom S0 * q - domainLocator dom S1 * h = g ∧
      S0.card + q.natDegree < k := by
  obtain ⟨q, hq0, hpq, hqdeg⟩ :=
    exists_lowDegree_quotient_of_rootSupport dom S0 p hp0 hpdeg hzero0
  have hzero1 : ∀ i ∈ S1, (p - g).eval (dom i) = 0 := by
    intro i hi
    simp only [eval_sub, hagree1 i hi, sub_self]
  obtain ⟨h, hph⟩ := domainLocator_dvd_of_eval_eq_zero
    dom S1 (p - g) hzero1
  refine ⟨q, h, hq0, hpq, hph, ?_, hqdeg⟩
  rw [← hpq, ← hph]
  ring

/-- **Three-bin locator Padé system.**  A single residual polynomial with
piecewise targets on three bins yields two Padé equations sharing the same
low-degree quotient, plus their coupled difference equation. -/
theorem exists_threeBin_locator_pade
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S0 S1 S2 : Finset iota)
    (p g1 g2 : F[X]) {k : Nat}
    (hp0 : p ≠ 0) (hpdeg : p.natDegree < k)
    (hzero0 : ∀ i ∈ S0, p.eval (dom i) = 0)
    (hagree1 : ∀ i ∈ S1, p.eval (dom i) = g1.eval (dom i))
    (hagree2 : ∀ i ∈ S2, p.eval (dom i) = g2.eval (dom i)) :
    ∃ q h1 h2 : F[X], q ≠ 0 ∧
      p = domainLocator dom S0 * q ∧
      p - g1 = domainLocator dom S1 * h1 ∧
      p - g2 = domainLocator dom S2 * h2 ∧
      domainLocator dom S0 * q - domainLocator dom S1 * h1 = g1 ∧
      domainLocator dom S0 * q - domainLocator dom S2 * h2 = g2 ∧
      domainLocator dom S2 * h2 - domainLocator dom S1 * h1 = g1 - g2 ∧
      S0.card + q.natDegree < k := by
  obtain ⟨q, hq0, hpq, hqdeg⟩ :=
    exists_lowDegree_quotient_of_rootSupport dom S0 p hp0 hpdeg hzero0
  have hzero1 : ∀ i ∈ S1, (p - g1).eval (dom i) = 0 := by
    intro i hi
    simp only [eval_sub, hagree1 i hi, sub_self]
  have hzero2 : ∀ i ∈ S2, (p - g2).eval (dom i) = 0 := by
    intro i hi
    simp only [eval_sub, hagree2 i hi, sub_self]
  obtain ⟨h1, hph1⟩ := domainLocator_dvd_of_eval_eq_zero
    dom S1 (p - g1) hzero1
  obtain ⟨h2, hph2⟩ := domainLocator_dvd_of_eval_eq_zero
    dom S2 (p - g2) hzero2
  have hpade1 : domainLocator dom S0 * q - domainLocator dom S1 * h1 = g1 := by
    rw [← hpq, ← hph1]
    ring
  have hpade2 : domainLocator dom S0 * q - domainLocator dom S2 * h2 = g2 := by
    rw [← hpq, ← hph2]
    ring
  refine ⟨q, h1, h2, hq0, hpq, hph1, hph2, hpade1, hpade2, ?_, hqdeg⟩
  linear_combination hpade1 - hpade2

/-- **Two-rider Padé elimination identity.**  Padé equations comparing a
common-lift reference line with the same external line at two riders can be
cross-multiplied to eliminate the unknown direction.  The result is an exact
four-locator representation of a scalar multiple of the external defect.
The bin supports may vary with the rider; this records honestly the extra
coupling required before root transfer on the saturated support `Q` can fire. -/
theorem twoRider_externalPade_eliminates_direction
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F)
    (S0gamma SEgamma S0delta SEdelta : Finset iota)
    (qgamma hgamma qdelta hdelta : F[X])
    (gamma0 gamma delta : F) (q0 : F[X])
    (line0 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hpadeGamma :
      domainLocator dom S0gamma * qgamma -
          domainLocator dom SEgamma * hgamma =
        (external.1 + C gamma * external.2) -
          (line0.1 + C gamma * line0.2))
    (hpadeDelta :
      domainLocator dom S0delta * qdelta -
          domainLocator dom SEdelta * hdelta =
        (external.1 + C delta * external.2) -
          (line0.1 + C delta * line0.2)) :
    C (delta - gamma0) *
          (domainLocator dom S0gamma * qgamma -
            domainLocator dom SEgamma * hgamma) -
        C (gamma - gamma0) *
          (domainLocator dom S0delta * qdelta -
            domainLocator dom SEdelta * hdelta) =
      C (gamma - delta) *
        (q0 - (external.1 + C gamma0 * external.2)) := by
  rw [hpadeGamma, hpadeDelta]
  exact twoRider_externalAffineDifference_eliminates_direction
    gamma0 gamma delta q0 line0 external hline0

/-- A bin agreement either is a global polynomial identity, or factors through
the bin locator with a nonzero quotient satisfying the sharp remaining-degree
budget. -/
theorem polynomial_eq_or_exists_lowDegree_binQuotient
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S : Finset iota) (p g : F[X]) {k : Nat}
    (hpdeg : p.natDegree < k) (hgdeg : g.natDegree < k)
    (hagree : ∀ i ∈ S, p.eval (dom i) = g.eval (dom i)) :
    p = g ∨ ∃ h : F[X], h ≠ 0 ∧
      p - g = domainLocator dom S * h ∧ S.card + h.natDegree < k := by
  by_cases heq : p = g
  · exact Or.inl heq
  · apply Or.inr
    have hres0 : p - g ≠ 0 := sub_ne_zero.mpr heq
    have hresdeg : (p - g).natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hpdeg hgdeg)
    have hzero : ∀ i ∈ S, (p - g).eval (dom i) = 0 := by
      intro i hi
      simp only [eval_sub, hagree i hi, sub_self]
    exact exists_lowDegree_quotient_of_rootSupport
      dom S (p - g) hres0 hresdeg hzero

/-- **Uniqueness of a low-degree two-locator Padé representation.**  For
disjoint locator supports, if the second quotient degrees are below the first
support size, equality of `L₂*h₂-L₁*h₁` forces equality of both quotient
pairs.  (The symmetric degree hypotheses can be obtained by swapping bins.) -/
theorem twoLocator_pade_solution_unique
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (S1 S2 : Finset iota)
    (hdisj : Disjoint S1 S2)
    (h1 h2 h1' h2' : F[X])
    (hh2deg : h2.natDegree < S1.card)
    (hh2deg' : h2'.natDegree < S1.card)
    (heq : domainLocator dom S2 * h2 - domainLocator dom S1 * h1 =
      domainLocator dom S2 * h2' - domainLocator dom S1 * h1') :
    h1 = h1' ∧ h2 = h2' := by
  have hcross : domainLocator dom S2 * (h2 - h2') =
      domainLocator dom S1 * (h1 - h1') := by
    linear_combination heq
  have hzero : ∀ i ∈ S1, (h2 - h2').eval (dom i) = 0 := by
    intro i hi
    have hi2 : i ∉ S2 := fun hiS2 => Finset.disjoint_left.mp hdisj hi hiS2
    have hL2 := domainLocator_eval_ne_zero_of_not_mem dom S2 hi2
    have hx := congrArg (fun p : F[X] => p.eval (dom i)) hcross
    simp only [eval_mul, eval_sub] at hx
    have hL1zero : (domainLocator dom S1).eval (dom i) = 0 := by
      rw [domainLocator, eval_prod]
      apply Finset.prod_eq_zero hi
      simp only [eval_sub, eval_X, eval_C, sub_self]
    rw [hL1zero, zero_mul] at hx
    rcases mul_eq_zero.mp hx with hbad | hgood
    · exact (hL2 hbad).elim
    · simpa only [eval_sub] using hgood
  have hh2eq : h2 = h2' := by
    by_contra hne
    have hdeg : (h2 - h2').natDegree < S1.card :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt hh2deg hh2deg')
    have hsub : S1 ⊆ Finset.univ.filter fun i =>
        (h2 - h2').eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hzero i hi
    have hroots := (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le dom (h2 - h2') (sub_ne_zero.mpr hne))
    omega
  have hh1eq : h1 = h1' := by
    rw [hh2eq, sub_self, mul_zero] at hcross
    have hL1 := domainLocator_ne_zero dom S1
    exact sub_eq_zero.mp (mul_eq_zero.mp hcross.symm |>.resolve_left hL1)
  exact ⟨hh1eq, hh2eq⟩

/-- Fixed-support two-locator Padé solutions are closed under arbitrary
scalar linear combinations.  In particular, when the target varies affinely
with the rider, two endpoint solutions generate solutions for every rider;
mere rider multiplicity does not create independent fixed-bin equations. -/
theorem twoLocator_pade_solution_linearCombination
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S1 S2 : Finset iota)
    (h1 h2 h1' h2' g g' : F[X]) (c d : F)
    (heq : domainLocator dom S2 * h2 - domainLocator dom S1 * h1 = g)
    (heq' : domainLocator dom S2 * h2' - domainLocator dom S1 * h1' = g') :
    domainLocator dom S2 * (C c * h2 + C d * h2') -
        domainLocator dom S1 * (C c * h1 + C d * h1') =
      C c * g + C d * g' := by
  linear_combination C c * heq + C d * heq'

/-- **Cross-bin root transfer for a Padé equation.**  If the Padé target
vanishes on a canonical support `R`, then the points of `R` assigned to either
locator bin become roots of the quotient belonging to the opposite bin.
Thus two nonzero low-degree quotients obey the two strict cross-budget
inequalities below.  This is the degree-sensitive constraint that remains
after ordinary three-color root counting has become subcritical. -/
theorem twoBin_pade_crossRoot_budget
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (S0 S1 R : Finset iota)
    (q h g : F[X]) {k : Nat}
    (hdisj : Disjoint S0 S1)
    (hq0 : q ≠ 0) (hh0 : h ≠ 0)
    (hqdeg : S0.card + q.natDegree < k)
    (hhdeg : S1.card + h.natDegree < k)
    (hpade : domainLocator dom S0 * q - domainLocator dom S1 * h = g)
    (hgzero : ∀ i ∈ R, g.eval (dom i) = 0) :
    (S1 ∩ R).card + S0.card < k ∧
      (S0 ∩ R).card + S1.card < k := by
  have hqzero : ∀ i ∈ S1 ∩ R, q.eval (dom i) = 0 := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hiS1, hiR⟩
    have hi0 : i ∉ S0 := fun hiS0 =>
      Finset.disjoint_left.mp hdisj hiS0 hiS1
    have hL0 := domainLocator_eval_ne_zero_of_not_mem dom S0 hi0
    have hL1zero : (domainLocator dom S1).eval (dom i) = 0 := by
      rw [domainLocator, eval_prod]
      apply Finset.prod_eq_zero hiS1
      simp only [eval_sub, eval_X, eval_C, sub_self]
    have hx := congrArg (fun p : F[X] => p.eval (dom i)) hpade
    simp only [eval_sub, eval_mul, hL1zero, zero_mul, sub_zero,
      hgzero i hiR] at hx
    exact (mul_eq_zero.mp hx).resolve_left hL0
  have hhzero : ∀ i ∈ S0 ∩ R, h.eval (dom i) = 0 := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hiS0, hiR⟩
    have hi1 : i ∉ S1 := fun hiS1 =>
      Finset.disjoint_left.mp hdisj hiS0 hiS1
    have hL1 := domainLocator_eval_ne_zero_of_not_mem dom S1 hi1
    have hL0zero : (domainLocator dom S0).eval (dom i) = 0 := by
      rw [domainLocator, eval_prod]
      apply Finset.prod_eq_zero hiS0
      simp only [eval_sub, eval_X, eval_C, sub_self]
    have hx := congrArg (fun p : F[X] => p.eval (dom i)) hpade
    simp only [eval_sub, eval_mul, hL0zero, zero_mul,
      hgzero i hiR, zero_sub] at hx
    have hprod : (domainLocator dom S1).eval (dom i) * h.eval (dom i) = 0 := by
      exact neg_eq_zero.mp hx
    exact (mul_eq_zero.mp hprod).resolve_left hL1
  have hqroots : (S1 ∩ R).card ≤ q.natDegree := by
    have hsub : S1 ∩ R ⊆ Finset.univ.filter fun i => q.eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hqzero i hi
    exact (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le dom q hq0)
  have hhroots : (S0 ∩ R).card ≤ h.natDegree := by
    have hsub : S0 ∩ R ⊆ Finset.univ.filter fun i => h.eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hhzero i hi
    exact (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le dom h hh0)
  omega

/-- **Stable-bin two-rider `Q`-support transfer.**  If two riders use the same
reference and external Padé bins, the four-locator elimination identity
collapses to a two-locator equation.  Whenever the two cross-rider quotient
differences remain nonzero and within their sharp degree budgets, roots of the
external defect on `Q` transfer to the opposite quotients exactly as in the
single-rider reference-support argument.  This theorem isolates repeated-bin
stability as a sufficient (but not automatically cardinally forced) bridge. -/
theorem twoRider_externalPade_stableBins_crossRoot_budget
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (S0 SE Q : Finset iota)
    (qgamma hgamma qdelta hdelta : F[X])
    (gamma0 gamma delta : F) (q0 : F[X])
    (line0 external : PolynomialLine F) {k : Nat}
    (hdisj : Disjoint S0 SE)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hpadeGamma :
      domainLocator dom S0 * qgamma - domainLocator dom SE * hgamma =
        (external.1 + C gamma * external.2) -
          (line0.1 + C gamma * line0.2))
    (hpadeDelta :
      domainLocator dom S0 * qdelta - domainLocator dom SE * hdelta =
        (external.1 + C delta * external.2) -
          (line0.1 + C delta * line0.2))
    (hdefectZero : ∀ i ∈ Q,
      (q0 - (external.1 + C gamma0 * external.2)).eval (dom i) = 0)
    (hq0 : C (delta - gamma0) * qgamma -
        C (gamma - gamma0) * qdelta ≠ 0)
    (hh0 : C (delta - gamma0) * hgamma -
        C (gamma - gamma0) * hdelta ≠ 0)
    (hqdeg : S0.card +
        (C (delta - gamma0) * qgamma -
          C (gamma - gamma0) * qdelta).natDegree < k)
    (hhdeg : SE.card +
        (C (delta - gamma0) * hgamma -
          C (gamma - gamma0) * hdelta).natDegree < k) :
    (SE ∩ Q).card + S0.card < k ∧
      (S0 ∩ Q).card + SE.card < k := by
  let q := C (delta - gamma0) * qgamma -
    C (gamma - gamma0) * qdelta
  let h := C (delta - gamma0) * hgamma -
    C (gamma - gamma0) * hdelta
  let g := C (gamma - delta) *
    (q0 - (external.1 + C gamma0 * external.2))
  have helim := twoRider_externalPade_eliminates_direction
    dom S0 SE S0 SE qgamma hgamma qdelta hdelta
      gamma0 gamma delta q0 line0 external hline0 hpadeGamma hpadeDelta
  have hpade : domainLocator dom S0 * q - domainLocator dom SE * h = g := by
    dsimp only [q, h, g]
    linear_combination helim
  have hgzero : ∀ i ∈ Q, g.eval (dom i) = 0 := by
    intro i hi
    simp only [g, eval_mul, eval_C, hdefectZero i hi, mul_zero]
  exact twoBin_pade_crossRoot_budget dom S0 SE Q q h g hdisj
    (by simpa only [q] using hq0) (by simpa only [h] using hh0)
    (by simpa only [q] using hqdeg) (by simpa only [h] using hhdeg)
    hpade hgzero

/-- **GCD-bin two-rider `Q`-support transfer.**  Exact bin reuse is not
necessary.  The intersections of the two riders' reference bins and external
bins provide common locator factors; the nonshared locator factors are
absorbed into new quotients.  If those two combined quotients are nonzero and
low-degree, the external-defect roots transfer across the *shared* bin
supports.  This is the natural polynomial-gcd weakening of stable-bin
transfer. -/
theorem twoRider_externalPade_interBin_crossRoot_budget
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F)
    (S0gamma SEgamma S0delta SEdelta Q : Finset iota)
    (qgamma hgamma qdelta hdelta : F[X])
    (gamma0 gamma delta : F) (q0 : F[X])
    (line0 external : PolynomialLine F) {k : Nat}
    (hdisjGamma : Disjoint S0gamma SEgamma)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hpadeGamma :
      domainLocator dom S0gamma * qgamma -
          domainLocator dom SEgamma * hgamma =
        (external.1 + C gamma * external.2) -
          (line0.1 + C gamma * line0.2))
    (hpadeDelta :
      domainLocator dom S0delta * qdelta -
          domainLocator dom SEdelta * hdelta =
        (external.1 + C delta * external.2) -
          (line0.1 + C delta * line0.2))
    (hdefectZero : ∀ i ∈ Q,
      (q0 - (external.1 + C gamma0 * external.2)).eval (dom i) = 0)
    (hq0 :
      C (delta - gamma0) *
            domainLocator dom (S0gamma \ S0delta) * qgamma -
          C (gamma - gamma0) *
            domainLocator dom (S0delta \ S0gamma) * qdelta ≠ 0)
    (hh0 :
      C (delta - gamma0) *
            domainLocator dom (SEgamma \ SEdelta) * hgamma -
          C (gamma - gamma0) *
            domainLocator dom (SEdelta \ SEgamma) * hdelta ≠ 0)
    (hqgammaDeg : S0gamma.card + qgamma.natDegree < k)
    (hqdeltaDeg : S0delta.card + qdelta.natDegree < k)
    (hhgammaDeg : SEgamma.card + hgamma.natDegree < k)
    (hhdeltaDeg : SEdelta.card + hdelta.natDegree < k) :
    ((SEgamma ∩ SEdelta) ∩ Q).card +
          (S0gamma ∩ S0delta).card < k ∧
      ((S0gamma ∩ S0delta) ∩ Q).card +
          (SEgamma ∩ SEdelta).card < k := by
  let A := S0gamma ∩ S0delta
  let B := SEgamma ∩ SEdelta
  let q := C (delta - gamma0) *
      domainLocator dom (S0gamma \ S0delta) * qgamma -
    C (gamma - gamma0) *
      domainLocator dom (S0delta \ S0gamma) * qdelta
  let h := C (delta - gamma0) *
      domainLocator dom (SEgamma \ SEdelta) * hgamma -
    C (gamma - gamma0) *
      domainLocator dom (SEdelta \ SEgamma) * hdelta
  let g := C (gamma - delta) *
    (q0 - (external.1 + C gamma0 * external.2))
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact Finset.disjoint_left.mp hdisjGamma
      (Finset.mem_inter.mp hiA).1 (Finset.mem_inter.mp hiB).1
  have helim := twoRider_externalPade_eliminates_direction
    dom S0gamma SEgamma S0delta SEdelta qgamma hgamma qdelta hdelta
      gamma0 gamma delta q0 line0 external hline0 hpadeGamma hpadeDelta
  rw [domainLocator_eq_inter_mul_sdiff dom S0gamma S0delta,
    domainLocator_eq_inter_mul_sdiff dom S0delta S0gamma,
    domainLocator_eq_inter_mul_sdiff dom SEgamma SEdelta,
    domainLocator_eq_inter_mul_sdiff dom SEdelta SEgamma] at helim
  rw [Finset.inter_comm S0delta S0gamma,
    Finset.inter_comm SEdelta SEgamma] at helim
  have hpade : domainLocator dom A * q - domainLocator dom B * h = g := by
    simp only [A, B, q, h, g]
    linear_combination helim
  have hgzero : ∀ i ∈ Q, g.eval (dom i) = 0 := by
    intro i hi
    simp only [g, eval_mul, eval_C, hdefectZero i hi, mul_zero]
  have hqgammaTerm := interLocator_sdiffQuotient_degree_budget
    dom S0gamma S0delta (delta - gamma0) qgamma hqgammaDeg
  have hqdeltaTerm := interLocator_sdiffQuotient_degree_budget
    dom S0delta S0gamma (gamma - gamma0) qdelta hqdeltaDeg
  rw [Finset.inter_comm S0delta S0gamma] at hqdeltaTerm
  have hqdeg : A.card + q.natDegree < k := by
    have hsub := Polynomial.natDegree_sub_le
      (C (delta - gamma0) *
        domainLocator dom (S0gamma \ S0delta) * qgamma)
      (C (gamma - gamma0) *
        domainLocator dom (S0delta \ S0gamma) * qdelta)
    have hmax := max_lt hqgammaTerm hqdeltaTerm
    rw [← add_max] at hmax
    exact lt_of_le_of_lt (Nat.add_le_add_left (by simpa only [q] using hsub) _) hmax
  have hhgammaTerm := interLocator_sdiffQuotient_degree_budget
    dom SEgamma SEdelta (delta - gamma0) hgamma hhgammaDeg
  have hhdeltaTerm := interLocator_sdiffQuotient_degree_budget
    dom SEdelta SEgamma (gamma - gamma0) hdelta hhdeltaDeg
  rw [Finset.inter_comm SEdelta SEgamma] at hhdeltaTerm
  have hhdeg : B.card + h.natDegree < k := by
    have hsub := Polynomial.natDegree_sub_le
      (C (delta - gamma0) *
        domainLocator dom (SEgamma \ SEdelta) * hgamma)
      (C (gamma - gamma0) *
        domainLocator dom (SEdelta \ SEgamma) * hdelta)
    have hmax := max_lt hhgammaTerm hhdeltaTerm
    rw [← add_max] at hmax
    exact lt_of_le_of_lt (Nat.add_le_add_left (by simpa only [h] using hsub) _) hmax
  have hout := twoBin_pade_crossRoot_budget dom A B Q q h g hdisj
    (by simpa only [q] using hq0) (by simpa only [h] using hh0)
    hqdeg hhdeg
    hpade hgzero
  simpa only [A, B] using hout

/-- **Cancellation forces bin stability.**  If the cross-rider combination of
the two leftover-locator quotients vanishes, each symmetric-difference
locator forces roots into the opposite quotient.  The individual quotient
budgets then bound both directed bin differences.  Thus the zero branch of a
two-rider elimination is not lost: it yields quantitative support overlap. -/
theorem zero_crossLocator_combination_forces_sdiff_budget
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F) (S T : Finset iota)
    (qS qT : F[X]) (a b : F) {k : Nat}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hqS0 : qS ≠ 0) (hqT0 : qT ≠ 0)
    (hqSdeg : S.card + qS.natDegree < k)
    (hqTdeg : T.card + qT.natDegree < k)
    (hcancel : C a * domainLocator dom (S \ T) * qS -
        C b * domainLocator dom (T \ S) * qT = 0) :
    (S \ T).card + T.card < k ∧
      (T \ S).card + S.card < k := by
  have hqTzero : ∀ i ∈ S \ T, qT.eval (dom i) = 0 := by
    intro i hi
    have hiST := Finset.mem_sdiff.mp hi
    have hiTS : i ∉ T \ S := by
      simp only [Finset.mem_sdiff]
      tauto
    have hLTS := domainLocator_eval_ne_zero_of_not_mem dom (T \ S) hiTS
    have hLSTzero : (domainLocator dom (S \ T)).eval (dom i) = 0 := by
      rw [domainLocator, eval_prod]
      apply Finset.prod_eq_zero hi
      simp only [eval_sub, eval_X, eval_C, sub_self]
    have hx := congrArg (fun p : F[X] => p.eval (dom i)) hcancel
    simp only [eval_sub, eval_mul, eval_C, eval_zero, hLSTzero,
      mul_zero, zero_mul, zero_sub, neg_eq_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left (mul_ne_zero hb hLTS)
  have hqSzero : ∀ i ∈ T \ S, qS.eval (dom i) = 0 := by
    intro i hi
    have hiTS := Finset.mem_sdiff.mp hi
    have hiST : i ∉ S \ T := by
      simp only [Finset.mem_sdiff]
      tauto
    have hLST := domainLocator_eval_ne_zero_of_not_mem dom (S \ T) hiST
    have hLTSzero : (domainLocator dom (T \ S)).eval (dom i) = 0 := by
      rw [domainLocator, eval_prod]
      apply Finset.prod_eq_zero hi
      simp only [eval_sub, eval_X, eval_C, sub_self]
    have hx := congrArg (fun p : F[X] => p.eval (dom i)) hcancel
    simp only [eval_sub, eval_mul, eval_C, eval_zero, hLTSzero,
      mul_zero, zero_mul, sub_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left (mul_ne_zero ha hLST)
  have hqTroots : (S \ T).card ≤ qT.natDegree := by
    have hsub : S \ T ⊆ Finset.univ.filter fun i => qT.eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hqTzero i hi
    exact (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le dom qT hqT0)
  have hqSroots : (T \ S).card ≤ qS.natDegree := by
    have hsub : T \ S ⊆ Finset.univ.filter fun i => qS.eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hqSzero i hi
    exact (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le dom qS hqS0)
  omega

/-- The leftover-locator cancellation is exactly proportionality of the two
original locator-factored residual polynomials.  The shared intersection
locator is nonzero and therefore loses no information. -/
theorem crossLocator_cancellation_iff_scaled_fullResiduals
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (S T : Finset iota)
    (qS qT : F[X]) (a b : F) :
    C a * domainLocator dom (S \ T) * qS -
          C b * domainLocator dom (T \ S) * qT = 0 ↔
      C a * (domainLocator dom S * qS) -
          C b * (domainLocator dom T * qT) = 0 := by
  rw [domainLocator_eq_inter_mul_sdiff dom S T,
    domainLocator_eq_inter_mul_sdiff dom T S,
    Finset.inter_comm T S]
  let L := domainLocator dom (S ∩ T)
  let z := C a * domainLocator dom (S \ T) * qS -
    C b * domainLocator dom (T \ S) * qT
  have hfactor :
      C a * (L * domainLocator dom (S \ T) * qS) -
          C b * (L * domainLocator dom (T \ S) * qT) = L * z := by
    simp only [z]
    ring
  rw [hfactor]
  constructor
  · intro hz
    have hz' : z = 0 := by simpa only [z] using hz
    rw [hz', mul_zero]
  · intro hLz
    exact (mul_eq_zero.mp hLz).resolve_left (domainLocator_ne_zero dom (S ∩ T))

/-- **Cancellation is common-base polynomial collinearity.**  After removing
the reference affine line, proportional rider residuals are equivalent to the
two rider witness polynomials and the lifted base polynomial lying on one
polynomial source line. -/
theorem scaled_referenceResiduals_eq_zero_iff_commonBase_collinear
    {F : Type} [Field F]
    (gamma0 gamma delta : F) (q0 pGamma pDelta : F[X])
    (line0 : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2) :
    C (delta - gamma0) *
          (pGamma - (line0.1 + C gamma * line0.2)) -
        C (gamma - gamma0) *
          (pDelta - (line0.1 + C delta * line0.2)) = 0 ↔
      C (delta - gamma0) * pGamma -
          C (gamma - gamma0) * pDelta =
        C (delta - gamma) * q0 := by
  rw [hline0]
  simp only [map_sub]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-- Direct Padé-facing composition: cancellation of the reference-bin
combined quotient forces the two decoded rider polynomials to be collinear
with the lifted base polynomial. -/
theorem crossLocator_cancellation_forces_commonBase_collinear
    {iota F : Type} [DecidableEq iota] [Field F]
    (dom : iota ↪ F) (Sgamma Sdelta : Finset iota)
    (qgamma qdelta : F[X])
    (gamma0 gamma delta : F) (q0 pGamma pDelta : F[X])
    (line0 : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hfactorGamma :
      pGamma - (line0.1 + C gamma * line0.2) =
        domainLocator dom Sgamma * qgamma)
    (hfactorDelta :
      pDelta - (line0.1 + C delta * line0.2) =
        domainLocator dom Sdelta * qdelta)
    (hcancel :
      C (delta - gamma0) *
            domainLocator dom (Sgamma \ Sdelta) * qgamma -
          C (gamma - gamma0) *
            domainLocator dom (Sdelta \ Sgamma) * qdelta = 0) :
    C (delta - gamma0) * pGamma -
        C (gamma - gamma0) * pDelta =
      C (delta - gamma) * q0 := by
  have hfull :=
    (crossLocator_cancellation_iff_scaled_fullResiduals
      dom Sgamma Sdelta qgamma qdelta
        (delta - gamma0) (gamma - gamma0)).mp hcancel
  rw [← hfactorGamma, ← hfactorDelta] at hfull
  exact (scaled_referenceResiduals_eq_zero_iff_commonBase_collinear
    gamma0 gamma delta q0 pGamma pDelta line0 hline0).mp hfull

/-- **Two-rider pencil-or-`Q` trichotomy.**  Given the two locator
factorizations for each rider, either the common-line combined quotient
cancels and the decoded witnesses join the reference-base pencil, or the
external-line combined quotient cancels and they join a pencil through the
external base lift, or neither cancels and canonical `Q` roots transfer across
the actual cross-rider bin intersections.  No algebraic cancellation branch
is left open. -/
theorem twoRider_pencil_or_externalPencil_or_QcrossRoot
    {iota F : Type} [Fintype iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    (dom : iota ↪ F)
    (S0gamma SEgamma S0delta SEdelta Q : Finset iota)
    (qgamma hgamma qdelta hdelta : F[X])
    (gamma0 gamma delta : F) (q0 pGamma pDelta : F[X])
    (line0 external : PolynomialLine F) {k : Nat}
    (hdisjGamma : Disjoint S0gamma SEgamma)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hqFactorGamma :
      pGamma - (line0.1 + C gamma * line0.2) =
        domainLocator dom S0gamma * qgamma)
    (hqFactorDelta :
      pDelta - (line0.1 + C delta * line0.2) =
        domainLocator dom S0delta * qdelta)
    (hhFactorGamma :
      pGamma - (external.1 + C gamma * external.2) =
        domainLocator dom SEgamma * hgamma)
    (hhFactorDelta :
      pDelta - (external.1 + C delta * external.2) =
        domainLocator dom SEdelta * hdelta)
    (hdefectZero : ∀ i ∈ Q,
      (q0 - (external.1 + C gamma0 * external.2)).eval (dom i) = 0)
    (hqgammaDeg : S0gamma.card + qgamma.natDegree < k)
    (hqdeltaDeg : S0delta.card + qdelta.natDegree < k)
    (hhgammaDeg : SEgamma.card + hgamma.natDegree < k)
    (hhdeltaDeg : SEdelta.card + hdelta.natDegree < k) :
    (C (delta - gamma0) * pGamma -
        C (gamma - gamma0) * pDelta = C (delta - gamma) * q0) ∨
      (C (delta - gamma0) * pGamma -
        C (gamma - gamma0) * pDelta =
          C (delta - gamma) *
            (external.1 + C gamma0 * external.2)) ∨
      (((SEgamma ∩ SEdelta) ∩ Q).card +
            (S0gamma ∩ S0delta).card < k ∧
        ((S0gamma ∩ S0delta) ∩ Q).card +
            (SEgamma ∩ SEdelta).card < k) := by
  let qcomb := C (delta - gamma0) *
      domainLocator dom (S0gamma \ S0delta) * qgamma -
    C (gamma - gamma0) *
      domainLocator dom (S0delta \ S0gamma) * qdelta
  let hcomb := C (delta - gamma0) *
      domainLocator dom (SEgamma \ SEdelta) * hgamma -
    C (gamma - gamma0) *
      domainLocator dom (SEdelta \ SEgamma) * hdelta
  by_cases hq : qcomb = 0
  · apply Or.inl
    exact crossLocator_cancellation_forces_commonBase_collinear
      dom S0gamma S0delta qgamma qdelta gamma0 gamma delta
        q0 pGamma pDelta line0 hline0 hqFactorGamma hqFactorDelta
        (by simpa only [qcomb] using hq)
  by_cases hh : hcomb = 0
  · apply Or.inr
    apply Or.inl
    exact crossLocator_cancellation_forces_commonBase_collinear
      dom SEgamma SEdelta hgamma hdelta gamma0 gamma delta
        (external.1 + C gamma0 * external.2) pGamma pDelta external rfl
        hhFactorGamma hhFactorDelta (by simpa only [hcomb] using hh)
  apply Or.inr
  apply Or.inr
  have hpadeGamma :
      domainLocator dom S0gamma * qgamma -
          domainLocator dom SEgamma * hgamma =
        (external.1 + C gamma * external.2) -
          (line0.1 + C gamma * line0.2) := by
    rw [← hqFactorGamma, ← hhFactorGamma]
    ring
  have hpadeDelta :
      domainLocator dom S0delta * qdelta -
          domainLocator dom SEdelta * hdelta =
        (external.1 + C delta * external.2) -
          (line0.1 + C delta * line0.2) := by
    rw [← hqFactorDelta, ← hhFactorDelta]
    ring
  exact twoRider_externalPade_interBin_crossRoot_budget
    dom S0gamma SEgamma S0delta SEdelta Q qgamma hgamma qdelta hdelta
      gamma0 gamma delta q0 line0 external hdisjGamma hline0
      hpadeGamma hpadeDelta hdefectZero
      (by simpa only [qcomb] using hq) (by simpa only [hcomb] using hh)
      hqgammaDeg hqdeltaDeg hhgammaDeg hhdeltaDeg

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

#print axioms one_universal_of_pair_covered_by_two_equivalences
#print axioms commonBase_collinear_iff_normalizedPolynomialSlope_eq
#print axioms family_universal_pencil_of_pair_covered_by_two_baseCollinearities
#print axioms weightedOverlap_eq_referenceInter_add_externalInterUnion
#print axioms pairOverlap_add_tripleOverlap_eq_twoFactorSupports
#print axioms natDegree_eq_pred_of_rootSupport_card_eq_pred
#print axioms domainLocator_ne_zero
#print axioms domainLocator_natDegree
#print axioms domainLocator_eq_inter_mul_sdiff
#print axioms domainLocator_union_mul_inter
#print axioms twoFactorSupport_union_eq_pairOverlap
#print axioms twoFactorSupport_inter_eq_tripleOverlap
#print axioms domainLocator_dvd_of_eval_eq_zero
#print axioms eq_C_mul_domainLocator_of_natDegree_eq_card
#print axioms exists_lowDegree_quotient_of_rootSupport
#print axioms domainLocator_eval_ne_zero_of_not_mem
#print axioms quotient_eval_eq_div_of_locator_factorization
#print axioms external_affineDifference_eq_directionDiff_sub_defect
#print axioms twoRider_externalAffineDifference_eliminates_direction
#print axioms threeRider_scaledResidual_eliminant_cocycle
#print axioms threeRider_locatorResidual_eliminant_cocycle
#print axioms commonLift_affineDifference_eq_smul_directionDiff
#print axioms exists_twoBin_locator_pade
#print axioms exists_threeBin_locator_pade
#print axioms twoRider_externalPade_eliminates_direction
#print axioms polynomial_eq_or_exists_lowDegree_binQuotient
#print axioms twoLocator_pade_solution_unique
#print axioms twoLocator_pade_solution_linearCombination
#print axioms twoBin_pade_crossRoot_budget
#print axioms twoRider_externalPade_stableBins_crossRoot_budget
#print axioms twoRider_externalPade_interBin_crossRoot_budget
#print axioms zero_crossLocator_combination_forces_sdiff_budget
#print axioms crossLocator_cancellation_iff_scaled_fullResiduals
#print axioms scaled_referenceResiduals_eq_zero_iff_commonBase_collinear
#print axioms crossLocator_cancellation_forces_commonBase_collinear
#print axioms twoRider_pencil_or_externalPencil_or_QcrossRoot
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
