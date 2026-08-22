/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterExtremeZeroJohnsonBand
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterProjectiveExtremeZeroSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAdjacentExactPin

/-!
# The common-factor amplifier cannot cross the final P1 lattice step

The saturated common-factor witness is bad at agreement threshold `592794965`; the exact-pin
predecessor asks for `592794966`.  This file proves that the gap is forced throughout the whole
primitive-direction amplifier architecture, not merely by the particular value of `d` chosen in
the concrete construction.

For an arbitrary amplifier size `d0`, the degree requirement is `2*d0+1 < m`.  At the literal P1
scale this forces `d0 <= d = (m-2)/2`, so its threshold `8*m+r+d0+1` is at most the existing
threshold and is strictly below the predecessor.  Equivalently, asking this architecture to reach
the predecessor forces the negation of its degree requirement.

This is architecture-local: a counterexample at the predecessor could still exist after changing
the base proper-pair locators, the primitive direction `(X,1)`, or the ownership design.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo

open P1RateQuarterScaleArithmetic
open P1RateQuarterCommonFactorArithmetic

local instance localInstance_P1RateQuarterCommonFactorOneStepNoGo_1 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩
local instance localInstance_P1RateQuarterCommonFactorOneStepNoGo_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

section PrimitiveDirectionTax

variable {F0 I : Type} [Field F0]

/-- A pair of distinct source factors agreeing on an injectively evaluated coordinate set must
spend at least one polynomial degree per coordinate.  This subset form avoids enlarging the count
to the whole field. -/
theorem agreement_card_le_difference_natDegree [DecidableEq I] [DecidableEq F0]
    (dom : I → F0) (hdom : Function.Injective dom)
    (f g : F0[X]) (S : Finset I) (hfg : f ≠ g)
    (hagree : ∀ x ∈ S, f.eval (dom x) = g.eval (dom x)) :
    S.card ≤ (f - g).natDegree := by
  have hne : f - g ≠ 0 := sub_ne_zero.mpr hfg
  have hsub : S.image dom ⊆ (f - g).roots.toFinset := by
    intro z hz
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
    exact hagree x hxS
  calc
    S.card = (S.image dom).card := (Finset.card_image_of_injective S hdom).symm
    _ ≤ (f - g).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (f - g).roots := Multiset.toFinset_card_le _
    _ ≤ (f - g).natDegree := Polynomial.card_roots' _

/-- Proper-pair agreement on a `3m` block forces one of the two source factors to have degree at
least `3m`.  Hence the base-locator degree in the common-factor construction cannot be lowered by
changing coefficients while retaining its pair blocks. -/
theorem three_mul_m_le_max_source_natDegree [DecidableEq I] [DecidableEq F0]
    (dom : I → F0) (hdom : Function.Injective dom)
    (f g : F0[X]) (S : Finset I) (hfg : f ≠ g)
    (hcard : S.card = 3 * m)
    (hagree : ∀ x ∈ S, f.eval (dom x) = g.eval (dom x)) :
    3 * m ≤ max f.natDegree g.natDegree := by
  calc
    3 * m = S.card := hcard.symm
    _ ≤ (f - g).natDegree :=
      agreement_card_le_difference_natDegree dom hdom f g S hfg hagree
    _ ≤ max f.natDegree g.natDegree := Polynomial.natDegree_sub_le f g

/-- A degree-`<K` polynomial with exactly `K-1` prescribed distinct roots is a scalar multiple of
their monic root product.  This is the saturation step that turns a polynomial split-locator
syzygy into a constant-coefficient affine locator relation. -/
theorem eq_C_mul_domainRootProduct_of_saturated_roots
    [Fintype I] [Nonempty I] [Fintype F0] [DecidableEq I] [DecidableEq F0]
    (dom : I ↪ F0) {K0 : Nat} (hK : 0 < K0)
    (p : F0[X]) (T : Finset I)
    (hpdeg : p.natDegree < K0) (hcard : T.card = K0 - 1)
    (hroot : ∀ i ∈ T, p.eval (dom i) = 0) :
    ∃ c : F0, p = C c * domainRootProduct dom T := by
  have hdvd : domainRootProduct dom T ∣ p :=
    domainRootProduct_dvd_of_eval_eq_zero dom T p hroot
  obtain ⟨q, hq⟩ := hdvd
  by_cases hq0 : q = 0
  · exact ⟨0, by simp [hq, hq0]⟩
  have hL0 : domainRootProduct dom T ≠ 0 :=
    (domainRootProduct_monic dom T).ne_zero
  have hqdeg : q.natDegree = 0 := by
    have hprod : (domainRootProduct dom T * q).natDegree =
        T.card + q.natDegree := by
      rw [Polynomial.natDegree_mul hL0 hq0, domainRootProduct_natDegree]
    rw [← hq] at hprod
    rw [hprod, hcard] at hpdeg
    omega
  have hqC : q = C (q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  refine ⟨q.coeff 0, ?_⟩
  calc
    p = domainRootProduct dom T * q := hq
    _ = domainRootProduct dom T * C (q.coeff 0) :=
      congrArg (domainRootProduct dom T * ·) hqC
    _ = C (q.coeff 0) * domainRootProduct dom T := mul_comm _ _

/-- Three saturated pair differences therefore force a constant-coefficient locator triangle.
Unlike the general next-lattice split-locator identity, no positive-degree quotient remains. -/
theorem saturated_pair_cycle_forces_affine_locator_triangle
    [Fintype I] [Nonempty I] [Fintype F0] [DecidableEq I] [DecidableEq F0]
    (dom : I ↪ F0) {K0 : Nat} (hK : 0 < K0)
    (f1 f2 f3 : F0[X]) (T12 T23 T31 : Finset I)
    (h12deg : (f2 - f1).natDegree < K0)
    (h23deg : (f3 - f2).natDegree < K0)
    (h31deg : (f1 - f3).natDegree < K0)
    (h12card : T12.card = K0 - 1)
    (h23card : T23.card = K0 - 1)
    (h31card : T31.card = K0 - 1)
    (h12root : ∀ i ∈ T12, (f2 - f1).eval (dom i) = 0)
    (h23root : ∀ i ∈ T23, (f3 - f2).eval (dom i) = 0)
    (h31root : ∀ i ∈ T31, (f1 - f3).eval (dom i) = 0) :
    ∃ c12 c23 c31 : F0,
      f2 - f1 = C c12 * domainRootProduct dom T12 ∧
      f3 - f2 = C c23 * domainRootProduct dom T23 ∧
      f1 - f3 = C c31 * domainRootProduct dom T31 ∧
      C c12 * domainRootProduct dom T12 +
          C c23 * domainRootProduct dom T23 +
        C c31 * domainRootProduct dom T31 = 0 := by
  obtain ⟨c12, hc12⟩ := eq_C_mul_domainRootProduct_of_saturated_roots
    dom hK (f2 - f1) T12 h12deg h12card h12root
  obtain ⟨c23, hc23⟩ := eq_C_mul_domainRootProduct_of_saturated_roots
    dom hK (f3 - f2) T23 h23deg h23card h23root
  obtain ⟨c31, hc31⟩ := eq_C_mul_domainRootProduct_of_saturated_roots
    dom hK (f1 - f3) T31 h31deg h31card h31root
  refine ⟨c12, c23, c31, hc12, hc23, hc31, ?_⟩
  rw [← hc12, ← hc23, ← hc31]
  ring

/-- Pairwise distinct source factors make every coefficient in the saturated locator triangle
nonzero.  This is the nondegenerate affine-triangle interface required by locator obstruction
arguments. -/
theorem saturated_pair_cycle_forces_nondegenerate_affine_locator_triangle
    [Fintype I] [Nonempty I] [Fintype F0] [DecidableEq I] [DecidableEq F0]
    (dom : I ↪ F0) {K0 : Nat} (hK : 0 < K0)
    (f1 f2 f3 : F0[X])
    (h12ne : f1 ≠ f2) (h23ne : f2 ≠ f3) (h31ne : f3 ≠ f1)
    (T12 T23 T31 : Finset I)
    (h12deg : (f2 - f1).natDegree < K0)
    (h23deg : (f3 - f2).natDegree < K0)
    (h31deg : (f1 - f3).natDegree < K0)
    (h12card : T12.card = K0 - 1)
    (h23card : T23.card = K0 - 1)
    (h31card : T31.card = K0 - 1)
    (h12root : ∀ i ∈ T12, (f2 - f1).eval (dom i) = 0)
    (h23root : ∀ i ∈ T23, (f3 - f2).eval (dom i) = 0)
    (h31root : ∀ i ∈ T31, (f1 - f3).eval (dom i) = 0) :
    ∃ c12 c23 c31 : F0,
      c12 ≠ 0 ∧ c23 ≠ 0 ∧ c31 ≠ 0 ∧
      f2 - f1 = C c12 * domainRootProduct dom T12 ∧
      f3 - f2 = C c23 * domainRootProduct dom T23 ∧
      f1 - f3 = C c31 * domainRootProduct dom T31 ∧
      C c12 * domainRootProduct dom T12 +
          C c23 * domainRootProduct dom T23 +
        C c31 * domainRootProduct dom T31 = 0 := by
  obtain ⟨c12, c23, c31, hc12, hc23, hc31, hcycle⟩ :=
    saturated_pair_cycle_forces_affine_locator_triangle
      dom hK f1 f2 f3 T12 T23 T31 h12deg h23deg h31deg
      h12card h23card h31card h12root h23root h31root
  have hc12ne : c12 ≠ 0 := by
    intro hc
    apply h12ne
    have hzero : f2 - f1 = 0 := by simpa [hc] using hc12
    exact (sub_eq_zero.mp hzero).symm
  have hc23ne : c23 ≠ 0 := by
    intro hc
    apply h23ne
    have hzero : f3 - f2 = 0 := by simpa [hc] using hc23
    exact (sub_eq_zero.mp hzero).symm
  have hc31ne : c31 ≠ 0 := by
    intro hc
    apply h31ne
    have hzero : f1 - f3 = 0 := by simpa [hc] using hc31
    exact (sub_eq_zero.mp hzero).symm
  exact ⟨c12, c23, c31, hc12ne, hc23ne, hc31ne,
    hc12, hc23, hc31, hcycle⟩

/-- Disjoint coordinate unions turn into products of their monic split locators. -/
theorem domainRootProduct_union_of_disjoint
    [Fintype I] [Nonempty I] [Fintype F0] [DecidableEq I] [DecidableEq F0]
    (dom : I ↪ F0) (C0 P0 : Finset I) (hdisj : Disjoint C0 P0) :
    domainRootProduct dom (C0 ∪ P0) =
      domainRootProduct dom C0 * domainRootProduct dom P0 := by
  simp only [domainRootProduct]
  rw [Finset.prod_union hdisj]

/-- A nonzero common locator cancels from a constant-coefficient affine locator relation. -/
theorem cancel_common_factor_from_affine_locator_triangle
    (G L12 L23 L31 : F0[X]) (c12 c23 c31 : F0) (hG : G ≠ 0)
    (hcycle : C c12 * (G * L12) + C c23 * (G * L23) +
      C c31 * (G * L31) = 0) :
    C c12 * L12 + C c23 * L23 + C c31 * L31 = 0 := by
  have hfactored : G *
      (C c12 * L12 + C c23 * L23 + C c31 * L31) = 0 := by
    calc
      G * (C c12 * L12 + C c23 * L23 + C c31 * L31) =
          C c12 * (G * L12) + C c23 * (G * L23) +
            C c31 * (G * L31) := by ring
      _ = 0 := hcycle
  exact (mul_eq_zero.mp hfactored).resolve_left hG

/-- Root-set form: if every saturated locator is a disjoint union of the same common block and a
proper-pair block, the saturated affine triangle descends to an affine triangle among the three
proper-pair locators. -/
theorem cancel_common_root_block_from_affine_locator_triangle
    [Fintype I] [Nonempty I] [Fintype F0] [DecidableEq I] [DecidableEq F0]
    (dom : I ↪ F0) (C0 P12 P23 P31 : Finset I)
    (h12disj : Disjoint C0 P12) (h23disj : Disjoint C0 P23)
    (h31disj : Disjoint C0 P31)
    (c12 c23 c31 : F0)
    (hcycle : C c12 * domainRootProduct dom (C0 ∪ P12) +
        C c23 * domainRootProduct dom (C0 ∪ P23) +
      C c31 * domainRootProduct dom (C0 ∪ P31) = 0) :
    C c12 * domainRootProduct dom P12 +
        C c23 * domainRootProduct dom P23 +
      C c31 * domainRootProduct dom P31 = 0 := by
  rw [domainRootProduct_union_of_disjoint dom C0 P12 h12disj,
    domainRootProduct_union_of_disjoint dom C0 P23 h23disj,
    domainRootProduct_union_of_disjoint dom C0 P31 h31disj] at hcycle
  exact cancel_common_factor_from_affine_locator_triangle
    (domainRootProduct dom C0) _ _ _ c12 c23 c31
    (domainRootProduct_monic dom C0).ne_zero hcycle

/-- A homogeneous nondegenerate relation among three monic polynomials of the same degree is an
ordinary affine combination.  The equality of leading coefficients forces the normalized weights
to sum to one. -/
theorem affine_combination_of_monic_triangle
    (P Q R : F0[X]) (n : Nat)
    (hPmonic : P.Monic) (hQmonic : Q.Monic) (hRmonic : R.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n)
    (hRdeg : R.natDegree = n)
    (cP cQ cR : F0) (hcR : cR ≠ 0)
    (hcycle : C cP * P + C cQ * Q + C cR * R = 0) :
    ∃ alpha beta : F0,
      alpha + beta = 1 ∧ R = C alpha * P + C beta * Q := by
  have hPtop : P.coeff n = 1 := by
    rw [← hPdeg]
    exact hPmonic.coeff_natDegree
  have hQtop : Q.coeff n = 1 := by
    rw [← hQdeg]
    exact hQmonic.coeff_natDegree
  have hRtop : R.coeff n = 1 := by
    rw [← hRdeg]
    exact hRmonic.coeff_natDegree
  have hsum : cP + cQ + cR = 0 := by
    have hcoeff := congrArg (fun p : F0[X] => p.coeff n) hcycle
    simpa [hPtop, hQtop, hRtop] using hcoeff
  refine ⟨-cP / cR, -cQ / cR, ?_, ?_⟩
  · field_simp [hcR]
    linear_combination -hsum
  · apply (mul_left_cancel₀ (C_ne_zero.mpr hcR))
    have halpha : cR * (-cP / cR) = -cP := by
      field_simp [hcR]
    have hbeta : cR * (-cQ / cR) = -cQ := by
      field_simp [hcR]
    have hCalpha : C cR * C (-cP / cR) = -C cP := by
      rw [← C_mul, halpha, C_neg]
    have hCbeta : C cR * C (-cQ / cR) = -C cQ := by
      rw [← C_mul, hbeta, C_neg]
    calc
      C cR * R = -(C cP * P + C cQ * Q) := by
        linear_combination hcycle
      _ = C cR * (C (-cP / cR) * P + C (-cQ / cR) * Q) := by
        rw [mul_add]
        rw [← mul_assoc, hCalpha, ← mul_assoc, hCbeta]
        ring

/-- Every anchored `2 x 2` coefficient minor vanishes along an affine polynomial line.  This is
the exact finite certificate checked by the locator-minor obstruction lanes. -/
theorem coefficient_minor_eq_zero_of_affine_combination
    (P Q R : F0[X]) (alpha beta : F0) (hab : alpha + beta = 1)
    (hR : R = C alpha * P + C beta * Q) (i j : Nat) :
    (R.coeff i - P.coeff i) * (Q.coeff j - P.coeff j) -
      (R.coeff j - P.coeff j) * (Q.coeff i - P.coeff i) = 0 := by
  have halpha : alpha = 1 - beta := by linear_combination hab
  rw [hR]
  simp only [coeff_add, coeff_C_mul]
  rw [halpha]
  ring

/-- Homogeneous monic-triangle form of the coefficient-minor consequence. -/
theorem coefficient_minors_vanish_of_monic_triangle
    (P Q R : F0[X]) (n : Nat)
    (hPmonic : P.Monic) (hQmonic : Q.Monic) (hRmonic : R.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n)
    (hRdeg : R.natDegree = n)
    (cP cQ cR : F0) (hcR : cR ≠ 0)
    (hcycle : C cP * P + C cQ * Q + C cR * R = 0) :
    ∀ i j : Nat,
      (R.coeff i - P.coeff i) * (Q.coeff j - P.coeff j) -
        (R.coeff j - P.coeff j) * (Q.coeff i - P.coeff i) = 0 := by
  obtain ⟨alpha, beta, hab, hR⟩ := affine_combination_of_monic_triangle
    P Q R n hPmonic hQmonic hRmonic hPdeg hQdeg hRdeg cP cQ cR hcR hcycle
  exact fun i j => coefficient_minor_eq_zero_of_affine_combination
    P Q R alpha beta hab hR i j

/-- Two distinct monic polynomials of the same degree are linearly independent over the scalar
field. -/
theorem monic_same_degree_pair_linear_independent
    (P Q : F0[X]) (n : Nat) (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n) (hPQ : P ≠ Q)
    (a b : F0) (hrel : C a * P + C b * Q = 0) :
    a = 0 ∧ b = 0 := by
  have hPtop : P.coeff n = 1 := by
    rw [← hPdeg]
    exact hPmonic.coeff_natDegree
  have hQtop : Q.coeff n = 1 := by
    rw [← hQdeg]
    exact hQmonic.coeff_natDegree
  have hab : a + b = 0 := by
    have hcoeff := congrArg (fun p : F0[X] => p.coeff n) hrel
    simpa [hPtop, hQtop] using hcoeff
  have ha : a = 0 := by
    by_contra ha0
    apply hPQ
    apply (mul_left_cancel₀ (C_ne_zero.mpr ha0))
    have hb : b = -a := by linear_combination hab
    rw [hb, C_neg] at hrel
    linear_combination hrel
  exact ⟨ha, by simpa [ha] using hab⟩

/-- Once `R = alpha*P + beta*Q`, every scalar relation among `P,Q,R` is uniquely determined by its
`R` coefficient.  This is the one-dimensional relation-space statement needed to compare the two
received-row component cocycles. -/
theorem affine_locator_relation_coefficients_unique
    (P Q R : F0[X]) (n : Nat)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n) (hPQ : P ≠ Q)
    (alpha beta : F0) (hR : R = C alpha * P + C beta * Q)
    (a b c : F0) (hrel : C a * P + C b * Q + C c * R = 0) :
    a = -c * alpha ∧ b = -c * beta := by
  have htwo : C (a + c * alpha) * P + C (b + c * beta) * Q = 0 := by
    rw [hR] at hrel
    simp only [C_add, C_mul, add_mul, mul_add, mul_assoc] at hrel ⊢
    linear_combination hrel
  obtain ⟨ha, hb⟩ := monic_same_degree_pair_linear_independent
    P Q n hPmonic hQmonic hPdeg hQdeg hPQ _ _ htwo
  constructor
  · simpa only [neg_mul] using eq_neg_of_add_eq_zero_left ha
  · simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hb

/-- Any two coefficient triples annihilating the same nondegenerate affine locator triangle are
proportional.  In a two-row polynomial-line construction this forces the two component cocycles
onto one constant projective direction. -/
theorem affine_locator_relation_space_one_dimensional
    (P Q R : F0[X]) (n : Nat)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n) (hPQ : P ≠ Q)
    (alpha beta : F0) (hR : R = C alpha * P + C beta * Q)
    (a b c a' b' c' : F0) (hc : c ≠ 0)
    (hrel : C a * P + C b * Q + C c * R = 0)
    (hrel' : C a' * P + C b' * Q + C c' * R = 0) :
    ∃ t : F0, a' = t * a ∧ b' = t * b ∧ c' = t * c := by
  obtain ⟨ha, hb⟩ := affine_locator_relation_coefficients_unique
    P Q R n hPmonic hQmonic hPdeg hQdeg hPQ alpha beta hR a b c hrel
  obtain ⟨ha', hb'⟩ := affine_locator_relation_coefficients_unique
    P Q R n hPmonic hQmonic hPdeg hQdeg hPQ alpha beta hR a' b' c' hrel'
  refine ⟨c' / c, ?_, ?_, ?_⟩
  · rw [ha, ha']
    field_simp [hc]
  · rw [hb, hb']
    field_simp [hc]
  · field_simp [hc]

/-- **Two-component collapse to one constant projective direction.**  Suppose both components of
three polynomial-pair source lines have saturated differences along the same locator triangle.
The one-dimensional relation space makes their coefficient triples proportional; consequently
`B_i - t*A_i` is independent of the source line `i`. -/
theorem saturated_two_component_lines_have_constant_projective_direction
    (P Q R : F0[X]) (n : Nat)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n) (hPQ : P ≠ Q)
    (alpha beta : F0) (hR : R = C alpha * P + C beta * Q)
    (A1 A2 A3 B1 B2 B3 : F0[X])
    (aP aQ aR bP bQ bR : F0) (haR : aR ≠ 0)
    (haRel : C aP * P + C aQ * Q + C aR * R = 0)
    (hbRel : C bP * P + C bQ * Q + C bR * R = 0)
    (hA12 : A2 - A1 = C aP * P) (hA23 : A3 - A2 = C aQ * Q)
    (hB12 : B2 - B1 = C bP * P) (hB23 : B3 - B2 = C bQ * Q) :
    ∃ t : F0,
      B2 - C t * A2 = B1 - C t * A1 ∧
      B3 - C t * A3 = B2 - C t * A2 := by
  obtain ⟨t, hbP, hbQ, _hbR⟩ := affine_locator_relation_space_one_dimensional
    P Q R n hPmonic hQmonic hPdeg hQdeg hPQ alpha beta hR
      aP aQ aR bP bQ bR haR haRel hbRel
  refine ⟨t, ?_, ?_⟩
  · apply sub_eq_zero.mp
    calc
      (B2 - C t * A2) - (B1 - C t * A1) =
          (B2 - B1) - C t * (A2 - A1) := by ring
      _ = C bP * P - C t * (C aP * P) := by rw [hA12, hB12]
      _ = 0 := by rw [hbP, C_mul]; ring
  · apply sub_eq_zero.mp
    calc
      (B3 - C t * A3) - (B2 - C t * A2) =
          (B3 - B2) - C t * (A3 - A2) := by ring
      _ = C bQ * Q - C t * (C aQ * Q) := by rw [hA23, hB23]
      _ = 0 := by rw [hbQ, C_mul]; ring

/-- Normalized form of the collapse: after the invertible row operation `B ↦ B-tA`, all three
source lines share one polynomial `H`; translating that common codeword makes their second
components identically zero.  This is the exact handoff to an extreme-zero branch. -/
theorem saturated_two_component_lines_normalize_to_common_second_component
    (P Q R : F0[X]) (n : Nat)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdeg : P.natDegree = n) (hQdeg : Q.natDegree = n) (hPQ : P ≠ Q)
    (alpha beta : F0) (hR : R = C alpha * P + C beta * Q)
    (A1 A2 A3 B1 B2 B3 : F0[X])
    (aP aQ aR bP bQ bR : F0) (haR : aR ≠ 0)
    (haRel : C aP * P + C aQ * Q + C aR * R = 0)
    (hbRel : C bP * P + C bQ * Q + C bR * R = 0)
    (hA12 : A2 - A1 = C aP * P) (hA23 : A3 - A2 = C aQ * Q)
    (hB12 : B2 - B1 = C bP * P) (hB23 : B3 - B2 = C bQ * Q) :
    ∃ t : F0, ∃ H : F0[X],
      B1 - C t * A1 = H ∧ B2 - C t * A2 = H ∧ B3 - C t * A3 = H := by
  obtain ⟨t, h21, h32⟩ :=
    saturated_two_component_lines_have_constant_projective_direction
      P Q R n hPmonic hQmonic hPdeg hQdeg hPQ alpha beta hR
      A1 A2 A3 B1 B2 B3 aP aQ aR bP bQ bR haR haRel hbRel
      hA12 hA23 hB12 hB23
  exact ⟨t, B1 - C t * A1, rfl, h21, h32.trans h21⟩

/-! ## The normalized cores cross the two-tier extreme-zero threshold -/

/-- Three-set inclusion--exclusion as an exact natural-number identity. -/
theorem card_three_union_add_pair_inters_eq
    {U : Type} [DecidableEq U] (A B C0 : Finset U) :
    (A ∪ B ∪ C0).card + (A ∩ B).card + (A ∩ C0).card + (B ∩ C0).card =
      A.card + B.card + C0.card + (A ∩ B ∩ C0).card := by
  have hAB := Finset.card_union_add_card_inter A B
  have hABC := Finset.card_union_add_card_inter (A ∪ B) C0
  have hdist : (A ∪ B) ∩ C0 = (A ∩ C0) ∪ (B ∩ C0) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hpair := Finset.card_union_add_card_inter (A ∩ C0) (B ∩ C0)
  have hinter : (A ∩ C0) ∩ (B ∩ C0) = A ∩ B ∩ C0 := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  rw [hdist] at hABC
  rw [hinter] at hpair
  omega

/-- Exact arithmetic behind the extreme-zero handoff. -/
theorem saturated_three_core_union_crosses_twoTier_zero_threshold_arithmetic :
    1017821824 + 3 * (k - 1) ≤
      3 * amplifiedThreshold + (2 * d + 1) := by
  norm_num [k, amplifiedThreshold, amplifiedCore, N, m, r, d]

/-- Three saturated normalized cores, with pair intersections at most `k-1` and common triple
core at least `2d+1`, force at least `1,017,821,824` zero-direction coordinates—the exact P1
two-tier Johnson threshold. -/
theorem saturated_three_core_union_card_ge_twoTier_zero_threshold
    {U : Type} [DecidableEq U] (A B C0 : Finset U)
    (hA : amplifiedThreshold ≤ A.card)
    (hB : amplifiedThreshold ≤ B.card)
    (hC : amplifiedThreshold ≤ C0.card)
    (hAB : (A ∩ B).card ≤ k - 1)
    (hAC : (A ∩ C0).card ≤ k - 1)
    (hBC : (B ∩ C0).card ≤ k - 1)
    (htriple : 2 * d + 1 ≤ (A ∩ B ∩ C0).card) :
    1017821824 ≤ (A ∪ B ∪ C0).card := by
  have hbook := card_three_union_add_pair_inters_eq A B C0
  have harith := saturated_three_core_union_crosses_twoTier_zero_threshold_arithmetic
  omega

/-- Zero-set adapter for the normalized direction: vanishing on all three saturated cores forces
the literal two-tier P1 zero threshold. -/
theorem saturated_three_cores_force_twoTier_direction_zero_set
    {U E : Type} [Fintype U] [DecidableEq U] [Zero E] [DecidableEq E]
    (u : U → E) (A B C0 : Finset U)
    (hA : amplifiedThreshold ≤ A.card)
    (hB : amplifiedThreshold ≤ B.card)
    (hC : amplifiedThreshold ≤ C0.card)
    (hAB : (A ∩ B).card ≤ k - 1)
    (hAC : (A ∩ C0).card ≤ k - 1)
    (hBC : (B ∩ C0).card ≤ k - 1)
    (htriple : 2 * d + 1 ≤ (A ∩ B ∩ C0).card)
    (hzeroA : ∀ x ∈ A, u x = 0)
    (hzeroB : ∀ x ∈ B, u x = 0)
    (hzeroC : ∀ x ∈ C0, u x = 0) :
    1017821824 ≤ (Finset.univ.filter fun x : U => u x = 0).card := by
  have hunion := saturated_three_core_union_card_ge_twoTier_zero_threshold
    A B C0 hA hB hC hAB hAC hBC htriple
  refine hunion.trans (Finset.card_le_card ?_)
  intro x hx
  rw [Finset.mem_union] at hx
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ x, ?_⟩
  rcases hx with hx | hx
  · rw [Finset.mem_union] at hx
    exact hx.elim (hzeroA x) (hzeroB x)
  · exact hzeroC x hx

/-- **MCA-facing safe-branch closure.**  The saturated three-core hypotheses and normalized
direction vanishing discharge the exact zero-cardinality premise of the existing two-tier Johnson
consumer, hence bound the predecessor bad-scalar count by `N`. -/
theorem predecessor_mcaEvent_filter_card_le_N_of_saturated_three_zero_cores
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F)
    (hsafe : _root_.ProximityGap.Ownership.ZeroDirectionSafeLine
      dom k P1RateQuarterPredecessorGenericSplit.predecessorThreshold u0 u1)
    (A B C0 : Finset (Fin N))
    (hA : amplifiedThreshold ≤ A.card)
    (hB : amplifiedThreshold ≤ B.card)
    (hC : amplifiedThreshold ≤ C0.card)
    (hAB : (A ∩ B).card ≤ k - 1)
    (hAC : (A ∩ C0).card ≤ k - 1)
    (hBC : (B ∩ C0).card ≤ k - 1)
    (htriple : 2 * d + 1 ≤ (A ∩ B ∩ C0).card)
    (hzeroA : ∀ x ∈ A, u1 x = 0)
    (hzeroB : ∀ x ∈ B, u1 x = 0)
    (hzeroC : ∀ x ∈ C0, u1 x = 0) :
    (Finset.univ.filter (fun gamma : P1RateQuarterScaleArithmetic.F =>
      _root_.ProximityGap.mcaEvent
        (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
          Set (Fin N → P1RateQuarterScaleArithmetic.F))
        P1RateQuarterPredecessorGenericSplit.predecessorDelta u0 u1 gamma)).card ≤ N := by
  apply P1RateQuarterExtremeZeroJohnsonBand.predecessor_mcaEvent_filter_card_le_N_of_zero_card_ge_twoTier
    dom u0 u1 hsafe
  rw [P1RateQuarterExtremeZeroJohnsonBand.twoTierZeroThreshold_eq]
  simpa only [_root_.ProximityGap.Ownership.directionZeroSet] using
    saturated_three_cores_force_twoTier_direction_zero_set
      u1 A B C0 hA hB hC hAB hAC hBC htriple hzeroA hzeroB hzeroC

/-- Absence of every threshold-size joint explanation implies zero-direction safety.  Indeed an
unsafe codeword paired with the zero codeword jointly explains the rows on its zero-direction
agreement set. -/
theorem zeroDirectionSafeLine_of_no_threshold_pairJointAgreement
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F)
    (hnonjoint : ∀ S : Finset (Fin N),
      P1RateQuarterPredecessorGenericSplit.predecessorThreshold ≤ S.card →
      ¬ _root_.ProximityGap.pairJointAgreesOn
        (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
          Set (Fin N → P1RateQuarterScaleArithmetic.F)) S u0 u1) :
    _root_.ProximityGap.Ownership.ZeroDirectionSafeLine
      dom k P1RateQuarterPredecessorGenericSplit.predecessorThreshold u0 u1 := by
  by_contra hunsafe
  obtain ⟨c, hc, hcard⟩ :=
    (_root_.ProximityGap.Ownership.not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
      dom k P1RateQuarterPredecessorGenericSplit.predecessorThreshold u0 u1).mp hunsafe
  let S := _root_.ProximityGap.Ownership.directionZeroAgreementSet c u0 u1
  apply hnonjoint S (by simpa only [S] using hcard)
  refine ⟨c, ?_, 0, ?_, ?_⟩
  · exact (_root_.ProximityGap.ExtremeZeroJohnsonBand.mem_rsCode_iff_mem_reedSolomonCode
      dom k c).mp hc
  · exact (ReedSolomon.code dom k).zero_mem
  · intro i hi
    have hi' := hi
    dsimp only [S] at hi'
    rw [_root_.ProximityGap.Ownership.directionZeroAgreementSet,
      Finset.mem_filter, _root_.ProximityGap.Ownership.directionZeroSet,
      Finset.mem_filter] at hi'
    exact ⟨hi'.2, hi'.1.2.symm⟩

/-- **Closed nonjoint saturated three-core branch.**  The nonjoint premise supplies safety, the
three-core union supplies the two-tier zero threshold, and the Johnson consumer gives the literal
predecessor bad-scalar cap. -/
theorem predecessor_mcaEvent_filter_card_le_N_of_nonjoint_saturated_three_zero_cores
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F)
    (hnonjoint : ∀ S : Finset (Fin N),
      P1RateQuarterPredecessorGenericSplit.predecessorThreshold ≤ S.card →
      ¬ _root_.ProximityGap.pairJointAgreesOn
        (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
          Set (Fin N → P1RateQuarterScaleArithmetic.F)) S u0 u1)
    (A B C0 : Finset (Fin N))
    (hA : amplifiedThreshold ≤ A.card)
    (hB : amplifiedThreshold ≤ B.card)
    (hC : amplifiedThreshold ≤ C0.card)
    (hAB : (A ∩ B).card ≤ k - 1)
    (hAC : (A ∩ C0).card ≤ k - 1)
    (hBC : (B ∩ C0).card ≤ k - 1)
    (htriple : 2 * d + 1 ≤ (A ∩ B ∩ C0).card)
    (hzeroA : ∀ x ∈ A, u1 x = 0)
    (hzeroB : ∀ x ∈ B, u1 x = 0)
    (hzeroC : ∀ x ∈ C0, u1 x = 0) :
    (Finset.univ.filter (fun gamma : P1RateQuarterScaleArithmetic.F =>
      _root_.ProximityGap.mcaEvent
        (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
          Set (Fin N → P1RateQuarterScaleArithmetic.F))
        P1RateQuarterPredecessorGenericSplit.predecessorDelta u0 u1 gamma)).card ≤ N := by
  exact predecessor_mcaEvent_filter_card_le_N_of_saturated_three_zero_cores
    dom u0 u1 (zeroDirectionSafeLine_of_no_threshold_pairJointAgreement dom u0 u1 hnonjoint)
    A B C0 hA hB hC hAB hAC hBC htriple hzeroA hzeroB hzeroC

/-- Compact extraction interface for the now-closed normalized saturated branch. -/
structure NonjointSaturatedThreeZeroCoreCertificate
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F) where
  core : Fin 3 → Finset (Fin N)
  nonjoint : ∀ S : Finset (Fin N),
    P1RateQuarterPredecessorGenericSplit.predecessorThreshold ≤ S.card →
    ¬ _root_.ProximityGap.pairJointAgreesOn
      (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
        Set (Fin N → P1RateQuarterScaleArithmetic.F)) S u0 u1
  core_card : ∀ i, amplifiedThreshold ≤ (core i).card
  pair_card : ∀ i j, i ≠ j → (core i ∩ core j).card ≤ k - 1
  triple_card : 2 * d + 1 ≤ (core 0 ∩ core 1 ∩ core 2).card
  direction_zero : ∀ i x, x ∈ core i → u1 x = 0

/-- A normalized saturated-three-core certificate directly discharges the canonical predecessor
bad-count target for the given stack. -/
theorem mcaBadCount_le_N_of_nonjointSaturatedThreeZeroCoreCertificate
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F)
    (cert : NonjointSaturatedThreeZeroCoreCertificate dom u0 u1) :
    _root_.ProximityGap.mcaBadCount
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
        Set (Fin N → P1RateQuarterScaleArithmetic.F))
      P1RateQuarterPredecessorGenericSplit.predecessorDelta u0 u1 ≤ N := by
  simpa only [_root_.ProximityGap.mcaBadCount] using
    predecessor_mcaEvent_filter_card_le_N_of_nonjoint_saturated_three_zero_cores
      dom u0 u1 cert.nonjoint (cert.core 0) (cert.core 1) (cert.core 2)
      (cert.core_card 0) (cert.core_card 1) (cert.core_card 2)
      (cert.pair_card 0 1 (by decide))
      (cert.pair_card 0 2 (by decide))
      (cert.pair_card 1 2 (by decide)) cert.triple_card
      (cert.direction_zero 0) (cert.direction_zero 1) (cert.direction_zero 2)

/-- Projective extraction interface: the saturated certificate may occur only after an invertible
row chart and subtraction of a codeword from the mixed direction. -/
structure ProjectiveNonjointSaturatedThreeZeroCoreCertificate
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F) where
  ma : P1RateQuarterScaleArithmetic.F
  mb : P1RateQuarterScaleArithmetic.F
  mc : P1RateQuarterScaleArithmetic.F
  md : P1RateQuarterScaleArithmetic.F
  det_ne : ma * md - mb * mc ≠ 0
  r : Fin N → P1RateQuarterScaleArithmetic.F
  r_mem : r ∈ P1RateQuarterPredecessorGenericSplit.predecessorCode dom
  core : Fin 3 → Finset (Fin N)
  nonjoint : ∀ S : Finset (Fin N),
    P1RateQuarterPredecessorGenericSplit.predecessorThreshold ≤ S.card →
    ¬ _root_.ProximityGap.pairJointAgreesOn
      (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
        Set (Fin N → P1RateQuarterScaleArithmetic.F)) S
      (ma • u0 + mb • u1) ((mc • u0 + md • u1) - r)
  core_card : ∀ i, amplifiedThreshold ≤ (core i).card
  pair_card : ∀ i j, i ≠ j → (core i ∩ core j).card ≤ k - 1
  triple_card : 2 * d + 1 ≤ (core 0 ∩ core 1 ∩ core 2).card
  direction_zero : ∀ i x, x ∈ core i → ((mc • u0 + md • u1) - r) x = 0

/-- A projectively normalized saturated certificate forces the original stack strictly below `N`.
The one-slot projective loss is absorbed by the sharper two-tier closed budget. -/
theorem mcaBadCount_lt_N_of_projectiveNonjointSaturatedThreeZeroCoreCertificate
    (dom : Fin N ↪ P1RateQuarterScaleArithmetic.F)
    (u0 u1 : Fin N → P1RateQuarterScaleArithmetic.F)
    (cert : ProjectiveNonjointSaturatedThreeZeroCoreCertificate dom u0 u1) :
    _root_.ProximityGap.mcaBadCount
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      (P1RateQuarterPredecessorGenericSplit.predecessorCode dom :
        Set (Fin N → P1RateQuarterScaleArithmetic.F))
      P1RateQuarterPredecessorGenericSplit.predecessorDelta u0 u1 < N := by
  let v0 := cert.ma • u0 + cert.mb • u1
  let v1 := (cert.mc • u0 + cert.md • u1) - cert.r
  have hsafe : _root_.ProximityGap.Ownership.ZeroDirectionSafeLine
      dom k P1RateQuarterPredecessorGenericSplit.predecessorThreshold v0 v1 :=
    zeroDirectionSafeLine_of_no_threshold_pairJointAgreement
      dom v0 v1 (by simpa only [v0, v1] using cert.nonjoint)
  have hzero : P1RateQuarterExtremeZeroJohnsonBand.twoTierZeroThreshold ≤
      (_root_.ProximityGap.Ownership.directionZeroSet v1).card := by
    rw [P1RateQuarterExtremeZeroJohnsonBand.twoTierZeroThreshold_eq]
    simpa only [v1, _root_.ProximityGap.Ownership.directionZeroSet] using
      saturated_three_cores_force_twoTier_direction_zero_set
        v1 (cert.core 0) (cert.core 1) (cert.core 2)
        (cert.core_card 0) (cert.core_card 1) (cert.core_card 2)
        (cert.pair_card 0 1 (by decide))
        (cert.pair_card 0 2 (by decide))
        (cert.pair_card 1 2 (by decide)) cert.triple_card
        (cert.direction_zero 0) (cert.direction_zero 1) (cert.direction_zero 2)
  have hsupport : (_root_.ProximityGap.Ownership.directionSupportSet v1).card ≤
      P1RateQuarterExtremeZeroJohnsonBand.twoTierSupportCap := by
    rw [_root_.ProximityGap.LineListMCAWeld.directionSupportSet_card_eq]
    rw [P1RateQuarterExtremeZeroJohnsonBand.twoTierZeroThreshold] at hzero
    have hcap : P1RateQuarterExtremeZeroJohnsonBand.twoTierSupportCap ≤ N := by
      norm_num [P1RateQuarterExtremeZeroJohnsonBand.twoTierSupportCap, N]
    omega
  simpa only [_root_.ProximityGap.mcaBadCount, v0, v1] using
    P1RateQuarterProjectiveExtremeZeroSplit.badCount_lt_N_of_rowMix_direction_translate_safe
      dom u0 u1 cert.r cert.det_ne cert.r_mem hsafe hsupport

/-! ## Global extraction residual and conditional exact pin -/

open P1RateQuarterCanonicalCodeBridge
open P1RateQuarterPredecessorGenericSplit

/-- New global extraction target: every allegedly over-budget canonical stack yields the closed
projective saturated-three-core certificate. -/
abbrev CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction : Prop :=
  ∀ u : _root_.Code.WordStack P1RateQuarterScaleArithmetic.F (Fin 2) (Fin N),
    N < _root_.ProximityGap.mcaBadCount
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      P1RateQuarterCanonicalCodeBridge.canonicalCode
      P1RateQuarterPredecessorGenericSplit.predecessorDelta (u 0) (u 1) →
    Nonempty (ProjectiveNonjointSaturatedThreeZeroCoreCertificate
      P1RateQuarterCanonicalCodeBridge.canonicalDomain (u 0) (u 1))

/-- The new extraction target implies the full canonical uniform predecessor count. -/
theorem canonical_uniform_predecessor_badCount_of_projectiveSaturatedExtraction
    (hextract : CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction) :
    ∀ u : _root_.Code.WordStack P1RateQuarterScaleArithmetic.F (Fin 2) (Fin N),
      _root_.ProximityGap.mcaBadCount
        (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
        P1RateQuarterCanonicalCodeBridge.canonicalCode
        P1RateQuarterPredecessorGenericSplit.predecessorDelta (u 0) (u 1) ≤ N := by
  intro u
  by_contra hover
  have hover' : N < _root_.ProximityGap.mcaBadCount
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      P1RateQuarterCanonicalCodeBridge.canonicalCode
      P1RateQuarterPredecessorGenericSplit.predecessorDelta (u 0) (u 1) :=
    Nat.lt_of_not_ge hover
  obtain ⟨cert⟩ := hextract u hover'
  have hlt := mcaBadCount_lt_N_of_projectiveNonjointSaturatedThreeZeroCoreCertificate
    P1RateQuarterCanonicalCodeBridge.canonicalDomain (u 0) (u 1) cert
  have hcode : P1RateQuarterPredecessorGenericSplit.predecessorCode
      P1RateQuarterCanonicalCodeBridge.canonicalDomain =
      P1RateQuarterCanonicalCodeBridge.canonicalCode := rfl
  rw [hcode] at hlt
  omega

/-- Honest logical audit: the guarded projective saturated extraction residual is equivalent to
the uniform predecessor count.  The reverse implication is vacuous—under a uniform bound, its
`N < badCount` guard is impossible and therefore constructs no geometry. -/
theorem canonicalLargeBadProjectiveSaturatedExtraction_iff_uniform_badCount :
    CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction ↔
      ∀ u : _root_.Code.WordStack P1RateQuarterScaleArithmetic.F (Fin 2) (Fin N),
        _root_.ProximityGap.mcaBadCount
          (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
          P1RateQuarterCanonicalCodeBridge.canonicalCode
          P1RateQuarterPredecessorGenericSplit.predecessorDelta (u 0) (u 1) ≤ N := by
  constructor
  · exact canonical_uniform_predecessor_badCount_of_projectiveSaturatedExtraction
  · intro huniform u hover
    exfalso
    exact (Nat.not_lt_of_ge (huniform u)) hover

/-- The extraction target supplies the structured residual expected by the adjacent-floor pin. -/
theorem predecessorStructuredFloorResidual_of_projectiveSaturatedExtraction
    (hextract : CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction) :
    P1RateQuarterPredecessorGenericSplit.PredecessorStructuredFloorResidual
      P1RateQuarterCanonicalCodeBridge.canonicalDomain := by
  unfold PredecessorStructuredFloorResidual
    ArkLib.ProximityGap.MCAFloorFactorization.StructuredFloorBound
  intro u0 u1 _hnear
  let u : _root_.Code.WordStack P1RateQuarterScaleArithmetic.F (Fin 2) (Fin N) :=
    fun i => if i = 0 then u0 else u1
  have hcount := canonical_uniform_predecessor_badCount_of_projectiveSaturatedExtraction
    hextract u
  simpa [_root_.ProximityGap.mcaBadCount,
    ArkLib.ProximityGap.MCAFloorFactorization.badCount, u,
    P1RateQuarterCanonicalCodeBridge.canonicalCode,
    P1RateQuarterPredecessorGenericSplit.predecessorCode] using hcount

/-- **Conditional exact P1 pin from the projective saturated-three-core extractor.** -/
theorem canonical_mcaDeltaStar_eq_common_delta_of_projectiveSaturatedExtraction
    (hextract : CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction) :
    _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      P1RateQuarterCanonicalCodeBridge.canonicalCode
      ((((2 : Nat) ^ 128 : Nat) : ENNReal)⁻¹ : ENNReal) =
      P1RateQuarterCommonFactorArithmetic.delta := by
  exact P1RateQuarterAdjacentExactPin.canonical_mcaDeltaStar_eq_common_delta_of_structured
    (predecessorStructuredFloorResidual_of_projectiveSaturatedExtraction hextract)

/-- Literal `evalCode` form of the conditional exact pin. -/
theorem evalCode_mcaDeltaStar_eq_common_delta_of_projectiveSaturatedExtraction
    (hextract : CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction) :
    _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      (ArkLib.ProximityGap.KKH26.evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g N (k - 1))
      ((((2 : Nat) ^ 128 : Nat) : ENNReal)⁻¹ : ENNReal) =
      P1RateQuarterCommonFactorArithmetic.delta := by
  rw [P1RateQuarterCanonicalCodeBridge.evalCode_eq_canonicalCode]
  exact canonical_mcaDeltaStar_eq_common_delta_of_projectiveSaturatedExtraction hextract

/-- Advertised closed form of the conditional exact pin. -/
theorem evalCode_mcaDeltaStar_eq_advertised_of_projectiveSaturatedExtraction
    (hextract : CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction) :
    _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar
      (F := P1RateQuarterScaleArithmetic.F) (A := P1RateQuarterScaleArithmetic.F)
      (ArkLib.ProximityGap.KKH26.evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g N (k - 1))
      ((((2 : Nat) ^ 128 : Nat) : ENNReal)⁻¹ : ENNReal) =
      (43 / 96 : NNReal) + 1 / (3 * N : Nat) := by
  rw [← P1RateQuarterCommonFactorArithmetic.delta_eq_fortyThree_over_ninetySix_correction]
  exact evalCode_mcaDeltaStar_eq_common_delta_of_projectiveSaturatedExtraction hextract

/-- Scalar label that makes the factored projective direction `(A,B)` vanish at a coordinate.
The formula remains useful as a degree obstruction even when `B` has zeros. -/
noncomputable def projectiveFreshLabel (dom : I → F0) (A B : F0[X]) (x : I) : F0 :=
  -(A.eval (dom x)) / B.eval (dom x)

/-- Two different fresh labels force at least one component of the projective direction to be
nonconstant.  Thus every factored architecture with injective fresh labels pays a degree-one tax;
replacing `(X,1)` by another polynomial pair cannot remove that tax. -/
theorem one_le_max_direction_natDegree_of_labels_ne
    (dom : I → F0) (A B : F0[X]) {x y : I}
    (hlabel : projectiveFreshLabel dom A B x ≠ projectiveFreshLabel dom A B y) :
    1 ≤ max A.natDegree B.natDegree := by
  by_contra hdegree
  have hAdeg : A.natDegree = 0 := by omega
  have hBdeg : B.natDegree = 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hAdeg,
    Polynomial.eq_C_of_natDegree_eq_zero hBdeg] at hlabel
  exact hlabel (by simp [projectiveFreshLabel])

/-- Injectivity on any two distinct coordinates forces the same degree-one projective tax. -/
theorem one_le_max_direction_natDegree_of_injective
    (dom : I → F0) (A B : F0[X])
    (hinj : Function.Injective (projectiveFreshLabel dom A B))
    {x y : I} (hxy : x ≠ y) :
    1 ≤ max A.natDegree B.natDegree :=
  one_le_max_direction_natDegree_of_labels_ne dom A B (hinj.ne hxy)

end PrimitiveDirectionTax

/-- The immediate predecessor agreement threshold, one above the common-factor endpoint. -/
abbrev predecessorThreshold : Nat := amplifiedThreshold + 1

theorem predecessor_threshold_value : predecessorThreshold = 592794966 := by
  norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

/-- Every degree-admissible amplifier parameter is bounded by the saturated choice `d`. -/
theorem amplifier_parameter_le_saturated {d0 : Nat} (hdegree : 2 * d0 + 1 < m) :
    d0 ≤ d := by
  norm_num [m, d] at hdegree ⊢
  omega

/-- The saturated choice is the exact largest degree-admissible parameter. -/
theorem amplifier_parameter_admissible_iff {d0 : Nat} :
    2 * d0 + 1 < m ↔ d0 ≤ d := by
  constructor
  · exact amplifier_parameter_le_saturated
  · intro hd0
    norm_num [m, d] at hd0 ⊢
    omega

/-- A degree-admissible primitive-direction amplifier remains strictly below the exact-pin
predecessor agreement threshold. -/
theorem amplifier_threshold_lt_predecessor {d0 : Nat} (hdegree : 2 * d0 + 1 < m) :
    8 * m + r + d0 + 1 < predecessorThreshold := by
  have hd0 := amplifier_parameter_le_saturated hdegree
  norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d] at hd0 ⊢
  omega

/-- Contrapositive form: reaching the predecessor inside this architecture necessarily overruns
the polynomial degree budget. -/
theorem degree_overrun_of_predecessor_le_threshold {d0 : Nat}
    (hreach : predecessorThreshold ≤ 8 * m + r + d0 + 1) :
    m ≤ 2 * d0 + 1 := by
  by_contra hnot
  push Not at hnot
  exact (not_lt_of_ge hreach) (amplifier_threshold_lt_predecessor hnot)

/-! ## The only degree-neutral escape has fatal label collisions -/

/-- With one extra common root but the same `d+1` holes, the formal ownership ledger would have
exactly one scalar of excess. -/
theorem odd_common_root_nominal_ledger :
    (N - (2 * d + 1) - (d + 1)) + 3 * (d + 1) = N + 1 := by
  norm_num [N, m, d]

/-- Consequently even one collision among the nominally charged labels destroys the strict
over-budget count. -/
theorem odd_common_root_one_collision_ledger :
    (N - (2 * d + 1) - (d + 1)) + 3 * (d + 1) - 1 = N := by
  norm_num [N, m, d]

/-- At the odd-root endpoint, the code degree budget forces the projective direction degree to be
zero.  This is the exact alternative to the current `2d` roots plus degree-one direction. -/
theorem odd_common_root_degree_forces_direction_constant {directionDegree : Nat}
    (hdegree : 3 * m + (2 * d + 1) + directionDegree < k) :
    directionDegree = 0 := by
  norm_num [m, d, k] at hdegree ⊢
  omega

/-- **Degree-versus-collision obstruction.**  A factored construction with `2d+1` common roots
cannot simultaneously fit the rate-quarter degree bound and give distinct fresh labels at two
coordinates.  Thus its nominal `N+1` ledger necessarily loses at least one label and falls to at
most `N`. -/
theorem odd_common_root_no_injective_projective_direction
    {F0 I : Type} [Field F0] (dom : I → F0) (A B : F0[X])
    (hdegree : 3 * m + (2 * d + 1) + max A.natDegree B.natDegree < k)
    (hinj : Function.Injective (projectiveFreshLabel dom A B))
    {x y : I} (hxy : x ≠ y) : False := by
  have hconstant := odd_common_root_degree_forces_direction_constant hdegree
  have hpositive := one_le_max_direction_natDegree_of_injective dom A B hinj hxy
  omega

/-- **Combined three-source degree wall.**  Retaining a `3m` proper-pair block, adding the odd
`2d+1` common-root locator needed for the predecessor, and retaining two distinct fresh labels
already requires degree supply at least `k`.  This statement allows arbitrary source-factor and
projective-direction coefficients; only the factored architecture and its exact block sizes remain.
-/
theorem factored_odd_endpoint_degree_supply_ge_k
    {F0 I : Type} [Field F0] [DecidableEq F0] [DecidableEq I]
    (dom : I → F0) (hdom : Function.Injective dom)
    (f g A B : F0[X]) (S : Finset I) (hfg : f ≠ g)
    (hcard : S.card = 3 * m)
    (hagree : ∀ x ∈ S, f.eval (dom x) = g.eval (dom x))
    {x y : I}
    (hlabel : projectiveFreshLabel dom A B x ≠ projectiveFreshLabel dom A B y) :
    k ≤ max f.natDegree g.natDegree + (2 * d + 1) +
      max A.natDegree B.natDegree := by
  have hsource := three_mul_m_le_max_source_natDegree
    dom hdom f g S hfg hcard hagree
  have hdirection := one_le_max_direction_natDegree_of_labels_ne dom A B hlabel
  norm_num [m, d, k] at hsource hdirection ⊢
  omega

/-- Impossibility form of the combined wall: no such factored odd-root endpoint can have its
degree supply strictly below the code dimension. -/
theorem factored_odd_endpoint_not_degree_lt_k
    {F0 I : Type} [Field F0] [DecidableEq F0] [DecidableEq I]
    (dom : I → F0) (hdom : Function.Injective dom)
    (f g A B : F0[X]) (S : Finset I) (hfg : f ≠ g)
    (hcard : S.card = 3 * m)
    (hagree : ∀ x ∈ S, f.eval (dom x) = g.eval (dom x))
    {x y : I}
    (hlabel : projectiveFreshLabel dom A B x ≠ projectiveFreshLabel dom A B y) :
    ¬ (max f.natDegree g.natDegree + (2 * d + 1) +
      max A.natDegree B.natDegree < k) := by
  exact not_lt_of_ge (factored_odd_endpoint_degree_supply_ge_k
    dom hdom f g A B S hfg hcard hagree hlabel)

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo

#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.amplifier_parameter_admissible_iff
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.one_le_max_direction_natDegree_of_injective
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.three_mul_m_le_max_source_natDegree
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.saturated_pair_cycle_forces_affine_locator_triangle
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.saturated_pair_cycle_forces_nondegenerate_affine_locator_triangle
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.cancel_common_root_block_from_affine_locator_triangle
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.affine_combination_of_monic_triangle
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.coefficient_minors_vanish_of_monic_triangle
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.affine_locator_relation_coefficients_unique
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.affine_locator_relation_space_one_dimensional
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.saturated_two_component_lines_have_constant_projective_direction
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.saturated_two_component_lines_normalize_to_common_second_component
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.saturated_three_core_union_card_ge_twoTier_zero_threshold
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.saturated_three_cores_force_twoTier_direction_zero_set
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.predecessor_mcaEvent_filter_card_le_N_of_saturated_three_zero_cores
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.predecessor_mcaEvent_filter_card_le_N_of_nonjoint_saturated_three_zero_cores
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.mcaBadCount_le_N_of_nonjointSaturatedThreeZeroCoreCertificate
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.mcaBadCount_lt_N_of_projectiveNonjointSaturatedThreeZeroCoreCertificate
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.canonical_mcaDeltaStar_eq_common_delta_of_projectiveSaturatedExtraction
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.canonicalLargeBadProjectiveSaturatedExtraction_iff_uniform_badCount
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.evalCode_mcaDeltaStar_eq_advertised_of_projectiveSaturatedExtraction
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.amplifier_threshold_lt_predecessor
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.degree_overrun_of_predecessor_le_threshold
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.odd_common_root_no_injective_projective_direction
#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorOneStepNoGo.factored_odd_endpoint_not_degree_lt_k
