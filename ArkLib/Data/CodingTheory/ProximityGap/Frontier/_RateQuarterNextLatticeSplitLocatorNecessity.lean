/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeCommonFactor

/-!
# Rate-quarter next lattice: the forced split-locator residual

The three- and four-core packing barriers at the first lattice beyond the
maximally thickened smooth construction force two decoded-line cores to meet
in at least `3*m+1` evaluation coordinates.  This file records the exact
algebraic consequence.

The monic locator of that common core divides both components of the decoded
line difference.  Since both components have degree below `4*m`, the two
quotients have degree below `m`.  For distinct lines at least one quotient is
nonzero.  Thus a next-lattice one-fresh construction cannot merely reuse the
old degree-`3*m` pair locator: it must exhibit a new split factor of degree at
least `3*m+1`.

For three polynomial factors the three pair factorizations also obey the
exact locator-cycle identity

```text
L12*q12 + L23*q23 + L31*q31 = 0.
```

The coefficients `qij` are polynomials in general.  Consequently the packing
barrier forces a split-locator *syzygy*, but does not by itself force the
constant-coefficient affine locator triangle used by the `mu_16` seed.  That
stronger conclusion needs an additional degree or symmetry argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor

namespace ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeSplitLocatorNecessity

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A degree-`<4m` polynomial vanishing on at least `3m+1` distinct domain
coordinates factors through their monic split locator, with quotient degree
strictly below `m`. -/
theorem exists_quotient_natDegree_lt_m_of_three_mul_add_one_roots
    (dom : I ↪ F) {m : Nat} (hm : 0 < m) (p : F[X])
    (hpdeg : p.natDegree < 4 * m)
    (T : Finset I) (hTcard : 3 * m + 1 ≤ T.card)
    (hroot : ∀ i ∈ T, p.eval (dom i) = 0) :
    ∃ q : F[X],
      p = domainRootProduct dom T * q ∧ q.natDegree < m := by
  have hdvd : domainRootProduct dom T ∣ p :=
    domainRootProduct_dvd_of_eval_eq_zero dom T p hroot
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, hq, ?_⟩
  by_cases hq0 : q = 0
  · rw [hq0, natDegree_zero]
    exact hm
  · have hlocator0 : domainRootProduct dom T ≠ 0 :=
      (domainRootProduct_monic dom T).ne_zero
    have hprodDeg :
        (domainRootProduct dom T * q).natDegree = T.card + q.natDegree := by
      rw [natDegree_mul hlocator0 hq0, domainRootProduct_natDegree]
    have hprodLt : (domainRootProduct dom T * q).natDegree < 4 * m := by
      rw [← hq]
      exact hpdeg
    omega

/-- **Forced next-lattice split locator.**  If two distinct degree-`<4m`
decoded polynomial lines have at least `3m+1` common-core coordinates, their
difference has a common monic split factor of degree at least `3m+1`; after
removing it, both component quotients have degree below `m`, and they are not
both zero. -/
theorem large_common_core_forces_split_locator
    (dom : I ↪ F) (u0 u1 : I → F) {m : Nat} (hm : 0 < m)
    (line1 line2 : F[X] × F[X]) (hne : line1 ≠ line2)
    (h1a : line1.1.natDegree < 4 * m)
    (h1r : line1.2.natDegree < 4 * m)
    (h2a : line2.1.natDegree < 4 * m)
    (h2r : line2.2.natDegree < 4 * m)
    (hlarge : 3 * m + 1 ≤
      (commonCoreBlock dom u0 u1 line1 line2).card) :
    ∃ L qa qr : F[X],
      L = domainRootProduct dom
        (commonCoreBlock dom u0 u1 line1 line2) ∧
      L.Monic ∧
      3 * m + 1 ≤ L.natDegree ∧
      line2.1 - line1.1 = L * qa ∧
      line2.2 - line1.2 = L * qr ∧
      qa.natDegree < m ∧ qr.natDegree < m ∧
      (qa ≠ 0 ∨ qr ≠ 0) := by
  let T := commonCoreBlock dom u0 u1 line1 line2
  have haDeg : (line2.1 - line1.1).natDegree < 4 * m :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt h2a h1a)
  have hrDeg : (line2.2 - line1.2).natDegree < 4 * m :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt h2r h1r)
  have hrootA : ∀ i ∈ T, (line2.1 - line1.1).eval (dom i) = 0 := by
    intro i hi
    exact (decoded_line_difference_eval_eq_zero_on_commonCore
      dom u0 u1 line1 line2 (by simpa only [T] using hi)).1
  have hrootR : ∀ i ∈ T, (line2.2 - line1.2).eval (dom i) = 0 := by
    intro i hi
    exact (decoded_line_difference_eval_eq_zero_on_commonCore
      dom u0 u1 line1 line2 (by simpa only [T] using hi)).2
  obtain ⟨qa, hfactorA, hqa⟩ :=
    exists_quotient_natDegree_lt_m_of_three_mul_add_one_roots
      dom hm (line2.1 - line1.1) haDeg T (by simpa only [T] using hlarge) hrootA
  obtain ⟨qr, hfactorR, hqr⟩ :=
    exists_quotient_natDegree_lt_m_of_three_mul_add_one_roots
      dom hm (line2.2 - line1.2) hrDeg T (by simpa only [T] using hlarge) hrootR
  have hnonzero : qa ≠ 0 ∨ qr ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hne
    apply Prod.ext
    · have hdiff : line2.1 - line1.1 = 0 := by rw [hfactorA, hzero.1, mul_zero]
      exact (sub_eq_zero.mp hdiff).symm
    · have hdiff : line2.2 - line1.2 = 0 := by rw [hfactorR, hzero.2, mul_zero]
      exact (sub_eq_zero.mp hdiff).symm
  refine ⟨domainRootProduct dom T, qa, qr, rfl,
    domainRootProduct_monic dom T, ?_, ?_, ?_, hqa, hqr, hnonzero⟩
  · rw [domainRootProduct_natDegree]
    simpa only [T] using hlarge
  · simpa only [T] using hfactorA
  · simpa only [T] using hfactorR

/-- **The old `mu_16` fibre ansatz cannot cross the next lattice.**  If the
common-core size of two distinct degree-`<4m` decoded lines is a multiple of
the old fibre size `m`, then it cannot be at least `3m+1`.

Indeed, the next possible multiple is `4m`.  Both component differences
would then have at least `4m` distinct roots despite degree below `4m`, so
both vanish and the lines coincide.  Therefore a construction beyond the
maximally thickened cell must break whole-`m`-fibre symmetry (or refine the
quotient scale); another union of the sixteen old fibres is impossible. -/
theorem not_three_mul_add_one_le_common_core_of_card_multiple
    (dom : I ↪ F) (u0 u1 : I → F) {m : Nat} (hm : 0 < m)
    (line1 line2 : F[X] × F[X]) (hne : line1 ≠ line2)
    (h1a : line1.1.natDegree < 4 * m)
    (h1r : line1.2.natDegree < 4 * m)
    (h2a : line2.1.natDegree < 4 * m)
    (h2r : line2.2.natDegree < 4 * m)
    (hmultiple : m ∣ (commonCoreBlock dom u0 u1 line1 line2).card) :
    ¬ 3 * m + 1 ≤ (commonCoreBlock dom u0 u1 line1 line2).card := by
  intro hlarge
  let T := commonCoreBlock dom u0 u1 line1 line2
  have hmultipleT : m ∣ T.card := by simpa only [T] using hmultiple
  obtain ⟨s, hs⟩ := hmultipleT
  have hfour : 4 * m ≤ T.card := by
    have hlargeT : 3 * m + 1 ≤ T.card := by simpa only [T] using hlarge
    have hs4 : 4 ≤ s := by
      by_contra hsnot
      have hsle : s ≤ 3 := by omega
      have hmul : m * s ≤ m * 3 := Nat.mul_le_mul_left m hsle
      have hcardle : T.card ≤ 3 * m := by
        rw [hs]
        simpa only [Nat.mul_comm] using hmul
      omega
    calc
      4 * m ≤ s * m := Nat.mul_le_mul_right m hs4
      _ = m * s := Nat.mul_comm _ _
      _ = T.card := hs.symm
  have hrootA : ∀ i ∈ T, (line2.1 - line1.1).eval (dom i) = 0 := by
    intro i hi
    exact (decoded_line_difference_eval_eq_zero_on_commonCore
      dom u0 u1 line1 line2 (by simpa only [T] using hi)).1
  have hrootR : ∀ i ∈ T, (line2.2 - line1.2).eval (dom i) = 0 := by
    intro i hi
    exact (decoded_line_difference_eval_eq_zero_on_commonCore
      dom u0 u1 line1 line2 (by simpa only [T] using hi)).2
  have haDeg : (line2.1 - line1.1).natDegree < 4 * m :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt h2a h1a)
  have hrDeg : (line2.2 - line1.2).natDegree < 4 * m :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt h2r h1r)
  have haZero : line2.1 - line1.1 = 0 := by
    by_contra haNonzero
    have hsub : T ⊆ Finset.univ.filter fun i ↦
        (line2.1 - line1.1).eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hrootA i hi
    have hcap := ArkLib.CS25.card_domain_roots_le
      dom (line2.1 - line1.1) haNonzero
    have := (Finset.card_le_card hsub).trans hcap
    omega
  have hrZero : line2.2 - line1.2 = 0 := by
    by_contra hrNonzero
    have hsub : T ⊆ Finset.univ.filter fun i ↦
        (line2.2 - line1.2).eval (dom i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hrootR i hi
    have hcap := ArkLib.CS25.card_domain_roots_le
      dom (line2.2 - line1.2) hrNonzero
    have := (Finset.card_le_card hsub).trans hcap
    omega
  apply hne
  exact Prod.ext (sub_eq_zero.mp haZero).symm (sub_eq_zero.mp hrZero).symm

/-- The algebraic cycle obeyed by any three pairwise split factorizations.
This is the polynomial-coefficient generalization of affine collinearity of
three monic locators. -/
theorem split_locator_cycle_identity
    (f1 f2 f3 L12 L23 L31 q12 q23 q31 : F[X])
    (h12 : f2 - f1 = L12 * q12)
    (h23 : f3 - f2 = L23 * q23)
    (h31 : f1 - f3 = L31 * q31) :
    L12 * q12 + L23 * q23 + L31 * q31 = 0 := by
  rw [← h12, ← h23, ← h31]
  ring

/-- Root-set form of the locator cycle: pairwise common coordinate blocks
automatically supply split factorizations, and their three products sum to
zero. -/
theorem exists_split_locator_cycle
    (dom : I ↪ F) (f1 f2 f3 : F[X])
    (T12 T23 T31 : Finset I)
    (h12root : ∀ i ∈ T12, (f2 - f1).eval (dom i) = 0)
    (h23root : ∀ i ∈ T23, (f3 - f2).eval (dom i) = 0)
    (h31root : ∀ i ∈ T31, (f1 - f3).eval (dom i) = 0) :
    ∃ q12 q23 q31 : F[X],
      f2 - f1 = domainRootProduct dom T12 * q12 ∧
      f3 - f2 = domainRootProduct dom T23 * q23 ∧
      f1 - f3 = domainRootProduct dom T31 * q31 ∧
      domainRootProduct dom T12 * q12 +
          domainRootProduct dom T23 * q23 +
        domainRootProduct dom T31 * q31 = 0 := by
  obtain ⟨q12, h12⟩ :=
    domainRootProduct_dvd_of_eval_eq_zero dom T12 (f2 - f1) h12root
  obtain ⟨q23, h23⟩ :=
    domainRootProduct_dvd_of_eval_eq_zero dom T23 (f3 - f2) h23root
  obtain ⟨q31, h31⟩ :=
    domainRootProduct_dvd_of_eval_eq_zero dom T31 (f1 - f3) h31root
  exact ⟨q12, q23, q31, h12, h23, h31,
    split_locator_cycle_identity f1 f2 f3 _ _ _ q12 q23 q31 h12 h23 h31⟩

end ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeSplitLocatorNecessity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeSplitLocatorNecessity
#print axioms exists_quotient_natDegree_lt_m_of_three_mul_add_one_roots
#print axioms large_common_core_forces_split_locator
#print axioms not_three_mul_add_one_le_common_core_of_card_multiple
#print axioms split_locator_cycle_identity
#print axioms exists_split_locator_cycle
