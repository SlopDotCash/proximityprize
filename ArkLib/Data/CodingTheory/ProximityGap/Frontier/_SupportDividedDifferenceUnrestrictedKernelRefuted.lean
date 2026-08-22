/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceOperator

/-!
# The unrestricted divided-difference kernel is never rigid

`SupportDividedDifferenceOperator.AnchoredKernelRigid` ranges over arbitrary polynomial
families.  On a finite evaluation domain this is too strong: the domain-vanishing polynomial
can be placed in any component other than the two anchors.  Every divided-difference row then
vanishes, while the gauged polynomial family is nonzero.

Thus the named universal residual cannot be discharged whenever the label set has a third
element.  A viable replacement must restrict the gauged source to the actual decoded degree
bound (at P1, degree `< K`); the counterexample below has degree exactly the domain size and is
then excluded because `K < N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted

open SupportDividedDifferenceOperator

variable {F I J : Type} [Field F] [Fintype I] [DecidableEq I] [DecidableEq J]

/-- The polynomial vanishing on every point of the finite domain. -/
noncomputable def domainVanishing (domain : I -> F) : F[X] :=
  Finset.univ.prod fun x => X - C (domain x)

theorem domainVanishing_monic (domain : I -> F) : (domainVanishing domain).Monic := by
  apply monic_prod_of_monic
  intro x _hx
  exact monic_X_sub_C (domain x)

theorem domainVanishing_ne_zero (domain : I -> F) : domainVanishing domain ≠ 0 :=
  (domainVanishing_monic domain).ne_zero

@[simp]
theorem domainVanishing_eval (domain : I -> F) (x : I) :
    (domainVanishing domain).eval (domain x) = 0 := by
  rw [domainVanishing, eval_prod]
  apply Finset.prod_eq_zero (i := x)
  · simp
  · simp

/-- **Refutation of the unrestricted residual.**  A third label supplies a nonzero element of
the two-anchor gauged kernel, independently of the support pattern and scalar labels. -/
theorem not_anchoredKernelRigid_of_third
    (domain : I -> F) (support : I -> Finset J) (label : J -> F)
    {a b c : J} (hca : c ≠ a) (hcb : c ≠ b) :
    ¬ AnchoredKernelRigid domain support label a b := by
  intro hrigid
  let Z : F[X] := domainVanishing domain
  let q : J -> F[X] := fun j => if j = c then Z else 0
  have hqeval : forall j x, (q j).eval (domain x) = 0 := by
    intro j x
    by_cases hj : j = c
    · simp [q, hj, Z]
    · simp [q, hj]
  have hqker : q ∈ (supportDividedDifference domain support label).ker := by
    rw [LinearMap.mem_ker]
    funext row
    change dividedDifferenceAt domain label q row = 0
    simp only [dividedDifferenceAt, hqeval, mul_zero, add_zero]
  have hqa : q a = 0 := by simp [q, Ne.symm hca]
  have hqb : q b = 0 := by simp [q, Ne.symm hcb]
  have hqzero := hrigid q hqker hqa hqb
  have hqc := congrFun hqzero c
  simp only [q, if_pos rfl, Pi.zero_apply] at hqc
  exact domainVanishing_ne_zero domain hqc

/-! ## Corrected degree-restricted target -/

/-- The meaningful two-anchor rank statement restricts every component to the decoded
Reed--Solomon degree bound. -/
def DegreeAnchoredKernelRigid (domain : I -> F) (support : I -> Finset J)
    (label : J -> F) (degree : Nat) (a b : J) : Prop :=
  ∀ q : J -> F[X],
    (∀ j, q j ∈ Polynomial.degreeLT F degree) ->
    q ∈ (supportDividedDifference domain support label).ker ->
    q a = 0 -> q b = 0 -> q = 0

/-- Coordinates on which the two anchors and a given label are all incident. -/
def commonAnchorCoords [Fintype I] [DecidableEq I]
    (support : I -> Finset J) (a b j : J) : Finset I :=
  Finset.univ.filter fun x => a ∈ support x ∧ b ∈ support x ∧ j ∈ support x

/-- Coordinates where `j` is incident with two distinct labels satisfying `zero`.

The two witnesses may depend on the coordinate.  This is the support condition naturally
produced by block-leaf elimination: a component needs `degree` roots forced by already-zero
components, but no single parent pair has to witness all of those roots. -/
noncomputable def coveredByTwoZeroCoords [Fintype I] [DecidableEq I]
    (support : I -> Finset J) (zero : J -> Prop) (j : J) : Finset I := by
  classical
  exact Finset.univ.filter fun x =>
    j ∈ support x ∧ ∃ p r, zero p ∧ zero r ∧ p ≠ r ∧ p ∈ support x ∧ r ∈ support x

/-- Fixed-pair coverage is a special case of coordinate-dependent two-zero coverage. -/
theorem commonAnchorCoords_subset_coveredByTwoZeroCoords
    [Fintype I] [DecidableEq I]
    (support : I -> Finset J) (zero : J -> Prop) {p r j : J}
    (hpzero : zero p) (hrzero : zero r) (hpr : p ≠ r) :
    commonAnchorCoords support p r j ⊆ coveredByTwoZeroCoords support zero j := by
  classical
  intro x hx
  simp only [commonAnchorCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [coveredByTwoZeroCoords, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hx.2.2, p, r, hpzero, hrzero, hpr, hx.1, hx.2.1⟩

/-- Two already-zero components force a third component to zero when their triple support has
at least as many coordinates as the polynomial degree bound. -/
theorem component_eq_zero_of_pairCoverage
    [Fintype I] [DecidableEq I]
    (domain : I ↪ F) (support : I -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {degree : Nat} [NeZero degree]
    (q : J -> F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈ (supportDividedDifference (fun x => domain x) support label).ker)
    {p r j : J} (hpr : p ≠ r) (hp : q p = 0) (hr : q r = 0)
    (hcoverage : degree ≤ (commonAnchorCoords support p r j).card) :
    q j = 0 := by
  let coords := commonAnchorCoords support p r j
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (q j) (coords.map domain)
  · intro y hy
    simp only [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : p ∈ support x ∧ r ∈ support x ∧ j ∈ support x := by
      simpa only [coords, commonAnchorCoords, Finset.mem_filter, Finset.mem_univ,
        true_and] using hx
    let row : SupportRow support :=
      { coordinate := x
        anchor₀ := p
        anchor₁ := r
        point := j
        anchor₀_mem := hx'.1
        anchor₁_mem := hx'.2.1
        point_mem := hx'.2.2 }
    have hrow := congrFun (LinearMap.mem_ker.mp hkernel) row
    change dividedDifferenceAt (fun x => domain x) label q row = 0 at hrow
    rw [dividedDifferenceAt, hp, hr] at hrow
    simp only [Polynomial.eval_zero, mul_zero, zero_add] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left
      (sub_ne_zero.mpr (hlabel.ne hpr))
  · rw [Finset.card_map]
    exact lt_of_lt_of_le (ReedSolomon.natDegree_lt_of_mem_degreeLT (hdegree j)) hcoverage

/-- Two coordinate-dependent already-zero witnesses force a component to zero once they cover
at least `degree` distinct coordinates.  This strictly generalizes fixed-pair coverage: the
labels `p,r` may be selected independently at every coordinate. -/
theorem component_eq_zero_of_twoZeroCoverage
    [Fintype I] [DecidableEq I]
    (domain : I ↪ F) (support : I -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {degree : Nat} [NeZero degree]
    (q : J -> F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈ (supportDividedDifference (fun x => domain x) support label).ker)
    (zero : J -> Prop) (hzero : ∀ p, zero p -> q p = 0) {j : J}
    (hcoverage : degree ≤ (coveredByTwoZeroCoords support zero j).card) :
    q j = 0 := by
  classical
  let coords := coveredByTwoZeroCoords support zero j
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (q j) (coords.map domain)
  · intro y hy
    simp only [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : j ∈ support x ∧
        ∃ p r, zero p ∧ zero r ∧ p ≠ r ∧ p ∈ support x ∧ r ∈ support x := by
      simpa only [coords, coveredByTwoZeroCoords, Finset.mem_filter, Finset.mem_univ,
        true_and] using hx
    obtain ⟨p, r, hpzero, hrzero, hpr, hp, hr⟩ := hx'.2
    let row : SupportRow support :=
      { coordinate := x
        anchor₀ := p
        anchor₁ := r
        point := j
        anchor₀_mem := hp
        anchor₁_mem := hr
        point_mem := hx'.1 }
    have hrow := congrFun (LinearMap.mem_ker.mp hkernel) row
    change dividedDifferenceAt (fun x => domain x) label q row = 0 at hrow
    rw [dividedDifferenceAt, hzero p hpzero, hzero r hrzero] at hrow
    simp only [Polynomial.eval_zero, mul_zero, zero_add] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left
      (sub_ne_zero.mpr (hlabel.ne hpr))
  · rw [Finset.card_map]
    exact lt_of_lt_of_le (ReedSolomon.natDegree_lt_of_mem_degreeLT (hdegree j)) hcoverage

/-- **One-step bootstrap rigidity.**  If every label meets the same two anchors on at least
`degree` coordinates, the degree-restricted gauged kernel is trivial.  On each common coordinate,
the divided-difference row with anchors `a,b` forces the third component to vanish; the
Reed--Solomon root bound then makes that component the zero polynomial. -/
theorem degreeAnchoredKernelRigid_of_commonAnchorCoverage
    [Fintype I] [DecidableEq I]
    (domain : I ↪ F) (support : I -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {degree : Nat} [NeZero degree]
    {a b : J} (hab : a ≠ b)
    (hcoverage : ∀ j, degree ≤ (commonAnchorCoords support a b j).card) :
    DegreeAnchoredKernelRigid (fun x => domain x) support label degree a b := by
  intro q hdegree hkernel hqa hqb
  funext j
  let coords := commonAnchorCoords support a b j
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (q j) (coords.map domain)
  · intro y hy
    simp only [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : a ∈ support x ∧ b ∈ support x ∧ j ∈ support x := by
      simpa only [coords, commonAnchorCoords, Finset.mem_filter, Finset.mem_univ,
        true_and] using hx
    let row : SupportRow support :=
      { coordinate := x
        anchor₀ := a
        anchor₁ := b
        point := j
        anchor₀_mem := hx'.1
        anchor₁_mem := hx'.2.1
        point_mem := hx'.2.2 }
    have hrow := congrFun (LinearMap.mem_ker.mp hkernel) row
    change dividedDifferenceAt (fun x => domain x) label q row = 0 at hrow
    rw [dividedDifferenceAt, hqa, hqb] at hrow
    simp only [Polynomial.eval_zero, mul_zero, zero_add] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left
      (sub_ne_zero.mpr (hlabel.ne hab))
  · rw [Finset.card_map]
    exact lt_of_lt_of_le (ReedSolomon.natDegree_lt_of_mem_degreeLT (hdegree j))
      (hcoverage j)

/-- **Coordinate-dependent bootstrap rigidity.**  At positive rank, each component only needs
`degree` coordinates on which it meets some two distinct lower-rank components.  The pair may
vary with the coordinate.  Strong induction first kills those lower-rank components and then
uses the Reed--Solomon root bound to kill the current one.

This is strictly more flexible than `degreeAnchoredKernelRigid_of_bootstrap`, which chooses one
fixed parent pair for each label. -/
theorem degreeAnchoredKernelRigid_of_coordinateBootstrap
    [Fintype I] [DecidableEq I]
    (domain : I ↪ F) (support : I -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {degree : Nat} [NeZero degree]
    {a b : J}
    (rank : J -> Nat)
    (hrankZero : ∀ j, rank j = 0 -> j = a ∨ j = b)
    (hcoverage : ∀ j, 0 < rank j -> degree ≤
      (coveredByTwoZeroCoords support (fun p => rank p < rank j) j).card) :
    DegreeAnchoredKernelRigid (fun x => domain x) support label degree a b := by
  intro q hdegree hkernel hqa hqb
  have hzero : ∀ n j, rank j = n -> q j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro j hj
        by_cases hn : n = 0
        · rcases hrankZero j (hj.trans hn) with rfl | rfl
          · exact hqa
          · exact hqb
        · have hnpos : 0 < rank j := by omega
          apply component_eq_zero_of_twoZeroCoverage domain support label hlabel q hdegree
            hkernel (fun p => rank p < rank j)
          · intro p hp
            apply ih (rank p)
            · simpa only [hj] using hp
            · exact rfl
          · exact hcoverage j hnpos
  funext j
  exact hzero (rank j) j rfl

/-- **Iterated bootstrap rigidity.**  Suppose every non-anchor label is assigned two distinct
parents of strictly smaller rank and shares at least `degree` coordinates with those parents.
Starting from the two zero-gauged anchors, repeated root forcing makes every component zero.

This is the finite combinatorial certificate the P1 support hypergraph now needs to supply; it is
strictly weaker than requiring one anchor pair to cover every label directly. -/
theorem degreeAnchoredKernelRigid_of_bootstrap
    [Fintype I] [DecidableEq I]
    (domain : I ↪ F) (support : I -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {degree : Nat} [NeZero degree]
    {a b : J} (hab : a ≠ b)
    (rank : J -> Nat) (parent₀ parent₁ : J -> J)
    (hrankZero : ∀ j, rank j = 0 -> j = a ∨ j = b)
    (hparentDistinct : ∀ j, 0 < rank j -> parent₀ j ≠ parent₁ j)
    (hparentRank₀ : ∀ j, 0 < rank j -> rank (parent₀ j) < rank j)
    (hparentRank₁ : ∀ j, 0 < rank j -> rank (parent₁ j) < rank j)
    (hcoverage : ∀ j, 0 < rank j ->
      degree ≤ (commonAnchorCoords support (parent₀ j) (parent₁ j) j).card) :
    DegreeAnchoredKernelRigid (fun x => domain x) support label degree a b := by
  intro q hdegree hkernel hqa hqb
  have hzero : ∀ n j, rank j = n -> q j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro j hj
        by_cases hn : n = 0
        · rcases hrankZero j (hj.trans hn) with rfl | rfl
          · exact hqa
          · exact hqb
        · have hnpos : 0 < rank j := by omega
          apply component_eq_zero_of_pairCoverage domain support label hlabel q hdegree hkernel
            (hparentDistinct j hnpos)
          · apply ih (rank (parent₀ j))
            · rw [← hj]
              exact hparentRank₀ j hnpos
            · exact rfl
          · apply ih (rank (parent₁ j))
            · rw [← hj]
              exact hparentRank₁ j hnpos
            · exact rfl
          · exact hcoverage j hnpos
  funext j
  exact hzero (rank j) j rfl

/-- Degree-restricted anchored rigidity still has the intended consequence: every low-degree
kernel family is the unique global polynomial pencil through its two anchors. -/
theorem eq_polynomialPencil_of_degreeAnchoredKernelRigid
    (domain : I -> F) (support : I -> Finset J) (label : J -> F)
    {degree : Nat} {a b : J} (hlabel : label a ≠ label b)
    (hrigid : DegreeAnchoredKernelRigid domain support label degree a b)
    (q : J -> F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hq : q ∈ (supportDividedDifference domain support label).ker) :
    q = polynomialPencil label (pencilBase label q a b) (pencilSlope label q a b) := by
  let base := pencilBase label q a b
  let slope := pencilSlope label q a b
  let pencil := polynomialPencil label base slope
  have hbaseSlope := pencilBaseSlope_mem_degreeLT label q (a := a) (b := b) hdegree
  have hpencilDegree : ∀ j, pencil j ∈ Polynomial.degreeLT F degree := by
    intro j
    exact (Polynomial.degreeLT F degree).add_mem hbaseSlope.1
      ((Polynomial.degreeLT F degree).smul_mem _ hbaseSlope.2)
  have hpencilKer : pencil ∈ (supportDividedDifference domain support label).ker :=
    polynomialPencil_mem_ker domain support label base slope
  have hdifferenceDegree : ∀ j, (q - pencil) j ∈ Polynomial.degreeLT F degree := by
    intro j
    exact (Polynomial.degreeLT F degree).sub_mem (hdegree j) (hpencilDegree j)
  have hdifferenceKer : q - pencil ∈
      (supportDividedDifference domain support label).ker :=
    (supportDividedDifference domain support label).ker.sub_mem hq hpencilKer
  have hzero : q - pencil = 0 := hrigid (q - pencil) hdifferenceDegree hdifferenceKer
    (by
      simp only [Pi.sub_apply, sub_eq_zero]
      exact pencil_at_anchor₀ label q a b |>.symm)
    (by
      simp only [Pi.sub_apply, sub_eq_zero]
      exact pencil_at_anchor₁ label q hlabel |>.symm)
  exact sub_eq_zero.mp hzero

/-- The corrected degree-restricted residual supplies the same downstream joint-agreement
conclusion as the refuted unrestricted statement. -/
theorem pairJointAgreesOn_of_degreeAnchoredKernelRigid
    [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype F] [DecidableEq F]
    (domain : I ↪ F) (support : I -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {a b : J} (hab : a ≠ b)
    {degree : Nat}
    (hrigid : DegreeAnchoredKernelRigid (fun x => domain x) support label degree a b)
    (q : J -> F[X]) (u₀ u₁ : I -> F)
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hcard : ∀ x, 2 ≤ (support x).card)
    (hagree : SupportedAgreement (fun x => domain x) support label q u₀ u₁)
    (S : Finset I) :
    ProximityGap.pairJointAgreesOn
      (ReedSolomon.code domain degree : Set (I -> F)) S u₀ u₁ := by
  let base := pencilBase label q a b
  let slope := pencilSlope label q a b
  have hkernel := mem_ker_of_supportedAgreement
    (fun x => domain x) support label q u₀ u₁ hagree
  have hpencil := eq_polynomialPencil_of_degreeAnchoredKernelRigid
    (fun x => domain x) support label (hlabel.ne hab) hrigid q hdegree hkernel
  have hstack := stack_eq_evaluation_of_polynomialPencil
    (fun x => domain x) support label hlabel q u₀ u₁ base slope hcard hagree hpencil
  have hdegree' := pencilBaseSlope_mem_degreeLT label q (a := a) (b := b) hdegree
  refine ⟨fun x => base.eval (domain x), ⟨base, hdegree'.1, rfl⟩,
    fun x => slope.eval (domain x), ⟨slope, hdegree'.2, rfl⟩, ?_⟩
  intro x _hx
  exact ⟨congrFun hstack.1 x |>.symm, congrFun hstack.2 x |>.symm⟩

end ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted

open ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted
#print axioms not_anchoredKernelRigid_of_third
#print axioms commonAnchorCoords_subset_coveredByTwoZeroCoords
#print axioms component_eq_zero_of_pairCoverage
#print axioms component_eq_zero_of_twoZeroCoverage
#print axioms degreeAnchoredKernelRigid_of_commonAnchorCoverage
#print axioms degreeAnchoredKernelRigid_of_coordinateBootstrap
#print axioms degreeAnchoredKernelRigid_of_bootstrap
#print axioms eq_polynomialPencil_of_degreeAnchoredKernelRigid
#print axioms pairJointAgreesOn_of_degreeAnchoredKernelRigid
