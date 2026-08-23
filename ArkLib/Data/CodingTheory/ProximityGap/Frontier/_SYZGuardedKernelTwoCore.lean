/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceUnrestrictedKernelRefuted

/-!
# Guarded two-cores of the support divided-difference kernel

The rate-quarter predecessor residual asks whether the degree-`< K` kernel of the
support divided-difference operator consists only of global polynomial pencils.  After fixing two
components to zero, any further nonzero kernel family is a genuine syzygy obstruction.

This file gives that obstruction a static hypergraph form.  For a label set `U`, a coordinate is
in the **external two-coverage** of `j ∈ U` when it contains `j` and two distinct labels outside
`U`.  If a kernel family is zero outside `U`, every such coordinate is a root of the `j`-component.
Consequently a nonzero degree-`< K` component has fewer than `K` externally two-covered
coordinates.

Thus the support of every nonzero gauged syzygy is a **guarded two-core**: every one of its
vertices has external two-boundary smaller than `K`.  Conversely, if every nonempty label set
avoiding the two gauge anchors has a vertex with external two-boundary at least `K`, the corrected
degree-restricted kernel is rigid.  This static circuit/core criterion repackages the existing
two-parent bootstrap and is known to be too strong for the all-small-triples miniature.

The genuinely new guard is pairwise.  A zero external label meeting two internal components on
`K` coordinates forces a global scalar relation between those components.  Two distinct critical
external labels kill the pair, so every nonzero syzygy pair has at most one critical external
channel.  These are exact implications to the current rank residual, not a proof that P1 event
supports force two critical channels.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.SYZGuardedKernelTwoCore

open SupportDividedDifferenceOperator
open SupportDividedDifferenceUnrestrictedKernelRefuted

variable {F I J : Type} [Field F]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Labels on which a polynomial family is nonzero. -/
noncomputable def nonzeroComponents (q : J → F[X]) : Finset J := by
  classical
  exact Finset.univ.filter fun j => q j ≠ 0

@[simp]
theorem mem_nonzeroComponents_iff (q : J → F[X]) (j : J) :
    j ∈ nonzeroComponents q ↔ q j ≠ 0 := by
  classical
  simp [nonzeroComponents]

@[simp]
theorem not_mem_nonzeroComponents_iff (q : J → F[X]) (j : J) :
    j ∉ nonzeroComponents q ↔ q j = 0 := by
  classical
  simp [nonzeroComponents]

/-- Coordinates containing `j` and two distinct labels outside `U`.

When a kernel family is supported inside `U`, the two outside labels are already-zero witnesses,
so every coordinate in this set forces a root of the `j`-component. -/
noncomputable def externalTwoCoverage
    (support : I → Finset J) (U : Finset J) (j : J) : Finset I :=
  coveredByTwoZeroCoords support (fun p => p ∉ U) j

/-- A nonempty label set is a guarded two-core at degree `K` when none of its components has
`K` coordinates containing two distinct labels outside the set. -/
def GuardedTwoCore
    (support : I → Finset J) (degree : ℕ) (U : Finset J) : Prop :=
  U.Nonempty ∧ ∀ j ∈ U, (externalTwoCoverage support U j).card < degree

/-- Static core-freeness after contracting the two gauge anchors.  Every nonempty set avoiding
the anchors has a peelable vertex whose external two-coverage reaches the degree bound. -/
def AnchorAvoidingTwoCoreFree
    (support : I → Finset J) (degree : ℕ) (a b : J) : Prop :=
  ∀ U : Finset J, a ∉ U → b ∉ U → U.Nonempty →
    ∃ j ∈ U, degree ≤ (externalTwoCoverage support U j).card

/-- **Syzygy support boundary bound.**  If `q` is a degree-`< K` kernel family, every nonzero
component has fewer than `K` coordinates at which it meets two distinct zero components.

Taking the zero predicate to be the complement of `nonzeroComponents q` makes this exactly the
external two-boundary of the support of the syzygy. -/
theorem externalTwoCoverage_card_lt_degree_of_mem_nonzeroComponents
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    {j : J} (hj : j ∈ nonzeroComponents q) :
    (externalTwoCoverage support (nonzeroComponents q) j).card < degree := by
  classical
  by_contra hnot
  have hcoverage : degree ≤
      (coveredByTwoZeroCoords support (fun p => p ∉ nonzeroComponents q) j).card := by
    simpa only [externalTwoCoverage] using le_of_not_gt hnot
  have hzero : ∀ p, p ∉ nonzeroComponents q → q p = 0 := by
    intro p hp
    exact (not_mem_nonzeroComponents_iff q p).mp hp
  have hjzero := component_eq_zero_of_twoZeroCoverage
    domain support label hlabel q hdegree hkernel
      (fun p => p ∉ nonzeroComponents q) hzero hcoverage
  exact (mem_nonzeroComponents_iff q j).mp hj hjzero

/-- **Every nonzero degree-bounded kernel support is a guarded two-core.**  This is the promised
static classification of a persistent syzygy circuit. -/
theorem nonzeroComponents_guardedTwoCore
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    (hq : q ≠ 0) :
    GuardedTwoCore support degree (nonzeroComponents q) := by
  classical
  constructor
  · by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hq
    funext j
    have hj : j ∉ nonzeroComponents q := by simp [hempty]
    exact (not_mem_nonzeroComponents_iff q j).mp hj
  · intro j hj
    exact externalTwoCoverage_card_lt_degree_of_mem_nonzeroComponents
      domain support label hlabel q hdegree hkernel hj

/-- A nonzero kernel family vanishing at the two gauge anchors produces an anchor-avoiding
guarded two-core.  This is the circuit witness extracted from failure of rigidity. -/
theorem exists_anchorAvoiding_guardedTwoCore_of_nonzero_gaugedKernel
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    {a b : J} (q : J → F[X])
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    (hqa : q a = 0) (hqb : q b = 0) (hq : q ≠ 0) :
    ∃ U : Finset J,
      a ∉ U ∧ b ∉ U ∧ GuardedTwoCore support degree U := by
  refine ⟨nonzeroComponents q, ?_, ?_, ?_⟩
  · exact (not_mem_nonzeroComponents_iff q a).mpr hqa
  · exact (not_mem_nonzeroComponents_iff q b).mpr hqb
  · exact nonzeroComponents_guardedTwoCore
      domain support label hlabel q hdegree hkernel hq

/-- **Guarded-core exclusion implies degree-restricted kernel rigidity.**  After the two global
pencil directions are gauged away, it is enough to prove the static core-freeness condition on the
support hypergraph.  Any hypothetical nonzero kernel vector supplies a guarded two-core by the
previous theorem, while core-freeness supplies a vertex with at least `K` forced roots.

This sufficient condition is intentionally not claimed for every P1 support: the known
all-small-triples miniature blocks its first peel for every anchor pair. -/
theorem degreeAnchoredKernelRigid_of_anchorAvoidingTwoCoreFree
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    {a b : J}
    (hcore : AnchorAvoidingTwoCoreFree support degree a b) :
    DegreeAnchoredKernelRigid (fun x => domain x) support label degree a b := by
  intro q hdegree hkernel hqa hqb
  by_contra hq
  obtain ⟨U, haU, hbU, hU⟩ :=
    exists_anchorAvoiding_guardedTwoCore_of_nonzero_gaugedKernel
      domain support label hlabel q hdegree hkernel hqa hqb hq
  obtain ⟨j, hjU, hjlarge⟩ := hcore U haU hbU hU.1
  have hjsmall := hU.2 j hjU
  omega

/-! ## A second guard: two internal components and two external anchors -/

/-- If one zero component `r` meets two components `i,j` on at least `degree` coordinates, the
corresponding scalar linear combination of `q i` and `q j` vanishes identically.  This is the
degree-bounded lift of one local three-label divided-difference syzygy. -/
theorem pair_relation_of_zero_externalAnchorCoverage
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    {degree : ℕ} [NeZero degree]
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    {i j r : J} (hr : q r = 0)
    (hcoverage : degree ≤ (commonAnchorCoords support i j r).card) :
    C (label j - label r) * q i + C (label r - label i) * q j = 0 := by
  classical
  let relation : F[X] :=
    C (label j - label r) * q i + C (label r - label i) * q j
  have hrelationDegree : relation ∈ Polynomial.degreeLT F degree := by
    change C (label j - label r) * q i + C (label r - label i) * q j ∈
      Polynomial.degreeLT F degree
    rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul]
    exact (Polynomial.degreeLT F degree).add_mem
      ((Polynomial.degreeLT F degree).smul_mem _ (hdegree i))
      ((Polynomial.degreeLT F degree).smul_mem _ (hdegree j))
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    relation ((commonAnchorCoords support i j r).map domain)
  · intro y hy
    simp only [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : i ∈ support x ∧ j ∈ support x ∧ r ∈ support x := by
      simpa only [commonAnchorCoords, Finset.mem_filter, Finset.mem_univ,
        true_and] using hx
    let row : SupportRow support :=
      { coordinate := x
        anchor₀ := i
        anchor₁ := j
        point := r
        anchor₀_mem := hx'.1
        anchor₁_mem := hx'.2.1
        point_mem := hx'.2.2 }
    have hrow := congrFun (LinearMap.mem_ker.mp hkernel) row
    change dividedDifferenceAt (fun x => domain x) label q row = 0 at hrow
    change relation.eval (domain x) = 0
    simp only [relation, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [dividedDifferenceAt, hr] at hrow
    simpa only [Polynomial.eval_zero, mul_zero, add_zero] using hrow
  · rw [Finset.card_map]
    exact lt_of_lt_of_le
      (ReedSolomon.natDegree_lt_of_mem_degreeLT hrelationDegree) hcoverage

/-- Two distinct zero external anchors, each covering the same internal pair on `degree`
coordinates, kill both internal components.  Algebraically the two global pair relations have
determinant

`(label j - label i) * (label s - label r)`,

which is nonzero for distinct internal labels and distinct external anchors. -/
theorem pair_eq_zero_of_two_zero_externalAnchorCoverages
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    {i j r s : J} (hij : i ≠ j) (hrs : r ≠ s) (hir : i ≠ r)
    (hr : q r = 0) (hs : q s = 0)
    (hcoverR : degree ≤ (commonAnchorCoords support i j r).card)
    (hcoverS : degree ≤ (commonAnchorCoords support i j s).card) :
    q i = 0 ∧ q j = 0 := by
  have hR := pair_relation_of_zero_externalAnchorCoverage
    domain support label q hdegree hkernel hr hcoverR
  have hS := pair_relation_of_zero_externalAnchorCoverage
    domain support label q hdegree hkernel hs hcoverS
  let determinant : F :=
    (label j - label r) * (label s - label i) -
      (label j - label s) * (label r - label i)
  have hdetEq : determinant =
      (label j - label i) * (label s - label r) := by
    simp only [determinant]
    ring
  have hdet : determinant ≠ 0 := by
    rw [hdetEq]
    exact mul_ne_zero
      (sub_ne_zero.mpr (hlabel.ne hij.symm))
      (sub_ne_zero.mpr (hlabel.ne hrs.symm))
  have hqiMul : C determinant * q i = 0 := by
    calc
      C determinant * q i =
          C (label s - label i) *
              (C (label j - label r) * q i + C (label r - label i) * q j) -
            C (label r - label i) *
              (C (label j - label s) * q i + C (label s - label i) * q j) := by
                simp only [determinant, map_sub, map_mul]
                ring
      _ = 0 := by rw [hR, hS]; ring
  have hqi : q i = 0 :=
    (mul_eq_zero.mp hqiMul).resolve_left (C_ne_zero.mpr hdet)
  have hri : label r - label i ≠ 0 :=
    sub_ne_zero.mpr (hlabel.ne hir.symm)
  have hqjMul : C (label r - label i) * q j = 0 := by
    rw [hqi] at hR
    simpa using hR
  have hqj : q j = 0 :=
    (mul_eq_zero.mp hqjMul).resolve_left (C_ne_zero.mpr hri)
  exact ⟨hqi, hqj⟩

/-- **Pair-channel guard for a nonzero syzygy support.**  A pair whose first component is nonzero
cannot be covered on `degree` coordinates with each of two distinct zero external anchors.
Therefore at least one of the two three-label channels is subcritical.

This is stronger than the guarded two-core bound: it controls a pair of internal components even
when no coordinate contains two zero labels simultaneously. -/
theorem externalAnchor_pair_channel_subcritical
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    {i j r s : J} (hi : i ∈ nonzeroComponents q) (hij : i ≠ j)
    (hr : r ∉ nonzeroComponents q) (hs : s ∉ nonzeroComponents q)
    (hrs : r ≠ s) :
    (commonAnchorCoords support i j r).card < degree ∨
      (commonAnchorCoords support i j s).card < degree := by
  by_contra hnot
  push Not at hnot
  have hir : i ≠ r := by
    intro hir
    subst r
    exact hr hi
  have hzeroR : q r = 0 := (not_mem_nonzeroComponents_iff q r).mp hr
  have hzeroS : q s = 0 := (not_mem_nonzeroComponents_iff q s).mp hs
  obtain ⟨hqi, _hqj⟩ := pair_eq_zero_of_two_zero_externalAnchorCoverages
    domain support label hlabel q hdegree hkernel hij hrs hir hzeroR hzeroS
      hnot.1 hnot.2
  exact (mem_nonzeroComponents_iff q i).mp hi hqi

/-- Outside labels whose three-label channel with the internal pair `i,j` reaches the full degree
threshold. -/
noncomputable def criticalExternalAnchors
    (support : I → Finset J) (degree : ℕ) (U : Finset J) (i j : J) : Finset J := by
  classical
  exact (Finset.univ \ U).filter fun r =>
    degree ≤ (commonAnchorCoords support i j r).card

@[simp]
theorem mem_criticalExternalAnchors_iff
    (support : I → Finset J) (degree : ℕ) (U : Finset J) (i j r : J) :
    r ∈ criticalExternalAnchors support degree U i j ↔
      r ∉ U ∧ degree ≤ (commonAnchorCoords support i j r).card := by
  classical
  simp [criticalExternalAnchors]

/-- **Critical-channel count.**  For a pair whose first component is nonzero in a degree-bounded
kernel family, at most one zero external label can have a `degree`-sized common triple support.

This is the quotient-count form of `externalAnchor_pair_channel_subcritical`: all repeated
three-label syzygy channels through one internal pair collapse to a single exceptional external
anchor. -/
theorem criticalExternalAnchors_card_le_one
    (domain : I ↪ F) (support : I → Finset J) (label : J → F)
    (hlabel : Function.Injective label) {degree : ℕ} [NeZero degree]
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hkernel : q ∈
      (supportDividedDifference (fun x => domain x) support label).ker)
    {i j : J} (hi : i ∈ nonzeroComponents q) (hij : i ≠ j) :
    (criticalExternalAnchors support degree (nonzeroComponents q) i j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro r hr s hs
  rw [mem_criticalExternalAnchors_iff] at hr hs
  by_contra hrs
  have hsubcritical := externalAnchor_pair_channel_subcritical
    domain support label hlabel q hdegree hkernel hi hij hr.1 hs.1 hrs
  rcases hsubcritical with hsmall | hsmall
  · exact (not_lt_of_ge hr.2) hsmall
  · exact (not_lt_of_ge hs.2) hsmall

end ArkLib.ProximityGap.Frontier.SYZGuardedKernelTwoCore

open ArkLib.ProximityGap.Frontier.SYZGuardedKernelTwoCore

#print axioms externalTwoCoverage_card_lt_degree_of_mem_nonzeroComponents
#print axioms nonzeroComponents_guardedTwoCore
#print axioms exists_anchorAvoiding_guardedTwoCore_of_nonzero_gaugedKernel
#print axioms degreeAnchoredKernelRigid_of_anchorAvoidingTwoCoreFree
#print axioms pair_relation_of_zero_externalAnchorCoverage
#print axioms pair_eq_zero_of_two_zero_externalAnchorCoverages
#print axioms externalAnchor_pair_channel_subcritical
#print axioms criticalExternalAnchors_card_le_one
