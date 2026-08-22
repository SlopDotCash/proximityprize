/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The support-dependent divided-difference operator

Suppose a family of low-degree polynomials `q i` is labelled by distinct field elements
`label i`.  At a coordinate `x`, every incident label satisfies

```text
(q i).eval (domain x) = u0 x + label i * u1 x.
```

For any three incident indices `a`, `b`, and `i`, eliminating the two received values gives

```text
(label b - label i) * q_a(x)
  + (label i - label a) * q_b(x)
  + (label a - label b) * q_i(x) = 0.
```

This file packages all such equations as an `F`-linear map.  Its evident kernel is the family
of global polynomial pencils `q i = base + label i * slope`.  It then proves the exact reduction
needed by the simultaneous-interpolation route:

* injectivity after fixing two label coordinates to zero implies that the whole kernel consists
  of global pencils;
* supported agreement puts every decoded polynomial family in the kernel;
* if every coordinate has two incident, distinctly labelled polynomials, kernel rigidity forces
  both received rows to be evaluations of low-degree polynomials, hence forces joint RS
  agreement on every coordinate set.

The universal anchored-kernel injectivity statement is deliberately left as a hypothesis here.
It is refuted for finite domains in
`_SupportDividedDifferenceUnrestrictedKernelRefuted.lean`: unrestricted polynomials contain the
domain-vanishing polynomial.  That module supplies the corrected degree-restricted rigidity
target and proves that it retains the intended joint-agreement consequence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.SupportDividedDifferenceOperator

variable {F X J : Type} [Field F] [DecidableEq J]

/-- A row of the support-dependent operator: one coordinate and three indices incident there.
The indices need not be distinct; allowing all triples makes the operator canonical and avoids
choosing coordinate-dependent anchors. -/
structure SupportRow (support : X -> Finset J) where
  coordinate : X
  anchor₀ : J
  anchor₁ : J
  point : J
  anchor₀_mem : anchor₀ ∈ support coordinate
  anchor₁_mem : anchor₁ ∈ support coordinate
  point_mem : point ∈ support coordinate

/-- One divided-difference row evaluated on a polynomial family. -/
def dividedDifferenceAt (domain : X -> F) (label : J -> F)
    (q : J -> F[X]) {support : X -> Finset J} (row : SupportRow support) : F :=
  (label row.anchor₁ - label row.point) * (q row.anchor₀).eval (domain row.coordinate) +
    (label row.point - label row.anchor₀) * (q row.anchor₁).eval (domain row.coordinate) +
    (label row.anchor₀ - label row.anchor₁) * (q row.point).eval (domain row.coordinate)

/-- The block-Vandermonde divided-difference operator restricted to the prescribed supports. -/
noncomputable def supportDividedDifference (domain : X -> F) (support : X -> Finset J)
    (label : J -> F) : (J -> F[X]) →ₗ[F] (SupportRow support -> F) where
  toFun q row := dividedDifferenceAt domain label q row
  map_add' q r := by
    funext row
    simp only [dividedDifferenceAt, Pi.add_apply, Polynomial.eval_add]
    ring
  map_smul' c q := by
    funext row
    simp only [dividedDifferenceAt, Pi.smul_apply, Polynomial.eval_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp]
theorem supportDividedDifference_apply (domain : X -> F) (support : X -> Finset J)
    (label : J -> F) (q : J -> F[X]) (row : SupportRow support) :
    supportDividedDifference domain support label q row =
      dividedDifferenceAt domain label q row := rfl

/-- A globally joint polynomial pencil with the prescribed scalar labels. -/
noncomputable def polynomialPencil (label : J -> F) (base slope : F[X]) : J -> F[X] :=
  fun i => base + label i • slope

/-- Every global polynomial pencil is in the divided-difference kernel. -/
theorem polynomialPencil_mem_ker (domain : X -> F) (support : X -> Finset J)
    (label : J -> F) (base slope : F[X]) :
    polynomialPencil label base slope ∈
      (supportDividedDifference domain support label).ker := by
  rw [LinearMap.mem_ker]
  funext row
  change dividedDifferenceAt domain label (polynomialPencil label base slope) row = 0
  simp only [dividedDifferenceAt, polynomialPencil,
    Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

/-- The slope of the unique polynomial pencil through two distinctly labelled entries. -/
noncomputable def pencilSlope (label : J -> F) (q : J -> F[X]) (a b : J) : F[X] :=
  (label b - label a)⁻¹ • (q b - q a)

/-- The base of the unique polynomial pencil through two distinctly labelled entries. -/
noncomputable def pencilBase (label : J -> F) (q : J -> F[X]) (a b : J) : F[X] :=
  q a - label a • pencilSlope label q a b

/-- Historical unrestricted rank statement.  On finite domains this is false when a third label
exists, because the domain-vanishing polynomial lies in the gauged kernel.  See
`_SupportDividedDifferenceUnrestrictedKernelRefuted.lean` for the corrected degree-restricted
statement. -/
def AnchoredKernelRigid (domain : X -> F) (support : X -> Finset J)
    (label : J -> F) (a b : J) : Prop :=
  ∀ q : J -> F[X],
    q ∈ (supportDividedDifference domain support label).ker ->
      q a = 0 -> q b = 0 -> q = 0

/-- Polynomial families satisfying the two-anchor gauge. -/
noncomputable def anchorGauge (a b : J) : Submodule F (J -> F[X]) where
  carrier := {q | q a = 0 ∧ q b = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro q r ⟨hqa, hqb⟩ ⟨hra, hrb⟩
    simp [hqa, hqb, hra, hrb]
  smul_mem' := by
    rintro c q ⟨hqa, hqb⟩
    simp [hqa, hqb]

/-- The support-dependent operator after imposing the two-anchor gauge.  This is the linear map
whose full-column-rank theorem would discharge `AnchoredKernelRigid`. -/
noncomputable def gaugedSupportDividedDifference (domain : X -> F)
    (support : X -> Finset J) (label : J -> F) (a b : J) :
    anchorGauge (F := F) a b →ₗ[F] (SupportRow support -> F) :=
  (supportDividedDifference domain support label).comp (anchorGauge (F := F) a b).subtype

/-- The named rigidity residual is exactly trivial kernel of the gauge-restricted linear map. -/
theorem anchoredKernelRigid_iff_gauged_ker_eq_bot
    (domain : X -> F) (support : X -> Finset J) (label : J -> F) (a b : J) :
    AnchoredKernelRigid domain support label a b ↔
      (gaugedSupportDividedDifference domain support label a b).ker = ⊥ := by
  constructor
  · intro hrigid
    apply le_antisymm
    · intro q hq
      rw [Submodule.mem_bot]
      apply Subtype.ext
      exact hrigid q.1 (by simpa [gaugedSupportDividedDifference] using hq) q.2.1 q.2.2
    · exact bot_le
  · intro hker q hq hqa hqb
    let qg : anchorGauge (F := F) a b := ⟨q, hqa, hqb⟩
    have hqg : qg ∈ (gaugedSupportDividedDifference domain support label a b).ker := by
      rw [LinearMap.mem_ker]
      exact LinearMap.mem_ker.mp hq
    have hqgbot : qg ∈ (⊥ : Submodule F (anchorGauge (F := F) a b)) := hker ▸ hqg
    have hqgzero : qg = 0 := by simpa using hqgbot
    exact congrArg Subtype.val hqgzero

/-- The interpolating pencil passes through its first anchor. -/
theorem pencil_at_anchor₀ (label : J -> F) (q : J -> F[X]) (a b : J) :
    polynomialPencil label (pencilBase label q a b) (pencilSlope label q a b) a = q a := by
  simp only [polynomialPencil, pencilBase]
  abel

/-- The interpolating pencil passes through its second anchor when the labels are distinct. -/
theorem pencil_at_anchor₁ (label : J -> F) (q : J -> F[X]) {a b : J}
    (hlabel : label a ≠ label b) :
    polynomialPencil label (pencilBase label q a b) (pencilSlope label q a b) b = q b := by
  have hdiff : label b - label a ≠ 0 := sub_ne_zero.mpr hlabel.symm
  have hslope : (label b - label a) • pencilSlope label q a b = q b - q a := by
    simp only [pencilSlope, smul_smul]
    rw [mul_inv_cancel₀ hdiff, one_smul]
  simp only [polynomialPencil, pencilBase]
  calc
    q a - label a • pencilSlope label q a b + label b • pencilSlope label q a b =
        q a + (label b - label a) • pencilSlope label q a b := by
          rw [sub_smul]
          abel
    _ = q a + (q b - q a) := by rw [hslope]
    _ = q b := by abel

/-- Triviality of the two-anchor gauge kernel implies that every kernel family is a global
polynomial pencil. -/
theorem eq_polynomialPencil_of_anchoredKernelRigid
    (domain : X -> F) (support : X -> Finset J) (label : J -> F) {a b : J}
    (hlabel : label a ≠ label b)
    (hrigid : AnchoredKernelRigid domain support label a b)
    (q : J -> F[X])
    (hq : q ∈ (supportDividedDifference domain support label).ker) :
    q = polynomialPencil label (pencilBase label q a b) (pencilSlope label q a b) := by
  let pencil := polynomialPencil label (pencilBase label q a b) (pencilSlope label q a b)
  have hpencil : pencil ∈ (supportDividedDifference domain support label).ker :=
    polynomialPencil_mem_ker domain support label _ _
  have hgauge : q - pencil ∈ (supportDividedDifference domain support label).ker :=
    (supportDividedDifference domain support label).ker.sub_mem hq hpencil
  have hzero : q - pencil = 0 := hrigid (q - pencil) hgauge
    (by
      simp only [Pi.sub_apply, sub_eq_zero]
      exact pencil_at_anchor₀ label q a b |>.symm)
    (by
      simp only [Pi.sub_apply, sub_eq_zero]
      exact pencil_at_anchor₁ label q hlabel |>.symm)
  exact sub_eq_zero.mp hzero

/-- Agreement of the decoded polynomials with a received affine stack on their supports. -/
def SupportedAgreement (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (q : J -> F[X]) (u₀ u₁ : X -> F) : Prop :=
  ∀ x i, i ∈ support x ->
    (q i).eval (domain x) = u₀ x + label i * u₁ x

/-- Supported affine agreement satisfies every divided-difference equation. -/
theorem mem_ker_of_supportedAgreement
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (q : J -> F[X]) (u₀ u₁ : X -> F)
    (hagree : SupportedAgreement domain support label q u₀ u₁) :
    q ∈ (supportDividedDifference domain support label).ker := by
  rw [LinearMap.mem_ker]
  funext row
  change dividedDifferenceAt domain label q row = 0
  simp only [dividedDifferenceAt]
  rw [hagree row.coordinate row.anchor₀ row.anchor₀_mem,
    hagree row.coordinate row.anchor₁ row.anchor₁_mem,
    hagree row.coordinate row.point row.point_mem]
  ring

/-- A global polynomial pencil meeting the received affine stack at two distinct labels on every
coordinate recovers both received rows pointwise. -/
theorem stack_eq_evaluation_of_polynomialPencil
    [Fintype F] [DecidableEq F]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label)
    (q : J -> F[X]) (u₀ u₁ : X -> F) (base slope : F[X])
    (hcard : ∀ x, 2 ≤ (support x).card)
    (hagree : SupportedAgreement domain support label q u₀ u₁)
    (hq : q = polynomialPencil label base slope) :
    u₀ = (fun x => base.eval (domain x)) ∧
      u₁ = (fun x => slope.eval (domain x)) := by
  have hpoint : ∀ x, u₀ x = base.eval (domain x) ∧ u₁ x = slope.eval (domain x) := by
    intro x
    have hone : 1 < (support x).card := lt_of_lt_of_le (by omega : 1 < 2) (hcard x)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hone
    have hlab : label a ≠ label b := fun h => hab (hlabel h)
    have haffine_a :
        base.eval (domain x) + label a • slope.eval (domain x) =
          u₀ x + label a • u₁ x := by
      have h := hagree x a ha
      rw [congrFun hq a] at h
      simpa [polynomialPencil, smul_eq_mul] using h
    have haffine_b :
        base.eval (domain x) + label b • slope.eval (domain x) =
          u₀ x + label b • u₁ x := by
      have h := hagree x b hb
      rw [congrFun hq b] at h
      simpa [polynomialPencil, smul_eq_mul] using h
    have hpinned := ProximityGap.affine_eq_of_two_smul_points hlab haffine_a haffine_b
    exact ⟨hpinned.1.symm, hpinned.2.symm⟩
  constructor
  · funext x
    exact (hpoint x).1
  · funext x
    exact (hpoint x).2

/-- The full algebraic reduction: supported agreement plus anchored-kernel rigidity turns the
decoded family into a global pencil and recovers both received rows. -/
theorem jointPolynomialRealization_of_anchoredKernelRigid
    [Fintype F] [DecidableEq F]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {a b : J} (hab : a ≠ b)
    (hrigid : AnchoredKernelRigid domain support label a b)
    (q : J -> F[X]) (u₀ u₁ : X -> F)
    (hcard : ∀ x, 2 ≤ (support x).card)
    (hagree : SupportedAgreement domain support label q u₀ u₁) :
    let base := pencilBase label q a b
    let slope := pencilSlope label q a b
    q = polynomialPencil label base slope ∧
      u₀ = (fun x => base.eval (domain x)) ∧
      u₁ = (fun x => slope.eval (domain x)) := by
  dsimp only
  have hkernel := mem_ker_of_supportedAgreement domain support label q u₀ u₁ hagree
  have hpencil := eq_polynomialPencil_of_anchoredKernelRigid domain support label
    (hlabel.ne hab) hrigid q hkernel
  exact ⟨hpencil,
    stack_eq_evaluation_of_polynomialPencil domain support label hlabel q u₀ u₁ _ _
      hcard hagree hpencil⟩

/-- The two polynomials recovered from low-degree decoded polynomials remain low degree. -/
theorem pencilBaseSlope_mem_degreeLT (label : J -> F) (q : J -> F[X]) {a b : J} {deg : Nat}
    (hdegree : ∀ i, q i ∈ Polynomial.degreeLT F deg) :
    pencilBase label q a b ∈ Polynomial.degreeLT F deg ∧
      pencilSlope label q a b ∈ Polynomial.degreeLT F deg := by
  have hslope : pencilSlope label q a b ∈ Polynomial.degreeLT F deg :=
    (Polynomial.degreeLT F deg).smul_mem _
      ((Polynomial.degreeLT F deg).sub_mem (hdegree b) (hdegree a))
  exact ⟨(Polynomial.degreeLT F deg).sub_mem (hdegree a)
    ((Polynomial.degreeLT F deg).smul_mem _ hslope), hslope⟩

/-- **Jointness consequence.**  Under the anchored rank hypothesis, a low-degree decoded family
whose support incidence is at least two forces `pairJointAgreesOn` for the Reed--Solomon code on
every requested coordinate set. -/
theorem pairJointAgreesOn_of_anchoredKernelRigid
    [Fintype X] [Nonempty X] [DecidableEq X]
    [Fintype F] [DecidableEq F]
    (domain : X ↪ F) (support : X -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) {a b : J} (hab : a ≠ b)
    (hrigid : AnchoredKernelRigid (fun x => domain x) support label a b)
    (q : J -> F[X]) (u₀ u₁ : X -> F) {deg : Nat}
    (hdegree : ∀ i, q i ∈ Polynomial.degreeLT F deg)
    (hcard : ∀ x, 2 ≤ (support x).card)
    (hagree : SupportedAgreement (fun x => domain x) support label q u₀ u₁)
    (S : Finset X) :
    ProximityGap.pairJointAgreesOn
      (ReedSolomon.code domain deg : Set (X -> F)) S u₀ u₁ := by
  let base := pencilBase label q a b
  let slope := pencilSlope label q a b
  have hjoint := jointPolynomialRealization_of_anchoredKernelRigid
    (fun x => domain x) support label hlabel hab hrigid q u₀ u₁ hcard hagree
  dsimp only at hjoint
  have hdegree' := pencilBaseSlope_mem_degreeLT label q (a := a) (b := b) hdegree
  refine ⟨fun x => base.eval (domain x), ?_, fun x => slope.eval (domain x), ?_, ?_⟩
  · exact ⟨base, hdegree'.1, rfl⟩
  · exact ⟨slope, hdegree'.2, rfl⟩
  · intro x _hx
    exact ⟨congrFun hjoint.2.1 x |>.symm, congrFun hjoint.2.2 x |>.symm⟩

end ArkLib.ProximityGap.Frontier.SupportDividedDifferenceOperator

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.SupportDividedDifferenceOperator
#print axioms polynomialPencil_mem_ker
#print axioms anchoredKernelRigid_iff_gauged_ker_eq_bot
#print axioms eq_polynomialPencil_of_anchoredKernelRigid
#print axioms mem_ker_of_supportedAgreement
#print axioms jointPolynomialRealization_of_anchoredKernelRigid
#print axioms pairJointAgreesOn_of_anchoredKernelRigid
