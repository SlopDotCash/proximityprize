/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceOperator

/-!
# Exact local rigidity of the support divided-difference rows

The global predecessor residual is a block-Vandermonde rank statement.  This file isolates its
degree-zero, one-coordinate factor: once two distinctly labelled anchor values are fixed, every
vanishing divided-difference row pins the remaining value to the unique affine function of the
label.  Thus a coordinate containing `s` labels has exactly `s - 2` independent local conditions;
any remaining loss in the global operator comes only from coupling these local conditions through
the degree bound.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SupportDividedDifferenceLocalRigidity

variable {F J : Type} [Field F]

open SupportDividedDifferenceOperator

/-- The affine slope through two distinctly labelled scalar values. -/
noncomputable def scalarSlope (label value : J → F) (a b : J) : F :=
  (label b - label a)⁻¹ * (value b - value a)

/-- The affine intercept through two distinctly labelled scalar values. -/
noncomputable def scalarBase (label value : J → F) (a b : J) : F :=
  value a - label a * scalarSlope label value a b

/-- One local divided-difference equation pins the third value to the affine interpolant through
the two anchors. -/
theorem value_eq_scalarBase_add_label_mul_scalarSlope
    (label value : J → F) {a b i : J} (hab : label a ≠ label b)
    (hrow :
      (label b - label i) * value a +
          (label i - label a) * value b +
          (label a - label b) * value i = 0) :
    value i = scalarBase label value a b + label i * scalarSlope label value a b := by
  have hd : label b - label a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [scalarBase, scalarSlope]
  field_simp
  linear_combination -hrow

/-- Conversely, values affine in their labels satisfy every local divided-difference row. -/
theorem dividedDifference_eq_zero_of_eq_affine
    (label value : J → F) (base slope : F) {a b i : J}
    (hvalue : ∀ j, value j = base + label j * slope) :
    (label b - label i) * value a +
        (label i - label a) * value b +
        (label a - label b) * value i = 0 := by
  rw [hvalue a, hvalue b, hvalue i]
  ring

/-- With distinct anchors, simultaneous local divided-difference vanishing is equivalent to the
explicit affine-in-label law. -/
theorem all_dividedDifferences_zero_iff_eq_affine
    (label value : J → F) {a b : J} (hab : label a ≠ label b) :
    (∀ i,
      (label b - label i) * value a +
          (label i - label a) * value b +
          (label a - label b) * value i = 0) ↔
      (∀ i, value i = scalarBase label value a b +
        label i * scalarSlope label value a b) := by
  constructor
  · intro h i
    exact value_eq_scalarBase_add_label_mul_scalarSlope label value hab (h i)
  · intro h i
    exact dividedDifference_eq_zero_of_eq_affine label value
      (scalarBase label value a b) (scalarSlope label value a b) h

/-- Direct operator-facing form: at one coordinate, a kernel family is forced to be affine in
the labels on the entire support as soon as two distinct anchor labels occur there. -/
theorem eval_eq_local_affine_of_mem_ker
    {I : Type} [DecidableEq J] (domain : I → F) (support : I → Finset J)
    (label : J → F) (q : J → Polynomial F) (x : I) {a b : J}
    (ha : a ∈ support x) (hb : b ∈ support x) (hab : label a ≠ label b)
    (hq : q ∈ (supportDividedDifference domain support label).ker) :
    ∀ i ∈ support x,
      (q i).eval (domain x) =
        scalarBase label (fun j => (q j).eval (domain x)) a b +
          label i * scalarSlope label (fun j => (q j).eval (domain x)) a b := by
  intro i hi
  let row : SupportRow support :=
    { coordinate := x
      anchor₀ := a
      anchor₁ := b
      point := i
      anchor₀_mem := ha
      anchor₁_mem := hb
      point_mem := hi }
  apply value_eq_scalarBase_add_label_mul_scalarSlope label
    (fun j => (q j).eval (domain x)) hab
  have hzero := congrFun (LinearMap.mem_ker.mp hq) row
  exact hzero

/-- If every coordinate support comes with two distinctly labelled anchors, membership in the
divided-difference kernel is *exactly* coordinatewise realizability by an affine received stack.
This pins the semantic content of the local rows: all additional force in the prize route must
come from the global low-degree coupling, not from an unextracted local constraint. -/
theorem mem_ker_iff_exists_supportedAgreement
    {I : Type} [DecidableEq J] (domain : I → F) (support : I → Finset J)
    (label : J → F) (anchor₀ anchor₁ : I → J)
    (hanchor₀ : ∀ x, anchor₀ x ∈ support x)
    (hanchor₁ : ∀ x, anchor₁ x ∈ support x)
    (hlabel : ∀ x, label (anchor₀ x) ≠ label (anchor₁ x))
    (q : J → Polynomial F) :
    q ∈ (supportDividedDifference domain support label).ker ↔
      ∃ u₀ u₁, SupportedAgreement domain support label q u₀ u₁ := by
  constructor
  · intro hq
    let u₀ : I → F := fun x =>
      scalarBase label (fun j => (q j).eval (domain x)) (anchor₀ x) (anchor₁ x)
    let u₁ : I → F := fun x =>
      scalarSlope label (fun j => (q j).eval (domain x)) (anchor₀ x) (anchor₁ x)
    refine ⟨u₀, u₁, ?_⟩
    intro x i hi
    exact eval_eq_local_affine_of_mem_ker domain support label q x
      (hanchor₀ x) (hanchor₁ x) (hlabel x) hq i hi
  · rintro ⟨u₀, u₁, hagree⟩
    exact mem_ker_of_supportedAgreement domain support label q u₀ u₁ hagree

end ArkLib.ProximityGap.Frontier.SupportDividedDifferenceLocalRigidity

open ArkLib.ProximityGap.Frontier.SupportDividedDifferenceLocalRigidity

#print axioms value_eq_scalarBase_add_label_mul_scalarSlope
#print axioms dividedDifference_eq_zero_of_eq_affine
#print axioms all_dividedDifferences_zero_iff_eq_affine
#print axioms eval_eq_local_affine_of_mem_ker
#print axioms mem_ker_iff_exists_supportedAgreement
