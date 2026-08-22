/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAHyperplaneVertex

/-!
# Rate-quarter half predecessor: cocircuit rigidity

The no-joint clause of an MCA witness makes its decoded affine explainer
unique in the full two-row extension of the Reed--Solomon code.  More exactly,
if a codeword explains a linear combination `a*u0+b*u1` on the same witness,
then its quotient direction and codeword are the scalar multiple
`(a, a*gamma, a*w)` of the selected explainer.

This normal rigidity has the support-minimal consequence needed by the
rate-quarter quotient formulation: any extension-code word whose support is
contained in the selected error support is a scalar multiple of that error.
Thus the selected error is a genuine cocircuit of
`RS + span{u0,u1}`, rather than merely a low-weight word.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open _root_.ProximityGap Code
open ProximityGap.Frontier.MCAHyperplaneVertex

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCocircuitRigidity

variable {F iota : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype iota] [Nonempty iota] [DecidableEq iota]

/-- **Decoded-normal rigidity.**  On a nonjoint Reed--Solomon witness, every
linear combination of the two received rows that is explained by a codeword
is the corresponding scalar multiple of the selected affine explainer.

Equivalently, the normal `(1,gamma,-w)` is the unique extension-code normal
vanishing on the witness, up to scalar. -/
theorem extension_explainer_eq_smul_of_vanishes_on_witness
    (domain : iota ↪ F) (k : Nat) (S : Finset iota)
    (u0 u1 : iota → F) (gamma : F)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn
      (ReedSolomon.code domain k : Set (iota → F)) S u0 u1)
    (w : ReedSolomon.code domain k)
    (hw : ∀ i ∈ S, w.1 i = u0 i + gamma * u1 i)
    (a b : F) (c : ReedSolomon.code domain k)
    (hc : ∀ i ∈ S, c.1 i = a * u0 i + b * u1 i) :
    b = a * gamma ∧ c = a • w := by
  have hinj := explainerRestriction_injective_of_mca_witness
    domain k S u0 u1 gamma hkS hno w hw
  have hpairs :
      (b - a * gamma, c - a • w) =
        (0, (0 : ReedSolomon.code domain k)) := by
    apply hinj
    funext i
    change (c - a • w).1 i.1 - (b - a * gamma) * u1 i.1 =
      (0 : ReedSolomon.code domain k).1 i.1 - 0 * u1 i.1
    simp only [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply,
      zero_mul, sub_zero]
    rw [hc i.1 i.2, hw i.1 i.2]
    ring
  have hfirst := congrArg Prod.fst hpairs
  have hsecond := congrArg Prod.snd hpairs
  constructor
  · exact sub_eq_zero.mp hfirst
  · exact sub_eq_zero.mp hsecond

/-- **Joint-core quotient span.**  On any coordinate set of size at least
`k` where both received rows have Reed--Solomon explainers, every explained
linear combination uses exactly the corresponding linear combination of those
two codewords.  This is the rank-two contraction behind line-core packing. -/
theorem extension_explainer_eq_span_of_vanishes_on_joint_witness
    (domain : iota ↪ F) (k : Nat) (S : Finset iota)
    (u0 u1 : iota → F) (hkS : k ≤ S.card)
    (w0 w1 : ReedSolomon.code domain k)
    (hw0 : ∀ i ∈ S, w0.1 i = u0 i)
    (hw1 : ∀ i ∈ S, w1.1 i = u1 i)
    (a b : F) (c : ReedSolomon.code domain k)
    (hc : ∀ i ∈ S, c.1 i = a * u0 i + b * u1 i) :
    c = a • w0 + b • w1 := by
  apply Subtype.ext
  apply ProximityGap.Frontier.RSRestrictInjOn.rs_restrict_injOn_of_k_le
    domain k S hkS c.2 (a • w0 + b • w1).2
  funext i
  change c.1 i.1 = a * w0.1 i.1 + b * w1.1 i.1
  rw [hc i.1 i.2, hw0 i.1 i.2, hw1 i.1 i.2]

/-- The selected error word associated to an affine explainer. -/
def extensionError (u0 u1 w : iota → F) (gamma : F) : iota → F :=
  fun i => u0 i + gamma * u1 i - w i

/-- The support of a finite word. -/
def wordSupport (v : iota → F) : Finset iota :=
  Finset.univ.filter fun i => v i ≠ 0

@[simp]
theorem mem_wordSupport_iff (v : iota → F) (i : iota) :
    i ∈ wordSupport v ↔ v i ≠ 0 := by
  simp [wordSupport]

/-- **Cocircuit form.**  If another extension-code word has support contained
in the selected error support, then it is a scalar multiple of the selected
error.  Hence every nonzero selected error is support-minimal in
`RS + span{u0,u1}`. -/
theorem extension_word_eq_smul_of_support_subset
    (domain : iota ↪ F) (k : Nat) (S : Finset iota)
    (u0 u1 : iota → F) (gamma : F)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn
      (ReedSolomon.code domain k : Set (iota → F)) S u0 u1)
    (w : ReedSolomon.code domain k)
    (hw : ∀ i ∈ S, w.1 i = u0 i + gamma * u1 i)
    (a b : F) (c : ReedSolomon.code domain k)
    (hsub : wordSupport (fun i => a * u0 i + b * u1 i - c.1 i) ⊆
      wordSupport (extensionError u0 u1 w.1 gamma)) :
    (fun i => a * u0 i + b * u1 i - c.1 i) =
      a • extensionError u0 u1 w.1 gamma := by
  have hc : ∀ i ∈ S, c.1 i = a * u0 i + b * u1 i := by
    intro i hi
    have hiNot : i ∉ wordSupport (extensionError u0 u1 w.1 gamma) := by
      rw [mem_wordSupport_iff]
      simp only [extensionError]
      rw [hw i hi]
      simp
    have hiOther :
        i ∉ wordSupport (fun j => a * u0 j + b * u1 j - c.1 j) := by
      intro himem
      exact hiNot (hsub himem)
    rw [mem_wordSupport_iff] at hiOther
    exact sub_eq_zero.mp (not_ne_iff.mp hiOther) |>.symm
  have hrigid := extension_explainer_eq_smul_of_vanishes_on_witness
    domain k S u0 u1 gamma hkS hno w hw a b c hc
  funext i
  rw [hrigid.1, hrigid.2]
  simp only [Pi.smul_apply, extensionError, Submodule.coe_smul]
  ring

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCocircuitRigidity

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCocircuitRigidity.extension_explainer_eq_smul_of_vanishes_on_witness
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCocircuitRigidity.extension_explainer_eq_span_of_vanishes_on_joint_witness
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCocircuitRigidity.extension_word_eq_smul_of_support_subset
