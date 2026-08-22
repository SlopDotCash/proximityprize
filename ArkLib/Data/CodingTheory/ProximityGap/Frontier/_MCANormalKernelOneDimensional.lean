/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAHyperplaneVertex
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# One-dimensional normal kernels for Reed--Solomon MCA witnesses

This file is the dual completion of `_MCAHyperplaneVertex.lean`.

For a degree-`<k` Reed--Solomon code, a coordinate `i` defines the row

`ell_i = (-u0(i), -u1(i), ev_i)`.

Here `ev_i` is evaluation on the `k`-dimensional polynomial/codeword space;
in the monomial coefficient basis it is exactly

`(1, domain(i), ..., domain(i)^(k-1))`.

A line explainer `w = u0 + gamma*u1` on `S` gives the normal

`z = (1, gamma, w)`.

The existing hyperplane-vertex theorem says that the auxiliary map
`(alpha,c) |-> c|S-alpha*u1|S` is injective under the no-joint clause and
`k <= |S|`.  We use it to prove the literal dual statement:

* the common kernel of the rows `ell_i`, `i in S`, is exactly `span{z}`;
* consequently that normal kernel has finrank one;
* every Reed--Solomon MCA event supplies such a one-dimensional normal
  kernel on its own witness set.

The second section completes the existing secant-slope lemma.  Two distinct
line explainers determine a source pair `(c0,c1)` on their shared
coordinates; if the overlap has at least `k` coordinates, MDS restriction
rigidity makes that source pair unique.

These are local rigidity bridges, not the global rich-hyperplane incidence
bound required for the saturated P1 lower endpoint.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped NNReal

namespace ProximityGap.Frontier.MCANormalKernelOneDimensional

open ArkLib.ProximityGap.Frontier.RSRestrictInjOn
open ProximityGap.Frontier.MCAHyperplaneVertex
open ProximityGap.MCAWitnessSpread

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## The row-normal kernel -/

/-- Normal coordinates `(a,b,c)`, where `c` is a degree-`<k`
Reed--Solomon codeword.  In a polynomial coefficient basis this is the
`k+2` dimensional space containing normals `(1,gamma,q)`. -/
abbrev NormalSpace (domain : ι ↪ F) (k : ℕ) :=
  F × F × ReedSolomon.code domain k

/-- Evaluate a normal against every witness row.  At `i` the value is

`c(i) - a*u0(i) - b*u1(i)`.

After identifying a codeword with its degree-`<k` coefficient vector, this
is dot product with `(-u0(i),-u1(i),1,x,...,x^(k-1))`. -/
noncomputable def normalEvaluation
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F) :
    NormalSpace domain k →ₗ[F] (S → F) where
  toFun z := fun i => z.2.2.1 i.1 - z.1 * u₀ i.1 - z.2.1 * u₁ i.1
  map_add' x y := by
    funext i
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The canonical normal attached to the explainer `w` at scalar `gamma`. -/
def eventNormal (domain : ι ↪ F) (k : ℕ) (gamma : F)
    (w : ReedSolomon.code domain k) : NormalSpace domain k :=
  (1, gamma, w)

theorem eventNormal_ne_zero
    (domain : ι ↪ F) (k : ℕ) (gamma : F)
    (w : ReedSolomon.code domain k) :
    eventNormal domain k gamma w ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simpa [eventNormal] using hfirst

/-- An explainer is literally a normal annihilating every witness row. -/
theorem eventNormal_mem_ker
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F)
    (gamma : F) (w : ReedSolomon.code domain k)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + gamma * u₁ i) :
    eventNormal domain k gamma w ∈
      LinearMap.ker (normalEvaluation domain k S u₀ u₁) := by
  rw [LinearMap.mem_ker]
  funext i
  change w.1 i.1 - 1 * u₀ i.1 - gamma * u₁ i.1 = 0
  rw [hw i.1 i.2]
  ring

/-- Every normal in an MCA witness kernel is the scalar multiple given by
its first coordinate of the event normal. -/
theorem normal_eq_fst_smul_eventNormal
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F)
    (gamma : F) (w : ReedSolomon.code domain k)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn
      (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + gamma * u₁ i)
    (z : NormalSpace domain k)
    (hz : z ∈ LinearMap.ker (normalEvaluation domain k S u₀ u₁)) :
    z = z.1 • eventNormal domain k gamma w := by
  have hinjective := explainerRestriction_injective_of_mca_witness
    domain k S u₀ u₁ gamma hkS hno w hw
  have hzcoord : ∀ i ∈ S,
      z.2.2.1 i - z.1 * u₀ i - z.2.1 * u₁ i = 0 := by
    intro i hi
    have hfun := congrFun (LinearMap.mem_ker.mp hz) ⟨i, hi⟩
    simpa [normalEvaluation] using hfun
  let alpha : F := z.2.1 - z.1 * gamma
  let d : ReedSolomon.code domain k := z.2.2 - z.1 • w
  have haux : explainerRestriction domain k S u₁ (alpha, d) = 0 := by
    funext i
    have hzi := hzcoord i.1 i.2
    change d.1 i.1 - alpha * u₁ i.1 = 0
    simp only [d, alpha, Submodule.coe_sub, Pi.sub_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hw i.1 i.2]
    linear_combination hzi
  have hpair : (alpha, d) = (0, 0) := by
    apply hinjective
    calc
      explainerRestriction domain k S u₁ (alpha, d) = 0 := haux
      _ = explainerRestriction domain k S u₁
          (0 : F × ReedSolomon.code domain k) := (map_zero _).symm
  have halpha : alpha = 0 := congrArg Prod.fst hpair
  have hd : d = 0 := congrArg Prod.snd hpair
  have hb : z.2.1 = z.1 * gamma := by
    exact sub_eq_zero.mp halpha
  have hc : z.2.2 = z.1 • w := by
    exact sub_eq_zero.mp hd
  apply Prod.ext
  · simp [eventNormal]
  · apply Prod.ext
    · simpa [eventNormal, hb]
    · simpa [eventNormal, hc]

/-- **Exact normal kernel.**  Nonjointness plus `k` witness coordinates
makes the row-normal kernel precisely the span of `(1,gamma,w)`. -/
theorem normalKernel_eq_span_eventNormal
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F)
    (gamma : F) (w : ReedSolomon.code domain k)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn
      (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + gamma * u₁ i) :
    LinearMap.ker (normalEvaluation domain k S u₀ u₁) =
      Submodule.span F {eventNormal domain k gamma w} := by
  apply le_antisymm
  · intro z hz
    apply Submodule.mem_span_singleton.mpr
    exact ⟨z.1, (normal_eq_fst_smul_eventNormal domain k S u₀ u₁
      gamma w hkS hno hw z hz).symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact eventNormal_mem_ker domain k S u₀ u₁ gamma w hw

/-- **One-dimensionality.**  The literal normal kernel of an MCA witness has
finrank exactly one. -/
theorem finrank_normalKernel_eq_one
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F)
    (gamma : F) (w : ReedSolomon.code domain k)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn
      (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + gamma * u₁ i) :
    Module.finrank F
      (LinearMap.ker (normalEvaluation domain k S u₀ u₁)) = 1 := by
  rw [normalKernel_eq_span_eventNormal domain k S u₀ u₁
    gamma w hkS hno hw]
  exact finrank_span_singleton (eventNormal_ne_zero domain k gamma w)

/-- **Every Reed--Solomon MCA-bad scalar is a unique projective normal.**
Unpacking an `mcaEvent` supplies a witness set and explainer whose row-normal
kernel is exactly the event-normal line. -/
theorem mcaEvent_exists_oneDimensional_normalKernel
    (domain : ι ↪ F) (k : ℕ) (delta : ℝ≥0) (u₀ u₁ : ι → F)
    (gamma : F)
    (hevent : mcaEvent (F := F) (A := F)
      (ReedSolomon.code domain k : Set (ι → F)) delta u₀ u₁ gamma) :
    ∃ S : Finset ι, ∃ w : ReedSolomon.code domain k,
      (S.card : ℝ≥0) ≥ (1 - delta) * Fintype.card ι ∧
      k < S.card ∧
      (∀ i ∈ S, w.1 i = u₀ i + gamma * u₁ i) ∧
      ¬ pairJointAgreesOn
        (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁ ∧
      LinearMap.ker (normalEvaluation domain k S u₀ u₁) =
        Submodule.span F {eventNormal domain k gamma w} ∧
      Module.finrank F
        (LinearMap.ker (normalEvaluation domain k S u₀ u₁)) = 1 := by
  obtain ⟨S, hcard, hkS, ⟨w, hwmem, hw⟩, hno⟩ :=
    mcaEvent_rs_exists_witness_card_gt domain hevent
  let wCode : ReedSolomon.code domain k := ⟨w, hwmem⟩
  have hwCode : ∀ i ∈ S, wCode.1 i = u₀ i + gamma * u₁ i := by
    intro i hi
    simpa [wCode, smul_eq_mul] using hw i hi
  refine ⟨S, wCode, hcard, hkS, hwCode, hno, ?_, ?_⟩
  · exact normalKernel_eq_span_eventNormal domain k S u₀ u₁ gamma wCode
      (Nat.le_of_lt hkS) hno hwCode
  · exact finrank_normalKernel_eq_one domain k S u₀ u₁ gamma wCode
      (Nat.le_of_lt hkS) hno hwCode

/-! ## Two explainers determine a unique source line -/

/-- The source direction obtained by a divided difference of two distinct
line explainers. -/
noncomputable def secantDirection
    (domain : ι ↪ F) (k : ℕ) (gamma eta : F)
    (wGamma wEta : ReedSolomon.code domain k) :
    ReedSolomon.code domain k :=
  (gamma - eta)⁻¹ • (wGamma - wEta)

/-- The source origin obtained after reconstructing the direction. -/
noncomputable def secantOrigin
    (domain : ι ↪ F) (k : ℕ) (gamma eta : F)
    (wGamma wEta : ReedSolomon.code domain k) :
    ReedSolomon.code domain k :=
  wGamma - gamma • secantDirection domain k gamma eta wGamma wEta

/-- Two distinct explainers give a source pair agreeing with `(u0,u1)` on
their shared coordinates, and both explainers lie on the resulting global
polynomial/codeword line. -/
theorem secantSourceLine_spec
    (domain : ι ↪ F) (k : ℕ) {S T : Finset ι} (u₀ u₁ : ι → F)
    {gamma eta : F} (hne : gamma ≠ eta)
    (wGamma wEta : ReedSolomon.code domain k)
    (hGamma : ∀ i ∈ S, wGamma.1 i = u₀ i + gamma * u₁ i)
    (hEta : ∀ i ∈ T, wEta.1 i = u₀ i + eta * u₁ i) :
    (∀ i ∈ S ∩ T,
      (secantOrigin domain k gamma eta wGamma wEta).1 i = u₀ i ∧
      (secantDirection domain k gamma eta wGamma wEta).1 i = u₁ i) ∧
    wGamma = secantOrigin domain k gamma eta wGamma wEta +
      gamma • secantDirection domain k gamma eta wGamma wEta ∧
    wEta = secantOrigin domain k gamma eta wGamma wEta +
      eta • secantDirection domain k gamma eta wGamma wEta := by
  have hslope := line_slope_codeword_of_two_witnesses
    (ReedSolomon.code domain k) hne wGamma.2 wEta.2 hGamma hEta
  constructor
  · intro i hi
    have hdir : (secantDirection domain k gamma eta wGamma wEta).1 i = u₁ i := by
      exact hslope.2 i hi
    refine ⟨?_, hdir⟩
    simp only [secantOrigin, Submodule.coe_sub, Pi.sub_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hGamma i (Finset.mem_inter.mp hi).1, hdir]
    ring
  · constructor
    · simp [secantOrigin]
    · apply Subtype.ext
      funext i
      simp only [secantOrigin, secantDirection, Submodule.coe_add,
        Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp [sub_ne_zero.mpr hne]
      ring

/-- **Unique shared source line.**  If two distinct explainer events overlap
on at least `k` coordinates, their secant origin and direction are the unique
degree-`<k` Reed--Solomon pair agreeing with the two source rows throughout
that overlap. -/
theorem secantSourceLine_unique_of_k_le_inter
    (domain : ι ↪ F) (k : ℕ) {S T : Finset ι} (u₀ u₁ : ι → F)
    {gamma eta : F} (hne : gamma ≠ eta)
    (wGamma wEta : ReedSolomon.code domain k)
    (hGamma : ∀ i ∈ S, wGamma.1 i = u₀ i + gamma * u₁ i)
    (hEta : ∀ i ∈ T, wEta.1 i = u₀ i + eta * u₁ i)
    (hk : k ≤ (S ∩ T).card) :
    ∃! source : ReedSolomon.code domain k × ReedSolomon.code domain k,
      (∀ i ∈ S ∩ T, source.1.1 i = u₀ i ∧ source.2.1 i = u₁ i) ∧
      wGamma = source.1 + gamma • source.2 ∧
      wEta = source.1 + eta • source.2 := by
  let source : ReedSolomon.code domain k × ReedSolomon.code domain k :=
    (secantOrigin domain k gamma eta wGamma wEta,
      secantDirection domain k gamma eta wGamma wEta)
  have hspec := secantSourceLine_spec domain k u₀ u₁ hne
    wGamma wEta hGamma hEta
  refine ⟨source, ?_, ?_⟩
  · exact hspec
  · intro other hother
    apply Prod.ext
    · apply Subtype.ext
      apply rs_restrict_injOn_of_k_le domain k (S ∩ T) hk
        other.1.2 source.1.2
      funext i
      exact (hother.1 i.1 i.2).1.trans (hspec.1 i.1 i.2).1.symm
    · apply Subtype.ext
      apply rs_restrict_injOn_of_k_le domain k (S ∩ T) hk
        other.2.2 source.2.2
      funext i
      exact (hother.1 i.1 i.2).2.trans (hspec.1 i.1 i.2).2.symm

end ProximityGap.Frontier.MCANormalKernelOneDimensional

/-! ## Axiom audit -/

open ProximityGap.Frontier.MCANormalKernelOneDimensional
#print axioms normal_eq_fst_smul_eventNormal
#print axioms normalKernel_eq_span_eventNormal
#print axioms finrank_normalKernel_eq_one
#print axioms mcaEvent_exists_oneDimensional_normalKernel
#print axioms secantSourceLine_spec
#print axioms secantSourceLine_unique_of_k_le_inter
