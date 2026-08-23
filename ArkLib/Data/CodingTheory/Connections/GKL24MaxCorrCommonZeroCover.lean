/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Connections.GKL24SunflowerCore
import ArkLib.ToMathlib.Bridge2GCXK25

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# GKL24 max-corr witness cover via the common-zero domain (#389)

This file sharpens the historical `GKL24MaxCorrStrictWitnessCoverFalseAsStated` reduction by
removing the two-distinct-witnesses case split of
`exists_maxCorrAgreeDomain_strict_of_two_witnesses`.

The key object is `commonZero u₀ u₁ w = {i : u₁ i = 0 ∧ w i = u₀ i}`, the canonical candidate
maximal correlated-agreement domain of GKL24 Lemma 1.  Its containment in every line-agreement
set `lineAgreeSet u₀ u₁ w γ` is **unconditional** (`commonZero_subset_lineAgreeSet`) — on
`commonZero`, `u₁ = 0`, so `u₀ + γ•u₁ = u₀ = w` regardless of `γ`.  The two distinct witnesses
in the prior theorem were used *only* for the `corrAgreeDomain` SIZE bound, never for
maximality or containment.

Consequences:
* `maxCorrAgreeDomain_commonZero_of_corrAgreeDomain` — maximality of `commonZero` from a single
  `corrAgreeDomain` + code-determination `hCodeDet`, for codewords of ANY witness multiplicity.
* `exists_maxCorrAgreeDomain_strict_of_commonZero_maximal` — the per-`w` strict subset-cover
  clause from maximality of `commonZero`, no witness split.
* `CommonZeroMaximalDomainFalseAsStated` — the smaller but still too-strong historical surface
  (per stack, per carried `w`, `commonZero` is a maximal domain; the carrier is automatic from
  `mcaBad_subset_biUnion_mcaBadWitness`).
* `GKL24MaxCorrWitnessCoverHypothesis_of_commonZeroMaximal` — the end-to-end route to the full
  max-corr hypothesis under `2δ ≤ p ≤ 1`.

This is useful as a reduction lemma, but not as a live residual: the unrestricted `∀ u` version is
false in the same isolated-bad-scalar regime as the older max-domain surfaces. The live open
interface remains the bounded carrier/list-size residual `GKL24FirstMomentWitnessCoverResidual`.
-/

namespace ProximityGap

open scoped NNReal
open Finset Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The common zero-agreement set of a codeword `w` against a stack `(u₀, u₁)`:
`{i : u₁ i = 0 ∧ w i = u₀ i}`. This is the canonical candidate maximal correlated-agreement
domain in GKL24 Lemma 1; it is joint-agreement (`pairJointAgreesOn_common`) and is contained in
every line-agreement set `lineAgreeSet w γ`. -/
def commonZero (u₀ u₁ w : ι → F) : Finset ι :=
  Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)

/-- **`commonZero` is contained in every line-agreement set, unconditionally.**  No second
witness, no `γ ≠ γ'` needed: on `commonZero`, `u₁ = 0` so `u₀ + γ • u₁ = u₀ = w`. This is the
single-witness-safe containment that the two-witness theorem proved only as a by-product. -/
theorem commonZero_subset_lineAgreeSet (u₀ u₁ w : ι → F) (γ : F) :
    commonZero u₀ u₁ w ⊆ lineAgreeSet u₀ u₁ w γ := by
  intro i hi
  rw [commonZero, Finset.mem_filter] at hi
  rw [mem_lineAgreeSet_iff, hi.2.1, smul_zero, add_zero]
  exact hi.2.2

/-- **Uniform per-codeword discharge (subset form), conditional on maximality of `commonZero`.**
If `commonZero u₀ u₁ w` is a maximal correlated-agreement domain at rate `p`, then it witnesses
the per-`w` clause of `GKL24MaxCorrStrictWitnessCoverFalseAsStated_of_subset_cover`: a maximal
correlated-agreement domain contained in every bad witness's line-agreement set.

Crucially this holds for `w` with ANY number of bad witnesses — zero, one, or many — because the
containment `commonZero ⊆ lineAgreeSet w γ` is unconditional. This strictly subsumes
`exists_maxCorrAgreeDomain_strict_of_two_witnesses` (which required two distinct witnesses and
`hCodeDet`) and isolates the open GKL24 first-moment kernel to the single maximality hypothesis. -/
theorem exists_maxCorrAgreeDomain_subset_of_commonZero_maximal
    {MC : Submodule F (ι → F)} {δ p : ℝ≥0} {u₀ u₁ w : ι → F}
    (hmax : maxCorrAgreeDomain MC p u₀ u₁ (commonZero u₀ u₁ w)) :
    ∃ D : Finset ι, maxCorrAgreeDomain MC p u₀ u₁ D ∧
      ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
        D ⊆ lineAgreeSet u₀ u₁ w γ :=
  ⟨commonZero u₀ u₁ w, hmax, fun γ _ => commonZero_subset_lineAgreeSet u₀ u₁ w γ⟩

/-- **Strict-expansion form, conditional on maximality of `commonZero`.**  Same hypothesis,
delivering the strict false surface's per-`w` clause directly (the strict expansion follows from the
containment via `ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn`, since `commonZero` is a
joint-agreement domain). -/
theorem exists_maxCorrAgreeDomain_strict_of_commonZero_maximal
    {MC : Submodule F (ι → F)} {δ p : ℝ≥0} {u₀ u₁ w : ι → F}
    (hmax : maxCorrAgreeDomain MC p u₀ u₁ (commonZero u₀ u₁ w)) :
    ∃ D : Finset ι, maxCorrAgreeDomain MC p u₀ u₁ D ∧
      ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
        D ⊂ lineAgreeSet u₀ u₁ w γ :=
  ⟨commonZero u₀ u₁ w, hmax, fun γ hγ =>
    ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn hγ
      (commonZero_subset_lineAgreeSet u₀ u₁ w γ) hmax.1.2⟩

/-- **Single-witness-safe maximality of `commonZero`.**  If `commonZero u₀ u₁ w` is already a
correlated-agreement domain (the OPEN size kernel: `|commonZero| ≥ (1−p)·n`), then under the
code-determination hypothesis `hCodeDet` (codewords agreeing on `commonZero` coincide — the
Johnson-regime `p·n < minDist` consequence) it is *maximal*.

This extracts exactly the maximality half of `maxCorrAgreeDomain_commonZero_of_two_witnesses`
(GKL24SunflowerCore) and shows it needs NO second witness — the two witnesses in that theorem
were used only to establish the `corrAgreeDomain` SIZE bound, not maximality. So the open content
collapses to a single set: `commonZero` is large. Maximality is free given `hCodeDet`, for
codewords with any witness multiplicity. -/
theorem maxCorrAgreeDomain_commonZero_of_corrAgreeDomain
    {MC : Submodule F (ι → F)} {p : ℝ≥0} {u₀ u₁ w : ι → F} (hw : w ∈ MC)
    (hcorr : corrAgreeDomain MC p u₀ u₁ (commonZero u₀ u₁ w))
    (hCodeDet : ∀ a ∈ MC, ∀ b ∈ MC,
      (∀ i ∈ commonZero u₀ u₁ w, a i = b i) → a = b) :
    maxCorrAgreeDomain MC p u₀ u₁ (commonZero u₀ u₁ w) := by
  classical
  refine ⟨hcorr, fun E hC₀E hE => ?_⟩
  obtain ⟨_, v₀, hv₀, v₁, hv₁, hagreeE⟩ := hE
  -- On commonZero, v₁ = 0 and v₀ = w by code-determination.
  have hv1zero : v₁ = 0 := by
    refine hCodeDet v₁ hv₁ 0 MC.zero_mem (fun i hi => ?_)
    have hmem := hi
    rw [commonZero, Finset.mem_filter] at hmem
    rw [Pi.zero_apply, (hagreeE i (hC₀E hi)).2]; exact hmem.2.1
  have hv0w : v₀ = w := by
    refine hCodeDet v₀ hv₀ w hw (fun i hi => ?_)
    have hmem := hi
    rw [commonZero, Finset.mem_filter] at hmem
    rw [(hagreeE i (hC₀E hi)).1]; exact hmem.2.2.symm
  intro i hiE
  rw [commonZero, Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_, ?_⟩
  · rw [← (hagreeE i hiE).2, hv1zero, Pi.zero_apply]
  · rw [← (hagreeE i hiE).1, hv0w]

/-- **The genuinely-open size kernel, isolated.**  Combining the above: from the OPEN size bound
`corrAgreeDomain MC p u₀ u₁ (commonZero u₀ u₁ w)` plus code-determination `hCodeDet`, the per-`w`
subset-cover clause holds for `w` of ANY witness multiplicity. This is the sharpest reduction:
the *entire* open content of the GKL24 first-moment / max-corr route is now the single inequality
`(1−p)·n ≤ |commonZero u₀ u₁ w|` (joint agreement on `commonZero` is already proven). -/
theorem exists_maxCorrAgreeDomain_subset_of_commonZero_large
    {MC : Submodule F (ι → F)} {δ p : ℝ≥0} {u₀ u₁ w : ι → F} (hw : w ∈ MC)
    (hcorr : corrAgreeDomain MC p u₀ u₁ (commonZero u₀ u₁ w))
    (hCodeDet : ∀ a ∈ MC, ∀ b ∈ MC,
      (∀ i ∈ commonZero u₀ u₁ w, a i = b i) → a = b) :
    ∃ D : Finset ι, maxCorrAgreeDomain MC p u₀ u₁ D ∧
      ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
        D ⊂ lineAgreeSet u₀ u₁ w γ :=
  exists_maxCorrAgreeDomain_strict_of_commonZero_maximal (δ := δ)
    (maxCorrAgreeDomain_commonZero_of_corrAgreeDomain hw hcorr hCodeDet)

/-- **The strictly smaller false-as-stated surface.**  Per stack and per carried codeword `w` in
the automatic biUnion carrier, the common zero-agreement set `commonZero u₀ u₁ w` is a maximal
correlated-agreement domain at rate `p`.

This is no longer counted as a residual because the unrestricted statement is too strong:
arbitrary stacks can have isolated bad scalars without a large common-zero maximal domain. It is
retained only as a named historical certificate for conditional reductions. -/
def CommonZeroMaximalDomainFalseAsStated
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (B_T : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        (∀ w ∈ (MC : Set (ι → F)), w ∈ T) ∧
        (T.card : ℝ) ≤ B_T ∧
        ∀ w ∈ T, maxCorrAgreeDomain MC p (u 0) (u 1) (commonZero (u 0) (u 1) w)

/-- **`CommonZeroMaximalDomainFalseAsStated ⟹ GKL24MaxCorrStrictWitnessCoverFalseAsStated`.**
The reduction: the carrier `T` covers all of `MC`, so `mcaBad ⊆ biUnion mcaBadWitness`
automatically (`mcaBad_subset_biUnion_mcaBadWitness`); and each carried `w` has its per-`w`
strict clause discharged by `exists_maxCorrAgreeDomain_strict_of_commonZero_maximal`. No
parameter relation, no `hCodeDet`, no witness-multiplicity split. -/
theorem GKL24MaxCorrStrictWitnessCoverFalseAsStated_of_commonZeroMaximal
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hres : CommonZeroMaximalDomainFalseAsStated MC δ p B_T) :
    GKL24MaxCorrStrictWitnessCoverFalseAsStated MC δ p B_T := by
  intro u
  obtain ⟨T, hTsub, hTcover, hcard, hTmax⟩ := hres u
  refine ⟨T, hTsub, ?_, hcard, fun w hw => ?_⟩
  · -- biUnion cover is automatic from the union bound, since `T ⊇ MC`.
    exact mcaBad_subset_biUnion_mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) T hTcover
  · exact exists_maxCorrAgreeDomain_strict_of_commonZero_maximal (δ := δ) (hTmax w hw)

/-- **End-to-end: `CommonZeroMaximalDomainFalseAsStated ⟹ GKL24MaxCorrWitnessCoverHypothesis`**
under the Johnson parameter relation `2δ ≤ p ≤ 1` (the pairwise large-intersection clause is
recovered by the in-tree `_of_strict_cover` bridge). This routes the full max-corr hypothesis
all the way down to the single isolated kernel `commonZero` is a maximal domain. -/
theorem GKL24MaxCorrWitnessCoverHypothesis_of_commonZeroMaximal
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hp_le_one : p ≤ 1)
    (hδp : 2 * (δ : ℝ) ≤ (p : ℝ))
    (hres : CommonZeroMaximalDomainFalseAsStated MC δ p B_T) :
    GKL24MaxCorrWitnessCoverHypothesis MC δ p B_T :=
  GKL24MaxCorrWitnessCoverHypothesis_of_strict_cover MC δ p hp_le_one hδp
    (GKL24MaxCorrStrictWitnessCoverFalseAsStated_of_commonZeroMaximal MC δ p hres)

end ProximityGap
