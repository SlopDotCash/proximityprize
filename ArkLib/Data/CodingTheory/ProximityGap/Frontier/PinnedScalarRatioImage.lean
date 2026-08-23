/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusScalarPartition

/-!
# The distinct-scalar count is dominated by the residual-ratio image (#444 census face)

The census-scalar partition (`CensusScalarPartition`) localized the open prize content to the
**distinct-`γ` count** `#pinnedScalars`, the number of nonempty parts of the exact census
partition, the quantity that governs `δ*` (NOT the larger `(subset,γ)`-incidence count
`#alignableSets`). What that file left without an a-priori handle is a STRUCTURAL bound on
`#pinnedScalars` itself.

This file supplies the structural reduction. Every pinned `γ` owns a non-degenerate aligned
`a`-set, hence a non-degenerate injective `(k+1)`-tuple `t` with
`residual t u₀ + γ · residual t u₁ = 0`. Non-degeneracy forces `residual t u₁ ≠ 0`
(else `residual t u₀ = 0` too, contradicting non-degeneracy), so

  **`γ = − residual t u₀ · (residual t u₁)⁻¹`**, a *divided-difference ratio* value.

Therefore the open distinct-`γ` set is contained in the **ratio image** of the residual pencil
over the injective tuples with nonzero denominator `residual t u₁ ≠ 0`:

  **`pinnedScalars  ⊆  ratioImage`**     (`pinnedScalars_subset_ratioImage`)
  **`#pinnedScalars ≤ #ratioImage`**     (`pinnedScalars_card_le_ratioImage`)

and `ratioImage` is in turn the image of the (finite) injective-tuple set under the explicit ratio
map, giving the crude but field-universal a-priori count
`#ratioImage ≤ #{injective (k+1)-tuples}` (`ratioImage_card_le_tuples`).

This is the honest reduction of the `δ*`-governing distinct-`γ` count to a *divided-difference
ratio image*, the object on which the BGK / incidence-geometry pencil lever actually lives. It
converts "count the bad scalars" into "count the values of an explicit rational map of the agreement
pencil", which is the geometric reformulation the prize's non-energy mechanism must control.

## Probe (`scripts/probes/probe_ratio_image.py`, ONE sweep, NEVER `n = q−1`)

Over PROPER 2-power subgroup domains `μ_n ⊊ F_p*` (`p ≡ 1 mod n`, including `p ≫ n³`):
`pinnedScalars ⊆ ratioImage` holds in **24/24** runs (the subset is the universal fact); equality
holds exactly at the minimal band `a = k+1` (15/24), and `#ratioImage ≪ |F|` in every run (a real
reduction). The subset, the load-bearing direction proved here, never failed.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure and NOT thinness-essential: this is field-universal combinatorics about the
census object (it holds for any embedded domain, any `k, a`, independent of thickness). It localizes
the open content precisely, the distinct-`γ` count is `≤` the residual-ratio-image count, without
bounding that image (the cyclotomic/incidence content of the ratio map for the thin subgroup stays
OPEN). `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

open Classical in
/-- The **residual-ratio map** of a non-degenerate injective tuple: the scalar
`γ = − residual t u₀ · (residual t u₁)⁻¹` that the pencil pins. (When `residual t u₁ = 0` the
`Field` inverse convention returns `0`, but such tuples never witness a finite pinned scalar; see
`pinnedScalars_subset_ratioImage`.) -/
noncomputable def residualRatio (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F)
    (t : Fin (k + 1) → Fin n) : F :=
  - residual dom k t u₀ * (residual dom k t u₁)⁻¹

open Classical in
/-- The (finite) set of injective `(k+1)`-tuples in `Fin n`, the index set of the ratio map. -/
noncomputable def injTuples (n k : ℕ) : Finset (Fin (k + 1) → Fin n) :=
  (Finset.univ : Finset (Fin (k + 1) → Fin n)).filter Function.Injective

open Classical in
/-- The **residual-ratio image**: all `γ` that arise as `residualRatio` of an injective tuple with
*nonzero* denominator `residual t u₁ ≠ 0` (the genuine finite divided-difference ratios). Filtering
on `residual t u₁ ≠ 0` (rather than the weaker non-joint-vanishing `¬(R₀=0 ∧ R₁=0)`) excludes the
`R₁ = 0, R₀ ≠ 0` tuples whose `residualRatio` would be the spurious `0` of the `0⁻¹ = 0`
convention, keeping the image exactly the set of finite pencil ratios. This is the explicit
candidate set for the distinct pinned scalars. -/
noncomputable def ratioImage (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) : Finset F :=
  ((injTuples n k).filter (fun t => residual dom k t u₁ ≠ 0)).image
    (residualRatio dom k u₀ u₁)

omit [Fintype F] [DecidableEq F] in
/-- **The pinning identity.** If an injective tuple `t` is `γ`-aligned and non-degenerate, then
`residual t u₁ ≠ 0` and `γ = residualRatio t`. The non-degeneracy (`¬(R₀=0 ∧ R₁=0)`) rules out the
`R₁ = 0` branch (which would force `R₀ = 0`), so the field inverse is genuine. -/
theorem residualRatio_eq_of_aligned {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ : F}
    {S : Finset (Fin n)} (halign : Aligned dom k u₀ u₁ γ S)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    residual dom k t u₁ ≠ 0 ∧ γ = residualRatio dom k u₀ u₁ t := by
  have hpencil : residual dom k t u₀ + γ * residual dom k t u₁ = 0 := halign t htinj htmem
  have hr1 : residual dom k t u₁ ≠ 0 := by
    intro hz
    exact hnd ⟨by rwa [hz, mul_zero, add_zero] at hpencil, hz⟩
  refine ⟨hr1, ?_⟩
  -- from R₀ + γ R₁ = 0 and R₁ ≠ 0: γ = -R₀ / R₁
  have : γ * residual dom k t u₁ = - residual dom k t u₀ := by
    linear_combination hpencil
  unfold residualRatio
  field_simp
  linear_combination this

/-- **The structural containment.** Every pinned scalar lies in the residual-ratio image:
`pinnedScalars ⊆ ratioImage`. Each pinned `γ` owns a non-degenerate aligned `a`-set, which contains
a non-degenerate injective tuple `t`; by `residualRatio_eq_of_aligned`, `t` is non-degenerate and
`γ = residualRatio t` with `residual t u₁ ≠ 0`, so `γ` is in the nonzero-denominator ratio image. -/
theorem pinnedScalars_subset_ratioImage (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    pinnedScalars dom k a u₀ u₁ ⊆ ratioImage dom k u₀ u₁ := by
  classical
  intro γ hγ
  rw [mem_pinnedScalars] at hγ
  obtain ⟨S, hS⟩ := hγ
  rw [mem_alignedSetsForScalar] at hS
  obtain ⟨-, halign, t, htinj, htmem, hnd⟩ := hS
  obtain ⟨hr1, hγeq⟩ := residualRatio_eq_of_aligned halign htinj htmem hnd
  rw [ratioImage, Finset.mem_image]
  refine ⟨t, ?_, hγeq.symm⟩
  rw [Finset.mem_filter]
  exact ⟨by rw [injTuples, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htinj⟩, hr1⟩

/-- **The distinct-`γ` count is dominated by the ratio-image count.** `#pinnedScalars ≤
#ratioImage`. This is the structural a-priori bound on the open `δ*`-governing count: the number of
distinct bad scalars is at most the number of distinct values of the residual pencil's ratio over
non-degenerate injective tuples. -/
theorem pinnedScalars_card_le_ratioImage (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (pinnedScalars dom k a u₀ u₁).card ≤ (ratioImage dom k u₀ u₁).card :=
  Finset.card_le_card (pinnedScalars_subset_ratioImage dom k a u₀ u₁)

omit [Fintype F] in
open Classical in
/-- **The crude a-priori tuple bound.** The ratio image is the image of (a subset of) the injective
`(k+1)`-tuples (those with nonzero denominator) under the ratio map, so
`#ratioImage ≤ #{injective (k+1)-tuples}`. A field-universal ceiling on the distinct-`γ` count that
does not depend on the prime `p` at all. -/
theorem ratioImage_card_le_tuples (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    (ratioImage dom k u₀ u₁).card ≤ (injTuples n k).card := by
  classical
  rw [ratioImage]
  exact le_trans (Finset.card_image_le) (Finset.card_filter_le _ _)

/-- **Composite: the distinct-`γ` count is `≤ #{injective (k+1)-tuples}`.** Chaining the two bounds:
the open `δ*`-governing distinct-`γ` count is bounded, `p`-independently, by the number of injective
`(k+1)`-tuples of the domain. -/
theorem pinnedScalars_card_le_tuples (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (pinnedScalars dom k a u₀ u₁).card ≤ (injTuples n k).card :=
  le_trans (pinnedScalars_card_le_ratioImage dom k a u₀ u₁)
    (ratioImage_card_le_tuples dom k u₀ u₁)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.residualRatio_eq_of_aligned
#print axioms ProximityGap.Ownership.pinnedScalars_subset_ratioImage
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_ratioImage
#print axioms ProximityGap.Ownership.ratioImage_card_le_tuples
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_tuples
