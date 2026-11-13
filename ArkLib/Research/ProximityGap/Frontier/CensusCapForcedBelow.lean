/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalAlignmentLaw

/-!
# The census cap is FORCED FROM BELOW by a single large aligned set (#444)

The census-domination weld (`CensusDominationWeld.lean`) proves the FORWARD direction of the
$1M obligation in census normal form: `CensusDomination dom k a0 K => delta* = 1 - r/2^mu`.
The reverse direction (whether `CensusDomination` is NECESSARY for the prize, i.e. the
equivalence to CORE) is asserted but never proven.  This file lands a real brick on the
necessity side: a clean, unconditional LOWER BOUND on the census cap `K` itself, the exact
analogue of `SupplyForcingLowerBound.supply_ge_towerZeroSum` (which forces the
`ExplainableCoreSupply` residual from below) but for the DISTINCT `alignableSets` object the
weld actually uses.

**The mechanism.**  Alignment is subset-monotone (`Aligned.mono`): if a set `A` is
`gamma`-aligned, so is every subset of `A`.  Hence, given ONE `gamma`-aligned set `A` of size
`>= a` that contains a non-degenerate `(k+1)`-tuple `t`, EVERY `a`-point subset `S` with
`image t <= S <= A` is itself `gamma`-aligned (by `mono`) and contains the same non-degenerate
tuple, so `S` lies in `alignableSets`.  The map `T |-> T union (image t)` injects
`(A \ image t).powersetCard (a - (k+1))` into `alignableSets`, so

  **`C(|A| - (k+1), a - (k+1)) <= #alignableSets`**  (`choose_card_le_alignableSets`),

and therefore any `K` witnessing `CensusDomination` must dominate that binomial
(`censusDomination_cap_ge_choose`).  At the prize band `a ~ (1 - delta) n` with `|A| = n`,
the floor is `C(n - (k+1), a - (k+1))`, which GROWS in `n`, a concrete necessity constraint
on `K` (validated exactly to `n = 64` by `scripts/probes/probe_census_necessity.py`).

**Honest scope.**  This is NOT a CORE closure and NOT a refutation.  It is the missing
necessity half of the census equivalence stated as an unconditional theorem: it pins how
strong `CensusDomination` must be (its `K` cannot be smaller than the alignment supply), the
exact companion to the in-tree forward weld.  It makes no capacity / beyond-Johnson / growth-
law claim (ASYMPTOTIC GUARD untouched).  Whether the floor is also an UPPER bound (the prize)
stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

-- `hAa : a ≤ A.card` keeps the floor in its NON-vacuous regime (the source powerset is
-- nonempty exactly there); it is a semantic guard, not used by the injection proof, so the
-- unused-variable linter is silenced locally rather than dropping an honesty-relevant
-- hypothesis. `NeZero n` is inherited from the section but unneeded here.
set_option linter.unusedVariables false in
open Classical in
omit [NeZero n] in
/-- **The census supply floor.**  If `A` is a `gamma`-aligned set of size `>= a` (with
`a >= k + 1`) that contains a non-degenerate injective `(k+1)`-tuple `t`, then every
`a`-point set sandwiched between `image t` and `A` is `gamma`-aligned and non-degenerate,
hence in `alignableSets`.  The map `T |-> T union (image t)` injects the
`(a - (k+1))`-subsets of `A \ image t` into `alignableSets`, giving
`C(|A| - (k+1), a - (k+1)) <= #alignableSets`. -/
theorem choose_card_le_alignableSets (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {γ : F} {A : Finset (Fin n)}
    (hAa : a ≤ A.card) (hka : k + 1 ≤ a)
    (halign : Aligned dom k u₀ u₁ γ A)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ A)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    (A.card - (k + 1)).choose (a - (k + 1)) ≤ (alignableSets dom k a u₀ u₁).card := by
  classical
  -- the image of the pinned tuple, a (k+1)-subset of A
  set I : Finset (Fin n) := Finset.univ.image t with hIdef
  have hIcard : I.card = k + 1 := by
    rw [hIdef, Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
  have hIsubA : I ⊆ A := by
    intro x hx; rw [hIdef] at hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    exact htmem b
  -- inject (A \ I).powersetCard (a - (k+1)) into alignableSets via T |-> T union I
  set src : Finset (Finset (Fin n)) := (A \ I).powersetCard (a - (k + 1)) with hsrc
  have hsdiff : (A \ I).card = A.card - (k + 1) := by
    rw [Finset.card_sdiff_of_subset hIsubA, hIcard]
  have hsrccard : src.card = (A.card - (k + 1)).choose (a - (k + 1)) := by
    rw [hsrc, Finset.card_powersetCard, hsdiff]
  rw [← hsrccard]
  refine Finset.card_le_card_of_injOn
    (f := fun T : Finset (Fin n) => T ∪ I) ?_ ?_
  · -- maps into alignableSets
    intro T hT
    rw [hsrc, Finset.mem_coe, Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    -- T and I are disjoint (T <= A \ I)
    have hdisj : Disjoint T I := by
      refine Finset.disjoint_left.mpr fun x hxT hxI => ?_
      exact (Finset.mem_sdiff.mp (hTsub hxT)).2 hxI
    have hTIcard : (T ∪ I).card = a := by
      rw [Finset.card_union_of_disjoint hdisj, hTcard, hIcard]
      omega
    have hTIsubA : T ∪ I ⊆ A := by
      refine Finset.union_subset ?_ hIsubA
      exact hTsub.trans (Finset.sdiff_subset)
    -- membership in alignableSets
    simp only [Finset.mem_coe]
    rw [alignableSets, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, hTIcard⟩, γ, ?_, t, htinj, ?_, hnd⟩
    · exact halign.mono hTIsubA
    · intro b
      refine Finset.mem_union_right _ ?_
      rw [hIdef]; exact Finset.mem_image_of_mem t (Finset.mem_univ b)
  · -- injectivity of T |-> T union I on the source
    intro T₁ hT₁ T₂ hT₂ hEq
    simp only [] at hEq
    rw [hsrc, Finset.mem_coe, Finset.mem_powersetCard] at hT₁ hT₂
    have hd₁ : Disjoint T₁ I :=
      Finset.disjoint_left.mpr fun x hxT hxI => (Finset.mem_sdiff.mp (hT₁.1 hxT)).2 hxI
    have hd₂ : Disjoint T₂ I :=
      Finset.disjoint_left.mpr fun x hxT hxI => (Finset.mem_sdiff.mp (hT₂.1 hxT)).2 hxI
    -- T = (T union I) \ I for disjoint T, I
    have e₁ : T₁ = (T₁ ∪ I) \ I := by
      rw [Finset.union_sdiff_cancel_right hd₁]
    have e₂ : T₂ = (T₂ ∪ I) \ I := by
      rw [Finset.union_sdiff_cancel_right hd₂]
    rw [e₁, e₂, hEq]

open Classical in
omit [NeZero n] in
/-- **The census cap is forced from below.**  If a single `gamma`-aligned set `A` of size
`>= a` with a non-degenerate `(k+1)`-tuple exists, then any `K` witnessing the per-stack
census bound at band `a` must dominate `C(|A| - (k+1), a - (k+1))`.  This is the necessity
companion to `CensusDominationWeld.kkh26_deltaStar_pin_of_censusDomination`. -/
theorem censusDomination_cap_ge_choose (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {γ : F} {A : Finset (Fin n)} {K : ℕ}
    (hAa : a ≤ A.card) (hka : k + 1 ≤ a)
    (halign : Aligned dom k u₀ u₁ γ A)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ A)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K) :
    (A.card - (k + 1)).choose (a - (k + 1)) ≤ K :=
  le_trans
    (choose_card_le_alignableSets dom u₀ u₁ hAa hka halign htinj htmem hnd) hcap

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.choose_card_le_alignableSets
#print axioms ProximityGap.Ownership.censusDomination_cap_ge_choose
