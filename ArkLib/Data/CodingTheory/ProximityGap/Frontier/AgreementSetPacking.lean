/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusScalarPartition

/-!
# Agreement-set PACKING: distinct pinned scalars share only DEGENERATE overlap (issue #444,
under-det face)

`CensusScalarPartition` proved the census decomposition `#alignableSets = Σ_γ
#alignedSetsForScalar γ`
and the SET-level uniqueness `alignedSetsForScalar_disjoint` (`Aligned.gamma_eq`: a non-degenerate
aligned `a`-set has a UNIQUE pinned scalar).  The OPEN object is a bound on the distinct-`γ` count
`#pinnedScalars` itself (`BadScalarsEqPinned`: `#bad = #pinnedScalars`; the deployed `δ*` budget).

This file supplies the structural PACKING lever the distinct-`γ` count needs — the
**agreement-set overlap law**, in the under-determined / agreement-sharing face:

> **Two non-degenerately aligned sets with DISTINCT scalars overlap only DEGENERATELY.**
> If `S` is non-degenerately `γ`-aligned and `S'` is non-degenerately `γ'`-aligned with `γ ≠ γ'`,
> then EVERY injective `(k+1)`-tuple inside `S ∩ S'` is degenerate (`residual u₀ = residual u₁ =
0`).

The mechanism is `Aligned.gamma_eq` lifted to the intersection: a non-degenerate `(k+1)`-tuple in
`S ∩ S'` would be both `γ`- and `γ'`-aligned, forcing `γ = γ'`.  So the *only* way two distinct
pinned scalars can share a `(k+1)`-subset is through a JOINTLY deg-`<k` (degenerate /
`pairJointAgreesOn`) core — exactly the structure the census EXCLUDES by its non-degeneracy clause.

## Why this is the under-det / sharing face (not the monomial proxy)

The monomial / over-determined proxy counts the incidence `#alignableSets` and was shown
(growth-law resolution, #444) to collapse to Johnson via the SAT-then-cliff staircase at `s ≈ n/2`.
The TRUE `δ*` is governed by the distinct-`γ` count `#pinnedScalars`, which the proxy over-counts by
the multiplicity excess `Σ(mult γ − 1)`.  This file isolates the agreement-SHARING contribution to
that gap: distinct pinned scalars can only share a DEGENERATE (jointly-deg`<k`) core.  Consequently
the per-scalar agreement-set "non-degenerate cores" pack — distinct scalars' aligned sets cannot
share a non-degenerate `(k+1)`-tuple.  Probe `probe_underdet_agreementset_packing.py` (exact `F_p`,
PROPER `μ_n`, `p ≫ n³`, never `n=q−1`, binding band `a = n/2`): for every structured/random stack
the
max pairwise overlap of distinct pinned scalars' agreement sets is `≤ k`, and at `a = n/2` the
distinct-`γ` count collapses (`#pinned = 1` at `n = 12, 16`) — the sharing does NOT sustain a
window-interior gap; any beyond-Johnson gap must live in the per-`γ` char-sum (BGK) wall.

## Scope (rules 3, 6 — honesty contract)

This is NOT a CORE closure and NOT thinness-essential: it is field-universal combinatorics about the
alignment census, sharpening the under-det / agreement-sharing face.  It pins the agreement-set
overlap structure exactly (degenerate-only sharing), the packing prerequisite for bounding the
distinct-`γ` count.  It does NOT yet bound `#pinnedScalars` (that needs the degenerate-core size
cap,
the open BGK-adjacent brick).  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- **THE OVERLAP LAW (tuple form).** A `(k+1)`-tuple that is simultaneously `γ`-aligned (lies in a
`γ`-aligned set) and `γ'`-aligned with `γ ≠ γ'` must be DEGENERATE: its two residuals both vanish.

Mechanism: `Aligned.gamma_eq` — a non-degenerate aligned tuple pins its scalar uniquely, so two
distinct scalars cannot both align the same non-degenerate tuple. -/
theorem residual_degenerate_of_two_aligned
    {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ γ' : F} (hne : γ ≠ γ')
    {t : Fin (k + 1) → Fin n}
    (hγ : residual dom k t u₀ + γ * residual dom k t u₁ = 0)
    (hγ' : residual dom k t u₀ + γ' * residual dom k t u₁ = 0) :
    residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0 := by
  -- (γ - γ') · residual u₁ = 0, and γ ≠ γ' ⟹ residual u₁ = 0 ⟹ residual u₀ = 0.
  have hkey : (γ - γ') * residual dom k t u₁ = 0 := by linear_combination hγ - hγ'
  have hr1 : residual dom k t u₁ = 0 := by
    rcases mul_eq_zero.mp hkey with hd | hd
    · exact absurd (sub_eq_zero.mp hd) hne
    · exact hd
  refine ⟨?_, hr1⟩
  rwa [hr1, mul_zero, add_zero] at hγ

omit [Fintype F] [DecidableEq F] in
/-- **THE OVERLAP LAW (set form).** If `S` is `γ`-aligned and `S'` is `γ'`-aligned with `γ ≠ γ'`,
then EVERY injective `(k+1)`-tuple contained in `S ∩ S'` is degenerate.

So two distinct scalars' aligned sets can share a `(k+1)`-subset only through a jointly-deg-`<k`
(degenerate) tuple — the agreement-sharing overlap is DEGENERATE-only. -/
theorem aligned_inter_tuple_degenerate
    {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ γ' : F} (hne : γ ≠ γ')
    {S S' : Finset (Fin n)} (hS : Aligned dom k u₀ u₁ γ S) (hS' : Aligned dom k u₀ u₁ γ' S')
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S ∩ S') :
    residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0 := by
  have hmemS : ∀ b, t b ∈ S := fun b => (Finset.mem_inter.mp (htmem b)).1
  have hmemS' : ∀ b, t b ∈ S' := fun b => (Finset.mem_inter.mp (htmem b)).2
  exact residual_degenerate_of_two_aligned hne (hS t htinj hmemS) (hS' t htinj hmemS')

omit [Fintype F] [DecidableEq F] in
/-- **DISTINCT-SCALAR SHARING ⟹ DEGENERATE CORE.** Contrapositive packing form: if two aligned sets
`S` (for `γ`) and `S'` (for `γ'`) share a NON-degenerate `(k+1)`-tuple, then `γ = γ'`.
Equivalently:
distinct pinned scalars' aligned sets cannot share a non-degenerate `(k+1)`-subset — their
non-degenerate cores are disjoint at the tuple level (the packing prerequisite for bounding
`#pinnedScalars`). -/
theorem gamma_eq_of_shared_nondeg_tuple
    {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ γ' : F}
    {S S' : Finset (Fin n)} (hS : Aligned dom k u₀ u₁ γ S) (hS' : Aligned dom k u₀ u₁ γ' S')
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S ∩ S')
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    γ = γ' := by
  by_contra hne
  exact hnd (aligned_inter_tuple_degenerate hne hS hS' htinj htmem)

open Classical in
/-- **THE PACKING INJECTION.** For each pinned scalar `γ` choose ONE non-degenerate aligned tuple;
its image is a `(k+1)`-subset of the domain.  Distinct pinned scalars give DISTINCT images: a shared
image would be a non-degenerate `(k+1)`-subset aligned for both, forcing the scalars equal
(`gamma_eq_of_shared_nondeg_tuple`).  This packs the distinct-`γ` count into the `(k+1)`-subsets:

> **`#pinnedScalars ≤ C(n, k+1)`**

a field-universal upper bound on the `δ*`-governing distinct-`γ` count via the agreement-set packing
lever (NOT the incidence-division route of `PinnedScalarMultDivision`). -/
theorem pinnedScalars_card_le_choose (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (pinnedScalars dom k a u₀ u₁).card ≤ n.choose (k + 1) := by
  classical
  -- Each pinned γ owns a non-degenerate aligned a-set, hence a non-degenerate (k+1)-tuple.
  -- Choose one and take its image; map γ ↦ that (k+1)-subset.
  have hchoose : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∃ S : Finset (Fin n), Aligned dom k u₀ u₁ γ S ∧
        ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
          ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0) := by
    intro γ hγ
    rw [mem_pinnedScalars] at hγ
    obtain ⟨S, hS⟩ := hγ
    rw [mem_alignedSetsForScalar] at hS
    exact ⟨S, hS.2.1, hS.2.2⟩
  -- the choice function
  choose Sγ halignγ tγ htγinj htγmemγ htγndγ using hchoose
  -- image map into (k+1)-subsets of univ; codomain card = C(n,k+1)
  rw [show n.choose (k + 1)
      = ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).card by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]]
  refine Finset.card_le_card_of_injOn
    (fun γ => if hγ : γ ∈ pinnedScalars dom k a u₀ u₁ then Finset.univ.image (tγ γ hγ) else ∅)
    ?_ ?_
  · -- maps into the (k+1)-subsets of univ
    intro γ hγ
    simp only [Finset.mem_coe] at hγ ⊢
    rw [dif_pos hγ, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (htγinj γ hγ), Finset.card_univ, Fintype.card_fin]
  · -- injective on pinnedScalars
    intro γ hγ γ' hγ' heq
    simp only [Finset.mem_coe] at hγ hγ'
    simp only [dif_pos hγ, dif_pos hγ'] at heq
    -- heq : univ.image (tγ γ hγ) = univ.image (tγ γ' hγ').  The shared image is a non-degenerate
    -- (k+1)-subset aligned for both γ and γ', forcing γ = γ'.
    have hmemInter : ∀ b, (tγ γ hγ) b ∈ Sγ γ hγ ∩ Sγ γ' hγ' := by
      intro b
      rw [Finset.mem_inter]
      refine ⟨htγmemγ γ hγ b, ?_⟩
      -- (tγ γ hγ) b ∈ image (tγ γ hγ) = image (tγ γ' hγ') ⟹ = (tγ γ' hγ') c ∈ Sγ γ' hγ'
      have hbT : (tγ γ hγ) b ∈ Finset.univ.image (tγ γ' hγ') := by
        rw [← heq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
      rw [Finset.mem_image] at hbT
      obtain ⟨c, -, hc⟩ := hbT
      rw [← hc]; exact htγmemγ γ' hγ' c
    exact gamma_eq_of_shared_nondeg_tuple (halignγ γ hγ) (halignγ γ' hγ')
      (htγinj γ hγ) hmemInter (htγndγ γ hγ)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.residual_degenerate_of_two_aligned
#print axioms ProximityGap.Ownership.aligned_inter_tuple_degenerate
#print axioms ProximityGap.Ownership.gamma_eq_of_shared_nondeg_tuple
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_choose
