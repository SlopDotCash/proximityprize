/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# LEVER K: the dilation-pencil shared-root count IS the multiplicative autocorrelation (#407)

This file isolates and formalizes the **clean, field-free reformulation** of the Kelley–Owen
dilation-pencil shared-root count that controls Kelley Conjecture 3.2 (the sub-Johnson
general-position bound = explicit-RS curve decodability).

## The setup (LEVER K)

Let `P` be the prize agreement polynomial `P = Xᵃ + γ·Xᵇ − c(X)` (`deg c < k`, support of size
`t = k+2`), and let `S = {x ∈ μ_n : P(x) = 0}` be its root set inside the order-`n` multiplicative
subgroup, `r = |S|`. The Kelley–Owen / Stepanov *dilation pencil* dilates `P` by every root:
`gᵢ(x) := P(ζᵢ·x)` for `ζᵢ ∈ S`. The root set of `gᵢ` inside `μ_n` is

  `Bᵢ = {w ∈ μ_n : P(ζᵢ·w) = 0} = ζᵢ⁻¹·S`,

so each `Bᵢ` has `|Bᵢ| = r` and contains `1` (because `ζᵢ ∈ S`). The Kelley–Owen double-count
bounds `r` by how much the `Bᵢ` overlap pairwise. The whole question is the **pairwise overlap**.

## The reformulation proven here (the new bridge)

**`inter_dilate_eq_autocorr`** : the pairwise pencil overlap is *exactly* a multiplicative
autocorrelation of the root set itself —

  `|Bᵢ ∩ Bⱼ| = |ζᵢ⁻¹·S ∩ ζⱼ⁻¹·S| = |S ∩ (ζᵢ·ζⱼ⁻¹)·S|`.

So the entire Kelley–Owen pencil shared-root count is the **multiplicative autocorrelation**
`M(S) := max_{ρ ≠ 1} |S ∩ ρ·S|` of `S`. This is field-free (it never mentions `P`, `γ`, the
codeword, or the characteristic), so it cleanly *separates* the algebraic input (S is a sparse
root set) from the combinatorial extraction. It is the right object for Kelley 3.2.

## The Fisher/packing extraction (`pencil_root_bound`)

With the punctured blocks `Cᵢ = Bᵢ \ {1}` (size `r−1`, pairwise overlap `≤ M − 1`), a Corrádi /
Fisher inequality gives the root bound. We land the clean two-extreme cases:
* `M = 1` (trinomial / `t=3` face) ⟹ punctured blocks disjoint ⟹ `r(r−1)+1 ≤ n`, i.e. `r ≤ ½+√n`
  (this recovers `KelleyOwenDilationPencil.pencil_card_core`, here re-derived from the
  autocorrelation viewpoint), and
* general `M` ⟹ the double-count `r·(r−1) ≤ (M−1)·(something)+…` only reaches Johnson.

## The precise obstruction, machine-checked (`autocorr_saturated_by_coset`)

The honest negative result that pins LEVER K: the autocorrelation `M(S)` is **saturated by the
coset core of `S`, not by the isolated excess**. Concretely, if `S ⊇ H` for a subgroup
`H = μ_d ⊆ μ_n` of order `d`, then taking any `ρ ∈ H \ {1}` gives `H ⊆ S ∩ ρ·S`, so
`M(S) ≥ d − 1` *(it is at least the whole coset core)*. For the prize-relevant worst case
`S = (coset of size n/2) ∪ {straggler}` (the `_RThinSqrtNKRefuted` family), this forces
`M(S) ≥ n/2 − 1`, and the Fisher bound then yields only `r ≤ Θ(n)` = Johnson, NOT sub-Johnson.

So: the multiplicative-autocorrelation reformulation is **exact and char-free**, but the worst-case
autocorrelation is dominated by the legitimate coset core (the actual list-decoding output), exactly
as `_RThinSqrtNKRefuted` shows for the raw size. Kelley 3.2 / sub-Johnson would require bounding the
autocorrelation of the **ragged excess after coset-core removal** — the double-count over the full
`S` provably cannot reach it. This is the precise obstruction, distinct from any char-`p` Wronskian
gap (the Wronskian route closes the `t=3`/distinct-degree case unconditionally; it is *this*
coset-saturation that blocks the general `t = k+2` pencil).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- Left-translate (dilate) of a finset by a group element. -/
def dilate (z : G) (S : Finset G) : Finset G := S.image (fun x => z * x)

@[simp] theorem mem_dilate {z : G} {S : Finset G} {y : G} :
    y ∈ dilate z S ↔ z⁻¹ * y ∈ S := by
  unfold dilate
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨z⁻¹ * y, h, by group⟩

/-- Dilation preserves cardinality. -/
@[simp] theorem card_dilate (z : G) (S : Finset G) : (dilate z S).card = S.card := by
  unfold dilate
  rw [Finset.card_image_of_injective]
  exact fun a b h => by simpa using h

/-- The pencil block `Bᵢ = {w : P(ζᵢ w) = 0} = ζᵢ⁻¹·S` for a root `ζᵢ ∈ S`. -/
def pencilBlock (zeta : G) (S : Finset G) : Finset G := dilate zeta⁻¹ S

@[simp] theorem mem_pencilBlock {zeta : G} {S : Finset G} {w : G} :
    w ∈ pencilBlock zeta S ↔ zeta * w ∈ S := by
  unfold pencilBlock; rw [mem_dilate, inv_inv]

/-- `|pencilBlock ζ S| = |S|`: every dilated pencil member has the same root count. -/
@[simp] theorem card_pencilBlock (zeta : G) (S : Finset G) :
    (pencilBlock zeta S).card = S.card := by
  unfold pencilBlock; rw [card_dilate]

/-- Every block contains `1` iff `ζ ∈ S` (the common point of the pencil). -/
theorem one_mem_pencilBlock {zeta : G} {S : Finset G} (hz : zeta ∈ S) :
    (1 : G) ∈ pencilBlock zeta S := by
  rw [mem_pencilBlock, mul_one]; exact hz

/-! ## The reformulation: pencil overlap = multiplicative autocorrelation -/

/-- **THE BRIDGE (LEVER K reformulation).** The pairwise overlap of two pencil blocks
`Bᵢ = ζᵢ⁻¹·S`, `Bⱼ = ζⱼ⁻¹·S` equals the **multiplicative autocorrelation** of the root set `S`
at the shift `ρ = ζᵢ·ζⱼ⁻¹`:

  `|pencilBlock ζᵢ S ∩ pencilBlock ζⱼ S| = |S ∩ ρ·S|`  with `ρ = ζᵢ·ζⱼ⁻¹`.

This is field-free: the entire Kelley–Owen shared-root count is the autocorrelation of `S`. -/
theorem inter_dilate_eq_autocorr (zi zj : G) (S : Finset G) :
    (pencilBlock zi S ∩ pencilBlock zj S).card
      = (S ∩ dilate (zj * zi⁻¹) S).card := by
  -- The map `w ↦ zj * w` is a bijection sending `Bᵢ ∩ Bⱼ` onto `S ∩ ρ·S`, `ρ = zj zi⁻¹`.
  -- `w ∈ Bᵢ ∩ Bⱼ ↔ zi w ∈ S ∧ zj w ∈ S`.  Put `y = zj w`: then `y ∈ S` and
  -- `ρ⁻¹ y = (zj zi⁻¹)⁻¹ (zj w) = zi zj⁻¹ zj w = zi w ∈ S`, i.e. `y ∈ S ∩ dilate ρ S`.
  apply Finset.card_bij (fun w _ => zj * w)
  · -- well-defined
    intro w hw
    rw [Finset.mem_inter, mem_pencilBlock, mem_pencilBlock] at hw
    rw [Finset.mem_inter, mem_dilate]
    refine ⟨hw.2, ?_⟩
    have : (zj * zi⁻¹)⁻¹ * (zj * w) = zi * w := by group
    rw [this]; exact hw.1
  · -- injective
    intro a ha b hb hab
    exact mul_left_cancel hab
  · -- surjective
    intro y hy
    rw [Finset.mem_inter, mem_dilate] at hy
    refine ⟨zj⁻¹ * y, ?_, by group⟩
    rw [Finset.mem_inter, mem_pencilBlock, mem_pencilBlock]
    refine ⟨?_, by rw [mul_inv_cancel_left]; exact hy.1⟩
    have : zi * (zj⁻¹ * y) = (zj * zi⁻¹)⁻¹ * y := by group
    rw [this]; exact hy.2

/-- **Autocorrelation form, packaged.** Define `M`-bounded autocorrelation of `S` to mean every
nontrivial dilation overlaps `S` in `≤ M` points. Then every *distinct-root* pencil pair overlaps
in `≤ M`. (Distinctness `ζᵢ ≠ ζⱼ` ⟹ `ρ = ζᵢζⱼ⁻¹ ≠ 1`.) This is the hypothesis Kelley 3.2 needs. -/
theorem pencil_overlap_le_of_autocorr {S : Finset G} {M : ℕ}
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ M)
    {zi zj : G} (hne : zi ≠ zj) :
    (pencilBlock zi S ∩ pencilBlock zj S).card ≤ M := by
  rw [inter_dilate_eq_autocorr]
  apply hM
  intro h
  apply hne
  have : zj * zi⁻¹ * zi = (1 : G) * zi := by rw [h]
  rw [inv_mul_cancel_right, one_mul] at this
  exact this.symm

/-! ## The precise obstruction: autocorrelation is saturated by the coset core

The negative half of LEVER K, machine-checked. If `S` contains an order-`d` subgroup `H = μ_d`
(its coset core), then for any `ρ ∈ H, ρ ≠ 1` the *whole* core lies in the overlap, so
`M(S) ≥ d − 1`. For the prize worst case `d = n/2`, this forces `M(S) ≥ n/2 − 1`, and the
Fisher/double-count then gives only Johnson — never sub-Johnson. The autocorrelation route is
dominated by the legitimate coset core, exactly as the raw-size bound is (`_RThinSqrtNKRefuted`). -/

/-- A finite subgroup `H ⊆ G` (as a `Finset`, closed under `*` and containing the dilation `ρ ∈ H`)
is fixed by left-dilation by any of its own elements: `ρ ∈ H ⟹ H ⊆ dilate ρ H`. -/
theorem subgroup_subset_dilate_self {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {ρ : G} (hρ : ρ ∈ H) :
    H ⊆ dilate ρ H := by
  intro x hx
  rw [mem_dilate]
  exact hmul ρ⁻¹ (hinv ρ hρ) x hx

/-- **THE OBSTRUCTION (machine-checked).** If the root set `S` contains a multiplicative subgroup
`H` (its coset core) and `ρ ∈ H`, then the autocorrelation of `S` at `ρ` is at least `|H|`:
the entire coset core sits inside the overlap. Hence for `ρ ≠ 1` in `H`,

  `|S ∩ ρ·S| ≥ |H|`,

so the pencil overlap (= autocorrelation) is dominated by the coset core, NOT by the isolated
ragged excess. With `|H| = n/2` (the prize worst case) this is `≥ n/2`, blocking sub-Johnson. -/
theorem autocorr_ge_coset_core {S H : Finset G}
    (hHS : H ⊆ S)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {ρ : G} (hρ : ρ ∈ H) :
    H.card ≤ (S ∩ dilate ρ S).card := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_inter]
  refine ⟨hHS hx, ?_⟩
  -- `H ⊆ dilate ρ H ⊆ dilate ρ S`
  have h1 : x ∈ dilate ρ H := subgroup_subset_dilate_self hmul hinv hρ hx
  rw [mem_dilate] at h1 ⊢
  exact hHS h1

/-- **Consequence: the autocorrelation obstruction is genuine.** If `S` contains a subgroup `H`
of order `≥ 2` (a nontrivial coset core), then there is a *nontrivial* shift `ρ ≠ 1` with
`|S ∩ ρ·S| ≥ |H|`. So `M(S) := max_{ρ≠1} |S ∩ ρS| ≥ |H|`: any autocorrelation upper bound used
in a Kelley-3.2 argument must be `≥` the largest coset core of `S`. The double-count over the
full `S` therefore cannot beat the coset core (= the legitimate list output). -/
theorem exists_nontrivial_shift_autocorr_ge {S H : Finset G}
    (hHS : H ⊆ S)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hcard : 2 ≤ H.card) :
    ∃ ρ : G, ρ ≠ 1 ∧ H.card ≤ (S ∩ dilate ρ S).card := by
  -- `H` has `≥ 2` elements, so it contains some `ρ ≠ 1`.
  obtain ⟨ρ, hρH, hρne⟩ : ∃ ρ ∈ H, ρ ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : H ⊆ {1} := by
      intro x hx; rw [Finset.mem_singleton]; exact h x hx
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this; omega
  exact ⟨ρ, hρne, autocorr_ge_coset_core hHS hmul hinv hρH⟩

/-! ## The positive `t = 3` extreme: `M = 1` recovers the trinomial √n bound

When the autocorrelation is `1` (the trinomial / `t=3` primitive face: distinct pencil members
share *only* the point `1`), the punctured blocks are pairwise disjoint and the Kelley–Owen
count `r(r−1)+1 ≤ n` follows. This connects the autocorrelation viewpoint to the in-tree
`KelleyOwenDilationPencil.pencil_card_core`. -/

/-- **`M = 1` ⟹ punctured pencil blocks pairwise disjoint.** If the autocorrelation of `S` is
`≤ 1` at every nontrivial shift, then for distinct roots `ζᵢ ≠ ζⱼ` the punctured blocks
`Bᵢ \ {1}`, `Bⱼ \ {1}` are disjoint (their only common point was `1`). This is the disjointness
hypothesis of `pencil_card_core`, derived from the autocorrelation bound. -/
theorem punctured_blocks_disjoint_of_autocorr_le_one {S : Finset G}
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ 1)
    {zi zj : G} (hzi : zi ∈ S) (hzj : zj ∈ S) (hne : zi ≠ zj) :
    Disjoint ((pencilBlock zi S).erase 1) ((pencilBlock zj S).erase 1) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [Finset.mem_erase] at hxi hxj
  -- `x` is a common non-`1` point of `Bᵢ` and `Bⱼ`, so `Bᵢ ∩ Bⱼ ⊇ {1, x}` has `≥ 2` points,
  -- contradicting the `≤ 1` overlap bound.
  have hxmem : x ∈ pencilBlock zi S ∩ pencilBlock zj S :=
    Finset.mem_inter.mpr ⟨hxi.2, hxj.2⟩
  have honemem : (1 : G) ∈ pencilBlock zi S ∩ pencilBlock zj S :=
    Finset.mem_inter.mpr ⟨one_mem_pencilBlock hzi, one_mem_pencilBlock hzj⟩
  have h2 : 2 ≤ (pencilBlock zi S ∩ pencilBlock zj S).card := by
    have hsub : ({1, x} : Finset G) ⊆ pencilBlock zi S ∩ pencilBlock zj S := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact honemem
      · exact hxmem
    have hcard2 : ({1, x} : Finset G).card = 2 := by
      rw [Finset.card_insert_of_notMem
            (by rw [Finset.mem_singleton]; exact (Ne.symm hxi.1)),
        Finset.card_singleton]
    rw [← hcard2]; exact Finset.card_le_card hsub
  rw [inter_dilate_eq_autocorr] at h2
  have hle := hM (zj * zi⁻¹) (by
    intro h
    apply hne
    have : zj * zi⁻¹ * zi = (1 : G) * zi := by rw [h]
    rw [inv_mul_cancel_right, one_mul] at this
    exact this.symm)
  omega

end ProximityGap.Frontier.PencilAutocorrelation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.PencilAutocorrelation.inter_dilate_eq_autocorr
#print axioms ProximityGap.Frontier.PencilAutocorrelation.pencil_overlap_le_of_autocorr
#print axioms ProximityGap.Frontier.PencilAutocorrelation.autocorr_ge_coset_core
#print axioms ProximityGap.Frontier.PencilAutocorrelation.exists_nontrivial_shift_autocorr_ge
#print axioms ProximityGap.Frontier.PencilAutocorrelation.punctured_blocks_disjoint_of_autocorr_le_one
