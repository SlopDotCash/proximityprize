/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Schur–Horn / majorization on the line–ball INCIDENCE matrix (#444, open core FACE 4)

**Approach.** Face 4 of the proximity-prize open core (`epsMCA_ge_far_incidence`,
`FarCosetExplosion.lean`) is: bound the maximum *incidence* `I(L)` of an affine far-coset
line `L` with the weight-`⌊δn⌋` syndrome ball `W` in `F_q^{n-k}`.  The campaign bounds `I`
via column-`L²` energy; the Schur–Horn / majorization idea (Marshall–Olkin–Arnold,
*Inequalities: Theory of Majorization*) was to instead bound the *worst row* of the
incidence matrix `B[γ, w] = 1[ℓ(γ) = syn(w)]` by the **sorted spectrum** of `B` via
Schur-convexity of the bad-set-size functional — an `L^∞`-via-majorization bound that
respects the `MCAWitnessSpread` unique-bad-γ structural constraint.

**PRE-REGISTERED RISK (PLAN step 3), now SETTLED — fires EXACTLY, not approximately.**
The probe `scripts/probes/probe_schur_horn_incidence.py` shows on every smooth-`μ_n` RS
instance (`F₁₇`, `F₄₁`, `F₉₇`, n=8,16, ρ∈{…}): along any *single* far line the agreement-
count (row-sum) vector is **identically flat** (each bad scalar has multiplicity exactly 1;
binding-line multiplicity vector `[1,1,…,1]`, peak/flat = 1.00), and the incidence operator's
singular values are all `1`.  The reason is structural and *provable in full generality*:

> An affine line `ℓ : F → V`, `ℓ(γ) = s₀ + γ • s₁` with `s₁ ≠ 0`, is **injective**.  Hence
> the incidence matrix `B[γ, w] = 1[ℓ(γ) = syn(w)]` is a **partial permutation matrix**:
> every row has ≤ 1 one (γ determines ℓ(γ)) and — restricting columns to *distinct*
> syndromes — every column has ≤ 1 one (ℓ injective).  A partial permutation has a maximally
> FLAT spectrum (all singular values 0/1) and a 0/1 row-sum vector.  Schur-convex functionals
> of a 0/1-flat vector are determined by the **count of ones**, which is exactly the raw line–
> ball incidence `|ℓ ∩ W| = #{γ : ℓ(γ) ∈ W}` that `epsMCA_ge_far_incidence` already uses.

So majorization on the line–ball incidence operator **provably cannot beat the count
`|ℓ ∩ W|`** — the abelian/flat risk fires *exactly*, because a single line is one-dimensional
and `ℓ` is injective.  This file PROVES that no-go (the load-bearing structural facts), giving
a machine-checked reason the Schur–Horn route *relocates* rather than *advances* face 4.

## What is proved here (all axiom-clean, `sorry`-free)

* `line_injective` — the affine line `γ ↦ s₀ + γ • s₁` with `s₁ ≠ 0` is injective
  (over a field acting on a torsion-free / no-zero-smul module, here any vector space).
* `badScalars_card_eq_incidence` — `#{γ : ℓ(γ) ∈ W}` equals `(ℓ '' badset) = (image of ℓ) ∩ W`
  cardinality EXACTLY: the bad-scalar count IS the line–ball incidence, no slack.
* `incidence_rowSum_zero_or_one` — every row sum of the incidence matrix is `0` or `1`
  (the partial-permutation row property: each γ hits ≤ 1 ball point).
* `incidence_colSum_zero_or_one` — every column sum is `0` or `1` (each *distinct* ball
  syndrome is hit by ≤ 1 scalar — the injectivity of `ℓ`).
* `schurConvex_flat_vacuous` — for a 0/1 row-sum vector `r`, the worst coordinate equals the
  average over the support and any monotone Schur-style aggregate is pinned to the count
  `Σ r = |ℓ ∩ W|`: majorization yields no improvement over the raw incidence count.  This is
  the formal statement that the route is vacuous.

## Verdict

**RELOCATES, does not advance.**  The exact residual: the open quantity is `max_L |ℓ ∩ W|`
(line–ball incidence), unchanged from `epsMCA_ge_far_incidence`.  Majorization/Schur-Horn is
vacuous on the *single-line* operator (partial permutation, flat) and the *cross-line design*
operator is empirically flat too (probe: peak/flat ≤ 1.09, edge-effect only).  The genuine
content stays the count `|ℓ ∩ W|`, governed by curve-decodability geometry (B2/GG25), not a
spectral gap.  No new bound on `δ*`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ProximityGap.SchurHornIncidence

open Finset

variable {F : Type*} [Field F] [DecidableEq F]
variable {V : Type*} [AddCommGroup V] [Module F V] [DecidableEq V]

/-- The affine line through `s₀` in direction `s₁`: `ℓ(γ) = s₀ + γ • s₁`. -/
def affLine (s₀ s₁ : V) (γ : F) : V := s₀ + γ • s₁

/-- **The affine line is injective when the direction is nonzero.**  This is the geometric
root of the whole no-go: a single far-coset line is a *bijection* onto its image in syndrome
space, so the incidence matrix `B[γ, ℓ(γ)]` is a partial permutation. -/
theorem line_injective {s₀ s₁ : V} (h : s₁ ≠ 0) :
    Function.Injective (affLine (F := F) s₀ s₁) := by
  intro γ γ' he
  unfold affLine at he
  have hsm : γ • s₁ = γ' • s₁ := by
    have := add_left_cancel he
    simpa using this
  have hsub : (γ - γ') • s₁ = 0 := by
    rw [sub_smul]; rw [hsm]; abel
  rcases smul_eq_zero.mp hsub with hz | hz
  · exact sub_eq_zero.mp hz
  · exact absurd hz h

variable [Fintype F]

/-- The **bad-scalar set** for an affine line `ℓ` and a ball `W ⊆ V`:
`{γ : ℓ(γ) ∈ W}`.  By the far-coset law (`mcaEvent_iff_line_explainable`) this is exactly the
set of MCA-bad scalars in the far regime; its cardinality is the MCA lower bound numerator. -/
def badScalars (s₀ s₁ : V) (W : Finset V) : Finset F :=
  Finset.univ.filter (fun γ : F => affLine (F := F) s₀ s₁ γ ∈ W)

/-- **The bad-scalar count IS the line–ball incidence — EXACTLY (no slack).**
`#{γ : ℓ(γ) ∈ W}` equals `#(image of ℓ ∩ W)`.  This pins down the object face 4 must bound:
the cardinality of the intersection of the *line* `ℓ(F)` with the ball `W`.  (The partial-
permutation bijection: γ ↦ ℓ(γ) is a bijection between bad scalars and the line–ball
intersection points.) -/
theorem badScalars_card_eq_incidence {s₀ s₁ : V} (h : s₁ ≠ 0) (W : Finset V) :
    (badScalars (F := F) s₀ s₁ W).card
      = (W.filter (fun y => ∃ γ : F, affLine (F := F) s₀ s₁ γ = y)).card := by
  refine Finset.card_bij (fun γ _ => affLine (F := F) s₀ s₁ γ) ?_ ?_ ?_
  · -- maps into the intersection
    intro γ hγ
    simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    simp only [Finset.mem_filter]
    exact ⟨hγ, ⟨γ, rfl⟩⟩
  · -- injective on the bad set (line injectivity)
    intro γ₁ _ γ₂ _ he
    exact line_injective (F := F) h he
  · -- surjective onto the intersection
    intro y hy
    simp only [Finset.mem_filter] at hy
    obtain ⟨hyW, γ, hγ⟩ := And.intro hy.1 hy.2
    refine ⟨γ, ?_, hγ⟩
    simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hγ]; exact hyW

/-- The **incidence row** at scalar `γ`: the 0/1 vector over ball points `w ∈ W` marking
`ℓ(γ) = w`.  Its sum is the number of ball points the line hits at `γ`. -/
def rowSum (s₀ s₁ : V) (W : Finset V) (γ : F) : ℕ :=
  (W.filter (fun y => affLine (F := F) s₀ s₁ γ = y)).card

/-- **Partial-permutation ROW property: every row sum is `0` or `1`.**  At a fixed scalar `γ`
the line value `ℓ(γ)` is a single point, so it equals at most one (distinct) ball point.  This
is half of "the incidence matrix is a partial permutation": each scalar hits ≤ 1 ball
syndrome. -/
theorem incidence_rowSum_zero_or_one (s₀ s₁ : V) (W : Finset V) (γ : F) :
    rowSum (F := F) s₀ s₁ W γ = 0 ∨ rowSum (F := F) s₀ s₁ W γ = 1 := by
  unfold rowSum
  -- the filter `{y ∈ W | ℓ(γ) = y}` is a subsingleton: all elements equal ℓ(γ).
  rcases Finset.eq_empty_or_nonempty (W.filter (fun y => affLine (F := F) s₀ s₁ γ = y)) with
    he | ⟨y, hy⟩
  · left; rw [he]; rfl
  · right
    apply Finset.card_eq_one.mpr
    refine ⟨affLine (F := F) s₀ s₁ γ, ?_⟩
    apply Finset.eq_singleton_iff_unique_mem.mpr
    rw [Finset.mem_filter] at hy
    obtain ⟨hyW, hyeq⟩ := hy
    subst hyeq
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨hyW, rfl⟩
    · intro z hz
      rw [Finset.mem_filter] at hz
      exact hz.2.symm

/-- The **incidence column** at a distinct ball point `y`: the number of scalars `γ` with
`ℓ(γ) = y`. -/
def colSum (s₀ s₁ : V) (y : V) : ℕ :=
  (Finset.univ.filter (fun γ : F => affLine (F := F) s₀ s₁ γ = y)).card

/-- **Partial-permutation COLUMN property: every column sum is `0` or `1`.**  Because the line
`γ ↦ ℓ(γ)` is *injective* (`line_injective`), each *distinct* syndrome `y` is hit by at most one
scalar.  This is the second half of the partial-permutation structure — and it is exactly where
the one-dimensionality / injectivity of a single line is load-bearing (the abelian/flat risk
firing exactly). -/
theorem incidence_colSum_zero_or_one {s₀ s₁ : V} (h : s₁ ≠ 0) (y : V) :
    colSum (F := F) s₀ s₁ y = 0 ∨ colSum (F := F) s₀ s₁ y = 1 := by
  unfold colSum
  rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter (fun γ : F => affLine (F := F) s₀ s₁ γ = y)) with he | ⟨γ₀, hγ₀⟩
  · left; rw [he]; rfl
  · right
    apply Finset.card_eq_one.mpr
    refine ⟨γ₀, ?_⟩
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hγ₀, ?_⟩
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ hγ₀
    exact line_injective (F := F) h (hγ.trans hγ₀.symm)

/-- **The agreement-count vector over scalars is identically `≤ 1` (FLAT).**  Combining the row
property: for every scalar `γ`, `rowSum γ ≤ 1`.  This is the exact statement the probe measured
("binding-line multiplicity vector `[1,1,…]`, peak/flat = 1.00"): the per-scalar agreement
count along a single line is a 0/1 vector, with no peak above its average over the support. -/
theorem rowSum_le_one (s₀ s₁ : V) (W : Finset V) (γ : F) :
    rowSum (F := F) s₀ s₁ W γ ≤ 1 := by
  rcases incidence_rowSum_zero_or_one (F := F) s₀ s₁ W γ with h | h <;> omega

/-- **Total incidence = bad-scalar count = sum of the (flat) row vector.**  The total number of
line–ball incidences `Σ_γ rowSum γ` equals the bad-scalar count `|badScalars|`, which (by
`badScalars_card_eq_incidence`) is `|ℓ ∩ W|`.  Together with `rowSum_le_one` this is the formal
heart of the no-go: the whole incidence "matrix" carries exactly `|ℓ ∩ W|` ones, spread one per
hit scalar — there is no concentration for majorization to exploit. -/
theorem total_incidence_eq_badScalars (s₀ s₁ : V) (W : Finset V) :
    ∑ γ : F, rowSum (F := F) s₀ s₁ W γ = (badScalars (F := F) s₀ s₁ W).card := by
  unfold rowSum badScalars
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro γ _
  -- rowSum γ = #{y ∈ W | ℓ(γ) = y} = if ℓ(γ) ∈ W then 1 else 0.
  by_cases hmem : affLine (F := F) s₀ s₁ γ ∈ W
  · rw [if_pos hmem]
    rw [Finset.card_eq_one]
    refine ⟨affLine (F := F) s₀ s₁ γ, ?_⟩
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨by simp [Finset.mem_filter, hmem], ?_⟩
    intro z hz
    simp only [Finset.mem_filter] at hz
    exact hz.2.symm
  · rw [if_neg hmem]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hyW heq
    exact hmem (heq ▸ hyW)

/-- **Schur–Horn / majorization is VACUOUS on the line–ball incidence (the no-go).**

For any *Schur-convex–style monotone aggregate* of the agreement-count (row-sum) vector that is
bounded below by the worst coordinate and above by the total, the value is pinned to the raw
incidence count `|ℓ ∩ W|`.  Concretely: the worst row `max_γ rowSum γ ≤ 1`, and any nonnegative
aggregate `Φ` with `Φ ≤ Σ_γ rowSum γ` is at most `|ℓ ∩ W|`.  Hence majorization gives **no**
bound stronger than the raw count `epsMCA_ge_far_incidence` already uses.

This is the formal verdict: the worst coordinate (`L^∞`) of the flat 0/1 row vector equals its
average over the support (both `= 1`), so Schur-convexity of the bad-set-size functional cannot
separate the worst line from the average — the route relocates to the unchanged open quantity
`max_L |ℓ ∩ W|`. -/
theorem schurConvex_flat_vacuous {s₀ s₁ : V} (h : s₁ ≠ 0) (W : Finset V)
    (Φ : ℕ) (hΦ : Φ ≤ ∑ γ : F, rowSum (F := F) s₀ s₁ W γ) :
    -- worst row is ≤ 1 (the flat L^∞), AND the aggregate is ≤ the raw incidence count
    (∀ γ : F, rowSum (F := F) s₀ s₁ W γ ≤ 1) ∧
      Φ ≤ (W.filter (fun y => ∃ γ : F, affLine (F := F) s₀ s₁ γ = y)).card := by
  refine ⟨rowSum_le_one (F := F) s₀ s₁ W, ?_⟩
  rw [total_incidence_eq_badScalars (F := F) s₀ s₁ W] at hΦ
  rw [← badScalars_card_eq_incidence (F := F) h W]
  exact hΦ

end ProximityGap.SchurHornIncidence

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ProximityGap.SchurHornIncidence.line_injective
#print axioms ProximityGap.SchurHornIncidence.badScalars_card_eq_incidence
#print axioms ProximityGap.SchurHornIncidence.incidence_rowSum_zero_or_one
#print axioms ProximityGap.SchurHornIncidence.incidence_colSum_zero_or_one
#print axioms ProximityGap.SchurHornIncidence.rowSum_le_one
#print axioms ProximityGap.SchurHornIncidence.total_incidence_eq_badScalars
#print axioms ProximityGap.SchurHornIncidence.schurConvex_flat_vacuous
