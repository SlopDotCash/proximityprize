/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanBoundBridge

/-!
# CZ25 coordinate-fiber cap: the unique-decoding slice (issues #74/#93/#94)

Discharges the deepest CZ25 residual `CZ25CoordFiberCap` (the Guruswami–Wang affine-flat
coordinate-fiber cap) **unconditionally in the unique-decoding regime** (`|L| ≤ 1`), plus the
missing elementary upper bound `coordAgreeSum ≤ |L|·n` (companion to the in-tree agreement
lower bound). For `|L| = 1` the budget `((|L|-1)·τ+1)·n = n` exactly accounts for the single
codeword; for `|L| = 0` the budget `(1-τ(r₀))·n ≥ 0` from the capacity guard `0 ≤ 1-τ(r₀)-η`.
The genuine `|L| > 1` affine-flat dimension count (the celebrated GW content) remains the
single named residual, tracked by #93.
-/


set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section CZ25CoordFiberCapUniqueDecoding

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Elementary `coordAgreeSum` upper bound.**  Each coordinate's agreement fiber
`{c ∈ Lset : c i = f i}` is a subset of `Lset`, so its cardinality is at most `|Lset|`;
summing over the `n = |ι|` coordinates gives

  `coordAgreeSum s f Lset ≤ |Lset| · n`.

This is the trivial pointwise cap (one full affine flat per coordinate is at most the whole
list).  It is precisely the bound that makes the affine-flat fiber cap `CZ25CoordFiberCap`
*automatic* once `|Lset| ≤ 1`, where the genuine `((|L|-1)·τ + 1)` budget degenerates to the
pointwise `1·n`.  Fully proven, axiom-clean. -/
theorem coordAgreeSum_le_card_mul_card_ι
    (s : ℕ) (f : ι → Fin s → F) (Lset : Finset (ι → Fin s → F)) :
    coordAgreeSum s f Lset ≤ (Lset.card : ℝ) * Fintype.card ι := by
  classical
  unfold coordAgreeSum
  -- Each filtered fiber has card ≤ |Lset|.
  have hterm : ∀ i : ι,
      ((Lset.filter (fun c => c i = f i)).card : ℝ) ≤ (Lset.card : ℝ) := by
    intro i
    have h := Finset.card_filter_le Lset (fun c => c i = f i)
    exact_mod_cast h
  calc (∑ i : ι, ((Lset.filter (fun c => c i = f i)).card : ℝ))
      ≤ ∑ _i : ι, (Lset.card : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Lset.card : ℝ) * Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **CZ25 affine-flat fiber cap in the unique-decoding regime (`|L| ≤ 1`).**

`CZ25CoordFiberCap` is the genuinely-deep Guruswami–Wang residual: the affine-flat coordinate
fiber cap `∑_i #{c ∈ L : c i = f i} ≤ ((|L| - 1)·τ(r₀) + 1)·n`.  In the unique-decoding /
sub-Johnson regime — every candidate list at the capacity radius has at most one codeword —
this cap holds *unconditionally*, with no subspace-design content:

  * `|L| = 1`: RHS `= (0·τ + 1)·n = n`, and `coordAgreeSum ≤ |L|·n = n` (each coordinate has
    at most one agreeing codeword).  ✓
  * `|L| = 0`: `coordAgreeSum = 0`, RHS `= (1 - τ(r₀))·n`, nonnegative because the guard
    `0 ≤ 1 - τ(r₀) - η` with `η > 0` forces `1 - τ(r₀) ≥ η > 0`.  ✓

This is the affine-flat-level counterpart of the in-tree `cz25SpanBound'_of_le_one` (which
discharges the *coarser* `CZ25SpanBound'` residual): the brick here discharges the *finer*
`CZ25CoordFiberCap` directly, so callers in the unique-decoding regime can exercise the full
affine-flat charge collapse `cz25SpanBound'_of_coordFiberCap` with a fully supplied (rather
than assumed) fiber cap.  Fully proven, axiom-clean — only the named in-tree API is used.

The candidate-list finset is realised as `closeCodewordsRelFinset`, whose membership and
cardinality agree with the `Set`-level `closeCodewordsRel`/`ncard`. -/
theorem cz25CoordFiberCap_of_ncard_le_one
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hle : ∀ f : ι → Fin s → F,
      (closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard ≤ 1) :
    CZ25CoordFiberCap s τ C h η hη := by
  classical
  intro f hδ
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδdef
  -- Realise the close list as the canonical finset over the (finite) block alphabet `Fin s → F`.
  refine ⟨closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ, ?_, ?_⟩
  · intro c
    exact mem_closeCodewordsRelFinset
  · -- Cardinality of the finset equals the `ncard`, which is ≤ 1 by hypothesis.
    set Lset : Finset (ι → Fin s → F) :=
      closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ with hLset
    have hcard_eq : (Lset.card : ℝ) =
        ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ).ncard : ℝ) := by
      rw [hLset, card_closeCodewordsRelFinset_eq_ncard]
    have hcard_le_one : (Lset.card : ℝ) ≤ 1 := by
      rw [hcard_eq]
      have := hle f
      exact_mod_cast this
    have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
    have hτ_le : τ r₀ ≤ 1 - η := by
      -- `hδ : 0 ≤ δ` with `hδdef : δ = 1 - τ r₀ - η`.
      have : (0 : ℝ) ≤ 1 - τ r₀ - η := by rw [← hδdef]; exact hδ
      linarith
    -- The elementary pointwise cap.
    have hcoord : coordAgreeSum s f Lset ≤ (Lset.card : ℝ) * Fintype.card ι :=
      coordAgreeSum_le_card_mul_card_ι s f Lset
    -- Target RHS: `((|Lset| - 1)·τ(r₀) + 1)·n`.
    -- Show `|Lset|·n ≤ ((|Lset| - 1)·τ(r₀) + 1)·n`, i.e. `|Lset| ≤ (|Lset|-1)·τ + 1`.
    -- Equivalently `(|Lset| - 1)·(1 - τ) ≤ 0`, which holds since `|Lset| - 1 ≤ 0` and
    -- `1 - τ ≥ η > 0`.
    have hkey : (Lset.card : ℝ) * Fintype.card ι ≤
        (((Lset.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
      apply mul_le_mul_of_nonneg_right _ hn_nonneg
      -- Goal: `(L : ℝ) ≤ (L - 1)·τ r₀ + 1`, i.e. `(1 - L)·(1 - τ r₀) ≥ 0`.
      nlinarith [hcard_le_one, hτ_le, le_of_lt hη,
        mul_nonneg (by linarith [hcard_le_one] : (0:ℝ) ≤ 1 - Lset.card)
          (by linarith [hτ_le, le_of_lt hη] : (0:ℝ) ≤ 1 - τ r₀)]
    exact le_trans hcoord hkey

/-- **In-tree CZ25 T3.4 `Λ`-bound in the unique-decoding regime, via the affine-flat bridge.**

Composes `cz25CoordFiberCap_of_ncard_le_one` with the in-tree affine-flat charge collapse
`subspaceDesign_list_decoding_cz25_of_coordFiberCap`.  This is the unique-decoding slice of
ABF26 T3.4 routed entirely through the *deepest* named residual `CZ25CoordFiberCap`, exercising
the genuine fiber-cap → span-bound → `Λ`-bound pipeline with a fully supplied fiber cap.

Distinct from the existing in-tree `subspaceDesign_list_decoding_cz25_of_spanBound'`-based
unique-decoding path (`cz25SpanBound'_of_le_one`) in that it discharges the affine-flat
`CZ25CoordFiberCap` obligation, not merely the coarser `CZ25SpanBound'`.  Fully proven,
axiom-clean. -/
theorem subspaceDesign_list_decoding_cz25_of_ncard_le_one
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hle : ∀ f : ι → Fin s → F,
      (closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard ≤ 1) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_coordFiberCap s τ C h η hη
    (cz25CoordFiberCap_of_ncard_le_one s τ C h η hη hle)

end CZ25CoordFiberCapUniqueDecoding

end CodingTheory

