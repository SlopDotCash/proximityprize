/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PinnedScalarRatioImage

/-!
# The residual-ratio is PERMUTATION-INVARIANT in the tuple, so the distinct-`γ` count
# factors through `(k+1)`-element SUBSETS: `#ratioImage ≤ C(n, k+1)` (#444 census face)

`PinnedScalarRatioImage` reduced the open `δ*`-governing distinct-`γ` count to the residual-ratio
image: `#pinnedScalars ≤ #ratioImage`, and gave the crude a-priori ceiling
`#ratioImage ≤ #{injective (k+1)-tuples} = n·(n-1)···(n-k)` (`ratioImage_card_le_tuples`).

This file supplies the structural **tightening** of that ceiling by a factor of `(k+1)!`.

## The mechanism (pure linear algebra, NOT orbit-law)

`residual dom k t y = det (borderedMatrix dom k t y)`, and the bordered matrix indexes its **rows**
by the tuple positions: `borderedMatrix dom k (t ∘ σ) y = (borderedMatrix dom k t y).submatrix σ id`
By `Matrix.det_permute`, permuting the rows scales the determinant by `Perm.sign σ` (a `±1` unit):

  **`residual dom k (t ∘ σ) y = Perm.sign σ • residual dom k t y`**
  (`residual_comp_perm_ratioImage`).

The residual is therefore permutation-EQUIVARIANT (it picks up the sign), NOT invariant.  But the
ratio `γ = − R₀ · R₁⁻¹` has the SAME sign appear in numerator and denominator, and the unit `±1`
cancels:

  **`residualRatio dom k u₀ u₁ (t ∘ σ) = residualRatio dom k u₀ u₁ t`** (`residualRatio_comp_perm`).

So the ratio map factors through the underlying `(k+1)`-element SET of the tuple.  Counting:

  **`#ratioImage ≤ C(n, k+1)`**     (`ratioImage_card_le_choose`),

the `(k+1)!`-fold improvement over `ratioImage_card_le_tuples` (`n·(n-1)···(n-k)`).  Chained with
`PinnedScalarRatioImage.pinnedScalars_card_le_ratioImage`:

  **`#pinnedScalars ≤ C(n, k+1)`**  (`pinnedScalars_card_le_choose`),

a sharper field-universal ceiling on the open `δ*`-governing distinct-`γ` count.

## Probe (`/tmp/probe_ratio_perm_invariant.py`, ONE sweep, NEVER `n = q-1`)

Over PROPER thin 2-power subgroups `μ_n ⊊ F_p*` (`p ≡ 1 mod n`, prize regime `p ≫ n³`, `β = 4..5`),
OFF-code planted stacks `u₀, u₁` (so the census is non-trivial), `n = 8,16,32`, `k = 1,2,3`,
sweeping ALL permutations of each `(k+1)`-subset:
- permutation-invariance of `residualRatio` holds in **100%** of runs (every permutation of a subset
  gives the identical ratio value);
- `#{ratio values} ≤ C(n, k+1)` in every run, TIGHT or near-tight at `k=1` (e.g. `n=8`: exactly
  `28 = C(8,2)`), and a real reduction vs the falling factorial (`n=8,k=3`: `70 = C(8,4)` vs
  `1680` ordered tuples, `24×` fewer).

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure and NOT thinness-essential: this is field-universal combinatorics (it holds for
any embedded domain, any `k`, independent of thickness: the determinant sign-cancellation is the
same over every field.  It is a structural TIGHTENING of the a-priori distinct-`γ` ceiling from the
ordered-tuple count to the subset count; it does NOT bound the ratio image below `C(n, k+1)`, and
`C(n, k+1) ~ n^{k+1}` is still far above the `√n` prize target. The cyclotomic/incidence content of
the ratio map for the thin subgroup (which actually collapses the image to `O(√n)`-many distinct
values) stays OPEN.  ASYMPTOTIC GUARD: the bound is a binomial in `n`, NOT a `δ*`/incidence object;
the cliff-at-`n/2` is UNTOUCHED.  `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- **The bordered matrix is row-permuted by precomposing the tuple with a permutation.**
`borderedMatrix dom k (t ∘ σ) y = (borderedMatrix dom k t y).submatrix σ id`: the entry at row `a`,
column `b` is `borderedMatrix dom k t y (σ a) b`, the row-`σ a` of the un-permuted matrix. -/
theorem borderedMatrix_comp_perm (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    (σ : Equiv.Perm (Fin (k + 1))) (y : Fin n → F) :
    borderedMatrix dom k (t ∘ σ) y
      = (borderedMatrix dom k t y).submatrix σ id := by
  funext a b
  simp only [borderedMatrix, Matrix.submatrix_apply, id_eq, Function.comp_apply]

/-- **The residual is permutation-EQUIVARIANT in the tuple.** Permuting the tuple by `σ` scales the
residual by the sign `Perm.sign σ` (a `±1` unit), since the residual is the determinant of the
bordered matrix and permuting the tuple permutes its rows (`Matrix.det_permute`). -/
theorem residual_comp_perm_ratioImage (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    (σ : Equiv.Perm (Fin (k + 1))) (y : Fin n → F) :
    residual dom k (t ∘ σ) y
      = ((Equiv.Perm.sign σ : ℤ) : F) * residual dom k t y := by
  unfold residual
  rw [borderedMatrix_comp_perm, Matrix.det_permute]

/-- **The residual-ratio is permutation-INVARIANT in the tuple** (the headline). The sign `Perm.sign
σ` appears in both numerator `R₀` and denominator `R₁` and cancels in the ratio. So the ratio map
`residualRatio` depends only on the underlying `(k+1)`-element SET of the tuple, not the order. -/
theorem residualRatio_comp_perm (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F)
    (t : Fin (k + 1) → Fin n) (σ : Equiv.Perm (Fin (k + 1))) :
    residualRatio dom k u₀ u₁ (t ∘ σ) = residualRatio dom k u₀ u₁ t := by
  unfold residualRatio
  rw [residual_comp_perm_ratioImage dom k t σ u₀,
    residual_comp_perm_ratioImage dom k t σ u₁]
  -- `s * R₀` and `(s * R₁)⁻¹`, with `s = ±1` the sign: the sign squares to `1` and cancels.
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h, mul_inv, mul_comm, mul_left_comm, mul_assoc]

open Classical in
/-- **Same range ⟹ same ratio.** If `t` is an injective `(k+1)`-tuple, its residual-ratio equals
the residual-ratio of the canonical (sorted) ordering `orderEmbOfFin` of its range. The two are
injective with the same range, hence differ by a permutation, and `residualRatio_comp_perm` ends it.
This is the step that collapses the ratio map from ordered tuples to `(k+1)`-element SETS. -/
theorem residualRatio_eq_orderEmb (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F)
    {t : Fin (k + 1) → Fin n} (ht : Function.Injective t)
    (h : ((Finset.univ : Finset (Fin (k + 1))).image t).card = k + 1) :
    residualRatio dom k u₀ u₁ t
      = residualRatio dom k u₀ u₁
          (⇑(((Finset.univ : Finset (Fin (k + 1))).image t).orderEmbOfFin h)) := by
  classical
  set S : Finset (Fin n) := (Finset.univ : Finset (Fin (k + 1))).image t with hS
  set e : Fin (k + 1) → Fin n := ⇑(S.orderEmbOfFin h) with he
  have he_inj : Function.Injective e := (S.orderEmbOfFin h).injective
  -- every `e a` lies in the range of `t`
  have hmem : ∀ a, e a ∈ S := fun a => Finset.orderEmbOfFin_mem S h a
  -- build the permutation `σ` with `t ∘ σ = e`
  have hex : ∀ a, ∃ j, t j = e a := by
    intro a
    have := hmem a
    rw [hS, Finset.mem_image] at this
    obtain ⟨j, _, hj⟩ := this
    exact ⟨j, hj⟩
  let σ : Fin (k + 1) → Fin (k + 1) := fun a => (hex a).choose
  have hσ : ∀ a, t (σ a) = e a := fun a => (hex a).choose_spec
  have hσinj : Function.Injective σ := by
    intro a b hab
    have : e a = e b := by rw [← hσ a, ← hσ b, hab]
    exact he_inj this
  let σe : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective σ
    ((Fintype.bijective_iff_injective_and_card σ).2 ⟨hσinj, rfl⟩)
  have hcomp : t ∘ σe = e := by
    funext a; exact hσ a
  calc residualRatio dom k u₀ u₁ t
      = residualRatio dom k u₀ u₁ (t ∘ σe) := (residualRatio_comp_perm dom k u₀ u₁ t σe).symm
    _ = residualRatio dom k u₀ u₁ e := by rw [hcomp]

open Classical in
/-- **The subset-indexed ratio map.** For a `(k+1)`-element subset `S ⊆ Fin n`, evaluate the ratio
on its canonical sorted ordering; off-card subsets map to `0` (never hit by the image below). -/
noncomputable def ratioOfSubset (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F)
    (S : Finset (Fin n)) : F :=
  if h : S.card = k + 1 then residualRatio dom k u₀ u₁ (⇑(S.orderEmbOfFin h)) else 0

open Classical in
/-- **The ratio image is contained in the image of the `(k+1)`-subsets** under `ratioOfSubset`.
Every `γ ∈ ratioImage` comes from an injective tuple `t` (nonzero denominator); by
`residualRatio_eq_orderEmb`, `γ` is the `ratioOfSubset` of the `(k+1)`-element range of `t`. -/
theorem ratioImage_subset_subsetImage (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    ratioImage dom k u₀ u₁
      ⊆ ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).image
          (ratioOfSubset dom k u₀ u₁) := by
  classical
  intro γ hγ
  rw [ratioImage, Finset.mem_image] at hγ
  obtain ⟨t, htmem, hγeq⟩ := hγ
  rw [Finset.mem_filter, injTuples, Finset.mem_filter] at htmem
  obtain ⟨⟨_, htinj⟩, _⟩ := htmem
  set S : Finset (Fin n) := (Finset.univ : Finset (Fin (k + 1))).image t with hS
  have hcard : S.card = k + 1 := by
    rw [hS, Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
  rw [Finset.mem_image]
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hcard⟩
  · rw [ratioOfSubset, dif_pos hcard, ← residualRatio_eq_orderEmb dom k u₀ u₁ htinj hcard, hγeq]

/-- **The `(k+1)!`-fold tightening.** The residual-ratio image, hence the open `δ*`-governing
distinct-`γ` count, is bounded by the number of `(k+1)`-element SUBSETS, `C(n, k+1)`, a factor
`(k+1)!` below the ordered-tuple ceiling `ratioImage_card_le_tuples`. -/
theorem ratioImage_card_le_choose (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    (ratioImage dom k u₀ u₁).card ≤ Nat.choose n (k + 1) := by
  classical
  refine le_trans (Finset.card_le_card (ratioImage_subset_subsetImage dom k u₀ u₁)) ?_
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The sharpened distinct-`γ` ceiling.** Chaining `pinnedScalars_card_le_ratioImage` with the
subset bound: the open `δ*`-governing distinct-`γ` count is `≤ C(n, k+1)`, a factor `(k+1)!` below
the in-tree `pinnedScalars_card_le_tuples`. -/
theorem pinnedScalars_card_le_choose (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (pinnedScalars dom k a u₀ u₁).card ≤ Nat.choose n (k + 1) :=
  le_trans (pinnedScalars_card_le_ratioImage dom k a u₀ u₁)
    (ratioImage_card_le_choose dom k u₀ u₁)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.borderedMatrix_comp_perm
#print axioms ProximityGap.Ownership.residual_comp_perm_ratioImage
#print axioms ProximityGap.Ownership.residualRatio_comp_perm
#print axioms ProximityGap.Ownership.residualRatio_eq_orderEmb
#print axioms ProximityGap.Ownership.ratioImage_subset_subsetImage
#print axioms ProximityGap.Ownership.ratioImage_card_le_choose
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_choose
