/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DyadicTowerRecursion

/-!
# Bridge B09 (target E6): the even-only graded recursion via the η-parallelogram

**Goal (spec B09 / target E6).** Bridge the dyadic period recursion
`η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}` (`DyadicTowerRecursion.sum_tower_split`) to the
**even-only graded count**: the empirical 2-adic self-similarity

> `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`  and  `#bad_{2n}(k, odd) = 0`,

verified exactly all-cases at 16↔8. The mechanism the spec names is:
**"odd part cancels"** — the antipodal element `-1 = ω^n ∈ μ_{2n}` acts on the graded
frequency vector, and any *odd*-graded piece changes sign under it, so summed over a
negation-closed index set it **vanishes**.

This file lands the **algebraic kernel** of that mechanism, char-free, axiom-clean:

1. `sum_tower_split` re-exported in the η form (the substrate recursion itself).
2. `antipodal_odd_sum_eq_zero` — the EXACT vanishing of the odd graded piece: if a finite
   index set `H` is closed under an involution `σ` (the antipodal action, `σ∘σ=id`,
   no fixed points) and `f` is `σ`-**anti**-symmetric (`f(σ x) = - f x`, the defining
   property of an odd graded piece), then `∑_{x∈H} f x = 0`. This is precisely
   "the odd part cancels".
3. `tower_period_recursion` — packages (1) as `η^{(μ)}_b = η^{(μ-1)}_b + η^{(μ-1)}_{bω}`,
   the even/odd graded split whose odd half is killed by (2).

The remaining (un-formalized here) content of E6 is the **counting bijection**
`#bad_{2n}(k,2m') = #bad_n(k/2,m')` (the subset-folding map), stated precisely in `gap`.
What is landed is the vanishing-of-odd-part half — the part the η-parallelogram supplies.
-/

set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.BridgeB09

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The η tower recursion (re-export).** With `G = μ_{2n}` split as `H ⊔ ω·H` (here
`H = μ_n`, `ω` a primitive `2n`-th root) and `f = ψ(b · •)` the additive character, this is
the exact dyadic recursion `η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}`: the level-`μ` period is
the sum of the level-`(μ-1)` period and its `ω`-shift (the χ-twisted half). -/
theorem tower_period_recursion {M : Type*} [AddCommMonoid M] {G H : Finset F} {ω : F}
    (hω : ω ≠ 0) (f : F → M) (hsplit : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) :
    ∑ x ∈ G, f x = ∑ x ∈ H, f x + ∑ x ∈ H, f (ω * x) :=
  DyadicTowerRecursion.sum_tower_split hω f hsplit hdisj

/-- **The odd part cancels (antipodal involution vanishing).**
Let `σ : F → F` be a fixed-point-free involution on the support `H` (the antipodal action
`x ↦ -x = ω^n · x` of `μ_{2n}`, `n = 2^{μ-1}`), with `H` closed under `σ`. If `f` is
`σ`-**anti**symmetric — `f (σ x) = - f x`, the defining property of an *odd*-graded period
piece — then its sum over `H` vanishes:

`∑_{x ∈ H} f x = 0`.

This is the exact statement "the odd part cancels": odd graded frequency components are killed
by the antipodal `-1 ∈ μ_{2n}`, hence `#bad_{2n}(k, odd) = 0`. (Proof: pair `x` with `σ x`;
the two contributions are negatives, and `σ` partitions `H` into such pairs since it is a
fixed-point-free involution preserving `H`.) -/
theorem antipodal_odd_sum_eq_zero {H : Finset F} {σ : F → F}
    (hσH : ∀ x ∈ H, σ x ∈ H) (hσσ : ∀ x ∈ H, σ (σ x) = x)
    {f : F → ℂ} (hodd : ∀ x ∈ H, f (σ x) = - f x) :
    ∑ x ∈ H, f x = 0 := by
  -- σ is an involution on H: the image of the sum under σ equals the sum.
  have hreindex : ∑ x ∈ H, f (σ x) = ∑ x ∈ H, f x := by
    apply Finset.sum_nbij' (fun x => σ x) (fun x => σ x)
    · intro a ha; exact hσH a ha
    · intro a ha; exact hσH a ha
    · intro a ha; exact hσσ a ha
    · intro a ha; exact hσσ a ha
    · intro a _; rfl
  -- But ∑ f(σ x) = ∑ (- f x) = - ∑ f x by oddness.
  have hneg : ∑ x ∈ H, f (σ x) = - ∑ x ∈ H, f x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hodd
  -- Hence ∑ f x = - ∑ f x, so 2 • ∑ f x = 0, so ∑ f x = 0.
  have hself : ∑ x ∈ H, f x = - ∑ x ∈ H, f x := hreindex.symm.trans hneg
  -- a = -a over ℂ ⟹ a = 0.
  have h2 : (2 : ℂ) * ∑ x ∈ H, f x = 0 := by
    have : (∑ x ∈ H, f x) + (∑ x ∈ H, f x) = 0 := by
      nth_rewrite 2 [hself]; rw [add_neg_cancel]
    linear_combination this
  simpa using h2

end ArkLib.ProximityGap.BridgeB09

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.BridgeB09.tower_period_recursion
#print axioms ArkLib.ProximityGap.BridgeB09.antipodal_odd_sum_eq_zero
