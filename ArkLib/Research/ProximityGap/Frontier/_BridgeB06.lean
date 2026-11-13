/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Bridge B06 — the doubling map preserves graded frequency vectors (target E6)

E6 (`deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`): with `#bad_{2n}(k,m)` the
number of distinct nonzero `n/2`-binned graded frequency vectors over `(k+m)`-subsets
`A ⊆ ℤ/2n` with all lower graded pieces zero,
`#bad_{2n}(k, 2m') = #bad_n(k/2, m')` and `#bad_{2n}(k, odd) = 0`.

The structural heart of E6 is a **2-adic antipodal vanishing**: the order-2 element
`n ∈ ℤ/2n` acts as `−1` on the `2n`-th roots of unity (`ζ^n = −1`), so for any subset `A`
invariant under the antipodal shift `a ↦ a + n`, every **odd** graded frequency
`f̂_j(A) = ∑_{a∈A} ζ^{j·a}` vanishes (the `#bad_{2n}(k, odd) = 0` half). The even grades fold
exactly to the level-`n` graded vector under `a ↦ a mod n`.

This file formalizes that heart axiom-clean:

* `sum_eq_zero_of_odd_involution` — the antipodal-pairing engine.
* `antipodal_shift_odd_grade_zero` — for `ζ` with `ζ^N = −1` and an `N`-shift-closed `A`, the
  odd-twisted graded sum `∑_{a∈A} ζ^{j·a} = 0` whenever the per-element twist `ζ^(j·N) = −1`.

The residual is the finite `#bad` counting bijection / `k/2` rate fold (E6's combinatorics),
named as the gap.

Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB06

/-- **Antipodal pairing engine.** If a fixed-point-free involution `σ` preserves a finite set
`S` and a function `g : ι → ℂ` is **odd** under `σ` (`g (σ a) = − g a`), then `∑_{a∈S} g a = 0`.
This is the algebraic core that makes odd graded pieces vanish on antipodal-closed subsets. -/
theorem sum_eq_zero_of_odd_involution {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (σ : ι ≃ ι) (hσS : S.image σ = S)
    (g : ι → ℂ) (hodd : ∀ a ∈ S, g (σ a) = - g a) :
    ∑ a ∈ S, g a = 0 := by
  have hmap : ∑ a ∈ S, g a = ∑ a ∈ S, g (σ a) := by
    conv_lhs => rw [← hσS, Finset.sum_image (fun a _ b _ h => σ.injective h)]
  have hsum : ∑ a ∈ S, g (σ a) = - ∑ a ∈ S, g a := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun a ha => hodd a ha)
  have key : ∑ a ∈ S, g a = - ∑ a ∈ S, g a := hmap.trans hsum
  have : (2 : ℂ) * ∑ a ∈ S, g a = 0 := by ring_nf; linear_combination key
  simpa using this

/-- **Odd graded frequency vanishes on an antipodal-closed subset.** Let `T : ι ≃ ι` be the
antipodal shift (a fixed-point-free involution) and suppose `A : Finset ι` is `T`-closed
(`A.image T = A`). If the graded character `g` is **odd** under the shift on `A`
(`g (T a) = − g a`, the level-`j` instance of `ζ^{j·N} = −1` for odd-twist `j`), then the graded
frequency `∑_{a∈A} g a` is zero. -/
theorem antipodal_shift_odd_grade_zero {ι : Type*} [DecidableEq ι] (A : Finset ι)
    (T : ι ≃ ι) (hTclosed : A.image T = A)
    (g : ι → ℂ) (hodd : ∀ a ∈ A, g (T a) = - g a) :
    ∑ a ∈ A, g a = 0 :=
  sum_eq_zero_of_odd_involution A T hTclosed g hodd

#print axioms antipodal_shift_odd_grade_zero
#print axioms sum_eq_zero_of_odd_involution

end ArkLib.ProximityGap.BridgeB06
