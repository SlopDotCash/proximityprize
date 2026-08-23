/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Off-diagonal second-moment ingredient for the curve proximity gap ([BCIKS20] §6)

The second-moment estimate `∑_z N(z)² = ∑_{c,c'} #{z : w z close to both c and c'}` underlies the
tight Johnson-radius proximity gap. This file supplies its off-diagonal support restriction: by the
Hamming triangle inequality, a curve point `e`-close to two targets forces those targets within
`2e`, so only codeword pairs at distance `≤ 2e` contribute. The number of such pairs is governed by
the (MDS) Reed–Solomon weight enumerator, linking this to the `RSWeightEnumerator` machinery.
-/

open Finset BigOperators

namespace ProximityGap

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The degree-`k` curve word `w z = ∑ t, z^t · u t` at parameter `z`. -/
def curveWord {k : ℕ} (u : Fin (k + 1) → ι → F) (z : F) : ι → F :=
  fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i

/-- **Off-diagonal second-moment support (triangle restriction).** If the curve point `w z` is
`e`-close (in Hamming distance) to *both* targets `c` and `c'`, then `c` and `c'` are within `2e`
of each other. So only codeword *pairs* at distance `≤ 2e` can be simultaneously close to any curve
point — the off-diagonal terms of the second moment `∑_z N(z)²` are supported on close pairs. -/
theorem curvePair_dist_le {k : ℕ} (u : Fin (k + 1) → ι → F) (c c' : ι → F) (e : ℕ) (z : F)
    (hc : hammingDist (curveWord u z) c ≤ e)
    (hc' : hammingDist (curveWord u z) c' ≤ e) :
    hammingDist c c' ≤ 2 * e := by
  calc hammingDist c c'
      ≤ hammingDist c (curveWord u z) + hammingDist (curveWord u z) c' :=
        hammingDist_triangle _ _ _
    _ ≤ e + e := by rw [hammingDist_comm c (curveWord u z)]; omega
    _ = 2 * e := by ring

/-- **Off-diagonal second-moment vanishing.** No curve parameter can be `e`-close to two targets
whose Hamming distance exceeds `2e`. Hence in `∑_z N(z)² = ∑_{c,c'} #{z : both close}`, every pair
`(c, c')` with `Δ₀(c,c') > 2e` contributes `0` — the second moment is supported on the diagonal plus
the `≤ 2e`-distance pairs, whose count is governed by the (MDS) weight enumerator. -/
theorem card_curvePairClose_eq_zero_of_dist_gt {k : ℕ} (u : Fin (k + 1) → ι → F)
    (c c' : ι → F) (e : ℕ) (h : 2 * e < hammingDist c c') :
    (Finset.univ.filter (fun z : F =>
      hammingDist (curveWord u z) c ≤ e ∧ hammingDist (curveWord u z) c' ≤ e)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro z - ⟨h1, h2⟩
  exact absurd (curvePair_dist_le u c c' e z h1 h2) (by omega)

end ProximityGap
