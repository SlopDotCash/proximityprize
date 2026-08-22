/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDeficitBudget
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Door-(iv) Lane-3: the UNIFORM per-level deficit threshold `(2−√2)/2` (axiom-clean, #444)

The variable telescope (`_DoorIVDilationDeficitBudget`) priced the dilation route by the *total* budget
`S = ∑ δ_k`.  The weld (`_DoorIVDilationFactorCoherenceWeld`) named the *per-level* threshold:
"a 2-dilation step must purchase a coherence deficit `≥ (2−√2)/2 ≈ 0.293` at every level" to reach the
prize per-level factor `√2` (from `_DoorIVTowerGrowthIteration`).  These two thresholds were never
**identified**: is the budget's per-level requirement the *same* `(2−√2)/2` the weld named?

This module proves they coincide, via the **EXACT** product (not the exp relaxation).  For a *uniform*
per-level deficit `δ k = δ*`, the per-level dilation factor is `c = 2·(1 − δ*)`, and the telescoped
worst period is `M a ≤ (2(1−δ*))^a · M 0`.  The prize per-level threshold is `c ≤ √2`.  We prove:

* `two_mul_one_sub_le_sqrt2_iff` : `2·(1 − δ*) ≤ √2  ⟺  δ* ≥ 1 − √2/2`, and
* `weld_threshold_eq` : `1 − √2/2 = (2 − √2)/2` — the budget's per-level threshold is **exactly the
  weld-named constant**;
* `uniform_deficit_telescope_le` : under `δ k = δ*` and the per-level factor bound, `M a ≤ (2(1−δ*))^a·M 0`;
* `uniform_deficit_reaches_sqrt2_iff` : the uniform per-level factor reaches the prize threshold `√2`
  iff `δ* ≥ (2 − √2)/2`.

The **exact** product threshold `(2−√2)/2 ≈ 0.2929` is sharper than the exp-relaxed budget threshold
`(log 2)/2 ≈ 0.3466` (since `e^{−x} ≥ 1 − x`, the exp bound demands a *larger* deficit).  Both are
*linear-in-a* sustained budgets; this file records that the EXACT per-level requirement matches the
weld constant exactly, unifying the budget and weld accounts.

Lane-3 constraint lemma: prices the route's exact per-level threshold; does NOT prove it is achievable.
No cancellation / moment / completion / anti-concentration / capacity claim.  CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVUniformDeficitThreshold

open Real

/-- **The per-level prize-factor inequality, solved for the deficit.**  `2·(1 − δ) ≤ √2` iff
`δ ≥ 1 − √2/2`.  (Plain real algebra: divide the threshold by `2`.) -/
theorem two_mul_one_sub_le_sqrt2_iff (δ : ℝ) :
    2 * (1 - δ) ≤ Real.sqrt 2 ↔ δ ≥ 1 - Real.sqrt 2 / 2 := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The budget threshold equals the weld-named constant.**  `1 − √2/2 = (2 − √2)/2`.  So the
per-level deficit the (uniform) dilation budget requires to reach the prize factor `√2` is *exactly*
the `(2−√2)/2` named by `_DoorIVDilationFactorCoherenceWeld`. -/
theorem weld_threshold_eq : (1 : ℝ) - Real.sqrt 2 / 2 = (2 - Real.sqrt 2) / 2 := by
  ring

/-- **Uniform-deficit telescope.**  If every level has the *same* deficit `δ k = δ*` (with
`δ* ∈ [0,1]`) and the per-level factor bound `M (k+1) ≤ (2 − 2·δ*)·M k` holds, then
`M a ≤ (2·(1 − δ*))^a · M 0`.  (Specialization of the variable telescope to a constant deficit, using
`2 − 2δ* = 2(1 − δ*)`.) -/
theorem uniform_deficit_telescope_le (M : ℕ → ℝ) (δstar : ℝ)
    (hδ0 : 0 ≤ δstar) (hδ1 : δstar ≤ 1) (hM : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ (2 - 2 * δstar) * M k) (a : ℕ) :
    M a ≤ (2 * (1 - δstar)) ^ a * M 0 := by
  have h1 : M a ≤ (∏ _k ∈ Finset.range a, (2 - 2 * δstar)) * M 0 :=
    DoorIVDilationDeficitBudget.telescope_variable_factor
      M (fun _ => δstar) (fun _ => hδ0) (fun _ => hδ1) hM hstep a
  have hprod : (∏ _k ∈ Finset.range a, (2 - 2 * δstar)) = (2 * (1 - δstar)) ^ a := by
    rw [Finset.prod_const, Finset.card_range]
    congr 1; ring
  rwa [hprod] at h1

/-- **The uniform per-level factor reaches the prize threshold `√2` iff `δ* ≥ (2 − √2)/2`.**  The
per-level factor `c = 2·(1 − δ*)` satisfies `c ≤ √2` exactly when the (uniform) coherence deficit
clears the weld-named threshold.  Below it the factor overshoots `√2` (super-`√n` growth per
`_DoorIVTowerGrowthIteration`); at or above it the factor is prize-admissible — but the deficit being
*sustained* at that level is precisely the open door-(iv) anti-concentration input. -/
theorem uniform_deficit_reaches_sqrt2_iff (δstar : ℝ) :
    2 * (1 - δstar) ≤ Real.sqrt 2 ↔ δstar ≥ (2 - Real.sqrt 2) / 2 := by
  rw [two_mul_one_sub_le_sqrt2_iff, weld_threshold_eq]

end ArkLib.ProximityGap.Frontier.DoorIVUniformDeficitThreshold
