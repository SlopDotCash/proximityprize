/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADualPencilLaw
import ArkLib.Data.CodingTheory.ProximityGap.TwoPlusAntipodalChordLaw
import ArkLib.Data.CodingTheory.ProximityGap.SecondLayerSeedFamily

/-!
# The slanted supply as wide circuits: the consumer weld

Campaign #357. The slanted supply laws (the two-plus-antipodal chord law and the two
universal seed families) are stated as collinearity equations; the matroid lane consumes
**dual dependencies** (`dualVec` combinations) through the pencil criterion
(`dependent_iff_collinear`). This file welds them: each supply family, instantiated on a
domain embedding taking root-of-unity values, **is a wide circuit** — a nontrivial
dependency of the three pair-triangle duals.

* `chordLaw_wide_circuit` — the `(d, d, n/2)` family: indices valued
  `ζ^i, ζ^{i+d}, ζ^j, ζ^{j+d}, ζ^k, ζ^{k+2^(m−1)}` with the chord congruence
  `2k ≡ i+j+d (mod 2^m)` carry a dependency (supply direction only — no
  non-antipodality or distinctness side conditions needed: the congruence kills the
  third factor of the chord factorization outright).
* `shape1_wide_circuit` / `shape2_wide_circuit` — the universal seed families as wide
  circuits, for every scale and parameter.

These are the *positive* counterparts of `independent_of_same_diff` (the negative law):
together they hand the collision matroid's circuit supply to the rainbow-or-monochrome
census optimization as explicit dependency terms.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357; `MCADualPencilLaw.dependent_iff_collinear` (the interface),
  `MCAParabolaStratification.independent_of_same_diff` (the negative counterpart),
  `TwoPlusAntipodalChordLaw.lean`, `SecondLayerSeedFamily.lean` (the laws).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open ProximityGap.MCADualPencilLaw
open ArkLib.ProximityGap.TwoPlusAntipodalChordLaw
open ArkLib.ProximityGap.SecondLayerSeedFamily
open ArkLib.ProximityGap.PairSumRigidityModP

namespace ArkLib.ProximityGap.SlantedSupplyWideCircuits

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The chord-law family as a wide circuit.** Six distinct indices valued
`ζ^i, ζ^{i+d}, ζ^j, ζ^{j+d}, ζ^k, ζ^{k+2^(m−1)}` with the chord congruence
`2k ≡ i+j+d (mod 2^m)`: the three pair-triangle duals carry a nontrivial dependency. -/
theorem chordLaw_wide_circuit (domain : ι ↪ F) {a a' b b' c c' : ι}
    (h6 : Distinct6 a a' b b' c c') {m : ℕ} (hm : 1 ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) {i j k d : ℕ}
    (hva : domain a = ζ ^ i) (hva' : domain a' = ζ ^ (i + d))
    (hvb : domain b = ζ ^ j) (hvb' : domain b' = ζ ^ (j + d))
    (hvc : domain c = ζ ^ k) (hvc' : domain c' = ζ ^ (k + 2 ^ (m - 1)))
    (hcong : (2 * k) % 2 ^ m = (i + j + d) % 2 ^ m) :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i', α * dualVec domain {a, a', b, b'} i' + β * dualVec domain {a, a', c, c'} i'
        + γ * dualVec domain {b, b', c, c'} i' = 0 := by
  rw [dependent_iff_collinear domain h6, hva, hva', hvb, hvb', hvc, hvc']
  have hpow : ζ ^ (i + j + d) = ζ ^ (2 * k) := by
    rw [pow_reduce hζ (i + j + d), pow_reduce hζ (2 * k), hcong]
  have hfac := chord_det_factor hm hζ i j k d
  linear_combination hfac + (ζ ^ j - ζ ^ i) * (1 + ζ ^ d) * hpow

/-- **The shape-I seed family as a wide circuit**, at every scale and parameter. -/
theorem shape1_wide_circuit (domain : ι ↪ F) {a a' b b' c c' : ι}
    (h6 : Distinct6 a a' b b' c c') {m : ℕ} (hm : 1 ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) {t : ℕ} (ht : t < 2 ^ (m - 1))
    (hva : domain a = ζ ^ 0) (hva' : domain a' = ζ ^ 1)
    (hvb : domain b = ζ ^ (t + 1)) (hvb' : domain b' = ζ ^ (2 ^ m - (2 * t + 1)))
    (hvc : domain c = ζ ^ (2 * t + 1)) (hvc' : domain c' = ζ ^ (2 ^ (m - 1) - t)) :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i', α * dualVec domain {a, a', b, b'} i' + β * dualVec domain {a, a', c, c'} i'
        + γ * dualVec domain {b, b', c, c'} i' = 0 := by
  rw [dependent_iff_collinear domain h6, hva, hva', hvb, hvb', hvc, hvc']
  linear_combination shape1_collinear hm hζ ht

/-- **The shape-II seed family as a wide circuit**, at every scale and parameter. -/
theorem shape2_wide_circuit (domain : ι ↪ F) {a a' b b' c c' : ι}
    (h6 : Distinct6 a a' b b' c c') {m : ℕ} (hm : 1 ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) {t : ℕ} (ht : t + 1 < 2 ^ (m - 1))
    (hva : domain a = ζ ^ 0) (hva' : domain a' = ζ ^ 1)
    (hvb : domain b = ζ ^ (t + 2)) (hvb' : domain b' = ζ ^ (2 ^ m - (2 * t + 2)))
    (hvc : domain c = ζ ^ (2 * t + 4))
    (hvc' : domain c' = ζ ^ (2 ^ (m - 1) - (t + 1))) :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i', α * dualVec domain {a, a', b, b'} i' + β * dualVec domain {a, a', c, c'} i'
        + γ * dualVec domain {b, b', c, c'} i' = 0 := by
  rw [dependent_iff_collinear domain h6, hva, hva', hvb, hvb', hvc, hvc']
  linear_combination shape2_collinear hm hζ ht

/-! ## Source audit -/

#print axioms chordLaw_wide_circuit
#print axioms shape1_wide_circuit
#print axioms shape2_wide_circuit

end ArkLib.ProximityGap.SlantedSupplyWideCircuits
