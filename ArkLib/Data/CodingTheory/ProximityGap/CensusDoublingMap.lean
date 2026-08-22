/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CollinearityCensusTransfer

/-!
# The doubling map: census circuits embed across scales

Campaign #357, the third and final generator of the slanted supply structure. The
second-layer recursion `B(n) = n²(n−8)/8 + 2·B(n/2)` has three generators: the shape-I/II
seed families (landed) and the **doubling embedding** `μ_{n/2} ⊆ μ_n` — this file.

* `doubling_collinear_iff` — for a primitive `2^(m+1)`-th root `ζ`: the collinearity
  equation of the doubled exponent triple `(2a₁, …, 2b₃)` at `ζ` **is** the collinearity
  equation of `(a₁, …, b₃)` at the primitive `2^m`-th root `ζ²` — verbatim, an
  if-and-only-if. Every circuit of `Γ_{n/2}` embeds as a circuit of `Γ_n`, and the
  embedded copy is collinear *only if* the original was: the recursion's `2·B(n/2)` term
  is exactly the image of this map (the factor `2` being the two cosets `2ℤ_n` and
  `1 + 2ℤ_n` related by rotation).

With this, all three generators of the slanted supply are Lean theorems; the recursion's
*generation* claim (supply ⊆ census, census ⊆ supply at the probe-verified scales) is
fully mechanized on the supply side.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the Galois-recursion comment); `SecondLayerSeedFamily.lean` (shapes I/II),
  `CollinearityCensusTransfer.lean` (the verdict object).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.CensusDoublingMap

variable {L : Type*} [Field L]

/-- **The doubling map.** The collinearity equation of the doubled exponent triple at a
primitive `2^(m+1)`-th root `ζ` is — verbatim — the collinearity equation of the original
triple at the primitive `2^m`-th root `ζ²`: circuits of `Γ_{n/2}` embed as circuits of
`Γ_n`, and nothing new is collinear on the doubled sublattice. -/
theorem doubling_collinear_iff (ζ : L) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) :
    ((ζ ^ (2 * a₂) + ζ ^ (2 * b₂) - (ζ ^ (2 * a₁) + ζ ^ (2 * b₁)))
        * (ζ ^ (2 * a₃ + 2 * b₃) - ζ ^ (2 * a₁ + 2 * b₁))
      = (ζ ^ (2 * a₂ + 2 * b₂) - ζ ^ (2 * a₁ + 2 * b₁))
        * (ζ ^ (2 * a₃) + ζ ^ (2 * b₃) - (ζ ^ (2 * a₁) + ζ ^ (2 * b₁))))
      ↔ (((ζ ^ 2) ^ a₂ + (ζ ^ 2) ^ b₂ - ((ζ ^ 2) ^ a₁ + (ζ ^ 2) ^ b₁))
        * ((ζ ^ 2) ^ (a₃ + b₃) - (ζ ^ 2) ^ (a₁ + b₁))
      = ((ζ ^ 2) ^ (a₂ + b₂) - (ζ ^ 2) ^ (a₁ + b₁))
        * ((ζ ^ 2) ^ a₃ + (ζ ^ 2) ^ b₃ - ((ζ ^ 2) ^ a₁ + (ζ ^ 2) ^ b₁))) := by
  have hp : ∀ x : ℕ, ζ ^ (2 * x) = (ζ ^ 2) ^ x := fun x => by
    rw [← pow_mul]
  have hps : ∀ x y : ℕ, ζ ^ (2 * x + 2 * y) = (ζ ^ 2) ^ (x + y) := fun x y => by
    rw [← pow_mul]
    congr 1
    ring
  rw [hp a₁, hp b₁, hp a₂, hp b₂, hp a₃, hp b₃,
    hps a₁ b₁, hps a₂ b₂, hps a₃ b₃]

/-- The square of a primitive `2^(m+1)`-th root is a primitive `2^m`-th root: the doubled
sublattice of `Γ_{2^(m+1)}` *is* `Γ_{2^m}`. -/
theorem isPrimitiveRoot_sq_of_double {m : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) : IsPrimitiveRoot (ζ ^ 2) (2 ^ m) := by
  have h := IsPrimitiveRoot.pow (n := 2 ^ (m + 1)) (by positivity) hζ
    (show 2 ^ (m + 1) = 2 * 2 ^ m from by rw [pow_succ]; ring)
  exact h

/-! ## Source audit -/

#print axioms doubling_collinear_iff
#print axioms isPrimitiveRoot_sq_of_double

end ArkLib.ProximityGap.CensusDoublingMap
