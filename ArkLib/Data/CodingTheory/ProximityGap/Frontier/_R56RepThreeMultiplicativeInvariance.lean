/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R55Depth3VarianceReformulation

/-!
# LANE B2 (#466 round 56): THE MULTIPLICATIVE SYMMETRY OF THE REPRESENTATION FUNCTION

Round 55 recast the depth-3 target as the ℓ²-flatness deficit of `rep3 G`.  This brick exploits
the one piece of structure that is special to `G = μ_n` and absent from a generic set: `G` is a
**multiplicative subgroup**, so the additive representation function inherits a multiplicative
symmetry.

  **`rep3_smul`** :  for `a ∈ G`, `rep3 G (a * c) = rep3 G c`.

Proof: `x ↦ a⁻¹ x` is a bijection of `G` (subgroup closure), and it carries the triples summing
to `a·c` onto the triples summing to `c`.

**Consequence (the sharpened lens).**  `rep3 G` is constant on each multiplicative coset `a·H`
of `G`.  So the flatness deficit `∑_c (q·rep3 G c − |G|³)²` — the DC-subtracted energy (round 55)
— is really a sum over the `(q−1)/|G|` **cosets** (the Gauss-period orbits), each contributing
`|G|` equal terms, plus the `c = 0` point:

  `∑_c (q·rep3(c) − |G|³)² = (deficit at 0) + |G| · ∑_{cosets O} (q·rep3(O) − |G|³)²`.

i.e. the depth-3 flatness problem has only `(q−1)/|G|` genuine degrees of freedom (the distinct
Gauss periods), NOT `q`.  This is exactly the reduction to the Gauss-period index set
`𝔽_q^* / G` that the character-sum picture also sees (each nontrivial `η_b` depends only on the
coset of `b`), now made explicit on the additive side.

`rep3_orbit_const` packages the coset-constancy.  This does not break the wall (the per-coset
values are still governed by Paley/BGK), but it is the correct structural normalization of the
round-55 variance and a genuinely `μ_n`-specific fact.  Issue #466, round 56.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance

open ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Multiplicative invariance of the 3-fold representation function.**  If `G` is closed under
multiplication and inverses and avoids `0` (a multiplicative subgroup), then for `a ∈ G` and any
target `c`, `rep3 G (a * c) = rep3 G c`. -/
theorem rep3_smul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    rep3 G (a * c) = rep3 G c := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hainv : a⁻¹ ∈ G := hinv ha
  -- the multiplication-by-`a` bijection of `G`
  have hmemA : ∀ x : F, a * x ∈ G ↔ x ∈ G := by
    intro x
    constructor
    · intro hx
      have : a⁻¹ * (a * x) ∈ G := hmul hainv hx
      rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
    · intro hx; exact hmul ha hx
  -- reindexing helper: `x ↦ a·x` permutes `G`, so `∑_{y∈G} f(a·y) = ∑_{y∈G} f y`
  have hreindex : ∀ f : F → ℕ, ∑ y ∈ G, f (a * y) = ∑ y ∈ G, f y := by
    intro f
    refine Finset.sum_nbij' (i := fun y => a * y) (j := fun y => a⁻¹ * y)
      (fun y hy => (hmemA y).mpr hy) (fun y hy => hmul hainv hy)
      (fun y _ => inv_mul_cancel_left₀ ha0 y)
      (fun y _ => mul_inv_cancel_left₀ ha0 y)
      (fun y _ => rfl)
  unfold rep3
  -- reindex the three `G`-sums of the `a·c`-target energy by `yᵢ ↦ a·yᵢ`
  rw [← hreindex (fun y₁ => ∑ y₂ ∈ G, ∑ y₃ ∈ G, if y₁ + y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₁ _ => ?_)
  rw [← hreindex (fun y₂ => ∑ y₃ ∈ G, if a * y₁ + y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₂ _ => ?_)
  rw [← hreindex (fun y₃ => if a * y₁ + a * y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₃ _ => ?_)
  -- pointwise: `a·y₁ + a·y₂ + a·y₃ = a·c  ↔  y₁ + y₂ + y₃ = c`
  rw [show a * y₁ + a * y₂ + a * y₃ = a * (y₁ + y₂ + y₃) by ring]
  simp only [mul_right_inj' ha0]

/-- **Coset-constancy.**  `rep3 G` is constant on each multiplicative coset of `G`: if
`a, a' ∈ G` then `rep3 G (a * c) = rep3 G (a' * c)`. -/
theorem rep3_orbit_const (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a a' : F} (ha : a ∈ G) (ha' : a' ∈ G) (c : F) :
    rep3 G (a * c) = rep3 G (a' * c) := by
  rw [rep3_smul G hmul hinv h0 ha c, rep3_smul G hmul hinv h0 ha' c]

end ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_smul
#print axioms ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_orbit_const
