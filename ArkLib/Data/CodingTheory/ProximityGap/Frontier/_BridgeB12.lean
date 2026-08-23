/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter

/-!
# Bridge B12 — target E3: the fixed-point `γ=0` contributes `z ∈ {0,1}` (#444)

E3 decomposes the monomial bad-α count as `D = z + S·O`, where `O` orbits each have size `S`
(the free-action part, off the fixed point) and `z` is the contribution of the single dilation
fixed point `γ = 0`.

This brick proves the **`z ∈ {0,1}`** part precisely and abstractly: the dilation `α ↦ α·h^{b−a}`
has `γ = 0` as its unique fixed point, so the fixed-point contribution to the bad set `B` is the
cardinality of the *single-element* filter `B.filter (· = 0)`, which is `≤ 1` (a single boolean
membership: `0 ∈ B` or `0 ∉ B`). Combined with the `card_eq_orbitCount_mul_size` substrate brick
on the complement, this is exactly the `D = z + S·O`, `z ∈ {0,1}` shape of E3.

Pure `Finset` counting; no `sorry`, no extra axioms.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB12

variable {ι : Type*} [DecidableEq ι]

/-- **The fixed-point contribution is a single boolean (`z ∈ {0,1}`).**
For any finite bad set `B` and any fixed point `fp` (here the dilation fixed point `γ = 0`),
the number of bad elements equal to `fp` is `0` or `1`: it is the cardinality of the filter of
`B` to the single value `fp`, which never exceeds `1`. -/
theorem fixedPoint_card_le_one (B : Finset ι) (fp : ι) :
    (B.filter (fun a => a = fp)).card ≤ 1 := by
  classical
  have hsub : B.filter (fun a => a = fp) ⊆ {fp} := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_singleton]; exact ha.2
  calc (B.filter (fun a => a = fp)).card ≤ ({fp} : Finset ι).card :=
          Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton fp

/-- **`z ∈ {0,1}` as a genuine disjunction.** The fixed-point contribution is exactly `0`
(when `fp ∉ B`) or `1` (when `fp ∈ B`). -/
theorem fixedPoint_card_eq_zero_or_one (B : Finset ι) (fp : ι) :
    (B.filter (fun a => a = fp)).card = 0 ∨ (B.filter (fun a => a = fp)).card = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (fixedPoint_card_le_one B fp) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **E3 split: `D = z + (off-fixed-point count)` with `z ≤ 1`.**
The total bad count `|B|` splits as the fixed-point contribution `z` (a single boolean, `≤ 1`)
plus the complementary count `|B.filter (· ≠ fp)|` (the free-action part that the substrate
`card_eq_orbitCount_mul_size` brick rewrites as `S·O`). -/
theorem card_split_fixedPoint (B : Finset ι) (fp : ι) :
    B.card = (B.filter (fun a => a = fp)).card + (B.filter (fun a => a ≠ fp)).card ∧
      (B.filter (fun a => a = fp)).card ≤ 1 := by
  classical
  refine ⟨?_, fixedPoint_card_le_one B fp⟩
  have := Finset.filter_card_add_filter_neg_card_eq_card
    (s := B) (p := fun a => a = fp)
  simpa using this.symm

/-- **Sanity instance.** Concretely `B = {0,1,2,3} ⊆ ℕ`, fixed point `fp = 0`: the
fixed-point contribution is `1` (since `0 ∈ B`), confirming `z ∈ {0,1}`. -/
example : (({0, 1, 2, 3} : Finset ℕ).filter (fun a => a = 0)).card = 1 := by decide

end ArkLib.ProximityGap.BridgeB12

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB12.fixedPoint_card_le_one
#print axioms ArkLib.ProximityGap.BridgeB12.fixedPoint_card_eq_zero_or_one
#print axioms ArkLib.ProximityGap.BridgeB12.card_split_fixedPoint
