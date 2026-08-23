/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ59EmptyMiddle
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ68GeneratorGapParity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ69ParityClassification

/-!
# SYZ70 — the first open middle-band slot is the balanced sextic `(6,6,6)` at `δ₁ = 7`

## What this file does

SYZ59/SYZ69 reduced the rate-`1/2` spread residual to one geometric claim: the product-convention
**middle band** `max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2` is empty on band-realizable triples.  Their finite
census only reaches balanced degrees `{3,4,5}`.  This file does the next arithmetic localisation,
without claiming the geometric exclusion:

1. The middle band is *arithmetically possible* iff `max + 3 ≤ ⌊S/2⌋`.
2. On a balanced profile `a = b = c = d`, that inequality is `6 ≤ d`.  So the SYZ59 census
   `{3,4,5}` is the complete list of balanced degrees whose middle is empty for *ℕ-arithmetic*
   reasons alone; no geometry is required there.
3. The first nonempty balanced middle is a **singleton**: `middleBand 6 6 6 δ₁ ↔ δ₁ = 7`.
   Under the degree-sum law this slot is `g = 4`, `ι = 2`, even-`S` parity-allowed.
4. Via the SYZ59 convention bridge `product = cofactor + max`, the slot is exactly a
   **degree-`1` cofactor syzygy** of three degree-`6` polynomials.  The first open geometric
   obligation is therefore: no band-realizable balanced sextic triple admits a linear-cofactor
   syzygy.

## What is not claimed

This file does **not** exclude `δ₁ = 7` on realizable triples.  It does not discharge
`UniformSylvesterInjective`, `ι ≤ 1`, or production `δ*`.  CORE remains OPEN / ON-BGK.  The
constant-syzygy family at `(6,6,6)` still attains the floor (`δ₁ = 6`); that is a different
class (SYZ69 floor-attained) and is recorded here only as the complementary slot.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ70

open ArkLib.ProximityGap

/-! ## 1. When the middle band can exist at all -/

/-- **Existence of a middle degree.**  There is an integer `δ₁` in the middle band iff the floor
sits at least three below the balanced edge: `max + 3 ≤ ⌊S/2⌋`.  Pure `ℕ`. -/
theorem exists_middleBand_iff (a b c : ℕ) :
    (∃ δ₁, SYZ59.middleBand a b c δ₁) ↔
      max a (max b c) + 3 ≤ (a + b + c) / 2 := by
  unfold SYZ59.middleBand
  constructor
  · rintro ⟨δ₁, hlt, hle⟩
    omega
  · intro h
    refine ⟨max a (max b c) + 1, ?_, ?_⟩
    · omega
    · omega

/-- **Balanced middle exists iff `d ≥ 6`.**  For `a = b = c = d` one has `S = 3d` and
`max = d`, so `d + 3 ≤ ⌊3d/2⌋` rearranges to `6 ≤ d`.  This is why the SYZ59 census
`d ∈ {3,4,5}` never needed geometry to rule the middle out. -/
theorem balanced_exists_middleBand_iff (d : ℕ) :
    (∃ δ₁, SYZ59.middleBand d d d δ₁) ↔ 6 ≤ d := by
  rw [exists_middleBand_iff]
  omega

/-- **The SYZ59 census degrees have an empty middle by arithmetic.** -/
theorem balanced_middle_empty_of_lt_six (d δ₁ : ℕ) (hd : d < 6) :
    ¬ SYZ59.middleBand d d d δ₁ := by
  intro h
  have : ∃ δ, SYZ59.middleBand d d d δ := ⟨δ₁, h⟩
  have := (balanced_exists_middleBand_iff d).1 this
  omega

/-! ## 2. The first open slot: balanced `(6,6,6)` at product-degree `7` -/

/-- **The first nonempty balanced middle is the singleton `{7}`.** -/
theorem first_balanced_middle_slot (δ₁ : ℕ) :
    SYZ59.middleBand 6 6 6 δ₁ ↔ δ₁ = 7 := by
  unfold SYZ59.middleBand
  omega

/-- Occupied: `δ₁ = 7` really is middle at `(6,6,6)`. -/
theorem first_balanced_middle_occupied : SYZ59.middleBand 6 6 6 7 :=
  (first_balanced_middle_slot 7).2 rfl

/-- Under the degree-sum law, the first slot has generator gap `4`. -/
theorem first_slot_gap (δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = 18) (hδ : δ₁ = 7) :
    δ₂ - δ₁ = 4 := by
  omega

/-- Under the degree-sum law, the first slot has imbalance `ι = 2`. -/
theorem first_slot_imbalance (δ₁ : ℕ) (hδ : δ₁ = 7) :
    SYZ45.imbalance 6 6 6 δ₁ = 2 := by
  unfold SYZ45.imbalance
  omega

/-- The first slot is even-`S` and parity-allowed (`g ≡ S (mod 2)`). -/
theorem first_slot_even_parity (δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = 18) (hle : δ₁ ≤ δ₂) :
    (δ₂ - δ₁) % 2 = (6 + 6 + 6) % 2 :=
  SYZ68.gap_parity 6 6 6 δ₁ δ₂ hsum hle

/-! ## 3. Convention-bridge reading: the slot is a linear cofactor -/

/-- **First slot = cofactor degree `1`.**  The SYZ59 bridge says
`productDeg = cofactorDeg + max`.  At the first middle slot `productDeg = 7` and `max = 6`,
so the cofactor vector has degree exactly `1`.  The geometric residual at this slot is
therefore the non-existence of a *linear* cofactor syzygy on a band-realizable balanced
sextic triple. -/
theorem first_slot_cofactor_degree_one
    (productDeg cofactorDeg : ℕ)
    (hbridge : productDeg = cofactorDeg + 6)
    (hprod : productDeg = 7) :
    cofactorDeg = 1 := by
  omega

/-- Complementary class: the floor-attained constant-syzygy family at `(6,6,6)` has
product-degree `6`, not `7`.  It is *not* a middle witness. -/
theorem first_slot_not_floor_attained :
    ¬ SYZ59.middleBand 6 6 6 6 := by
  unfold SYZ59.middleBand
  omega

/-- Packaged obligation: excluding the first middle slot is exactly excluding product-degree
`7` (equivalently cofactor degree `1`) on balanced sextics. -/
theorem exclude_first_slot_iff_exclude_degree_seven (hδ : ℕ → Prop) :
    (∀ δ₁, SYZ59.middleBand 6 6 6 δ₁ → ¬ hδ δ₁) ↔ ¬ hδ 7 := by
  constructor
  · intro h
    exact h 7 first_balanced_middle_occupied
  · intro h δ₁ hmid
    have : δ₁ = 7 := (first_balanced_middle_slot δ₁).1 hmid
    exact this ▸ h

end ArkLib.ProximityGap.SYZ70

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ70.exists_middleBand_iff
#print axioms ArkLib.ProximityGap.SYZ70.balanced_exists_middleBand_iff
#print axioms ArkLib.ProximityGap.SYZ70.balanced_middle_empty_of_lt_six
#print axioms ArkLib.ProximityGap.SYZ70.first_balanced_middle_slot
#print axioms ArkLib.ProximityGap.SYZ70.first_balanced_middle_occupied
#print axioms ArkLib.ProximityGap.SYZ70.first_slot_gap
#print axioms ArkLib.ProximityGap.SYZ70.first_slot_imbalance
#print axioms ArkLib.ProximityGap.SYZ70.first_slot_even_parity
#print axioms ArkLib.ProximityGap.SYZ70.first_slot_cofactor_degree_one
#print axioms ArkLib.ProximityGap.SYZ70.first_slot_not_floor_attained
#print axioms ArkLib.ProximityGap.SYZ70.exclude_first_slot_iff_exclude_degree_seven
