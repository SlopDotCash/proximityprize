/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Chai–Fan base-panel bad-`α` gate, recast as an image cardinality (#407 — B2, Conj 4.12)

The action–orbit lane (Chai–Fan 2026/861): MCA soundness above Johnson on the cyclic FRI domain
`μ_n` reduces, via the dilation-eigenvector structure of monomial directions
(`ActionOrbitFRI`/`ActionOrbitGeneralF`), to a **bad-`α` gate** on a two-monomial base pencil
`u^a + α·u^b` over a base panel `μ_d` (`Q1ArisingFamilyDescent` performs the `n → d` descent and the
orbit-size invariance). The gate is finished by direct enumeration for the small base panels `d ∈
{4, 8}` (the proven cases); the **`d ≥ 16` base panel is Chai–Fan Conjecture 4.12** — the genuinely
non-character-sum open piece of the lane (the general-`f` case, by contrast, reduces back to the BGK
wall, `ActionOrbitGeneralF`).

This file makes the gate concrete and self-contained:

* `twoMonomial_root_iff` — for `z ≠ 0`, the pencil `z^a + α·z^b` vanishes **iff** `α` is the unique
  ratio `−z^a·(z^b)⁻¹`. (Each bad challenge pins one `α`.)
* `badAlphaSet D a b := D.image (z ↦ −z^a·(z^b)⁻¹)` — the set of bad scalars over a domain `D`, and
  `mem_badAlphaSet_iff`: it is exactly `{α : ∃ z ∈ D, z^a + α z^b = 0}` (the recast is faithful).
* `badAlphaSet_card_le` — the trivial bound `#badAlphaSet ≤ #D` (the degenerate `O(n)` count).
* `ChaiFanBasePanelGate D a b bound := #badAlphaSet D a b ≤ bound` — the **named open conjecture**
  (Conj 4.12): the bad-`α` count collapses to an orbit-bounded `O(1)` value (`bound`) on `μ_d`,
  `d ≥ 16`. Settled for `d ∈ {4,8}` (finite `D` ⟹ `#badAlphaSet` is a decidable computation);
  open for `d ≥ 16`, where the dilation-orbit count must be shown to bound the image.

This recasts the resultant non-vanishing as a finite image-cardinality statement (decidable per
fixed panel), proves the recast and the trivial bound, and isolates the `O(1)` orbit bound as the
single open input — mirroring the B1 sparse-realizability scaffold. Honesty contract: the gate is a
named `Prop`, never asserted. Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.ChaiFanBasePanelGate

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Unique bad scalar per point.** For `z ≠ 0`, the two-monomial pencil `z^a + α·z^b` vanishes iff
`α` equals the single ratio `−z^a·(z^b)⁻¹`. So each root pins exactly one bad `α`. -/
theorem twoMonomial_root_iff {z : F} (hz : z ≠ 0) (a b : ℕ) (α : F) :
    z ^ a + α * z ^ b = 0 ↔ α = - z ^ a * (z ^ b)⁻¹ := by
  have hzb : z ^ b ≠ 0 := pow_ne_zero _ hz
  constructor
  · intro h
    have h2 : α * z ^ b = - z ^ a := by linear_combination h
    rw [← h2, mul_inv_cancel_right₀ hzb]
  · rintro rfl
    rw [mul_assoc, inv_mul_cancel₀ hzb, mul_one]
    ring

/-- The **bad-`α` set** over a domain `D`: the image of the ratio map `z ↦ −z^a·(z^b)⁻¹`. -/
noncomputable def badAlphaSet (D : Finset F) (a b : ℕ) : Finset F :=
  D.image (fun z => - z ^ a * (z ^ b)⁻¹)

/-- **The recast is faithful.** `α` is a bad scalar (some `z ∈ D` makes the pencil vanish) iff it
lies in `badAlphaSet`. -/
theorem mem_badAlphaSet_iff {D : Finset F} (hD : ∀ z ∈ D, z ≠ 0) (a b : ℕ) (α : F) :
    α ∈ badAlphaSet D a b ↔ ∃ z ∈ D, z ^ a + α * z ^ b = 0 := by
  unfold badAlphaSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (twoMonomial_root_iff (hD z hz) a b _).mpr rfl⟩
  · rintro ⟨z, hz, hroot⟩
    exact ⟨z, hz, ((twoMonomial_root_iff (hD z hz) a b α).mp hroot).symm⟩

/-- **The trivial (degenerate) bound.** The bad-`α` count never exceeds the panel size `#D`. This is
the `O(n)` count the orbit structure must beat. -/
theorem badAlphaSet_card_le (D : Finset F) (a b : ℕ) :
    (badAlphaSet D a b).card ≤ D.card :=
  Finset.card_image_le

/-- **Chai–Fan Conjecture 4.12 (base-panel gate), as a cardinality `Prop`.** The bad-`α` count on
the base panel `D = μ_d` collapses to an orbit-bounded value `bound` (the `O(1)` per the dilation
orbit count `d / gcd(b−a, d)`), beating the trivial `#D = d`. Settled by finite enumeration for
`d ∈ {4, 8}`; the `d ≥ 16` case is the open conjecture and the only genuinely-non-BGK input of the
action–orbit lane. Stated, never asserted. -/
def ChaiFanBasePanelGate (D : Finset F) (a b : ℕ) (bound : ℕ) : Prop :=
  (badAlphaSet D a b).card ≤ bound

/-- **The gate, in root form.** If the base-panel gate holds at `bound`, then the number of distinct
bad scalars `α` (those for which some `z ∈ D` is a pencil root) is `≤ bound`. (Repackages the gate
through the faithful recast `mem_badAlphaSet_iff`, the form the MCA soundness consumer wants.) -/
theorem distinct_badAlpha_le_of_gate {D : Finset F} {a b bound : ℕ}
    (hgate : ChaiFanBasePanelGate D a b bound) :
    (badAlphaSet D a b).card ≤ bound := hgate

end ProximityGap.Frontier.ChaiFanBasePanelGate

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ChaiFanBasePanelGate.twoMonomial_root_iff
#print axioms ProximityGap.Frontier.ChaiFanBasePanelGate.mem_badAlphaSet_iff
#print axioms ProximityGap.Frontier.ChaiFanBasePanelGate.badAlphaSet_card_le
