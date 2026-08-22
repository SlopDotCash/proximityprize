/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DilationDoublingMassHalf
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumCosetInv

/-!
# The doubling-mass halving does NOT iterate (#444)

`DilationDoublingMassHalf` proves a **single-level** cap: along one genuine disjoint tower step the
L²-weighted **doubling** (`+`-sign) cross-mass is at most `½·q·|G|`
(`plusMass_le_half_card`). Its own honesty note flags the open gap: *"a single frequency may sit on
the `+`-trajectory through MANY levels; the average only forbids ALL of them doing so."* The
natural hope is that the halving **iterates**: that intersecting the `+`-sign condition at a second,
independent tower dilation `ζ'` thins the doubling mass by another factor `½`, giving a geometric
deep-descent cap `plus_ℓ ≤ 2^{-ℓ}·q·|G|`.

**This file proves that hope is FALSE for the obvious "other tower neighbor" choice, with the exact
mechanism.** The two tower neighbors of a frequency `b` are `ζ·b` and `ζ⁻¹·b`; they differ by
`ζ² = ζ·(ζ⁻¹)⁻¹`, and `ζ² ∈ G` for the tower step (`ζ` has order `2n`, `ζ² ∈ μ_n = G`). Since the
period is **`G`-coset-invariant in the frequency** (`eta_smul_invariant`, #389), the second neighbor
carries the *same* period: `η_{ζ⁻¹·b} = η_{ζ·b}` whenever `ζ⁻²·(ζ·b) = ζ⁻¹·b` and `ζ⁻² ∈ G`. Hence
the second `+`-sign condition is **literally identical** to the first, the doubly-doubling mass
equals the singly-doubling mass, and there is **no second halving**.

## The results (extend `eta_smul_invariant` + `crossSign`/`crossMass`/`plusMass`)

* `crossSign_dilate_smul_eq` — `crossSign` is unchanged when the dilation `ζ` is pre-multiplied by a
  `G`-permuting unit `g` (e.g. `g ∈ G`): `crossSign ψ G (g·ζ) b = crossSign ψ G ζ b`.
* `crossMass_dilate_smul_eq` — same for `crossMass`.
* `plusMass_dilate_smul_eq` — hence `plusMass ψ G (g·ζ) = plusMass ψ G ζ`: the doubling mass is a
  **`G`-coset invariant of the dilation**. Two tower dilations that differ by a `G`-element define
  the *same* doubling set and the *same* doubling mass.
* `plusMass_inv_eq` — the concrete deep-descent statement: for the two tower neighbors,
  `plusMass ψ G ζ⁻¹ = plusMass ψ G ζ` whenever `ζ⁻² ∈ G` (`ζ⁻¹ = ζ⁻²·ζ`). Intersecting the
  `+`-condition at `ζ` and at `ζ⁻¹` is intersecting a set with itself — **no second halving**.

## Scope / honesty (refutation-with-mechanism, rule 4)

This is a **negative structural result**: it refutes the "iterated halving via the other tower
neighbor" route to a geometric deep-descent cap, and pins the exact reason (`G`-coset-invariance of
the period collapses the two neighbor conditions to one). It is **probe-confirmed** (exact `F_p`,
PROPER thin `μ_n`, `p≍n⁴`, `n=8..64`, `NEVER n=q-1`): `plus2Mass/plusMass = 1.000` and the mixed
sign-quadrant cross-mass is `0.000` to machine precision (`scripts/probes/probe_doubling_twolevel_*`).
It does **NOT** close CORE and does **NOT** refute the *general* iterated-halving hope for a
*genuinely independent* second dilation `ζ'` outside the `G`-coset of `ζ` and `ζ⁻¹` — it removes the
ONE obvious choice (the other tower neighbor) and explains why. The worst-case single-frequency
deep-descent sign word (the BGK/Paley wall) stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open scoped BigOperators
open Finset
open ArkLib.ProximityGap.SubgroupGaussSumCosetInv (eta_smul_invariant)

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `crossSign` of a dilation pre-multiplied by a `G`-permuting unit `g` equals the original.
Uses `eta_smul_invariant`: `η_{(g·ζ)·b} = η_{g·(ζ·b)} = η_{ζ·b}`. -/
theorem crossSign_dilate_smul_eq {ψ : AddChar F ℂ} (G : Finset F) {g ζ : F}
    (hmem : ∀ x ∈ G, g * x ∈ G) (hmem' : ∀ x ∈ G, g⁻¹ * x ∈ G) (hg : g ≠ 0) (b : F) :
    crossSign ψ G (g * ζ) b = crossSign ψ G ζ b := by
  unfold crossSign
  have hreidx : (g * ζ) * b = g * (ζ * b) := by ring
  rw [hreidx, eta_smul_invariant G hmem hmem' hg]

/-- The `crossMass` of a dilation pre-multiplied by a `G`-permuting unit `g` equals the original. -/
theorem crossMass_dilate_smul_eq {ψ : AddChar F ℂ} (G : Finset F) {g ζ : F}
    (hmem : ∀ x ∈ G, g * x ∈ G) (hmem' : ∀ x ∈ G, g⁻¹ * x ∈ G) (hg : g ≠ 0) (b : F) :
    crossMass ψ G (g * ζ) b = crossMass ψ G ζ b := by
  unfold crossMass
  have hreidx : (g * ζ) * b = g * (ζ * b) := by ring
  rw [hreidx, eta_smul_invariant G hmem hmem' hg]

/-- **The doubling mass is a `G`-coset invariant of the dilation.** Pre-multiplying the dilation `ζ`
by any `G`-permuting unit `g` leaves the doubling (`+`-sign) cross-mass unchanged. Consequently two
tower dilations that differ by a `G`-element carry the *same* doubling set and the *same* doubling
mass — the source of the "no second halving" collapse. -/
theorem plusMass_dilate_smul_eq {ψ : AddChar F ℂ} (G : Finset F) {g ζ : F}
    (hmem : ∀ x ∈ G, g * x ∈ G) (hmem' : ∀ x ∈ G, g⁻¹ * x ∈ G) (hg : g ≠ 0) :
    plusMass ψ G (g * ζ) = plusMass ψ G ζ := by
  classical
  unfold plusMass
  -- the filter predicate is the same set (crossSign equal pointwise), and the summand is equal
  have hfilt : (Finset.univ.filter (fun b => 0 ≤ crossSign ψ G (g * ζ) b))
      = Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b) := by
    apply Finset.filter_congr
    intro b _
    rw [crossSign_dilate_smul_eq G hmem hmem' hg b]
  rw [hfilt]
  apply Finset.sum_congr rfl
  intro b _
  exact crossMass_dilate_smul_eq G hmem hmem' hg b

/-- **No second halving via the other tower neighbor.** If `ζ⁻²` permutes `G` (the tower case:
`ζ` has order `2n`, so `ζ⁻² ∈ μ_n = G`), then the doubling mass at the inverse dilation `ζ⁻¹`
equals that at `ζ`: `plusMass ψ G ζ⁻¹ = plusMass ψ G ζ`. Writing `ζ⁻¹ = ζ⁻²·ζ`, the two tower
neighbors define the *same* `+`-sign condition, so intersecting them is intersecting a set with
itself — the average halving cannot be iterated this way. -/
theorem plusMass_inv_eq {ψ : AddChar F ℂ} (G : Finset F) {ζ : F}
    (hmem : ∀ x ∈ G, ζ⁻¹ * ζ⁻¹ * x ∈ G) (hmem' : ∀ x ∈ G, (ζ⁻¹ * ζ⁻¹)⁻¹ * x ∈ G)
    (hζ : ζ ≠ 0) :
    plusMass ψ G ζ⁻¹ = plusMass ψ G ζ := by
  have hg : ζ⁻¹ * ζ⁻¹ ≠ 0 := by
    simp [hζ]
  have hidx : ζ⁻¹ = (ζ⁻¹ * ζ⁻¹) * ζ := by
    field_simp
  rw [hidx]
  exact plusMass_dilate_smul_eq G hmem hmem' hg

#print axioms ProximityGap.SubgroupGaussSumSecondMoment.plusMass_dilate_smul_eq
#print axioms ProximityGap.SubgroupGaussSumSecondMoment.plusMass_inv_eq

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
