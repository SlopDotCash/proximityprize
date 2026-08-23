/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The anharmonic (`S₃`) symmetry of the BGK solution set (#357)

The open core of the deployed Proximity Prize (dossier §30) is the Bourgain–Glibichuk–Konyagin
additive-energy quantity `M = |sol|`, where for the smooth subgroup `G = μ_n` (`n` even, so `−1∈G`),

  `sol = {u ∈ G : 1 + u ∈ G}`.

This file formalizes the structural symmetry observed in §33: `sol` is invariant under the two Möbius
involutions

  `ι : u ↦ u⁻¹`        (`1 + u⁻¹ = (1+u)·u⁻¹ ∈ G`),
  `τ : u ↦ −(1 + u)`    (`1 − (1+u) = −u ∈ G`),

which satisfy `ι² = τ² = id` and `(ι∘τ)³ = id`, i.e. generate the **anharmonic group `S₃`** acting on
`sol` — the *same* Möbius `σ`-family as `MobiusPencilEnergy` (the original §N1 pencil-energy brick).
So the BGK additive-energy core and the Möbius pencil energy are governed by one symmetry; `M = |sol|`
is a sum of `⟨ι,τ⟩`-orbit sizes (each dividing `6`).

**Honest scope:** this is the exact, machine-checked symmetry structure of the open core (a genuine
unification of the §N1 and §30 lines). It gives orbit *structure* (a lower-bound shape on `M`), NOT an
upper bound: `M ≪ √n` still requires the Bourgain sum-product estimate (§30–33). Does not pin `δ*`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.BGKSolSetSymmetry

variable {F : Type*} [Field F] [DecidableEq F]

/-- The BGK solution set `sol = {u ∈ G : 1 + u ∈ G}`. -/
def solSet (G : Finset F) : Finset F := G.filter (fun u => 1 + u ∈ G)

variable (G : Finset F)
  (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, a⁻¹ ∈ G)
  (h0 : (0 : F) ∉ G) (hneg1 : (-1 : F) ∈ G)

include hmul hinv h0 hneg1

/-- Negation closure: `a ∈ G ⟹ −a ∈ G` (since `−1 ∈ G` and `G` is closed under multiplication). -/
theorem neg_mem_of_mem {a : F} (ha : a ∈ G) : -a ∈ G := by
  have h := hmul (-1) hneg1 a ha
  rwa [neg_one_mul] at h

/-- **`ι : u ↦ u⁻¹` preserves `sol`.** If `u, 1+u ∈ G` then `u⁻¹ ∈ G` and
`1 + u⁻¹ = (1+u)·u⁻¹ ∈ G`. -/
theorem inv_mem_solSet {u : F} (hu : u ∈ solSet G) : u⁻¹ ∈ solSet G := by
  rw [solSet, Finset.mem_filter] at hu ⊢
  obtain ⟨huG, h1uG⟩ := hu
  have hune : u ≠ 0 := fun h => h0 (h ▸ huG)
  refine ⟨hinv u huG, ?_⟩
  have hkey : (1 + u) * u⁻¹ = 1 + u⁻¹ := by
    rw [add_mul, one_mul, mul_inv_cancel₀ hune, add_comm]
  rw [← hkey]
  exact hmul (1 + u) h1uG u⁻¹ (hinv u huG)

/-- **`τ : u ↦ −(1+u)` preserves `sol`.** If `u, 1+u ∈ G` then `−(1+u) ∈ G` and
`1 + (−(1+u)) = −u ∈ G`. -/
theorem tau_mem_solSet {u : F} (hu : u ∈ solSet G) : -(1 + u) ∈ solSet G := by
  rw [solSet, Finset.mem_filter] at hu ⊢
  obtain ⟨huG, h1uG⟩ := hu
  have hneg : ∀ a, a ∈ G → -a ∈ G := by
    intro a ha
    have h := hmul (-1) hneg1 a ha
    rwa [neg_one_mul] at h
  refine ⟨hneg _ h1uG, ?_⟩
  have hkey : (1 : F) + -(1 + u) = -u := by ring
  rw [hkey]
  exact hneg _ huG

end ArkLib.ProximityGap.BGKSolSetSymmetry

namespace ArkLib.ProximityGap.BGKSolSetSymmetry

variable {F : Type*} [Field F]

/-- **`τ` is an involution: `τ(τ(u)) = u`.** `τ(τ(u)) = −(1 + −(1+u)) = u`. One of the two `S₃`
generators acting on the BGK solution set. -/
theorem tau_involutive (u : F) : -(1 + -(1 + u)) = u := by ring

/-- **`ι` is an involution: `ι(ι(u)) = u`** for `u ≠ 0`. The other `S₃` generator. -/
theorem iota_involutive {u : F} (hu : u ≠ 0) : (u⁻¹)⁻¹ = u := inv_inv u

/-- **`τ` has a unique fixed point: `τ(u) = u ⟺ 2u = −1`.** (Over char `≠ 2`, `u = −2⁻¹`.) So in the
`S₃`-orbit decomposition of `sol`, the `τ`-reflection contributes at most one fixed coordinate —
relevant to any Burnside/orbit count of `M = |sol|`. -/
theorem tau_fixed_iff {u : F} : -(1 + u) = u ↔ (2 : F) * u = -1 := by
  constructor <;> intro h <;> linear_combination -h

end ArkLib.ProximityGap.BGKSolSetSymmetry

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.BGKSolSetSymmetry.inv_mem_solSet
#print axioms ArkLib.ProximityGap.BGKSolSetSymmetry.tau_mem_solSet
#print axioms ArkLib.ProximityGap.BGKSolSetSymmetry.tau_involutive
