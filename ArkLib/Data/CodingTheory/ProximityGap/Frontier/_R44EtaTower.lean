/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R43GaussUnification

/-!
# LANE A (#466 round 44): the A-side tower FOR FREE — `WallHolds`' moment tower collapses
  through the round-27 machinery with the Gauss sequence

Since `conj(λ_j(b)) = λ_{−j}(b)`, the round-43 expansion says the A-side object IS a pure
face of the calculus:

* **`eta_eq_pureFace`** — `m·η_b + 1 = pureFace 𝔤⁻ lam b` for `b ≠ 0`, where
  `𝔤⁻(j) = 𝔤_{−j}`;
* **`eta_tower_collapse`** — hence for EVERY depth `r`:
  `∑_{b≠0} ‖m·η_b + 1‖^{2r} = (q−1)·∑_c ‖(𝔤⁻)^{∗r}(c)‖²`.

`WallHolds`' moment tower (the DC-shifted `η`-moments) is the iterated self-convolution
ℓ²-profile of the Gauss-coefficient sequence — the SAME statement-shape as the B-side ladder
(`IterConvEnergyWick`, r27) with `𝔤⁻` in place of `J`, on the same `ℤ/m`, with the same
proven rungs available (Parseval at r = 1 via `lamExpansion_parseval` is immediate).  The
prize's two towers are now formally one tower with two coefficient sequences, entangled by
the classical Gauss-ratio `J_j = 𝔤_j·𝔤(χ)/𝔤(λ_jχ)`.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 44, LANE A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R44EtaTower

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R24InvolutionNoGo
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity
open ArkLib.ProximityGap.Frontier.R43GaussUnification

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- **The A-side object is a pure face**: `m·η_b + 1 = pureFace 𝔤⁻ lam b` (`b ≠ 0`). -/
theorem eta_eq_pureFace (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) :
    (m : ℂ) * eta ψ G b + 1
      = pureFace (fun j => gaussCoeff lam ψ (-j)) lam b := by
  rw [eta_gauss_expansion hfam hgrp hψ hb]
  rw [pureFace]
  have hre : ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
      gaussCoeff lam ψ j * (starRingEnd ℂ) (lam j b)
      = ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          gaussCoeff lam ψ (-j) * lam j b := by
    refine Finset.sum_nbij' (fun j => -j) (fun j => -j) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hj0 : j ≠ 0 := by
        have := (Finset.mem_sdiff.mp hj).2; simpa using this
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa using neg_ne_zero.mpr hj0
    · intro j hj
      have hj0 : j ≠ 0 := by
        have := (Finset.mem_sdiff.mp hj).2; simpa using this
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa using neg_ne_zero.mpr hj0
    · intro j _; dsimp only; ring
    · intro j _; dsimp only; ring
    · intro j hj
      dsimp only
      rw [conj_lam hfam hgrp j hb]
      rw [neg_neg]
  rw [hre]
  ring

/-- **THE A-SIDE FULL-TOWER COLLAPSE (round-44 main theorem)** — `WallHolds`' moment tower
is the iterated self-convolution ℓ²-profile of the Gauss sequence, at every depth. -/
theorem eta_tower_collapse (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (r : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖(m : ℂ) * eta ψ G b + 1‖ ^ (2 * r)
      = ((Fintype.card F - 1 : ℕ) : ℝ)
          * ∑ c : ZMod m, ‖iterConv (fun j => gaussCoeff lam ψ (-j)) r c‖ ^ 2 := by
  have hpt : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖(m : ℂ) * eta ψ G b + 1‖ ^ (2 * r)
        = ‖pureFace (fun j => gaussCoeff lam ψ (-j)) lam b‖ ^ (2 * r) := by
    intro b hb
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    rw [eta_eq_pureFace hfam hgrp hψ hb0]
  rw [Finset.sum_congr rfl hpt]
  exact fullTower_collapse hfam hgrp (fun j => gaussCoeff lam ψ (-j)) r

end ArkLib.ProximityGap.Frontier.R44EtaTower

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R44EtaTower.eta_eq_pureFace
#print axioms ArkLib.ProximityGap.Frontier.R44EtaTower.eta_tower_collapse
