/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22SexticConvolutionCollapse

/-!
# LANE B2 (#466 round 23): the calibrated r = 3 named input and its consumer chain —
  plus the probe finding that NO spike correction is needed at the Jacobi level

## Probe verdict (`probe_r23_tripleconv_energy.py`, profile follow-up; collapse identity
   validated to 1e-13 against the Lean `tripleConv`)

* the triple-convolution energy satisfies `∑_d ‖(J∗J∗J)(d)‖² / (6·m³q³) ∈ [1.5, 3.2]` across
  all probed cells (n = 8/16/32, β = 2.5–4.6), FLUCTUATING and O(1)-bounded — the Gaussian
  constant 6 is right up to a small absolute factor;
* **no spike structure**: the top-5 indices carry only 5–18% of the energy (shrinking in `m`),
  and the profile is flat at `‖tc(d)‖ ≈ 3·m·q^{3/2}` — unlike level 0 (rounds 15–16), the
  Jacobi level needs NO diagonal deletion; the excess over Gaussian is distributed arithmetic
  correlation (the Gauss-angle correlations — Katz territory);
* `‖J_j‖ ∈ {1, √q}` exactly as classical theory predicts (one degenerate index).

## What this brick lands

* `TripleConvEnergyBound C` — the calibrated NAMED OPEN INPUT: `∑_d ‖(J∗J∗J)(d)‖² ≤ C·m³·q³`
  (`C = 40` covers every probed cell with ≥ 2× margin; the Gaussian prediction is `C = 6`);
* `sextic_moment_of_tripleConvEnergyBound` — the consumer: the named input yields the r = 3
  rung for the face, `∑_{s≠0} ‖T‖⁶ ≤ C·(q−1)·m³·q³`, by the round-22 exact collapse;
* `sup_pureFace_of_tripleConvEnergyBound` — the sixth-moment pointwise consequence:
  `‖T(s)‖ ≤ (C·(q−1)·m³·q³)^{1/6}` for every `s ≠ 0`.

This completes the normal-form program for the delimited open core: the r = 3 rung is ONE
named, probe-calibrated, manifestly-nonnegative inequality about an explicit sequence, with
its full consumer chain to the tower machine-checked.  CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 23, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- **The calibrated named open input (the campaign's delimited r = 3 core).**
Triple-convolution energy of the coefficient sequence at Wick scale: probes give
ratio-to-`6m³q³` in `[1.5, 3.2]` with no spike structure; `C = 40` is comfortable. -/
def TripleConvEnergyBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3

/-- **Consumer: the named input IS the r = 3 rung for the face** (via the round-22 exact
collapse — no analytic content in this step). -/
theorem sextic_moment_of_tripleConvEnergyBound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) {C : ℝ}
    (h : TripleConvEnergyBound J (Fintype.card F) C) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  rw [sextic_convolution_collapse hfam hgrp J]
  have hq : (0:ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left h hq

/-- **Pointwise consequence: the sixth-moment sup bound.**  For every `s ≠ 0`,
`‖T(s)‖⁶ ≤ C·(q−1)·m³·q³`; taking sixth roots is left to consumers (kept in power form to
avoid `rpow` plumbing). -/
theorem sup_pureFace_of_tripleConvEnergyBound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) {C : ℝ}
    (h : TripleConvEnergyBound J (Fintype.card F) C) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  have hmem : s ∈ Finset.univ.erase (0 : F) :=
    Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩
  have hsingle : ‖pureFace J lam s‖ ^ 6
      ≤ ∑ s' ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s'‖ ^ 6 :=
    Finset.single_le_sum (f := fun s' => ‖pureFace J lam s'‖ ^ 6)
      (fun s' _ => by positivity) hmem
  exact le_trans hsingle (sextic_moment_of_tripleConvEnergyBound hfam hgrp J h)

end ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput.sextic_moment_of_tripleConvEnergyBound
#print axioms
  ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput.sup_pureFace_of_tripleConvEnergyBound
