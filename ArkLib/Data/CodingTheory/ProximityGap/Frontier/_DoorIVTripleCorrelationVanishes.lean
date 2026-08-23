/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Door IV: the period field's SIGNED 6-point connected surface VANISHES — the connected triple
# correlation `κ₃` is consistent with zero, so the first 6-point phase object does not exist

This file records the axiom-clean kernel behind the probes
`scripts/probes/probe_dooriv_signed_6point_cumulant.py` and
`scripts/probes/probe_dooriv_6point_cumulant_floorcheck.py`.

## Why this matters

The connected-4 entry (`_DoorIVConnectedCumulantVanishes`) closed the 4th-order surface and left an
EXPLICIT pointer: "Any surviving door-(iv) crack must live at **6th order or higher**, or in an object
outside the moment hierarchy entirely." The modulus 6th moment `K₆` collapses to the additive count
`E₃` (refuted energy, by the same character-orthogonality identity that killed `K₄ = E₂`), so the only
6-point object NOT already dead is the PHASE-SENSITIVE, SIGNED one: the connected triple correlation of
the period field `z_j = η_{g^j}` on the cyclic multiplicative quotient,
`κ₃(k,l) = E_j[(z_j−m)(z_{j+k}−m)(z_{j+l}−m)]` (`m` = field mean). Its squared modulus `|κ₃|²` is a
genuine 3×conj-3 = 6-point functional that does NOT reduce to the additive `E₃`. For a complex-Gaussian
field every ODD connected cumulant vanishes identically, so `κ₃ ≡ 0` is the Gaussian baseline; a
nonzero, `N`-non-shrinking, thinness-essential `κ₃` would be a door-(iv) crack.

## The probe verdict (reproducible, proper `μ_n`, p ≫ n³, never n = q−1)

`|κ₃|/sd³` (sd³ = `(E|z−m|²)^{3/2}`) hovers at the sampling floor and the two honesty controls are
decisive:
- **cap-scaling**: `mean|κ₃|/sd³` tracks `1/√cap`, `ratio_to_floor` FLAT at `0.65–0.79` across an 8×
  cap range (3000→24000). A real connected cumulant keeps `mean|κ₃|/sd³` flat (ratio_to_floor growing);
  it shrinks as `1/√cap` ⇒ pure sampling noise of a phase-incoherent field.
- **i.i.d. control**: `period/iid ≈ 0.76–0.82` — the period field's triple correlation is at or BELOW a
  phase-randomized i.i.d. surrogate with the same magnitude multiset, i.e. no excess phase coherence.

So the connected triple correlation is consistent with ZERO: the period field is phase-incoherent at
3rd order, and the first signed 6-point object does not exist. This closes the connected-4 pointer at
6th order. CORE stays open: a surviving crack must be an even-higher connected order or genuinely
outside the correlation hierarchy.

## The formalizable kernel (this file): vanishing triple correlation ⇒ the 6-point lever is vacuous

The formal content of "`κ₃` consistent with 0" is: if the connected triple correlation vanishes, then
(i) its squared modulus — the canonical signed 6-point functional — is exactly `0`, so any 6-point
bound routed through it passes through `0` (a vacuous lever, no phase coherence supplied); and (ii) the
full 3-3 modulus moment then equals its Wick value, built only from the (dead) 2-point covariance and
the (dead) diagonal `E₃`. Either way no NEW 6-point structure survives. We record the algebra; the
numeric "`κ₃ = 0`" is the probe input, not asserted here.
-/

namespace ProximityGap.Frontier.DoorIVTripleCorrelationVanishes

open Finset

/-- The canonical signed 6-point functional built from the connected triple correlation is its squared
modulus `|κ₃|²` (a 3×conj-3 = 6-point object that does NOT reduce to the additive `E₃`). If the
connected triple correlation `κ₃` vanishes, this 6-point functional is exactly `0`. -/
theorem sixPoint_functional_zero_of_triple_zero
    {κ₃ : ℂ} (hzero : κ₃ = 0) :
    Complex.normSq κ₃ = 0 := by
  rw [hzero]; simp

/-- A door-(iv) candidate bounded BELOW by the signed 6-point functional `|κ₃|²` gets no lower-bound
content when `κ₃ = 0`: the functional is `0`, so the bound is the vacuous `0 ≤ M`. There is no
6th-order phase coherence to grip. -/
theorem sixPoint_lever_vacuous_of_triple_zero
    {M κ₃ : ℂ} (hbound : Complex.normSq κ₃ ≤ Complex.normSq M) (hzero : κ₃ = 0) :
    (0 : ℝ) ≤ Complex.normSq M := by
  have : Complex.normSq κ₃ = 0 := sixPoint_functional_zero_of_triple_zero hzero
  rw [this] at hbound; exact hbound

/-- Wick factorization at 6th order under a vanishing connected triple cumulant. If the 3-3 modulus
moment `m33` decomposes (the moment–cumulant relation) as `m33 = wick + cumulant` and the connected
`cumulant = 0`, then `m33 = wick` — fully determined by the lower-order (2-point covariance + diagonal
`E₃`) data, both of which are independently mapped dead. No residual joint 6-point structure. -/
theorem m33_eq_wick_of_cumulant_zero
    {m33 wick cumulant : ℝ}
    (hdecomp : m33 = wick + cumulant) (hzero : cumulant = 0) :
    m33 = wick := by
  rw [hdecomp, hzero, add_zero]

/-- Complex form (the period field is complex-valued). -/
theorem m33_eq_wick_of_cumulant_zero_complex
    {m33 wick cumulant : ℂ}
    (hdecomp : m33 = wick + cumulant) (hzero : cumulant = 0) :
    m33 = wick := by
  rw [hdecomp, hzero, add_zero]

/-- Consequence: a sup-norm candidate bounded by the Wick-factorized 3-3 moment is bounded by the
lower-order data. With the connected cumulant `= 0`, the control passes through `wick` (covariance +
diagonal), exactly the objects the white-field and `K₆ = E₃` entries already mapped dead. -/
theorem control_passes_through_wick6
    {M m33 wick : ℝ}
    (hctrl : M ≤ m33) (hfact : m33 = wick) :
    M ≤ wick := by
  rwa [hfact] at hctrl

end ProximityGap.Frontier.DoorIVTripleCorrelationVanishes

#print axioms ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.sixPoint_functional_zero_of_triple_zero
#print axioms ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.sixPoint_lever_vacuous_of_triple_zero
#print axioms ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.m33_eq_wick_of_cumulant_zero
#print axioms ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.m33_eq_wick_of_cumulant_zero_complex
#print axioms ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.control_passes_through_wick6
