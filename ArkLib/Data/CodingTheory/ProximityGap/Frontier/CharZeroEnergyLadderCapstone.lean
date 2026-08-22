/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergySixExact
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvGER_CharZeroEnergyRecursion

/-!
# AVENUE A capstone: the char-0 additive-energy ladder `E₁…E₆` is EXACTLY the tabulated closed forms

The files `CharZeroEnergyThree/Four/Five/SixExact.lean` solved each depth-`r` additive-energy zero-sum
count `B (2r) m = E_r(μ_{2m})` from the add-one-class recursion (relative to the two elementary named
inputs). The closed forms are exactly the polynomials tabulated independently in
`_AvGER_CharZeroEnergyRecursion` as `Ecz r n` (`E1…E6`). This file states that agreement as a single
citable capstone: given a `BalancedCount12 B` witness, for every depth `r ∈ {1,…,6}` the recursion-
solved count `B (2r) m` equals the tabulated closed form `Ecz r (2m)`.

## Why this is the citable Lane-2 deliverable

`Ecz` is the canonical in-tree ladder indexer that the cross-step rungs (`CrossStepRungOne…Seven`) and
the ρ-monotone chain consume as the char-0 energy values. This capstone certifies, in ONE statement,
that those tabulated values are not merely `def`'d/probe-anchored but are the EXACT solutions of the
combinatorial recursion — kernel-checked — for the whole `E₁…E₆` range. It is the assembled, certain,
citable form of the four per-rung exactness theorems.

## What this proves (axiom-clean; pure assembly of the proven per-rung closed forms)

* `B2_eq_Ecz` … `B12_eq_Ecz` — `B (2r) m = Ecz r (2m)` for `r = 1,…,6` individually.
* `ladder_exact` — the combined statement: for all `r ∈ {1,…,6}`, `B (2r) m = Ecz r (2m)`.

## Honest scope

This is an ASSEMBLY of already-proven exactness theorems against the canonical indexer; it adds NO new
analytic content and makes NO CORE/cancellation/completion/moment-saving/anti-concentration/capacity
claim. The two elementary named inputs (Lam–Leung balance + add-one-class recursion) are still carried
via the `BalancedCount12` witness, NOT discharged. The deep BGK/Paley wall (depth `r ≈ log m`) is
untouched; prize CORE stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyLadder

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree (B2_closed B4_closed B6_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFour (B8_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFive (B10_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergySix (BalancedCount12 B12_closed)
open ProximityGap.Frontier.CharZeroEnergyRecursion (Ecz E1 E2 E3 E4 E5 E6)

variable {B : ℕ → ℕ → ℤ}

/-- `B 2 m = Ecz 1 (2m)` (`= E₁(2m) = 2m`). -/
theorem B2_eq_Ecz (h : BalancedCount12 B) (m : ℕ) :
    B 2 m = Ecz 1 (2 * (m : ℤ)) := by
  rw [B2_closed h.toBalancedCount10.toBalancedCount8.toBalancedCount m]
  simp only [Ecz, E1]; try ring

/-- `B 4 m = Ecz 2 (2m)` (`= E₂(2m) = 12m² − 6m`). -/
theorem B4_eq_Ecz (h : BalancedCount12 B) (m : ℕ) :
    B 4 m = Ecz 2 (2 * (m : ℤ)) := by
  rw [B4_closed h.toBalancedCount10.toBalancedCount8.toBalancedCount m]
  simp only [Ecz, E2]; try ring

/-- `B 6 m = Ecz 3 (2m)` (`= E₃(2m) = 15n³−45n²+40n`). -/
theorem B6_eq_Ecz (h : BalancedCount12 B) (m : ℕ) :
    B 6 m = Ecz 3 (2 * (m : ℤ)) := by
  rw [B6_closed h.toBalancedCount10.toBalancedCount8.toBalancedCount m]
  simp only [Ecz, E3]; try ring

/-- `B 8 m = Ecz 4 (2m)` (`= E₄(2m)`). -/
theorem B8_eq_Ecz (h : BalancedCount12 B) (m : ℕ) :
    B 8 m = Ecz 4 (2 * (m : ℤ)) := by
  rw [B8_closed h.toBalancedCount10.toBalancedCount8 m]
  simp only [Ecz, E4]; try ring

/-- `B 10 m = Ecz 5 (2m)` (`= E₅(2m)`). -/
theorem B10_eq_Ecz (h : BalancedCount12 B) (m : ℕ) :
    B 10 m = Ecz 5 (2 * (m : ℤ)) := by
  rw [B10_closed h.toBalancedCount10 m]
  simp only [Ecz, E5]; try ring

/-- `B 12 m = Ecz 6 (2m)` (`= E₆(2m)`). -/
theorem B12_eq_Ecz (h : BalancedCount12 B) (m : ℕ) :
    B 12 m = Ecz 6 (2 * (m : ℤ)) := by
  rw [B12_closed h]
  simp only [Ecz, E6]; try ring

/-- **The char-0 energy ladder is exactly the tabulated closed forms, `r = 1…6`.** For a
`BalancedCount12 B` witness, every depth-`r` recursion-solved zero-sum count `B (2r) m` equals the
canonical in-tree ladder value `Ecz r (2m)`, for all `r ∈ {1,…,6}`. -/
theorem ladder_exact (h : BalancedCount12 B) (m : ℕ) :
    ∀ r, 1 ≤ r → r ≤ 6 → B (2 * r) m = Ecz r (2 * (m : ℤ)) := by
  intro r hr1 hr6
  interval_cases r
  · exact B2_eq_Ecz h m
  · exact B4_eq_Ecz h m
  · exact B6_eq_Ecz h m
  · exact B8_eq_Ecz h m
  · exact B10_eq_Ecz h m
  · exact B12_eq_Ecz h m

end ArkLib.ProximityGap.Frontier.CharZeroEnergyLadder

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyLadder.B12_eq_Ecz
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyLadder.ladder_exact
