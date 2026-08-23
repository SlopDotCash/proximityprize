/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# K1 ⟹ `GaussianEnergyBound`: the pairing route to the prize per-frequency carrier (#389)

`GaussPeriodMomentBound.GaussianEnergyBound G r := E_r(G) ≤ (2r−1)‼·|G|^r` is the prize program's
"cleanest cited carrier of the open core" (the moment-method input that yields the Paley/Ramanujan
per-frequency bound `B ≤ √(2n ln q)`). The guide notes it is PROVEN in char 0 (Lam–Leung) but **not
yet Lean-formalized**. The K1 counting core (`zeroSumCount_le_pairings`, `NegationClosedWalkBound`)
*is* that formalization: the zero-sum count of `2r`-tuples is `≤ (#pairings)·|G|^r` under the
antipodal-pairing residual, and `#pairings = (2r−1)‼`.

This file wires the two together. **`gaussianEnergyBound_of_pairing`** derives `GaussianEnergyBound G
r` from exactly three localized inputs:

* `henergy : rEnergy G r = zeroSumCount G (2r)` — the negation-closure bijection `(v,w) ↦ v ⧺ (−w)`
  (pure combinatorics; the energy *is* the zero-sum count for `−1 ∈ G`);
* `hcount : #{pairings of Fin (2r)} ≤ (2r−1)‼` — the perfect-matching count (pure combinatorics;
  fixed-point-free involutions of `Fin (2r)` number `(2r−1)‼`);
* `H` — the antipodal-pairing residual (every zero-sum `2r`-tuple of `G` is antipodally paired):
  the genuine char-0 / above-threshold Lam–Leung input.

`henergy` and `hcount` carry **no open content** (decidable combinatorics); the lone genuine input
is `H`. So this reduces the prize carrier to the K1 bound plus two finite combinatorial facts —
exactly localizing what the char-0 Lam–Leung proof supplies. Axiom-clean
(`propext, Classical.choice, Quot.sound`).

## References
* `GaussPeriodMomentBound.lean` (`GaussianEnergyBound`, the moment-method bridge);
  `NegationClosedWalkBound.lean` (`zeroSumCount_le_pairings`, K1); `scripts/conjectures/PROOFS.md`.
-/

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.GaussianEnergyFromPairing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **K1 discharges the prize energy carrier.** Given the negation-closure energy↔zero-sum
identity (`henergy`), the perfect-matching count bound (`hcount`), and the antipodal-pairing
residual (`H`), the real-Gaussian energy bound `E_r(G) ≤ (2r−1)‼·|G|^r` holds. -/
theorem gaussianEnergyBound_of_pairing (G : Finset F) (r : ℕ)
    (henergy : rEnergy G r = zeroSumCount G (2 * r))
    (hcount : (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card
        ≤ Nat.doubleFactorial (2 * r - 1))
    (H : ∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G), (∑ i, c i = 0) →
        ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i) :
    GaussianEnergyBound G r := by
  unfold GaussianEnergyBound
  -- E_r(G) = zeroSumCount ≤ (#pairings)·|G|^r ≤ (2r−1)‼·|G|^r, all in ℕ then cast to ℝ
  have hk : zeroSumCount G (2 * r)
      ≤ (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card
          * G.card ^ r := zeroSumCount_le_pairings G H
  have hnat : rEnergy G r ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r := by
    calc rEnergy G r = zeroSumCount G (2 * r) := henergy
      _ ≤ (Finset.univ.filter
            (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card * G.card ^ r := hk
      _ ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r := by
          exact Nat.mul_le_mul_right _ hcount
  calc (rEnergy G r : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) * G.card ^ r : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by push_cast; ring

/-! ## Source audit -/

#print axioms gaussianEnergyBound_of_pairing

end ArkLib.ProximityGap.GaussianEnergyFromPairing
