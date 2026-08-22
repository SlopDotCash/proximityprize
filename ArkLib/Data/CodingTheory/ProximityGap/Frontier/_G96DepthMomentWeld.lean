/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G95CardinalityDeepCapNoGo

/-!
# G96: the depth–moment weld — sector machinery meets the production prize object

Until now the corrected-padding sector machinery (G83M/G86/G87/G88, assembled by G89/G90 and
semantically pinned by G95) lived on an *abstract* mass/envelope interface.  This file welds it
to the production analytic object:

1. `rEnergy_eq_addREnergy`: the moment carrier `rEnergy G r` — the indicator double sum inside
   `DCEnergyBound`, which feeds `eta_pow_le_of_dcEnergyBound` and the prize sup-norm chain
   `M ≤ √(2n·ln q)` — is exactly the `r`-fold additive energy `Finset.addREnergy r G`.
2. `rEnergy_eq_sum_depthFiber`: composed with G95's exact partition, the `2r`-th-moment object
   decomposes by G83M maximal-cancellation depth: `rEnergy G r = Σ_{s=0}^{r} depthFiber G r s`.
3. `dcEnergyBound_iff_nat`: `DCEnergyBound G r` is equivalent to the ℕ-clean inequality
   `q·rEnergy G r ≤ q·(2r-1)!!·#G^r + #G^(2r)` — the real-subtraction form cleared.
4. `dcEnergyBound_of_depth_allowances` (**headline consumer**): if per-depth caps and per-depth
   DC allowances satisfy `Σ cap ≤ (2r-1)!!·#G^r`, `Σ D ≤ #G^(2r)`, and each depth obeys
   `q·depthFiber G r s ≤ q·cap s + D s`, then `DCEnergyBound G r` holds.

Point 4 states the open wall in its exact per-depth *centered* form: the admissible mass at
depth `s` is `cap s` plus the `1/q`-scale DC share `D s / q` — precisely the weighting G95
proved mandatory, and the shape the R366/G75 `relationAnomaly` calibration predicted.  A future
proof of the per-depth centered bounds at the production point would close `DCEnergyBound` at
prize scale through this consumer with no further plumbing.

**Honest scope.**  No claim that the allowances exist — that IS the open analytic wall
(square-root-scale cancellation / BGK face).  This file is connective tissue: it is the exact
"wired into `DCEnergyBound` and the production connective tissue" weld listed as missing in the
G87 KB note.  CORE remains OPEN / ON-BGK.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G96DepthMomentWeld

open Finset Fintype
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The prize-chain moment carrier `rEnergy` is exactly the `r`-fold additive energy. -/
theorem rEnergy_eq_addREnergy (G : Finset F) (r : ℕ) :
    rEnergy G r = Finset.addREnergy r G := by
  classical
  rw [Finset.addREnergy_def, Finset.card_filter, Finset.sum_product]
  unfold rEnergy
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
  congr 1

/-- **The depth–moment weld.**  The `2r`-th-moment object decomposes exactly by G83M
maximal-cancellation depth. -/
theorem rEnergy_eq_sum_depthFiber (G : Finset F) (r : ℕ) :
    rEnergy G r = ∑ s ∈ Finset.range (r + 1), depthFiber G r s := by
  rw [rEnergy_eq_addREnergy, addREnergy_eq_sum_depthFiber]

/-- `DCEnergyBound` cleared of real subtraction: the ℕ-clean two-sided form. -/
theorem dcEnergyBound_iff_nat (G : Finset F) (r : ℕ) :
    DCEnergyBound G r ↔
      Fintype.card F * rEnergy G r
        ≤ Fintype.card F * (Nat.doubleFactorial (2 * r - 1) * G.card ^ r)
            + G.card ^ (2 * r) := by
  unfold DCEnergyBound
  rw [sub_le_iff_le_add]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- **Per-depth DC-allowance consumer** — the open wall in its exact centered per-depth shape.
If the total caps fit the Wick budget, the total DC allowances fit the DC mass `#G^(2r)`, and
each depth's fiber obeys its cap-plus-allowance bound, then the production prize hypothesis
`DCEnergyBound G r` follows. -/
theorem dcEnergyBound_of_depth_allowances
    (G : Finset F) (r : ℕ) (cap D : ℕ → ℕ)
    (hfib : ∀ s ∈ Finset.range (r + 1),
      Fintype.card F * depthFiber G r s ≤ Fintype.card F * cap s + D s)
    (hcap : ∑ s ∈ Finset.range (r + 1), cap s
        ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r)
    (hD : ∑ s ∈ Finset.range (r + 1), D s ≤ G.card ^ (2 * r)) :
    DCEnergyBound G r := by
  rw [dcEnergyBound_iff_nat, rEnergy_eq_sum_depthFiber, Finset.mul_sum]
  calc
    ∑ s ∈ Finset.range (r + 1), Fintype.card F * depthFiber G r s
        ≤ ∑ s ∈ Finset.range (r + 1), (Fintype.card F * cap s + D s) :=
      Finset.sum_le_sum hfib
    _ = Fintype.card F * ∑ s ∈ Finset.range (r + 1), cap s
          + ∑ s ∈ Finset.range (r + 1), D s := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Fintype.card F * (Nat.doubleFactorial (2 * r - 1) * G.card ^ r)
          + G.card ^ (2 * r) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hcap) hD

/-- The depth fiber of the FULL pair cube (no equal-sum condition): the population count at
maximal-cancellation depth `s`. -/
def allPairsDepthFiber (G : Finset F) (r s : ℕ) : ℕ :=
  #(((piFinset fun _ : Fin r => G) ×ˢ (piFinset fun _ : Fin r => G)).filter
    fun x => cancelDepth x = s)

/-- The population depth fibers sum exactly to `#G^(2r)`: the canonical DC allowances spend the
DC mass with zero slack. -/
theorem sum_allPairsDepthFiber (G : Finset F) (r : ℕ) :
    ∑ s ∈ Finset.range (r + 1), allPairsDepthFiber G r s = G.card ^ (2 * r) := by
  classical
  have hpart :
      #((piFinset fun _ : Fin r => G) ×ˢ (piFinset fun _ : Fin r => G))
        = ∑ s ∈ Finset.range (r + 1), allPairsDepthFiber G r s :=
    Finset.card_eq_sum_card_fiberwise
      (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (cancelDepth_le x)))
  rw [← hpart, Finset.card_product, card_piFinset_const, ← pow_add]
  congr 1
  omega

/-- **Canonical centered consumer** — zero free parameters.  Choosing the population fibers as
the DC allowances turns the per-depth hypothesis into the exact centered inequality
`q·(equal-sum pairs at depth s) ≤ q·cap s + (all pairs at depth s)`, i.e. the depth-`s`
collision count exceeds its uniform expectation by at most `cap s`.  If the caps total the Wick
budget, `DCEnergyBound G r` follows.  This is the `relationAnomaly`-style centered object,
stated at the production interface. -/
theorem dcEnergyBound_of_centered_depth_bounds
    (G : Finset F) (r : ℕ) (cap : ℕ → ℕ)
    (hfib : ∀ s ∈ Finset.range (r + 1),
      Fintype.card F * depthFiber G r s
        ≤ Fintype.card F * cap s + allPairsDepthFiber G r s)
    (hcap : ∑ s ∈ Finset.range (r + 1), cap s
        ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_depth_allowances G r cap (allPairsDepthFiber G r) hfib hcap
    (le_of_eq (sum_allPairsDepthFiber G r))

/-- Sanity corollary re-deriving the G95 semantics through the weld: with every DC allowance
zero, the consumer demands `rEnergy ≤ Wick` outright — which the pigeonhole floor refutes at
prize scale (G95).  The allowances are therefore load-bearing, not decorative. -/
theorem rEnergy_le_wick_of_zero_allowances
    (G : Finset F) (r : ℕ) (cap : ℕ → ℕ)
    (hfib : ∀ s ∈ Finset.range (r + 1),
      Fintype.card F * depthFiber G r s ≤ Fintype.card F * cap s)
    (hcap : ∑ s ∈ Finset.range (r + 1), cap s
        ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r)
    (hq : 0 < Fintype.card F) :
    rEnergy G r ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r := by
  have hsum : Fintype.card F * rEnergy G r
      ≤ Fintype.card F * (Nat.doubleFactorial (2 * r - 1) * G.card ^ r) := by
    rw [rEnergy_eq_sum_depthFiber, Finset.mul_sum]
    calc
      ∑ s ∈ Finset.range (r + 1), Fintype.card F * depthFiber G r s
          ≤ ∑ s ∈ Finset.range (r + 1), Fintype.card F * cap s :=
        Finset.sum_le_sum hfib
      _ = Fintype.card F * ∑ s ∈ Finset.range (r + 1), cap s := by
        rw [Finset.mul_sum]
      _ ≤ Fintype.card F * (Nat.doubleFactorial (2 * r - 1) * G.card ^ r) :=
        Nat.mul_le_mul_left _ hcap
  exact Nat.le_of_mul_le_mul_left hsum hq

end ArkLib.ProximityGap.Frontier.G96DepthMomentWeld

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.rEnergy_eq_addREnergy
#print axioms ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.rEnergy_eq_sum_depthFiber
#print axioms ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.dcEnergyBound_iff_nat
#print axioms ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.dcEnergyBound_of_depth_allowances
#print axioms ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.sum_allPairsDepthFiber
#print axioms
  ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.dcEnergyBound_of_centered_depth_bounds
#print axioms
  ArkLib.ProximityGap.Frontier.G96DepthMomentWeld.rEnergy_le_wick_of_zero_allowances
