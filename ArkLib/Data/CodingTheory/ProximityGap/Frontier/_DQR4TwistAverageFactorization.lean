/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4GeneralStratumRepCorrelation

/-!
# DQR-4 twist-average factorization: the average stratum is a product of power sums — #466

Ninth identity of the DQR arc. The ledger strata `T_{k,j}(a) = ∑_{b≠0} η_b^k·η_{b·a}^j`
depend on the twist `a`; the production instance uses 29 specific twists. This file computes
the average over ALL twists exactly:

* `oddPowerSum_eq_rep_zero` — `P_r := ∑_{b≠0} η_b^r = q·f_r(0) − n^r`: the (possibly odd)
  power sums of the period spectrum are the centered zero-value representation counts —
  `f_r(0)` counts the r-tuples of `G` summing to ZERO (for `μ_n`, the vanishing sums of
  roots of unity, the Lam–Leung-structured quantity).

* `twistAverage_factorizes` — **the factorization (new)**:
  `∑_{a≠0} T_{k,j}(a) = P_k · P_j`. Proof: for fixed `b ≠ 0`, `a ↦ b·a` permutes the nonzero
  frequencies, so the double sum splits.

Consequence: the twist-AVERAGED signed ledger is an explicit polynomial in the zero-sum
counts `f_r(0)` (`r ≤ 14`) — quantities with exact cyclotomic structure. The ENTIRE open
content of DQR-4 is therefore the deviation of the 29 production twist points from the twist
average: a discrepancy statement about specific points, with the mean now in closed form.
Nothing here discharges it. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization

namespace ArkLib.ProximityGap.Frontier.DQR4TwistAverageFactorization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Power sums are centered zero-representation counts**:
`∑_{b≠0} η_b^r = q·f_r(0) − n^r`. Holds for every `r` (odd included). -/
theorem oddPowerSum_eq_rep_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ r
      = (Fintype.card F : ℂ) * (repCount G r (0 : F) : ℂ) - (G.card : ℂ) ^ r := by
  have hpow : ∀ b : F, (eta ψ G b) ^ r
      = ∑ y ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * ∑ i, y i) := by
    intro b
    rw [eta, Finset.sum_pow']
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum, ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw.addChar_map_sum]
  have hfull : ∑ b : F, (eta ψ G b) ^ r
      = (Fintype.card F : ℂ) * (repCount G r (0 : F) : ℂ) := by
    calc ∑ b : F, (eta ψ G b) ^ r
        = ∑ y ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ b : F, ψ (b * ∑ i, y i) := by
          rw [Finset.sum_congr rfl (fun b _ => hpow b)]
          exact Finset.sum_comm
      _ = ∑ y ∈ Fintype.piFinset (fun _ : Fin r => G),
            (if (∑ i, y i) = 0 then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [AddChar.sum_mulShift _ hψ]
          by_cases h : (∑ i, y i) = 0 <;> simp [h]
      _ = (Fintype.card F : ℂ) * (repCount G r (0 : F) : ℂ) := by
          rw [repCount, Finset.card_filter]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          by_cases h : (∑ i, y i) = 0 <;> simp [h]
  have hzero : (eta ψ G (0 : F)) ^ r = (G.card : ℂ) ^ r := by
    rw [ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.eta_zero]
  have hsplit : ∑ b : F, (eta ψ G b) ^ r
      = (eta ψ G 0) ^ r + ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ r :=
    (Finset.add_sum_erase _ (fun b => (eta ψ G b) ^ r) (Finset.mem_univ 0)).symm
  rw [hsplit, hzero] at hfull
  linear_combination hfull

/-- **The twist-average factorization**: summing any ledger stratum over ALL nonzero twists
factorizes into power sums, `∑_{a≠0} ∑_{b≠0} η_b^k·η_{b·a}^j = P_k·P_j`. -/
theorem twistAverage_factorizes (ψ : AddChar F ℂ) (G : Finset F) (k j : ℕ) :
    ∑ a ∈ Finset.univ.erase (0 : F), ∑ b ∈ Finset.univ.erase (0 : F),
        (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
      = (∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k)
        * (∑ c ∈ Finset.univ.erase (0 : F), (eta ψ G c) ^ j) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
  rw [← Finset.mul_sum]
  congr 1
  -- `a ↦ b·a` permutes the nonzero frequencies.
  apply Finset.sum_nbij' (i := fun a => b * a) (j := fun c => b⁻¹ * c)
  · intro a ha
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast ha)
    simp [Finset.mem_coe, Finset.mem_erase, mul_ne_zero hb0 ha0]
  · intro c hc
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hc)
    simp [Finset.mem_coe, Finset.mem_erase, mul_ne_zero (inv_ne_zero hb0) hc0]
  · intro a _
    rw [inv_mul_cancel_left₀ hb0]
  · intro c _
    rw [mul_inv_cancel_left₀ hb0]
  · intro a _
    rfl

end ArkLib.ProximityGap.Frontier.DQR4TwistAverageFactorization

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4TwistAverageFactorization.oddPowerSum_eq_rep_zero
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4TwistAverageFactorization.twistAverage_factorizes
