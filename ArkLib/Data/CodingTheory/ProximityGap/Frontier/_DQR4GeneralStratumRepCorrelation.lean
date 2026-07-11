/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4CrossMomentRepLocalization

/-!
# DQR-4 general stratum: every ledger cross-moment is a dilated rep-rep correlation — #466

Completes the exact data layer for the DQR-4 contraction question, respecting the concurrent
falsify-first warning (`_DQRSecondMomentAnticorrelationNoGo`: the quadratic ledger alone cannot
force fourteenth-moment contraction — higher mixed moments or field structure are mandatory).
This file supplies ALL the higher mixed moments in exact form:

* `mixedSolutionCount` — `N_{k,j}(a) = #{(y⃗,z⃗) ∈ G^k × G^j : ∑yᵢ + a·∑z_l = 0}`.
* `crossMoment_eq_mixedCount` — **the general stratum law (new)**: for primitive `ψ`,

    `∑_{b≠0} η_b^k · η_{b·a}^j = q·N_{k,j}(a) − n^{k+j}`.

* `mixedSolutionCount_eq_repCorrelation` — the fiber formula:
  `N_{k,j}(a) = ∑_c f_j(c) · f_k(−a·c)` — the dilated correlation of two representation
  functions. So the ENTIRE signed depth-14 dyadic ledger is now an exact polynomial (with
  binomial coefficients) in the dilated rep-rep correlations at the 29 twist points: the
  complete, machine-checked data layer that any DQR-4 contraction proof must control. Per the
  no-go, the quadratic (`k = j = 1`) stratum is proven insufficient alone; the open content is
  the joint behavior of these correlations at the production prime. Nothing here discharges
  it. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification
open ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization

namespace ArkLib.ProximityGap.Frontier.DQR4GeneralStratumRepCorrelation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `N_{k,j}(a)`: solutions of `∑ yᵢ + a·∑ z_l = 0` with all coordinates in `G`. -/
noncomputable def mixedSolutionCount (G : Finset F) (k j : ℕ) (a : F) : ℕ :=
  (((Fintype.piFinset (fun _ : Fin k => G)) ×ˢ (Fintype.piFinset (fun _ : Fin j => G))).filter
    (fun p => (∑ i, p.1 i) + a * (∑ l, p.2 l) = 0)).card

/-- **The general stratum law**: `∑_{b≠0} η_b^k·η_{b·a}^j = q·N_{k,j}(a) − n^{k+j}`. -/
theorem crossMoment_eq_mixedCount {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (a : F) (k j : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
      = (Fintype.card F : ℂ) * (mixedSolutionCount G k j a : ℂ)
        - (G.card : ℂ) ^ (k + j) := by
  have hpow : ∀ (b : F) (r : ℕ) (c : F), (eta ψ G c) ^ r
      = ∑ y ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (c * ∑ i, y i) := by
    intro b r c
    rw [eta, Finset.sum_pow']
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum, ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw.addChar_map_sum]
  have hfull : ∑ b : F, (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
      = (Fintype.card F : ℂ) * (mixedSolutionCount G k j a : ℂ) := by
    have hexp : ∀ b : F, (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
        = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G),
            ∑ z ∈ Fintype.piFinset (fun _ : Fin j => G),
              ψ (b * ((∑ i, y i) + a * (∑ l, z l))) := by
      intro b
      rw [hpow b k b, hpow b j (b * a), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
      rw [← AddChar.map_add_eq_mul]
      ring_nf
    calc ∑ b : F, (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
        = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G),
            ∑ z ∈ Fintype.piFinset (fun _ : Fin j => G), ∑ b : F,
              ψ (b * ((∑ i, y i) + a * (∑ l, z l))) := by
          rw [Finset.sum_congr rfl (fun b _ => hexp b), Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
      _ = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G),
            ∑ z ∈ Fintype.piFinset (fun _ : Fin j => G),
              (if (∑ i, y i) + a * (∑ l, z l) = 0 then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl
            (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
          rw [AddChar.sum_mulShift _ hψ]
          by_cases h : (∑ i, y i) + a * (∑ l, z l) = 0 <;> simp [h]
      _ = (Fintype.card F : ℂ) * (mixedSolutionCount G k j a : ℂ) := by
          rw [mixedSolutionCount, Finset.card_filter]
          push_cast
          rw [Finset.mul_sum, Finset.sum_product]
          refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
          by_cases h : (∑ i, y i) + a * (∑ l, z l) = 0 <;> simp [h]
  have hzero : (eta ψ G (0 : F)) ^ k * (eta ψ G ((0 : F) * a)) ^ j
      = (G.card : ℂ) ^ (k + j) := by
    rw [zero_mul, ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.eta_zero, ← pow_add]
  have hsplit : ∑ b : F, (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
      = (eta ψ G 0) ^ k * (eta ψ G (0 * a)) ^ j
        + ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j :=
    (Finset.add_sum_erase _ (fun b => (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j)
      (Finset.mem_univ 0)).symm
  rw [hsplit, hzero] at hfull
  linear_combination hfull

/-- **The fiber formula**: `N_{k,j}(a) = ∑_c f_j(c)·f_k(−a·c)` — the general ledger stratum
is the dilated correlation of two representation functions. -/
theorem mixedSolutionCount_eq_repCorrelation (G : Finset F) (k j : ℕ) (a : F) :
    mixedSolutionCount G k j a = ∑ c : F, repCount G j c * repCount G k (-(a * c)) := by
  rw [mixedSolutionCount, Finset.card_filter, Finset.sum_product]
  -- fiber the y-sum over `c = ∑ z`, then count.
  rw [Finset.sum_comm]
  -- LHS is now `∑ z ∑ y [∑y + a∑z = 0]`; group `z` by its sum `c`.
  have hz : ∀ z ∈ Fintype.piFinset (fun _ : Fin j => G),
      (∑ y ∈ Fintype.piFinset (fun _ : Fin k => G),
        if (∑ i, y i) + a * (∑ l, z l) = 0 then 1 else 0)
      = repCount G k (-(a * (∑ l, z l))) := by
    intro z _
    simp only [add_eq_zero_iff_eq_neg]
    rw [repCount, Finset.card_filter]
  rw [Finset.sum_congr rfl hz]
  -- now `∑_z f_k(−a·∑z) = ∑_c f_j(c)·f_k(−a·c)` by fibering `z` over its sum.
  classical
  rw [← Finset.sum_fiberwise (g := fun z : Fin j → F => ∑ l, z l)
    (s := Fintype.piFinset (fun _ : Fin j => G))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [repCount, Finset.card_filter, Finset.sum_mul]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases h : (∑ l, z l) = c
  · simp [h]
  · simp [h]

end ArkLib.ProximityGap.Frontier.DQR4GeneralStratumRepCorrelation

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4GeneralStratumRepCorrelation.crossMoment_eq_mixedCount
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4GeneralStratumRepCorrelation.mixedSolutionCount_eq_repCorrelation
