/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false

/-!
# Sharp lower bound on the worst subgroup Gaussian period (#389)

The 4th-moment (Cauchy–Schwarz) lower bound on the WORST period, dual to the moment-method upper
bound. From `∑_b ‖η_b‖⁴ = q·E(G)` and `∑_b ‖η_b‖² = q·|G|` (peeling the trivial term `η_0 = |G|`):

> `exists_period_sq_ge` :  `∃ b ≠ 0,  q·E(G) − |G|⁴  ≤  ‖η_b‖² · (q·|G| − |G|²)`.

Since `E(G) ≥ |G|²` (the diagonal energy), the worst nontrivial period satisfies `‖η_b‖² ≳ |G|`
once `q ≫ |G|²` — so the conjectured square-root cancellation `√(n log f)` is OPTIMAL (the worst
period is genuinely `Ω(√n)`). With the completion bound `√q` this brackets the worst period in
`[√n, √q]`; the open Dyadic conjecture pins it to `√(n log f)`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- `η_0 = ∑_{y∈G} ψ(0) = |G|`, so `‖η_0‖² = |G|²` and `‖η_0‖⁴ = |G|⁴`. -/
private theorem eta_zero_normsq (ψ : AddChar F ℂ) (G : Finset F) :
    ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 ∧ ‖eta ψ G (0 : F)‖ ^ 4 = (G.card : ℝ) ^ 4 := by
  have h0 : eta ψ G (0 : F) = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  rw [h0, Complex.norm_natCast]
  exact ⟨rfl, rfl⟩

/-- **Sharp 4th-moment lower bound on the worst period.** There is a nontrivial frequency `b ≠ 0`
with `‖η_b‖² · (q·|G| − |G|²) ≥ q·E(G) − |G|⁴`. (Cross-multiplied form of
`max_{b≠0} ‖η_b‖² ≥ (q·E(G) − |G|⁴)/(q·|G| − |G|²) ≳ |G|`, the optimality of square-root cancellation.) -/
theorem exists_period_sq_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∃ b : F, b ≠ 0 ∧
      (Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4
        ≤ ‖eta ψ G b‖ ^ 2 * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set S : Finset F := Finset.univ.erase (0 : F) with hS
  have hmemS : ∀ b : F, b ∈ S ↔ b ≠ 0 := by
    intro b; rw [hS, Finset.mem_erase]; simp
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : F)
    exact ⟨x, (hmemS x).mpr hx⟩
  have h0 := eta_zero_normsq ψ G
  -- second and fourth moments restricted to the nonzero frequencies
  have hsum2 : ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 = q * G.card - (G.card : ℝ) ^ 2 := by
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b => ‖eta ψ G b‖ ^ 2) (Finset.mem_univ (0 : F))).symm
    rw [subgroup_gaussSum_secondMoment hψ G] at hsplit
    rw [← hS, h0.1] at hsplit
    linarith
  have hsum4 : ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 = q * addEnergy G - (G.card : ℝ) ^ 4 := by
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b => ‖eta ψ G b‖ ^ 4) (Finset.mem_univ (0 : F))).symm
    rw [subgroup_gaussSum_fourthMoment hψ G] at hsplit
    rw [← hS, h0.2] at hsplit
    linarith
  obtain ⟨b₀, hb₀S, hb₀max⟩ := S.exists_max_image (fun b => ‖eta ψ G b‖ ^ 2) hSne
  refine ⟨b₀, (hmemS b₀).mp hb₀S, ?_⟩
  have hkey : ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 ≤ ‖eta ψ G b₀‖ ^ 2 * ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b hb => ?_)
    have hpow : ‖eta ψ G b‖ ^ 4 = ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 := by ring
    rw [hpow]
    exact mul_le_mul_of_nonneg_right (hb₀max b hb) (by positivity)
  rw [hsum4, hsum2] at hkey
  exact hkey

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.exists_period_sq_ge
