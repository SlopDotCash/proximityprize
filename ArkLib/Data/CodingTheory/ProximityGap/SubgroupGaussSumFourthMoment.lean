/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The subgroup Gauss-sum FOURTH moment = `q · (additive energy)` (#389)

This extends `SubgroupGaussSumSecondMoment` (`∑_b ‖η_b‖² = q·|G|`, Parseval) to the **fourth
moment**, supplying the exact bridge from the **additive energy** of a subset `G ⊆ F` — the
object that controls the cubic/`ℓ`-fold supply, hence δ\* — to the **incomplete character sum**
`η_b = ∑_{y∈G} ψ(b·y)`:

> **`subgroup_gaussSum_fourthMoment`** — `∑_b ‖η_b‖⁴ = q · E(G)`, where
> `E(G) = #{(a,a',c,c') ∈ G⁴ : a+a' = c+c'}` is the additive energy.

Pure additive-character orthogonality (`AddChar.sum_mulShift`); no Weil input. The payoff:

> **`addEnergy_le`** — if `‖η_b‖² ≤ M` for all `b ≠ 0`, then
> `q·E(G) ≤ |G|⁴ + M·(q|G| − |G|²)`.

Splitting off the spike `b=0` (`‖η_0‖ = |G|`) and using the second moment. Consequence for the
δ\* programme: in the deployed regime `q ≥ |G|²` this gives `E(G) = O(|G|²)` — the sharp,
**Weil-strength** energy/supply bound that closes the interior up to capacity — **iff** the
worst-case incomplete sum obeys `|η_b| ≤ C√|G|` for `b ≠ 0`. That worst-case bound is the open
Bourgain residual (CLAUDE.md face #3); this file is the precise reduction of the energy/supply
side to it. The *average* `∑_{b≠0}‖η_b‖² = q|G|−|G|²` (i.e. `√|G|` typical) is the in-tree second
moment; the per-frequency worst case stays open. All proofs axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive energy `E(G) = #{(a,a',c,c') ∈ G⁴ : a+a' = c+c'}`, as a nested indicator sum. -/
noncomputable def addEnergy (G : Finset F) : ℕ :=
  ∑ a ∈ G, ∑ a' ∈ G, ∑ c ∈ G, ∑ c' ∈ G, (if a + a' = c + c' then 1 else 0)

/-- **The subgroup Gauss-sum fourth moment, exactly: `∑_b ‖η_b‖⁴ = q · E(G)`.** -/
theorem subgroup_gaussSum_fourthMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖eta ψ G b‖ ^ 4 = (Fintype.card F : ℝ) * addEnergy G := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hetaconj : ∀ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G b)
      = ∑ a ∈ G, ∑ c ∈ G, ψ (b * (a - c)) := by
    intro b
    have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
      rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (b * y))
    have hL : eta ψ G b = ∑ y ∈ G, ψ (b * y) := rfl
    rw [hconjeta, hL, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have h : b * a + -(b * c) = b * (a - c) := by ring
    rw [← AddChar.map_add_eq_mul, h]
  have hnorm4 : ∀ b : F,
      (eta ψ G b * (starRingEnd ℂ) (eta ψ G b)) ^ 2 = ((‖eta ψ G b‖ ^ 4 : ℝ) : ℂ) := by
    intro b
    have hsq : eta ψ G b * (starRingEnd ℂ) (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [hsq]; push_cast; ring
  have hcomplex : (∑ b : F, (eta ψ G b * (starRingEnd ℂ) (eta ψ G b)) ^ 2)
      = (Fintype.card F : ℂ) * addEnergy G := by
    calc ∑ b : F, (eta ψ G b * (starRingEnd ℂ) (eta ψ G b)) ^ 2
        = ∑ b : F, ∑ a ∈ G, ∑ a' ∈ G, ∑ c ∈ G, ∑ c' ∈ G,
            ψ (b * ((a - c) + (a' - c'))) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hetaconj b, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun a' _ => ?_)
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          refine Finset.sum_congr rfl (fun c' _ => ?_)
          have h : b * (a - c) + b * (a' - c') = b * ((a - c) + (a' - c')) := by ring
          rw [← AddChar.map_add_eq_mul, h]
      _ = ∑ a ∈ G, ∑ a' ∈ G, ∑ c ∈ G, ∑ c' ∈ G, ∑ b : F,
            ψ (b * ((a - c) + (a' - c'))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a' _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.sum_comm]
      _ = (Fintype.card F : ℂ) * addEnergy G := by
          simp only [addEnergy]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a' _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c' _ => ?_)
          rw [AddChar.sum_mulShift ((a - c) + (a' - c')) hψ]
          have hiff : ((a - c) + (a' - c') = 0) ↔ (a + a' = c + c') := by
            constructor <;> intro h <;> linear_combination h
          by_cases h : a + a' = c + c' <;> simp [hiff, h]
  have hcast : ((∑ b : F, ‖eta ψ G b‖ ^ 4 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * addEnergy G := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun b _ => (hnorm4 b).symm)
  have hreal : ((∑ b : F, ‖eta ψ G b‖ ^ 4 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * addEnergy G : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-- **The energy↔character-sum bridge.** If the worst-case (off-zero) subgroup Gauss sum
satisfies `‖η_b‖² ≤ M` for all `b ≠ 0`, then
`q·E(G) ≤ |G|⁴ + M·(q|G| − |G|²)`.  Splitting `∑_b‖η_b‖⁴ = q·E` at the spike `b=0`
(`‖η_0‖ = |G|`) and bounding `‖η_b‖⁴ ≤ M‖η_b‖²` off it, using the second moment
`∑_{b≠0}‖η_b‖² = q|G|−|G|²`.  Hence `E(G) = O(|G|²)` once `q ≥ |G|²` **and** `M = O(|G|)`
(worst-case `|η_b| ≤ C√|G|`) — the sharp Weil-strength supply bound for the deployed regime. -/
theorem addEnergy_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {M : ℝ}
    (hM : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 ≤ M) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + M * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
  rw [← subgroup_gaussSum_fourthMoment hψ G]
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp [eta, AddChar.map_zero_eq_one]
  have hn0sq : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by rw [h0, Complex.norm_natCast]
  have hn04 : ‖eta ψ G 0‖ ^ 4 = (G.card : ℝ) ^ 4 := by rw [h0, Complex.norm_natCast]
  have hb : ∀ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4 ≤ M * ‖eta ψ G b‖ ^ 2 := by
    intro b hbm
    have hbne : b ≠ 0 := (Finset.mem_erase.mp hbm).1
    have hsq := hM b hbne
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := sq_nonneg _
    nlinarith [hsq, hnn]
  have hsum2 : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    have h2 := subgroup_gaussSum_secondMoment hψ G
    have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 2
        = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    rw [hsp, hn0sq] at h2
    linarith [h2]
  calc ∑ b : F, ‖eta ψ G b‖ ^ 4
      = ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4 :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    _ ≤ ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, M * ‖eta ψ G b‖ ^ 2 := by
        have hsle := Finset.sum_le_sum hb; linarith
    _ = ‖eta ψ G 0‖ ^ 4 + M * ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (G.card : ℝ) ^ 4 + M * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
        rw [hn04, hsum2]

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.subgroup_gaussSum_fourthMoment
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_le
