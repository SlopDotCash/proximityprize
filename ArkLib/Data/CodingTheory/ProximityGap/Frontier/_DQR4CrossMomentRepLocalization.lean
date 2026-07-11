/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR23TwoScaleCenteredRecursion

/-!
# DQR-4 leading stratum: cross-moments are rep-function point-evaluations at the twist — #466

Continues the DQR renormalization angle (attack matrix 2026-07-11). The signed depth-14
ledger's cross terms `∑_{b≠0} η_b^k · η_{b·a}^{j}` govern the DQR-4 contraction question.
This file computes the ENTIRE `j = 1` stratum exactly:

* `repCount` — `f_k(c) = #{(y_1,…,y_k) ∈ G^k : ∑ y_i = c}` (the k-fold representation count).
* `repCount_smul` — coset invariance: `f_k(c·u) = f_k(c)` for `u ∈ G` (multiplicatively
  closed `G`, `0 ∉ G`).
* `sum_repCount` — total mass `∑_c f_k(c) = n^k` (mean `n^k/q`).
* `crossMoment_eq_rep` — **the localization (new)**: for primitive `ψ`, mult. closed `G` with
  `−1 ∈ G`, and any `a ≠ 0`,

    `∑_{b≠0} η_b^k · η_{b·a} = q·n·f_k(a) − n^{k+1}`,

  i.e. exactly `q·n·(f_k(a) − n^k/q)` — the k↔1 cross-moment IS the centered k-fold
  representation count evaluated at the single twist point `a`.

Consequence for the renormalization flow: at each of the 29 dyadic levels, the leading
(`j = 1`) contraction stratum has a DEFINITE sign criterion — it is favorable (negative)
exactly when the twist point `a_j` is UNDER-represented as a sum of `k` level-`j` subgroup
elements. The `k = 1` case recovers `cross_correlation_exact` (`f_1(a) = 0` since `a ∉ G`).
The open DQR-4 content is now: the joint sign/size of `{f_k^{(j)}(a_j) − n_j^k/q}` across
levels and strata — per-level, per-point equidistribution data, the sharpest localization of
the wall on this angle so far. Nothing here discharges it. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification

namespace ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `k`-fold representation count `f_k(c) = #{(y_1,…,y_k) ∈ G^k : ∑ y_i = c}`. -/
noncomputable def repCount (G : Finset F) (k : ℕ) (c : F) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => G)).filter (fun y => ∑ i, y i = c)).card

/-- Coset invariance of the representation count: `f_k(u·c) = f_k(c)` for `u ∈ G`. -/
theorem repCount_smul {G : Finset F} (hG : MulClosed G) {u : F} (hu : u ∈ G)
    (k : ℕ) (c : F) : repCount G k (u * c) = repCount G k c := by
  have hu0 : u ≠ 0 := fun h => hG.zero_not_mem (h ▸ hu)
  have hinvmem : ∀ x ∈ G, u⁻¹ * x ∈ G := by
    intro x hx
    have hperm := image_mul_self hG hu
    have hx' : x ∈ G.image (fun z => u * z) := hperm.symm ▸ hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx'
    rw [← hzx, inv_mul_cancel_left₀ hu0]
    exact hz
  unfold repCount
  apply Finset.card_nbij' (i := fun y => fun i => u⁻¹ * y i) (j := fun y => fun i => u * y i)
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hy ⊢
    refine ⟨fun i => hinvmem _ (hy.1 i), ?_⟩
    rw [← Finset.mul_sum, hy.2, inv_mul_cancel_left₀ hu0]
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hy ⊢
    refine ⟨fun i => hG.mul_mem u hu (y i) (hy.1 i), ?_⟩
    rw [← Finset.mul_sum, hy.2]
  · intro y _
    funext i
    simp [mul_inv_cancel_left₀ hu0]
  · intro y _
    funext i
    simp [inv_mul_cancel_left₀ hu0]

/-- Total representation mass: `∑_c f_k(c) = n^k`. -/
theorem sum_repCount (G : Finset F) (k : ℕ) :
    ∑ c : F, repCount G k c = G.card ^ k := by
  unfold repCount
  rw [← Finset.card_biUnion]
  · rw [show G.card ^ k = (Fintype.piFinset (fun _ : Fin k => G)).card by
      rw [Fintype.card_piFinset]; simp]
    congr 1
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨c, hy, _⟩ => hy, fun hy => ⟨∑ i, y i, hy, rfl⟩⟩
  · intro c _ c' _ hcc'
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    simp only [Finset.mem_filter] at hy hy'
    exact hcc' (hy.2.symm.trans hy'.2)

/-- **The `(k,1)` cross-moment localization**: for primitive `ψ` and any `a`,

  `∑_b η_b^k · η_{b·a} = q · ∑_{z∈G} f_k(−a·z)`,

specializing (mult. closed `G`, `−1 ∈ G`) to `∑_{b≠0} η_b^k·η_{b·a} = q·n·f_k(a) − n^{k+1}`:
the cross-moment is exactly the centered rep count at the twist point, scaled by `q·n`. -/
theorem crossMoment_eq_rep {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : MulClosed G) (hneg : (-1 : F) ∈ G) {a : F} (ha : a ≠ 0)
    (k : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * eta ψ G (b * a)
      = (Fintype.card F : ℂ) * (G.card : ℂ) * (repCount G k a : ℂ)
        - (G.card : ℂ) ^ (k + 1) := by
  -- Full-sum orthogonality: `∑_b η_b^k η_{ba} = q · #{(y⃗, z) : ∑yᵢ + a·z = 0}`.
  have hpow : ∀ b : F, (eta ψ G b) ^ k
      = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G), ψ (b * ∑ i, y i) := by
    intro b
    rw [eta, Finset.sum_pow']
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum, ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw.addChar_map_sum]
  have hfull : ∑ b : F, (eta ψ G b) ^ k * eta ψ G (b * a)
      = (Fintype.card F : ℂ) * (G.card : ℂ) * (repCount G k a : ℂ) := by
    have hexp : ∀ b : F, (eta ψ G b) ^ k * eta ψ G (b * a)
        = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G), ∑ z ∈ G,
            ψ (b * ((∑ i, y i) + a * z)) := by
      intro b
      rw [hpow b, eta, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
      rw [← AddChar.map_add_eq_mul]
      ring_nf
    calc ∑ b : F, (eta ψ G b) ^ k * eta ψ G (b * a)
        = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G), ∑ z ∈ G, ∑ b : F,
            ψ (b * ((∑ i, y i) + a * z)) := by
          rw [Finset.sum_congr rfl (fun b _ => hexp b), Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
      _ = ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G), ∑ z ∈ G,
            (if (∑ i, y i) + a * z = 0 then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
          rw [AddChar.sum_mulShift _ hψ]
          by_cases h : (∑ i, y i) + a * z = 0 <;> simp [h]
      _ = (Fintype.card F : ℂ) * (G.card : ℂ) * (repCount G k a : ℂ) := by
          -- for each `z ∈ G`: `∑yᵢ = −a·z` has `f_k(−a·z) = f_k(a)` solutions.
          rw [Finset.sum_comm]
          have hcount : ∀ z ∈ G,
              ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G),
                (if (∑ i, y i) + a * z = 0 then (Fintype.card F : ℂ) else 0)
              = (Fintype.card F : ℂ) * (repCount G k a : ℂ) := by
            intro z hz
            have hfilter : ∑ y ∈ Fintype.piFinset (fun _ : Fin k => G),
                (if (∑ i, y i) + a * z = 0 then (Fintype.card F : ℂ) else 0)
                = (repCount G k (-(a * z)) : ℂ) * (Fintype.card F : ℂ) := by
              simp only [add_eq_zero_iff_eq_neg]
              rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
                nsmul_eq_mul]
              rw [repCount]
            have hrep : repCount G k (-(a * z)) = repCount G k a := by
              have hu : (-1 : F) * z ∈ G := hG.mul_mem (-1) hneg z hz
              have harg : -(a * z) = ((-1 : F) * z) * a := by ring
              rw [harg, repCount_smul hG hu k a]
            rw [hfilter, hrep]
            ring
          rw [Finset.sum_congr rfl hcount, Finset.sum_const, nsmul_eq_mul]
          ring
  -- split off `b = 0`, where `η₀ = n`.
  have hzero : (eta ψ G (0 : F)) ^ k * eta ψ G ((0 : F) * a) = (G.card : ℂ) ^ (k + 1) := by
    rw [zero_mul, ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.eta_zero]
    ring
  have hsplit : ∑ b : F, (eta ψ G b) ^ k * eta ψ G (b * a)
      = (eta ψ G 0) ^ k * eta ψ G (0 * a)
        + ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * eta ψ G (b * a) :=
    (Finset.add_sum_erase _ (fun b => (eta ψ G b) ^ k * eta ψ G (b * a))
      (Finset.mem_univ 0)).symm
  rw [hsplit, hzero] at hfull
  linear_combination hfull

end ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization.repCount_smul
#print axioms ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization.sum_repCount
#print axioms ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization.crossMoment_eq_rep
