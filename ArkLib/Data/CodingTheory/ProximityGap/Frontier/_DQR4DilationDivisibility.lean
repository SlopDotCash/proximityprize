/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4ShiftDivisibility
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification

/-!
# DQR-4 integrality completed: the `n·r` law for zero-sum counts — #466

Eleventh result of the arc; completes the probe-verified integrality
(`probe_dqr4_zero_rep_divisibility.py`).

* `one_mem` / `inv_mem` — a multiplicatively closed finite set of nonzero field elements
  contains `1` and inverses (finite cancellative ⟹ group).
* `dilation_dvd_repCount_zero` — **`n ∣ f_r(0)`** (`r ≥ 1`): the free dilation action gives
  the exact factorization `{y ∈ G^r : ∑y = 0} ≃ G × {y : ∑y = 0, y₀ = 1}` by
  first-coordinate normalization — no orbit machinery.
* `mul_dvd_repCount_zero` — **the `n·r` law**: for odd prime `r` (so `gcd(r, 2³⁰) = 1`),
  `n·r ∣ f_r(0)` — the full integrality constraint on the odd power sums
  `P_r = q·f_r(0) − n^r` and hence on the twist-average closed form `P_k·P_j`.

Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification
open ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization
open ArkLib.ProximityGap.Frontier.DQR4ShiftDivisibility

namespace ArkLib.ProximityGap.Frontier.DQR4DilationDivisibility

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A nonempty multiplicatively closed finite set of nonzero elements contains `1`. -/
theorem one_mem {G : Finset F} (hG : MulClosed G) {u : F} (hu : u ∈ G) : (1 : F) ∈ G := by
  have hu0 : u ≠ 0 := fun h => hG.zero_not_mem (h ▸ hu)
  have hperm := image_mul_self hG hu
  have : u ∈ G.image (fun z => u * z) := hperm.symm ▸ hu
  obtain ⟨x, hx, hux⟩ := Finset.mem_image.mp this
  have hx1 : x = 1 := mul_left_cancel₀ hu0 (hux.trans (mul_one u).symm)
  exact hx1 ▸ hx

/-- Inverses: `u ∈ G ⟹ u⁻¹ ∈ G`. -/
theorem inv_mem {G : Finset F} (hG : MulClosed G) {u : F} (hu : u ∈ G) : u⁻¹ ∈ G := by
  have hu0 : u ≠ 0 := fun h => hG.zero_not_mem (h ▸ hu)
  have hperm := image_mul_self hG hu
  have h1 : (1 : F) ∈ G.image (fun z => u * z) := hperm.symm ▸ one_mem hG hu
  obtain ⟨x, hx, hux⟩ := Finset.mem_image.mp h1
  have hxu : x = u⁻¹ := eq_inv_of_mul_eq_one_right hux
  exact hxu ▸ hx

/-- **Dilation divisibility**: `n ∣ f_r(0)` for `r ≥ 1`. Free dilation factorizes the
solution set as `G × (first-coordinate-normalized solutions)`. -/
theorem dilation_dvd_repCount_zero {G : Finset F} (hG : MulClosed G)
    {r : ℕ} (hr : 0 < r) :
    G.card ∣ repCount G r (0 : F) := by
  classical
  haveI : NeZero r := ⟨hr.ne'⟩
  set i0 : Fin r := ⟨0, hr⟩
  set S := (Fintype.piFinset (fun _ : Fin r => G)).filter (fun y => ∑ i, y i = (0 : F))
    with hS
  set T := S.filter (fun y => y i0 = 1) with hT
  have hcard : S.card = G.card * T.card := by
    rw [← Finset.card_product]
    apply Finset.card_nbij' (i := fun y => (y i0, fun i => (y i0)⁻¹ * y i))
      (j := fun p => fun i => p.1 * p.2 i)
    · intro y hy
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hy
      have hy0G : y i0 ∈ G := hy.1 i0
      have hy00 : y i0 ≠ 0 := fun h => hG.zero_not_mem (h ▸ hy0G)
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hT, hS,
        Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨hy0G, ⟨⟨fun i => ?_, ?_⟩, ?_⟩⟩
      · exact hG.mul_mem _ (inv_mem hG hy0G) _ (hy.1 i)
      · rw [← Finset.mul_sum, hy.2, mul_zero]
      · rw [inv_mul_cancel₀ hy00]
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hT, hS,
        Finset.mem_filter, Fintype.mem_piFinset] at hp
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset]
      refine ⟨fun i => hG.mul_mem _ hp.1 _ (hp.2.1.1 i), ?_⟩
      rw [← Finset.mul_sum, hp.2.1.2, mul_zero]
    · intro y hy
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hy
      have hy00 : y i0 ≠ 0 := fun h => hG.zero_not_mem (h ▸ hy.1 i0)
      funext i
      simp [mul_inv_cancel_left₀ hy00]
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hT, hS,
        Finset.mem_filter, Fintype.mem_piFinset] at hp
      have hp0 : p.1 ≠ 0 := fun h => hG.zero_not_mem (h ▸ hp.1)
      have hnorm : p.2 i0 = 1 := hp.2.2
      apply Prod.ext
      · simp [hnorm, hp0]
      · funext i
        simp [hnorm, hp0, inv_mul_cancel_left₀ hp0]
  have : repCount G r (0 : F) = S.card := rfl
  rw [this, hcard]
  exact Dvd.intro _ rfl

/-- **The `n·r` law**: for odd prime `r` coprime to `n = |G|`, `n·r ∣ f_r(0)` — the complete
probe-verified integrality of the zero-sum counts (at production `n = 2³⁰`, every odd `r`). -/
theorem mul_dvd_repCount_zero {G : Finset F} (hG : MulClosed G)
    {r : ℕ} (hr : r.Prime) (hrF : (r : F) ≠ 0) (hcop : Nat.Coprime G.card r) :
    G.card * r ∣ repCount G r (0 : F) :=
  hcop.mul_dvd_of_dvd_of_dvd
    (dilation_dvd_repCount_zero hG hr.pos)
    (shift_dvd_repCount_zero G hr hrF hG.zero_not_mem)

end ArkLib.ProximityGap.Frontier.DQR4DilationDivisibility

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.DQR4DilationDivisibility.inv_mem
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4DilationDivisibility.dilation_dvd_repCount_zero
#print axioms ArkLib.ProximityGap.Frontier.DQR4DilationDivisibility.mul_dvd_repCount_zero
