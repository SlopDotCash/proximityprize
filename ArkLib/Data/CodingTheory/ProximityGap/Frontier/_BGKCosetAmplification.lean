/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthNineThreshold

/-!
# Coset amplification: the sup is attained `n` times — depth-7 Wick now suffices — #466

`_BGKDepthNineThreshold` showed depth-9 Wick closes the nine-bit gap and depth ≤ 7 plain
moment certificates cannot. This file adds the missing multiplicative ingredient and LOWERS
the sufficiency threshold to depth 7:

* `eta_mul_right` — for a multiplicatively closed `G` (`0 ∉ G`), `η_{b·g} = η_b` for `g ∈ G`:
  the period is constant on cosets `b·G`.
* `card_nsmul_le_offZero_moment` — **the amplification**: for `b ≠ 0`, the coset `b·G` has `n`
  distinct nonzero elements all attaining `‖η_b‖`, so
  `n·‖η_b‖^{2r} ≤ ∑_{c≠0} ‖η_c‖^{2r} = q·E_r − n^{2r}`.
  Plain single-frequency extraction loses this factor `n = 2³⁰`.
* `depthSeven_amplified_closes` — **the upgraded sufficiency**: `E₇ ≤ 2¹⁸·n⁷` at `|G| = 2³⁰`,
  `q ≤ 2¹⁵⁹` gives `WorstCaseIncompleteSumBound ψ G (2⁵¹)` — the nine-bit target. The
  constant `2¹⁸ = 262144` is only `1.94×` the depth-7 Wick constant `13‼ = 135135`: the open
  input is now depth-SEVEN Wick with a factor-2 cushion, two full depths below the previous
  requirement (and the depth-7 *plain* no-go of `_BGKDepthNineThreshold` shows the coset
  amplification is exactly what unlocks it).

The open content is now `E₇(μ_n) ≤ 2¹⁸·n⁷` at `n = 2³⁰`, `p ≈ 2¹⁵⁸`. Nothing here discharges
it. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024
set_option maxRecDepth 16384

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw

namespace ArkLib.ProximityGap.Frontier.BGKCosetAmplification

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A multiplicatively closed finite set of nonzero elements (e.g. `μ_n`). -/
structure MulClosed (G : Finset F) : Prop where
  zero_not_mem : (0 : F) ∉ G
  mul_mem : ∀ g ∈ G, ∀ y ∈ G, g * y ∈ G

/-- Multiplication by `g ∈ G` permutes `G`. -/
theorem image_mul_self {G : Finset F} (hG : MulClosed G) {g : F} (hg : g ∈ G) :
    G.image (fun y => g * y) = G := by
  have hg0 : g ≠ 0 := fun h => hG.zero_not_mem (h ▸ hg)
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
    exact hG.mul_mem g hg y hy
  · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hg0)]

/-- **Coset invariance of the period**: `η_{b·g} = η_b` for `g ∈ G`. -/
theorem eta_mul_right {G : Finset F} (hG : MulClosed G) (ψ : AddChar F ℂ)
    (b : F) {g : F} (hg : g ∈ G) :
    eta ψ G (b * g) = eta ψ G b := by
  have hg0 : g ≠ 0 := fun h => hG.zero_not_mem (h ▸ hg)
  calc eta ψ G (b * g) = ∑ y ∈ G, ψ (b * (g * y)) := by
        rw [eta]
        exact Finset.sum_congr rfl (fun y _ => by ring_nf)
    _ = ∑ c ∈ G.image (fun y => g * y), ψ (b * c) := by
        rw [Finset.sum_image (fun y _ y' _ h => mul_right_injective₀ hg0 h)]
    _ = eta ψ G b := by rw [image_mul_self hG hg, eta]

/-- **The amplification**: for `b ≠ 0`, the worst frequency is attained on the whole coset
`b·G` (`n` distinct nonzero frequencies), so `n·‖η_b‖^{2r} ≤ ∑_{c≠0}‖η_c‖^{2r}`. -/
theorem card_nsmul_le_offZero_moment {G : Finset F} (hG : MulClosed G)
    (ψ : AddChar F ℂ) {b : F} (hb : b ≠ 0) (r : ℕ) :
    (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ (2 * r) := by
  have hsub : G.image (fun g => b * g) ⊆ Finset.univ.erase 0 := by
    intro c hc
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hc
    have hg0 : g ≠ 0 := fun h => hG.zero_not_mem (h ▸ hg)
    exact Finset.mem_erase.mpr ⟨mul_ne_zero hb hg0, Finset.mem_univ _⟩
  have hcoset : ∑ c ∈ G.image (fun g => b * g), ‖eta ψ G c‖ ^ (2 * r)
      = (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r) := by
    rw [Finset.sum_image (fun g _ g' _ h => mul_left_cancel₀ hb h)]
    calc ∑ g ∈ G, ‖eta ψ G (b * g)‖ ^ (2 * r)
        = ∑ g ∈ G, ‖eta ψ G b‖ ^ (2 * r) :=
          Finset.sum_congr rfl (fun g hg => by rw [eta_mul_right hG ψ b hg])
      _ = (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [← hcoset]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => by positivity)

/-- **Depth-7 Wick suffices under amplification.** For multiplicatively closed `G` with
`|G| = 2³⁰`, `q ≤ 2¹⁵⁹`: if `E₇(G) ≤ 2¹⁸·|G|⁷` (only `1.94×` the Wick constant `13‼`), then
`WorstCaseIncompleteSumBound ψ G (2⁵¹)` — the nine-bit target. Two depths below the
unamplified requirement. -/
theorem depthSeven_amplified_closes {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : MulClosed G) (hcard : G.card = 2 ^ 30)
    (hqu : Fintype.card F ≤ 2 ^ 159)
    (hwick : rEnergy G 7 ≤ 2 ^ 18 * G.card ^ 7) :
    WorstCaseIncompleteSumBound ψ G (2 ^ 51) := by
  intro b hb
  have hamp := card_nsmul_le_offZero_moment hG ψ hb 7
  have hlaw := moment_eq_card_energy hψ G 7
  have hsplit : ∑ c : F, ‖eta ψ G c‖ ^ (2 * 7)
      = ‖eta ψ G 0‖ ^ (2 * 7) + ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ (2 * 7) :=
    (Finset.add_sum_erase _ (fun c => ‖eta ψ G c‖ ^ (2 * 7)) (Finset.mem_univ 0)).symm
  have h0 : (0 : ℝ) ≤ ‖eta ψ G 0‖ ^ (2 * 7) := by positivity
  -- off-zero mass ≤ q·E₇ ≤ 2¹⁵⁹·2¹⁸·2²¹⁰ = 2³⁸⁷; divide by n = 2³⁰ → (2⁵¹)⁷.
  have hoff : ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ (2 * 7)
      ≤ (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
    have : ‖eta ψ G 0‖ ^ (2 * 7) + ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ (2 * 7)
        = (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
      rw [← hsplit]; simpa using hlaw
    linarith
  have hqE : (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 387 := by
    have hqR : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 159 := by exact_mod_cast hqu
    have hER : (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7 := by
      have h1 : (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7 := by
        exact_mod_cast hwick
      rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at h1
    calc (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ)
        ≤ (2 : ℝ) ^ 159 * ((2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7) := by
          exact mul_le_mul hqR hER (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 387 := by norm_num [← pow_mul, ← pow_add]
  have hbn : (G.card : ℝ) * ‖eta ψ G b‖ ^ 14 ≤ (2 : ℝ) ^ 387 := by
    have h14 : (2 : ℕ) * 7 = 14 := by norm_num
    calc (G.card : ℝ) * ‖eta ψ G b‖ ^ 14
        = (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * 7) := by norm_num
      _ ≤ ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ (2 * 7) := hamp
      _ ≤ (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := hoff
      _ ≤ (2 : ℝ) ^ 387 := hqE
  have hcardR : (G.card : ℝ) = (2 : ℝ) ^ 30 := by
    rw [hcard]; norm_num
  have hpow14 : ‖eta ψ G b‖ ^ 14 ≤ (2 : ℝ) ^ 357 := by
    rw [hcardR] at hbn
    have h2 : (0 : ℝ) < (2 : ℝ) ^ 30 := by positivity
    have := (le_div_iff₀' h2).mpr hbn
    calc ‖eta ψ G b‖ ^ 14 ≤ (2 : ℝ) ^ 387 / (2 : ℝ) ^ 30 := this
      _ = (2 : ℝ) ^ 357 := by
          rw [eq_comm, eq_div_iff (ne_of_gt h2), ← pow_add]
  -- seventh root: `(‖η‖²)⁷ ≤ (2⁵¹)⁷ ⟹ ‖η‖² ≤ 2⁵¹`.
  have hfin : (‖eta ψ G b‖ ^ 2) ^ 7 ≤ ((2 : ℝ) ^ 51) ^ 7 := by
    rw [← pow_mul]
    calc ‖eta ψ G b‖ ^ (2 * 7) = ‖eta ψ G b‖ ^ 14 := by norm_num
      _ ≤ (2 : ℝ) ^ 357 := hpow14
      _ = ((2 : ℝ) ^ 51) ^ 7 := by rw [← pow_mul]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hfin

end ArkLib.ProximityGap.Frontier.BGKCosetAmplification

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKCosetAmplification.eta_mul_right
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCosetAmplification.card_nsmul_le_offZero_moment
#print axioms ArkLib.ProximityGap.Frontier.BGKCosetAmplification.depthSeven_amplified_closes
