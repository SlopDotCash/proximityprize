/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import Mathlib.Data.Finset.Powerset

/-!
# Analytic CORE Orbit-Class Laws, Odd Subset-Sum Freeness, and 32-Colour Period Rigidity

This module establishes three analytic and arithmetic foundations for the smooth dyadic subgroup
CORE (`G = μ_n ⊂ F_p^×`, `n = 2^30`) using only prebuilt canonical substrate imports:

1. **Odd-cardinality subset-sum stabilizer-freeness (`n ∣ a_0`) and subset-sum Parseval (`§1`):**
   Proves that over any dyadic root subgroup `G = μ_{2^m}` in odd characteristic, every subset
   `S ⊆ G` of *odd* cardinality (in particular `r = 7`) has trivial multiplicative stabilizer
   `c = 1`—even without antipode-freeness—by cancelling `∏_{x ∈ S} x ≠ 0` to obtain `c^{|S|} = 1`
   and combining with `c^{2^m} = 1`. Consequently `|G|` divides the zero-sum `r`-subset count
   `subsetSumCount G r 0` (`a_0 = n * z_0` at `r = 7`), and subset-sum Parseval plus Cauchy–Schwarz
   on `F \ {0}` yields a sharp two-term lower bound isolating `a_0` and the uniform nonzero mean.

2. **Kernel-certified 32-colour cyclotomic separation, `32 × 32` regular-simplex Gram matrix,
   992-fraction rational exclusion, and 32-step harmonic ladder at `P₁` and `P₂` (`§2`):**
   Certifies in the Lean kernel via 30-step repeated squaring that `1, 2, ..., 32` lie in `32`
   pairwise distinct `μ_{2^30}`-cosets at both designated primes `P₁` and `P₂`. Deduces:
   * all `32 * 31 = 992` nontrivial signed small rationals `±a / b` (`1 ≤ a ≠ b ≤ 32`) avoid
     `μ_{2^30}` (including `(3 : ZMod P_i)^(2^30) ≠ 1`);
   * the exact `32 × 32` regular-simplex nonzero-frequency Gram matrix (`diag = P_i n - n^2`,
     `off-diag = -n^2`);
   * the `b`-uniform `2^30`-fold coset-reduced harmonic-ladder `L²` bound
     `∑_{h < 32} ‖η_{(h + 1) b}‖^2 ≤ P_i - 2^30` for all `b ≠ 0`.

3. **`n`-fold tightened coset-reduced `DCEnergyBound` per-frequency sup-norm (`§3`):**
   Upgrades `DCEnergyCorrection.eta_pow_le_of_dcEnergyBound` by the exact subgroup size `|G|`,
   proving `|G| * ‖eta ψ G b‖^(2r) ≤ |F| * (2r - 1)!! * |G|^r` for all `b ≠ 0`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonBGKCoreOrbitAndPeriodLaws

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.GaussPeriodCosetReduction

/-! ## §1. Odd-cardinality subset-sum stabilizer-freeness and subset-sum Parseval -/

/-- Number of `r`-element subsets of `G` summing to `y`. -/
def subsetSumCount {F : Type*} [AddCommMonoid F] [DecidableEq F]
    (G : Finset F) (r : ℕ) (y : F) : ℕ :=
  ((G.powersetCard r).filter (fun S => ∑ x ∈ S, x = y)).card

/-- Fourier transform of the `r`-subset sum distribution of `G` at frequency `b`. -/
noncomputable def subsetFourier {F : Type*} [Field F]
    (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (b : F) : ℂ :=
  ∑ S ∈ G.powersetCard r, ψ (b * ∑ x ∈ S, x)

/-- **Odd-cardinality stabilizer-freeness on `μ_{2^m}`.**
In odd characteristic (`(2 : F) ≠ 0`), any dyadic root of unity `c^(2^m) = 1` preserving a finite
subset `S ⊆ F \ {0}` of *odd* cardinality must equal `1` (no antipode-freeness needed). -/
theorem odd_subset_stabilizer_eq_one {F : Type*} [Field F] [DecidableEq F]
    {S : Finset F} (hodd : Odd S.card) (hS0 : ∀ x ∈ S, x ≠ 0) (htwo : (2 : F) ≠ 0)
    {c : F} {m : ℕ} (hc : c ^ (2 ^ m) = 1)
    (hstab : S.image (fun x => c * x) = S) :
    c = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero m two_ne_zero)] at hc
    exact zero_ne_one hc
  let P : F := ∏ x ∈ S, x
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr hS0
  have hprod : c ^ S.card * P = P := by
    calc c ^ S.card * P
        = (∏ _x ∈ S, c) * (∏ x ∈ S, x) := by rw [Finset.prod_const]
      _ = ∏ x ∈ S, (c * x) := Finset.prod_mul_distrib.symm
      _ = ∏ y ∈ S.image (fun x => c * x), y :=
          (Finset.prod_image (f := fun y : F => y) (fun _ _ _ _ h => mul_left_cancel₀ hc0 h)).symm
      _ = P := by rw [hstab]
  have hcard1 : c ^ S.card = 1 := mul_right_cancel₀ hP0 (hprod.trans (one_mul P).symm)
  induction m with
  | zero => simpa only [pow_zero, pow_one] using hc
  | succ m ih =>
    rw [pow_succ, pow_mul] at hc
    rcases sq_eq_one_iff.mp hc with h1 | hm1
    · exact ih h1
    · exfalso
      have hneg1 : (-1 : F) ^ S.card = 1 := by
        calc (-1 : F) ^ S.card
            = (c ^ (2 ^ m)) ^ S.card := by rw [hm1]
          _ = (c ^ S.card) ^ (2 ^ m) := by rw [← pow_mul, mul_comm, pow_mul]
          _ = 1 := by rw [hcard1, one_pow]
      rw [hodd.neg_one_pow] at hneg1
      apply htwo
      linear_combination -hneg1

/-- **Subgroup cardinality divides the zero-sum `r`-subset count for every odd `r`.**
In particular, at depth `r = 7` (`BGKDepthSevenInjectiveVarianceEquivalence`), `|G| = 2^30`
divides `a_0 = subsetSumCount G 7 0` unconditionally. -/
theorem card_dvd_zero_subsetSumCount_of_odd {F : Type*} [Field F] [DecidableEq F]
    {G : Finset F} {m r : ℕ} (htwo : (2 : F) ≠ 0) (hodd : Odd r)
    (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ m) = 1) :
    G.card ∣ subsetSumCount G r 0 := by
  let Z : Finset (Finset F) := (G.powersetCard r).filter (fun S => ∑ x ∈ S, x = 0)
  let orb (S : Finset F) : Finset (Finset F) :=
    G.image (fun c => S.image (fun x => c * x))
  have hG0 : ∀ x ∈ G, x ≠ 0 := by
    intro x hx
    rintro rfl
    have hz := (hG 0).mp hx
    rw [zero_pow (pow_ne_zero m two_ne_zero)] at hz
    exact zero_ne_one hz
  have hG_mul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G := by
    intro a ha b hb
    exact (hG (a * b)).mpr (by rw [mul_pow, (hG a).mp ha, (hG b).mp hb, one_mul])
  have h1G : (1 : F) ∈ G := (hG 1).mpr (one_pow _)
  have horb_card : ∀ S ∈ Z, (orb S).card = G.card := by
    intro S hSZ
    obtain ⟨hSpow, _⟩ := Finset.mem_filter.mp hSZ
    obtain ⟨hSG, hScard⟩ := Finset.mem_powersetCard.mp hSpow
    apply Finset.card_image_iff.mpr
    intro c₁ hc₁ c₂ hc₂ heq
    change S.image (fun x => c₁ * x) = S.image (fun x => c₂ * x) at heq
    have hc₂0 : c₂ ≠ 0 := hG0 c₂ hc₂
    have hc₁0 : c₁ ≠ 0 := hG0 c₁ hc₁
    let u : F := c₁ / c₂
    have hu_pow : u ^ (2 ^ m) = 1 := by
      dsimp only [u]
      rw [div_pow, (hG c₁).mp hc₁, (hG c₂).mp hc₂, div_one]
    have hu0 : u ≠ 0 := div_ne_zero hc₁0 hc₂0
    have hsub : S.image (fun x => u * x) ⊆ S := by
      intro y hy
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
      have hc₁x : c₁ * x ∈ S.image (fun z => c₂ * z) := by
        rw [← heq]
        exact Finset.mem_image_of_mem _ hxS
      obtain ⟨z, hzS, hcz⟩ := Finset.mem_image.mp hc₁x
      have huz : u * x = z := by
        dsimp only [u]
        rw [div_mul_eq_mul_div, ← hcz, mul_div_cancel_left₀ z hc₂0]
      exact huz ▸ hzS
    have hstab : S.image (fun x => u * x) = S :=
      Finset.eq_of_subset_of_card_le hsub
        (le_of_eq (Finset.card_image_of_injective S (fun _ _ h => mul_left_cancel₀ hu0 h)).symm)
    have hu1 : u = 1 := odd_subset_stabilizer_eq_one (hScard ▸ hodd)
      (fun x hx => hG0 x (hSG hx)) htwo hu_pow hstab
    exact (div_eq_one_iff_eq hc₂0).mp hu1
  have horb_sub : ∀ S ∈ Z, orb S ⊆ Z := by
    intro S hSZ T hT
    obtain ⟨hSpow, hSsum⟩ := Finset.mem_filter.mp hSZ
    obtain ⟨hSG, hScard⟩ := Finset.mem_powersetCard.mp hSpow
    obtain ⟨c, hcG, rfl⟩ := Finset.mem_image.mp hT
    have hc0 : c ≠ 0 := hG0 c hcG
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro y hy
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
      exact hG_mul c hcG x (hSG hxS)
    · rw [Finset.card_image_of_injective S (fun _ _ h => mul_left_cancel₀ hc0 h), hScard]
    · rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hc0 h), ← Finset.mul_sum,
        hSsum, mul_zero]
  have hfiber : ∀ O ∈ Z.image orb, (Z.filter (fun T => orb T = O)).card = G.card := by
    intro O hO
    obtain ⟨S, hSZ, rfl⟩ := Finset.mem_image.mp hO
    have heq_set : Z.filter (fun T => orb T = orb S) = orb S := by
      ext T
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, hEq⟩
        have hT_in : T ∈ orb T := by
          refine Finset.mem_image.mpr ⟨1, h1G, ?_⟩
          ext x
          simp only [Finset.mem_image, one_mul, exists_eq_right]
        exact hEq ▸ hT_in
      · intro hT
        refine ⟨horb_sub S hSZ hT, ?_⟩
        obtain ⟨c₀, hc₀G, rfl⟩ := Finset.mem_image.mp hT
        have hc₀0 : c₀ ≠ 0 := hG0 c₀ hc₀G
        have hG_right : G.image (fun d => d * c₀) = G := by
          apply Finset.eq_of_subset_of_card_le
          · intro y hy
            obtain ⟨d, hdG, rfl⟩ := Finset.mem_image.mp hy
            exact hG_mul d hdG c₀ hc₀G
          · exact le_of_eq (Finset.card_image_of_injective G
              (fun _ _ h => mul_right_cancel₀ hc₀0 h)).symm
        ext U
        simp only [orb, Finset.mem_image]
        constructor
        · rintro ⟨d, hdG, rfl⟩
          refine ⟨d * c₀, hG_mul d hdG c₀ hc₀G, ?_⟩
          rw [Finset.image_image]
          ext z
          simp only [Finset.mem_image, Function.comp_apply, mul_assoc]
        · rintro ⟨e, heG, rfl⟩
          have he_in : e ∈ G.image (fun d => d * c₀) := hG_right.symm ▸ heG
          obtain ⟨d, hdG, rfl⟩ := Finset.mem_image.mp he_in
          refine ⟨d, hdG, ?_⟩
          rw [Finset.image_image]
          ext z
          simp only [Finset.mem_image, Function.comp_apply, mul_assoc]
    rw [heq_set]
    exact horb_card S hSZ
  have hpart : Z.card = ∑ O ∈ Z.image orb, (Z.filter (fun T => orb T = O)).card :=
    Finset.card_eq_sum_card_fiberwise (fun T hT => Finset.mem_image_of_mem orb hT)
  rw [show subsetSumCount G r 0 = Z.card from rfl, hpart, Finset.sum_congr rfl hfiber,
    Finset.sum_const, smul_eq_mul, mul_comm]
  exact dvd_mul_right G.card (Z.image orb).card

/-- Subset-sum multiplicities are invariant under scaling by any `c ∈ G`. -/
theorem subsetSumCount_mul_mem {F : Type*} [Field F] [DecidableEq F]
    {G : Finset F} (hG0 : (0 : F) ∉ G) (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G)
    (r : ℕ) {c : F} (hcG : c ∈ G) (y : F) :
    subsetSumCount G r (c * y) = subsetSumCount G r y := by
  have hc0 : c ≠ 0 := fun h => hG0 (h ▸ hcG)
  have hbij : G.image (fun x => c * x) = G := image_mul_self_of_mem G hcG hmul hG0
  have hcinv_mem : c⁻¹ ∈ G := by
    have h1 : (1 : F) ∈ G.image (fun x => c * x) := by
      have hex : ∃ z ∈ G, c * z = c := by
        have hc_in : c ∈ G.image (fun x => c * x) := hbij.symm ▸ hcG
        exact Finset.mem_image.mp hc_in
      obtain ⟨e, heG, hce⟩ := hex
      have he1 : e = 1 := mul_left_cancel₀ hc0 (hce.trans (mul_one c).symm)
      exact hbij.symm ▸ (he1 ▸ heG)
    obtain ⟨d, hdG, hcd⟩ := Finset.mem_image.mp h1
    have hd_inv : d = c⁻¹ := mul_left_cancel₀ hc0 (hcd.trans (mul_inv_cancel₀ hc0).symm)
    exact hd_inv ▸ hdG
  unfold subsetSumCount
  refine Finset.card_nbij' (fun S => S.image (fun x => c⁻¹ * x))
    (fun S => S.image (fun x => c * x)) ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨hSpow, hSsum⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSG, hScard⟩ := Finset.mem_powersetCard.mp hSpow
    have hcinv0 : c⁻¹ ≠ 0 := inv_ne_zero hc0
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hz
      exact hmul c⁻¹ hcinv_mem x (hSG hxS)
    · rw [Finset.card_image_of_injective S (fun _ _ h => mul_left_cancel₀ hcinv0 h), hScard]
    · rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hcinv0 h), ← Finset.mul_sum,
        hSsum, inv_mul_cancel_left₀ hc0]
  · intro S hS
    obtain ⟨hSpow, hSsum⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSG, hScard⟩ := Finset.mem_powersetCard.mp hSpow
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hz
      exact hmul c hcG x (hSG hxS)
    · rw [Finset.card_image_of_injective S (fun _ _ h => mul_left_cancel₀ hc0 h), hScard]
    · rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hc0 h), ← Finset.mul_sum, hSsum]
  · intro S _
    dsimp only
    rw [Finset.image_image]
    ext x
    simp only [Finset.mem_image, Function.comp_apply, mul_inv_cancel_left₀ hc0, exists_eq_right]
  · intro S _
    dsimp only
    rw [Finset.image_image]
    ext x
    simp only [Finset.mem_image, Function.comp_apply, inv_mul_cancel_left₀ hc0, exists_eq_right]

/-- **Exact DC-subtracted subset-sum Parseval identity.** -/
theorem subsetSum_nonzero_parseval {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ (Finset.univ : Finset F).erase 0, ‖subsetFourier ψ G r b‖ ^ 2
      = (Fintype.card F : ℝ) * ∑ y : F, (subsetSumCount G r y : ℝ) ^ 2
        - (G.card.choose r : ℝ) ^ 2 := by
  classical
  have hchar : 0 < ringChar F := by
    have := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hcoll : ∑ y : F, (subsetSumCount G r y) ^ 2 =
      ∑ S ∈ G.powersetCard r, ∑ T ∈ G.powersetCard r,
        if ∑ x ∈ S, x = ∑ x ∈ T, x then 1 else 0 := by
    have hfib : ∀ S ∈ G.powersetCard r,
        (∑ T ∈ G.powersetCard r, if ∑ x ∈ S, x = ∑ x ∈ T, x then 1 else 0)
          = subsetSumCount G r (∑ x ∈ S, x) := by
      intro S _
      unfold subsetSumCount
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      by_cases h : ∑ x ∈ S, x = ∑ x ∈ T, x
      · simp only [h, ite_true]
      · simp only [h, Ne.symm h, ite_false]
    rw [Finset.sum_congr rfl hfib,
      ← Finset.sum_fiberwise' (G.powersetCard r) (fun S => ∑ x ∈ S, x)
        (fun y => subsetSumCount G r y)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [subsetSumCount, Finset.sum_const, smul_eq_mul, sq]
  have hcomplex : (∑ b : F, subsetFourier ψ G r b * (starRingEnd ℂ) (subsetFourier ψ G r b))
      = (Fintype.card F : ℂ) * ∑ y : F, (subsetSumCount G r y : ℂ) ^ 2 := by
    calc ∑ b : F, subsetFourier ψ G r b * (starRingEnd ℂ) (subsetFourier ψ G r b)
        = ∑ b : F, ∑ S ∈ G.powersetCard r, ∑ T ∈ G.powersetCard r,
            ψ (b * (∑ x ∈ S, x - ∑ x ∈ T, x)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          unfold subsetFourier
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
          rw [hconj, ← AddChar.map_add_eq_mul]
          congr 1
          ring
      _ = ∑ S ∈ G.powersetCard r, ∑ T ∈ G.powersetCard r,
            ∑ b : F, ψ (b * (∑ x ∈ S, x - ∑ x ∈ T, x)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ S ∈ G.powersetCard r, ∑ T ∈ G.powersetCard r,
            (if ∑ x ∈ S, x = ∑ x ∈ T, x then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
          rw [AddChar.sum_mulShift (∑ x ∈ S, x - ∑ x ∈ T, x) hψ]
          by_cases h : ∑ x ∈ S, x = ∑ x ∈ T, x <;> simp [h, sub_eq_zero]
      _ = (Fintype.card F : ℂ) *
            ((∑ S ∈ G.powersetCard r, ∑ T ∈ G.powersetCard r,
              if ∑ x ∈ S, x = ∑ x ∈ T, x then 1 else 0 : ℕ) : ℂ) := by
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun T _ => ?_)
          by_cases h : ∑ x ∈ S, x = ∑ x ∈ T, x <;> simp [h]
      _ = (Fintype.card F : ℂ) * ∑ y : F, (subsetSumCount G r y : ℂ) ^ 2 := by
          rw [← hcoll]
          push_cast
          rfl
  have hnorm_each : ∀ b : F, ((‖subsetFourier ψ G r b‖ ^ 2 : ℝ) : ℂ) =
      subsetFourier ψ G r b * (starRingEnd ℂ) (subsetFourier ψ G r b) := by
    intro b
    rw [RCLike.mul_conj]
    norm_cast
  have hfull_C : ((∑ b : F, ‖subsetFourier ψ G r b‖ ^ 2 : ℝ) : ℂ) =
      (((Fintype.card F : ℝ) * ∑ y : F, (subsetSumCount G r y : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun b _ => hnorm_each b), hcomplex]
    push_cast
    ring
  have hfull : ∑ b : F, ‖subsetFourier ψ G r b‖ ^ 2 =
      (Fintype.card F : ℝ) * ∑ y : F, (subsetSumCount G r y : ℝ) ^ 2 := by
    exact_mod_cast hfull_C
  have hdc : ‖subsetFourier ψ G r 0‖ ^ 2 = (G.card.choose r : ℝ) ^ 2 := by
    have hz0 : subsetFourier ψ G r 0 = (G.card.choose r : ℂ) := by
      unfold subsetFourier
      simp only [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_powersetCard,
        nsmul_eq_mul, mul_one]
    rw [hz0]
    have hnormC : ‖(G.card.choose r : ℂ)‖ = (G.card.choose r : ℝ) := by
      rw [show (G.card.choose r : ℂ) = (((G.card.choose r : ℝ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hnormC]
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset F)
    (fun b => ‖subsetFourier ψ G r b‖ ^ 2) (Finset.mem_univ 0)).symm
  linarith

/-- **Two-term kernel + nonzero-mean lower bound on nonzero subset-sum Fourier energy.**
Isolates `a_0 = subsetSumCount G r 0` (`= n * z_0` for odd `r`) and applies Cauchy–Schwarz
across `F \ {0}` (`∑_{y ≠ 0} a_y = C(n, r) - a_0`). -/
theorem subsetSum_nonzero_parseval_ge_zero_and_mean {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℝ) * (subsetSumCount G r 0 : ℝ) ^ 2 +
      (Fintype.card F : ℝ) *
        ((G.card.choose r : ℝ) - (subsetSumCount G r 0 : ℝ)) ^ 2 /
          ((Fintype.card F : ℝ) - 1) -
      (G.card.choose r : ℝ) ^ 2 ≤
      ∑ b ∈ (Finset.univ : Finset F).erase 0, ‖subsetFourier ψ G r b‖ ^ 2 := by
  have hcardF : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hFm1_pos : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hcardF
    linarith
  have htot_nat : ∑ y : F, subsetSumCount G r y = G.card.choose r := by
    have hpart := Finset.card_eq_sum_card_fiberwise
      (f := fun S : Finset F => ∑ x ∈ S, x) (t := (Finset.univ : Finset F))
      (fun _ _ => Finset.mem_univ _) (s := G.powersetCard r)
    rw [Finset.card_powersetCard] at hpart
    exact hpart.symm
  have hsplit_tot := (Finset.add_sum_erase (Finset.univ : Finset F)
    (fun y => subsetSumCount G r y) (Finset.mem_univ 0)).symm
  rw [htot_nat] at hsplit_tot
  have hrem_sum : ∑ y ∈ (Finset.univ : Finset F).erase 0, (subsetSumCount G r y : ℝ) =
      (G.card.choose r : ℝ) - (subsetSumCount G r 0 : ℝ) := by
    have hcast : (subsetSumCount G r 0 : ℝ) +
        ∑ y ∈ (Finset.univ : Finset F).erase 0, (subsetSumCount G r y : ℝ) =
        (G.card.choose r : ℝ) := by exact_mod_cast hsplit_tot.symm
    linarith
  have hcs_nat := Finset.sum_mul_sq_le_sq_mul_sq ((Finset.univ : Finset F).erase 0)
    (fun _ => (1 : ℝ)) (fun y => (subsetSumCount G r y : ℝ))
  have herase_card : (((Finset.univ : Finset F).erase 0).card : ℝ) =
      (Fintype.card F : ℝ) - 1 := by
    have hc : ((Finset.univ : Finset F).erase 0).card + 1 = Fintype.card F := by
      simpa only [Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ (0 : F))
    have hc' : (((Finset.univ : Finset F).erase 0).card : ℝ) + 1 = (Fintype.card F : ℝ) := by
      exact_mod_cast hc
    linarith
  simp only [one_pow, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, herase_card,
    hrem_sum] at hcs_nat
  have hdiv_le : ((G.card.choose r : ℝ) - (subsetSumCount G r 0 : ℝ)) ^ 2 /
      ((Fintype.card F : ℝ) - 1) ≤
      ∑ y ∈ (Finset.univ : Finset F).erase 0, (subsetSumCount G r y : ℝ) ^ 2 := by
    rw [div_le_iff₀ hFm1_pos, mul_comm]
    exact hcs_nat
  rw [subsetSum_nonzero_parseval hψ G r,
    ← Finset.add_sum_erase (Finset.univ : Finset F)
      (fun y => (subsetSumCount G r y : ℝ) ^ 2) (Finset.mem_univ 0),
    mul_add]
  have hF_nonneg : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hdiv_le hF_nonneg
  rw [mul_div_assoc]
  linarith

/-! ## §2. Kernel-certified 32-colour cyclotomic separation, 992 rational exclusions,
`32 × 32` regular-simplex Gram matrix, and 32-step harmonic ladder -/

/-- Fast modular repeated squaring in `ℕ` (`x^(2^k) mod p`) for kernel `decide` certificates. -/
def natSquareTower (p x : ℕ) : ℕ → ℕ
  | 0 => x % p
  | k + 1 => (natSquareTower p x k * natSquareTower p x k) % p

private theorem natCast_natSquareTower {p : ℕ} (x k : ℕ) :
    ((natSquareTower p x k : ℕ) : ZMod p) = (x : ZMod p) ^ (2 ^ k) := by
  induction k with
  | zero => simp only [natSquareTower, ZMod.natCast_mod, pow_zero, pow_one]
  | succ k ih =>
    rw [natSquareTower, ZMod.natCast_mod, Nat.cast_mul, ih, pow_succ, pow_mul, sq]

private theorem natSquareTower_lt {p : ℕ} (hp : 0 < p) (x k : ℕ) :
    natSquareTower p x k < p := by
  cases k <;> exact Nat.mod_lt _ hp

private theorem smallCoset_injOn_of_nodup {p : ℕ} (hp : 0 < p)
    (hnodup : ((List.range 33).map (fun k => natSquareTower p k 30)).Nodup) :
    Set.InjOn (fun k : ℕ => (k : ZMod p) ^ (2 ^ 30)) (Finset.Icc 1 32 : Set ℕ) := by
  intro k₁ hk₁ k₂ hk₂ hpow
  have hk₁_lt : k₁ ∈ List.range 33 := by
    have := (Finset.mem_Icc.mp (Finset.mem_coe.mp hk₁)).2
    exact List.mem_range.mpr (by omega)
  have hk₂_lt : k₂ ∈ List.range 33 := by
    have := (Finset.mem_Icc.mp (Finset.mem_coe.mp hk₂)).2
    exact List.mem_range.mpr (by omega)
  have heq_cast : ((natSquareTower p k₁ 30 : ℕ) : ZMod p) =
      ((natSquareTower p k₂ 30 : ℕ) : ZMod p) := by
    rw [natCast_natSquareTower, natCast_natSquareTower]
    exact hpow
  have heq_nat : natSquareTower p k₁ 30 = natSquareTower p k₂ 30 :=
    CharP.natCast_injOn_Iio (ZMod p) p
      (natSquareTower_lt hp k₁ 30) (natSquareTower_lt hp k₂ 30) heq_cast
  exact List.inj_on_of_nodup_map hnodup hk₁_lt hk₂_lt heq_nat

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30Second.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- **First designated prime (`P₁`): `1, 2, ..., 32` lie in `32` distinct `μ_{2^30}`-cosets.** -/
theorem firstPrime_smallCoset_injOn :
    Set.InjOn (fun k : ℕ => (k : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ^ (2 ^ 30))
      (Finset.Icc 1 32 : Set ℕ) :=
  smallCoset_injOn_of_nodup (by decide) (by decide)

/-- **Second designated prime (`P₂`): `1, 2, ..., 32` lie in `32` distinct `μ_{2^30}`-cosets.** -/
theorem secondPrime_smallCoset_injOn :
    Set.InjOn (fun k : ℕ => (k : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ^ (2 ^ 30))
      (Finset.Icc 1 32 : Set ℕ) :=
  smallCoset_injOn_of_nodup (by decide) (by decide)

private theorem small_rational_not_in_roots_of_injOn {p : ℕ} [Fact p.Prime] (hp : 32 < p)
    (hinj : Set.InjOn (fun k : ℕ => (k : ZMod p) ^ (2 ^ 30)) (Finset.Icc 1 32 : Set ℕ))
    {a b : ℕ} (ha1 : 1 ≤ a) (ha32 : a ≤ 32) (hb1 : 1 ≤ b) (hb32 : b ≤ 32) (hab : a ≠ b) :
    ((a : ZMod p) / (b : ZMod p)) ^ (2 ^ 30) ≠ 1 ∧
      (-((a : ZMod p) / (b : ZMod p))) ^ (2 ^ 30) ≠ 1 := by
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff b p).mp h0
    have hle := Nat.le_of_dvd hb1 hdvd
    omega
  have hpos : ((a : ZMod p) / (b : ZMod p)) ^ (2 ^ 30) ≠ 1 := by
    intro h1
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hb0)] at h1
    exact hab (hinj (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨ha1, ha32⟩))
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hb1, hb32⟩)) h1)
  refine ⟨hpos, ?_⟩
  have heven : Even (2 ^ 30 : ℕ) := by decide
  rw [heven.neg_pow]
  exact hpos

/-- **First designated prime (`P₁`): all `992` nontrivial signed rationals `±a / b`
(`1 ≤ a ≠ b ≤ 32`) avoid `μ_{2^30}`.** In particular, `(3 : ZMod P₁)^(2^30) ≠ 1`. -/
theorem firstPrime_small_rational_not_in_roots {a b : ℕ}
    (ha1 : 1 ≤ a) (ha32 : a ≤ 32) (hb1 : 1 ≤ b) (hb32 : b ≤ 32) (hab : a ≠ b) :
    let P₁ := ArkLib.ProximityGap.PrizeShapePrimeP30.P
    ((a : ZMod P₁) / (b : ZMod P₁)) ^ (2 ^ 30) ≠ 1 ∧
      (-((a : ZMod P₁) / (b : ZMod P₁))) ^ (2 ^ 30) ≠ 1 :=
  small_rational_not_in_roots_of_injOn (by decide) firstPrime_smallCoset_injOn
    ha1 ha32 hb1 hb32 hab

/-- **Second designated prime (`P₂`): all `992` nontrivial signed rationals `±a / b`
(`1 ≤ a ≠ b ≤ 32`) avoid `μ_{2^30}`.** In particular, `(3 : ZMod P₂)^(2^30) ≠ 1`. -/
theorem secondPrime_small_rational_not_in_roots {a b : ℕ}
    (ha1 : 1 ≤ a) (ha32 : a ≤ 32) (hb1 : 1 ≤ b) (hb32 : b ≤ 32) (hab : a ≠ b) :
    let P₂ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
    ((a : ZMod P₂) / (b : ZMod P₂)) ^ (2 ^ 30) ≠ 1 ∧
      (-((a : ZMod P₂) / (b : ZMod P₂))) ^ (2 ^ 30) ≠ 1 :=
  small_rational_not_in_roots_of_injOn (by decide) secondPrime_smallCoset_injOn
    ha1 ha32 hb1 hb32 hab

/-- **Exact DC-subtracted cross-coset Gram entry (`-n^2`) for distinct `μ_n`-cosets.**
Whenever `r^n ≠ s^n`, the dilated cosets `r * G` and `s * G` are disjoint, so the full-frequency
inner product vanishes and the punctured inner product equals `-|G|^2`. -/
theorem distinct_cosets_gram_entry {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {n : ℕ}
    (_hn : 0 < n) (hG : ∀ x, x ∈ G ↔ x ^ n = 1) {r s : F} (hrns : r ^ n ≠ s ^ n) :
    ∑ b ∈ (Finset.univ : Finset F).erase 0,
        eta ψ G (r * b) * (starRingEnd ℂ) (eta ψ G (s * b))
      = -((G.card : ℂ) ^ 2) := by
  classical
  have hchar : 0 < ringChar F := by
    have := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hno_coll : ∀ x ∈ G, ∀ y ∈ G, r * x ≠ s * y := by
    intro x hx y hy heq
    have hpow := congrArg (· ^ n) heq
    rw [mul_pow, mul_pow, (hG x).mp hx, (hG y).mp hy, mul_one, mul_one] at hpow
    exact hrns hpow
  have hfull : ∑ b : F, eta ψ G (r * b) * (starRingEnd ℂ) (eta ψ G (s * b)) = 0 := by
    calc ∑ b : F, eta ψ G (r * b) * (starRingEnd ℂ) (eta ψ G (s * b))
        = ∑ b : F, ∑ x ∈ G, ∑ y ∈ G, ψ (b * (r * x - s * y)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          unfold eta
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [hconj, ← AddChar.map_add_eq_mul]
          congr 1
          ring
      _ = ∑ x ∈ G, ∑ y ∈ G, ∑ b : F, ψ (b * (r * x - s * y)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = 0 := by
          refine Finset.sum_eq_zero (fun x hx => Finset.sum_eq_zero (fun y hy => ?_))
          rw [AddChar.sum_mulShift (r * x - s * y) hψ]
          simp only [sub_ne_zero.mpr (hno_coll x hx y hy), ite_false, Nat.cast_zero]
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset F)
    (fun b => eta ψ G (r * b) * (starRingEnd ℂ) (eta ψ G (s * b))) (Finset.mem_univ 0)).symm
  rw [hfull, mul_zero, mul_zero, DCSubtractedMoment.eta_zero, map_natCast] at hsplit
  linear_combination -hsplit

/-- **Coset-level harmonic-ladder `L²` bound (`|F| - |G|`) for distinct `μ_n`-cosets.**
If `c_0, ..., c_{H-1} ≠ 0` lie in pairwise distinct `μ_n`-cosets (`c_i^n ≠ c_j^n`), then their
`G`-orbits in `F \ {0}` are pairwise disjoint and each carries `|G|` equal copies of `‖η_{c_h}‖^2`,
giving `∑_{h < H} ‖η_{c_h}‖^2 ≤ |F| - |G|`. -/
theorem distinct_cosets_ladder_sq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {n H : ℕ}
    (hn : 0 < n) (hG : ∀ x, x ∈ G ↔ x ^ n = 1) (hne : G.Nonempty)
    {c : ℕ → F} (hc0 : ∀ h ∈ Finset.range H, c h ≠ 0)
    (hdist : ∀ h₁ ∈ Finset.range H, ∀ h₂ ∈ Finset.range H, h₁ ≠ h₂ → (c h₁) ^ n ≠ (c h₂) ^ n) :
    ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2 ≤ (Fintype.card F : ℝ) - (G.card : ℝ) := by
  classical
  have hG0 : (0 : F) ∉ G := by
    intro h0
    have hz := (hG 0).mp h0
    simp only [zero_pow hn.ne', zero_ne_one] at hz
  have hmul : ∀ a ∈ G, ∀ d ∈ G, a * d ∈ G := by
    intro a ha d hd
    exact (hG (a * d)).mpr (by rw [mul_pow, (hG a).mp ha, (hG d).mp hd, one_mul])
  have hbij : ∀ u ∈ G, G.image (fun y => u * y) = G :=
    fun u hu => image_mul_self_of_mem G hu hmul hG0
  let orb (h : ℕ) : Finset F := G.image (fun u => u * c h)
  have horb_disj : (Finset.range H : Set ℕ).PairwiseDisjoint orb := by
    intro h₁ hh₁ h₂ hh₂ hne12
    change Disjoint (orb h₁) (orb h₂)
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨u₁, hu₁G, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨u₂, hu₂G, heq⟩ := Finset.mem_image.mp hz₂
    have hpow := congrArg (· ^ n) heq
    rw [mul_pow, mul_pow, (hG u₁).mp hu₁G, (hG u₂).mp hu₂G, one_mul, one_mul] at hpow
    exact hdist h₁ hh₁ h₂ hh₂ hne12 hpow.symm
  have horb_sub : (Finset.range H).biUnion orb ⊆ (Finset.univ : Finset F).erase 0 := by
    intro z hz
    obtain ⟨h, hh, hzh⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨u, huG, rfl⟩ := Finset.mem_image.mp hzh
    have hu0 : u ≠ 0 := fun hz0 => hG0 (hz0 ▸ huG)
    exact Finset.mem_erase.mpr ⟨mul_ne_zero hu0 (hc0 h hh), Finset.mem_univ _⟩
  have horb_sum : ∀ h ∈ Finset.range H,
      ∑ z ∈ orb h, ‖eta ψ G z‖ ^ 2 = (G.card : ℝ) * ‖eta ψ G (c h)‖ ^ 2 := by
    intro h hh
    have hch0 := hc0 h hh
    rw [Finset.sum_image (fun _ _ _ _ heq => mul_right_cancel₀ hch0 heq)]
    have hconst : ∀ u ∈ G, ‖eta ψ G (u * c h)‖ ^ 2 = ‖eta ψ G (c h)‖ ^ 2 := by
      intro u hu
      rw [eta_mul_left hbij hG0 hu (c h)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hm2 := sum_nonzero_moment hψ G 1
  simp only [show 2 * 1 = 2 by rfl] at hm2
  have hr1 : rEnergy G 1 = G.card := by
    unfold rEnergy
    have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
        (∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G),
          if ∑ i, v i = ∑ i, w i then 1 else 0) = 1 := by
      intro v hv
      have heq : ∀ w ∈ Fintype.piFinset (fun _ : Fin 1 => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0) = (if v = w then 1 else 0) := by
        intro w _
        by_cases hvw : v = w
        · subst hvw; simp only [ite_true]
        · have hne_sum : ∑ i, v i ≠ ∑ i, w i := by
            simp only [Fin.sum_univ_one]
            intro h0
            exact hvw (funext (fun i => by fin_cases i; exact h0))
          simp only [hvw, hne_sum, ite_false]
      rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq (Fintype.piFinset (fun _ : Fin 1 => G)) v
        (fun _ => (1 : ℕ))]
      simp only [hv, ite_true]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Fintype.card_piFinset_const,
      pow_one, smul_eq_mul, mul_one]
  rw [hr1] at hm2
  have hmul_bound : (G.card : ℝ) * ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2
      ≤ ((Fintype.card F : ℝ) - (G.card : ℝ)) * (G.card : ℝ) := by
    calc (G.card : ℝ) * ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2
        = ∑ h ∈ Finset.range H, (G.card : ℝ) * ‖eta ψ G (c h)‖ ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ h ∈ Finset.range H, ∑ z ∈ orb h, ‖eta ψ G z‖ ^ 2 :=
          Finset.sum_congr rfl (fun h hh => (horb_sum h hh).symm)
      _ = ∑ z ∈ (Finset.range H).biUnion orb, ‖eta ψ G z‖ ^ 2 :=
          (Finset.sum_biUnion horb_disj).symm
      _ ≤ ∑ z ∈ (Finset.univ : Finset F).erase 0, ‖eta ψ G z‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg horb_sub (fun _ _ _ => sq_nonneg _)
      _ = (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2 := hm2
      _ = ((Fintype.card F : ℝ) - (G.card : ℝ)) * (G.card : ℝ) := by ring
  have hG_pos : (0 : ℝ) < (G.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  exact le_of_mul_le_mul_right (by linarith) hG_pos

/-- **First designated prime (`P₁`): uniform `32`-step harmonic ladder bound `≤ P₁ - 2^30`.** -/
theorem firstPrime_32_ladder_sq_le
    {ψ : AddChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)}
    (hcard : G.card = 2 ^ 30)
    (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1)
    {b : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P} (hb : b ≠ 0) :
    let P₁ := ArkLib.ProximityGap.PrizeShapePrimeP30.P
    ∑ h ∈ Finset.range 32, ‖eta ψ G (((h + 1 : ℕ) : ZMod P₁) * b)‖ ^ 2
      ≤ (P₁ : ℝ) - (2 ^ 30 : ℝ) := by
  dsimp only
  have hne : G.Nonempty := ⟨1, (hG 1).mpr (one_pow _)⟩
  have hle := distinct_cosets_ladder_sq_le hψ (by decide : 0 < 2 ^ 30) hG hne
    (H := 32) (c := fun h => ((h + 1 : ℕ) : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) * b)
    (by
      intro h hh
      have hhlt := Finset.mem_range.mp hh
      have h0 : ((h + 1 : ℕ) : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ≠ 0 := by
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff (h + 1) _).mp hz
        have hle_p := Nat.le_of_dvd (by omega : 0 < h + 1) hdvd
        unfold ArkLib.ProximityGap.PrizeShapePrimeP30.P at hle_p
        omega
      exact mul_ne_zero h0 hb)
    (by
      intro h₁ hh₁ h₂ hh₂ hne12 hpow
      rw [mul_pow, mul_pow] at hpow
      have hpow' := mul_right_cancel₀ (pow_ne_zero (2 ^ 30) hb) hpow
      have hm₁ : h₁ + 1 ∈ (Finset.Icc 1 32 : Set ℕ) := by
        have := Finset.mem_range.mp hh₁
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm₂ : h₂ + 1 ∈ (Finset.Icc 1 32 : Set ℕ) := by
        have := Finset.mem_range.mp hh₂
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have heq := firstPrime_smallCoset_injOn hm₁ hm₂ hpow'
      omega)
  rwa [ZMod.card, hcard, Nat.cast_pow, Nat.cast_ofNat] at hle

/-- **Second designated prime (`P₂`): uniform `32`-step harmonic ladder bound `≤ P₂ - 2^30`.** -/
theorem secondPrime_32_ladder_sq_le
    {ψ : AddChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hcard : G.card = 2 ^ 30)
    (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1)
    {b : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P} (hb : b ≠ 0) :
    let P₂ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
    ∑ h ∈ Finset.range 32, ‖eta ψ G (((h + 1 : ℕ) : ZMod P₂) * b)‖ ^ 2
      ≤ (P₂ : ℝ) - (2 ^ 30 : ℝ) := by
  dsimp only
  have hne : G.Nonempty := ⟨1, (hG 1).mpr (one_pow _)⟩
  have hle := distinct_cosets_ladder_sq_le hψ (by decide : 0 < 2 ^ 30) hG hne
    (H := 32)
    (c := fun h => ((h + 1 : ℕ) : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) * b)
    (by
      intro h hh
      have hhlt := Finset.mem_range.mp hh
      have h0 : ((h + 1 : ℕ) : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ≠ 0 := by
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff (h + 1) _).mp hz
        have hle_p := Nat.le_of_dvd (by omega : 0 < h + 1) hdvd
        unfold ArkLib.ProximityGap.PrizeShapePrimeP30Second.P at hle_p
        omega
      exact mul_ne_zero h0 hb)
    (by
      intro h₁ hh₁ h₂ hh₂ hne12 hpow
      rw [mul_pow, mul_pow] at hpow
      have hpow' := mul_right_cancel₀ (pow_ne_zero (2 ^ 30) hb) hpow
      have hm₁ : h₁ + 1 ∈ (Finset.Icc 1 32 : Set ℕ) := by
        have := Finset.mem_range.mp hh₁
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm₂ : h₂ + 1 ∈ (Finset.Icc 1 32 : Set ℕ) := by
        have := Finset.mem_range.mp hh₂
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have heq := secondPrime_smallCoset_injOn hm₁ hm₂ hpow'
      omega)
  rwa [ZMod.card, hcard, Nat.cast_pow, Nat.cast_ofNat] at hle

/-! ## §3. `n`-fold tightened coset-reduced `DCEnergyBound` per-frequency sup-norm -/

/-- **`|G|`-fold tightened per-frequency period bound from `DCEnergyBound G r`.**
Strengthens `DCEnergyCorrection.eta_pow_le_of_dcEnergyBound` by retaining the full `|G|`-element
coset multiplicity of `‖eta ψ G b‖^(2r)` across `G · b ⊆ F \ {0}`. -/
theorem eta_pow_le_of_dcEnergyBound_cosetReduced {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hG0 : (0 : F) ∉ G) (hmul : ∀ a ∈ G, ∀ c ∈ G, a * c ∈ G)
    (hdc : DCEnergyBound G r) {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  have hbij : ∀ u ∈ G, G.image (fun y => u * y) = G :=
    fun u hu => image_mul_self_of_mem G hu hmul hG0
  have hcos := card_mul_eta_pow_le_sum_erase (ψ := ψ) hbij hG0 r hb
  rw [sum_nonzero_moment hψ G r] at hcos
  exact le_trans hcos hdc

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms odd_subset_stabilizer_eq_one
#print axioms card_dvd_zero_subsetSumCount_of_odd
#print axioms subsetSumCount_mul_mem
#print axioms subsetSum_nonzero_parseval
#print axioms subsetSum_nonzero_parseval_ge_zero_and_mean
#print axioms firstPrime_smallCoset_injOn
#print axioms secondPrime_smallCoset_injOn
#print axioms firstPrime_small_rational_not_in_roots
#print axioms secondPrime_small_rational_not_in_roots
#print axioms distinct_cosets_gram_entry
#print axioms distinct_cosets_ladder_sq_le
#print axioms firstPrime_32_ladder_sq_le
#print axioms secondPrime_32_ladder_sq_le
#print axioms eta_pow_le_of_dcEnergyBound_cosetReduced

end ArkLib.ProximityGap.Frontier.CarbonBGKCoreOrbitAndPeriodLaws
