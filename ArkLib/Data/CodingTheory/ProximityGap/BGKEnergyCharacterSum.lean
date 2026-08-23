/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The honest (BGK / di Benedetto) energy → character-sum chain (#407)

This file formalizes **PIECE A** of the di Benedetto–Garaev–García–González-Sánchez–
Shparlinski–Trujillo / Bourgain–Glibichuk–Konyagin program: the *reduction* from a
**sum-product additive-energy bound** to a **per-frequency character-sum bound** for a
multiplicative subgroup `G = μ_n ≤ F_p^*`.

## What is honest here

This is the **state of the art**, NOT a prize closure. The character-sum bound proven here is

  `B = max_{b≠0} ‖η_b‖ ≤ n^{(θ+D)/(2r)}`,

which, under the literature energy gain, gives `B ≤ n^{1-c'}` with a *small* `c' > 0`
(di Benedetto SOTA: `c' = 31/2880 ≈ 1.08·10⁻²`; BGK: `c' = o(1)`). It does **NOT** reach the
conjectured Gaussian/Ramanujan bound `√(2 n ln q)`. It is the cleanest *proven* bound known.

## The single deep NAMED input (not fabricated)

`SumProductEnergyBound G r θ : Prop := (E_r(G) : ℝ) ≤ |G|^θ`. The honest content is that, for a
multiplicative subgroup `G = μ_n`, the `r`-fold additive energy beats the trivial Sidon/Cauchy–
Schwarz ceiling `E_r(G) ≤ n^{2r-1}` by a power saving:

  `E_r(μ_n) ≤ n^{2r-1-κ_r}`,  `κ_r > 0`   (the sum-product gain; θ = 2r-1-κ_r).

This is exactly the deep theorem of the BGK / di Benedetto line, established via Rudnev's
point–plane incidence bound and iterated dyadic sum-product amplification (di Benedetto et al.,
arXiv:2003.06165, §5; Bourgain–Glibichuk–Konyagin, J. LMS 73 (2006) 380–398; Kowalski,
arXiv:2401.04756 for the clean BGK proof). **Mathlib lacks Rudnev's incidence bound**, so the
energy gain is named as a `Prop` and consumed; it is NOT proven here and NOT fabricated.

## The chain proven here (axiom-clean, all real)

The moment substrate (`GaussPeriodMomentBound`, `subgroup_gaussSum_moment`) is in-tree and PROVEN:
`∑_b ‖η_b‖^{2r} = q·E_r(G)`. We add the elementary `rpow` optimization:

* `eta_pow_le_of_sumProduct` : `‖η_b‖^{2r} ≤ q·n^θ` (single term ≤ full moment, then energy bound).
* `eta_sq_le_of_sumProduct`  : `‖η_b‖² ≤ (q·n^θ)^{1/r}`            (`r`-th root).
* `bgk_character_sum_bound`   : in the regime `q ≤ n^D`, `‖η_b‖² ≤ n^{(θ+D)/r}`, hence the
  headline `‖η_b‖ ≤ n^{(θ+D)/(2r)}`.
* `bgk_subUnit_of_gain`       : the honest non-trivial conclusion `‖η_b‖ ≤ n^{1-c'}` packaged as a
  hypothesis `(θ+D)/(2r) ≤ 1 - c'` — i.e. the energy gain `κ_r` must beat the field-size exponent
  `D` (`θ+D < 2r` ⟺ `κ_r > D - 1`); when it does, the per-frequency sum is genuinely sub-`n`.

Only `propext, Classical.choice, Quot.sound`. Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

set_option autoImplicit false

namespace ArkLib.ProximityGap.BGKEnergyCharacterSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The deep named inputs (the literature theorems, stated as `Prop`s) -/

/-- **The sum-product additive-energy bound** (di Benedetto / BGK, arXiv:2003.06165 §5; the deep
input, *not* in Mathlib): the `r`-fold additive energy of the multiplicative subgroup `G = μ_n`
is bounded by `|G|^θ`. The honest content is a power saving `θ = 2r-1-κ_r` (with `κ_r > 0`) over
the trivial Sidon ceiling `E_r ≤ n^{2r-1}`, established via Rudnev's point–plane incidence bound.
Stated as a `Prop` and consumed below; never asserted. -/
def SumProductEnergyBound (G : Finset F) (r : ℕ) (θ : ℝ) : Prop :=
  (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ θ

/-- **The polynomial field-size regime** `q ≤ n^D` (`n = |G|`): the BGK/di Benedetto bound is
non-trivial exactly when the subgroup is a *power* of the field size, `n = |G| > p^ε`, i.e.
`q = p ≤ n^{1/ε} = n^D` with `D = 1/ε`. Stated as a `Prop`. -/
def FieldSizePolyBound (G : Finset F) (D : ℝ) : Prop :=
  (Fintype.card F : ℝ) ≤ (G.card : ℝ) ^ D

/-! ## The reduction chain (all proven from the in-tree moment identity) -/

/-- **Step 1 — moment → per-frequency power bound.** From `SumProductEnergyBound G r θ`, every
Gauss period satisfies `‖η_b‖^{2r} ≤ q·n^θ`. Proof: a single term is `≤` the full `2r`-th
moment `∑_b ‖η_b‖^{2r} = q·E_r(G)` (`subgroup_gaussSum_moment`), then apply the energy bound. -/
theorem eta_pow_le_of_sumProduct {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    {θ : ℝ} (h : SumProductEnergyBound G r θ) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ θ := by
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_moment hψ G r] at hterm
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := hterm
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ θ :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **Step 2 — the `r`-th root.** `‖η_b‖² ≤ (q·n^θ)^{1/r}`. -/
theorem eta_sq_le_of_sumProduct {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    {θ : ℝ} (hr : 1 ≤ r) (h : SumProductEnergyBound G r θ) (b : F) :
    ‖eta ψ G b‖ ^ 2 ≤ ((Fintype.card F : ℝ) * (G.card : ℝ) ^ θ) ^ ((r : ℝ)⁻¹) := by
  set X : ℝ := (Fintype.card F : ℝ) * (G.card : ℝ) ^ θ with hX
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_of_sumProduct hψ h b
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- **Step 3 — collapse the field size into the regime `q ≤ n^D`.** With both deep inputs,
`‖η_b‖² ≤ n^{(θ+D)/r}`. This is the per-frequency square bound in pure `n`-power form. -/
theorem eta_sq_le_npow {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    {θ D : ℝ} (hr : 1 ≤ r) (hn : 1 ≤ (G.card : ℝ))
    (hE : SumProductEnergyBound G r θ) (hq : FieldSizePolyBound G D) (b : F) :
    ‖eta ψ G b‖ ^ 2 ≤ (G.card : ℝ) ^ ((θ + D) / r) := by
  have hn0 : (0 : ℝ) < (G.card : ℝ) := lt_of_lt_of_le zero_lt_one hn
  -- `q·n^θ ≤ n^D · n^θ = n^{θ+D}`
  have hstep : (Fintype.card F : ℝ) * (G.card : ℝ) ^ θ ≤ (G.card : ℝ) ^ (θ + D) := by
    calc (Fintype.card F : ℝ) * (G.card : ℝ) ^ θ
        ≤ (G.card : ℝ) ^ D * (G.card : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = (G.card : ℝ) ^ (θ + D) := by rw [← Real.rpow_add hn0]; ring_nf
  -- raise to the `1/r` power
  have hroot := eta_sq_le_of_sumProduct hψ hr hE b
  refine hroot.trans ?_
  calc ((Fintype.card F : ℝ) * (G.card : ℝ) ^ θ) ^ ((r : ℝ)⁻¹)
      ≤ ((G.card : ℝ) ^ (θ + D)) ^ ((r : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hstep (by positivity)
    _ = (G.card : ℝ) ^ ((θ + D) * (r : ℝ)⁻¹) := by
        rw [← Real.rpow_mul hn0.le]
    _ = (G.card : ℝ) ^ ((θ + D) / r) := by rw [div_eq_mul_inv]

/-- **The headline character-sum bound.** `B = ‖η_b‖ ≤ n^{(θ+D)/(2r)}`. This is the per-frequency
incomplete subgroup Gauss sum in the BGK/di Benedetto form. -/
theorem bgk_character_sum_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    {θ D : ℝ} (hr : 1 ≤ r) (hn : 1 ≤ (G.card : ℝ))
    (hE : SumProductEnergyBound G r θ) (hq : FieldSizePolyBound G D) (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) ^ ((θ + D) / (2 * r)) := by
  have hsq := eta_sq_le_npow hψ hr hn hE hq b
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  -- ‖η_b‖ = (‖η_b‖²)^{1/2} ≤ (n^{(θ+D)/r})^{1/2} = n^{(θ+D)/(2r)}
  calc ‖eta ψ G b‖
      = (‖eta ψ G b‖ ^ 2) ^ ((2 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hnn (by norm_num)).symm
    _ ≤ ((G.card : ℝ) ^ ((θ + D) / r)) ^ ((2 : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hsq (by positivity)
    _ = (G.card : ℝ) ^ ((θ + D) / (2 * r)) := by
        rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ (G.card:ℝ))]
        congr 1
        field_simp

/-- **The honest BGK conclusion: `B ≤ n^{1-c'}`.** Packaged with the genuine non-triviality
hypothesis `(θ+D)/(2r) ≤ 1 - c'` (`c' > 0`), which is exactly the requirement that the
sum-product energy gain beats the field-size exponent: `θ + D < 2r` ⟺ `κ_r > D - 1`
(`θ = 2r-1-κ_r`). When the gain is large enough, the per-frequency incomplete subgroup Gauss
sum is genuinely sub-`n` — the SOTA bound (di Benedetto: `c' = 31/2880`; BGK: `c' = o(1)`),
short of the conjectured `√(2 n ln q)`. -/
theorem bgk_subUnit_of_gain {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    {θ D c' : ℝ} (hr : 1 ≤ r) (hn : 1 ≤ (G.card : ℝ))
    (hE : SumProductEnergyBound G r θ) (hq : FieldSizePolyBound G D)
    (hgain : (θ + D) / (2 * r) ≤ 1 - c') (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) ^ (1 - c') := by
  refine (bgk_character_sum_bound hψ hr hn hE hq b).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le hn hgain

end ArkLib.ProximityGap.BGKEnergyCharacterSum

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.BGKEnergyCharacterSum.eta_pow_le_of_sumProduct
#print axioms ArkLib.ProximityGap.BGKEnergyCharacterSum.eta_sq_le_of_sumProduct
#print axioms ArkLib.ProximityGap.BGKEnergyCharacterSum.eta_sq_le_npow
#print axioms ArkLib.ProximityGap.BGKEnergyCharacterSum.bgk_character_sum_bound
#print axioms ArkLib.ProximityGap.BGKEnergyCharacterSum.bgk_subUnit_of_gain
