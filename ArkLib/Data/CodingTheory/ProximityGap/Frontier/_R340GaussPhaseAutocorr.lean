/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# R340: the Gauss-phase autocorrelation identity (Theorem 2 of the 2026-07-09 audit)

Companion to `_R339GaussPhaseMellinTwist` (the Mellin identity). For the `d`-torsion
subgroup, full-order `χ`, primitive `ψ`, and lag `0 < h < t = (q−1)/d`:

  `∑_{j<t} τ(χ^{d(j+h)}, ψ) · conj(τ(χ^{dj}, ψ))
      = t · τ(χ^{dh}, ψ) · ∑_{r ∈ torsion \ {1}} (χ^{dh})⁻¹(r − 1)`.

So the cyclic autocorrelation hierarchy of the Gauss-phase vector `(τ(χ^{dj},ψ))_j`
(the object whose Mellin peak is the open PAPR wall) is EXACTLY the family of shifted
thin-subgroup character sums `∑_{r∈μ_n} λ(r−1)` — the same family the corrected
off-diagonal bridge reduces to (dossier v3). No free lunch: this is L⁴/second-moment
information only (even perfect flatness gives an `m^{3/4}`-scale peak bound, not the
`√(m log m)` target), but it welds the two open faces into one object family and gives
the lag-side attack surface exact algebraic form.

Identity numerically verified to ~1e-10 (incl. τ₀ = −1 term) for (p,n) up to (3329,64).
Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.R340GaussPhaseAutocorr

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Extracting a nonzero shift from a Gauss sum as a multiplicative twist
(self-contained copy of `R339GaussPhaseMellinTwist.gaussSum_mulShift_twist`, kept
local so this lane iterates on the fast path without a frontier-to-frontier olean). -/
theorem gaussSum_mulShift_twist (χ' : MulChar F ℂ) (ψ : AddChar F ℂ) {b : F}
    (hb : b ≠ 0) :
    gaussSum χ' (AddChar.mulShift ψ b) = χ'⁻¹ b * gaussSum χ' ψ := by
  have hu : IsUnit b := isUnit_iff_ne_zero.mpr hb
  have h := gaussSum_mulShift χ' ψ hu.unit
  rw [IsUnit.unit_spec] at h
  have hne : χ' b ≠ 0 := by
    intro h0
    have hn := norm_mulChar_apply_unit χ' hb
    rw [h0, norm_zero] at hn
    norm_num at hn
  have hinv : χ'⁻¹ b * χ' b = 1 := by
    rw [MulChar.inv_apply_eq_inv' χ' b, inv_mul_cancel₀ hne]
  calc gaussSum χ' (AddChar.mulShift ψ b)
      = (χ'⁻¹ b * χ' b) * gaussSum χ' (AddChar.mulShift ψ b) := by rw [hinv, one_mul]
    _ = χ'⁻¹ b * (χ' b * gaussSum χ' (AddChar.mulShift ψ b)) := by ring
    _ = χ'⁻¹ b * gaussSum χ' ψ := by rw [h]

/-- A full-order character is trivial on the `d`-power residue class iff the argument
is `d`-torsion: the set `{z ≠ 0 : (χ z)^d = 1}` IS `torsion F d` (orthogonality count
`= d` on both sides; replayed from the interior of `completion_identity`). -/
theorem chiPow_eq_one_iff_torsion {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {z : F} (hz : z ≠ 0) :
    (χ z) ^ d = 1 ↔ z ∈ torsion F d := by
  classical
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  set B : Finset F := Finset.univ.filter (fun y => y ≠ 0 ∧ (χ y) ^ d = 1) with hB
  have hpoint : ∀ y : F, ∑ j ∈ Finset.range t, (χ ^ (d * j)) y
      = if y ∈ B then (t : ℂ) else 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy
      rw [Finset.sum_congr rfl fun j _ => MulChar.map_nonunit _ (by simp),
        Finset.sum_const, smul_zero, if_neg (by simp [hB])]
    · have happ : ∀ j, (χ ^ (d * j)) y = ((χ y) ^ d) ^ j := by
        intro j
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          rw [mul_zero, pow_zero, pow_zero, MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)]
        · rw [MulChar.pow_apply' χ (by positivity) y, pow_mul]
      rw [Finset.sum_congr rfl fun j _ => happ j]
      have hxt : ((χ y) ^ d) ^ t = 1 := by
        rw [← pow_mul, mul_comm d t, htd, ← map_pow,
          FiniteField.pow_card_sub_one_eq_one y hy, map_one]
      rw [geom_indicator hxt]
      by_cases hxy : (χ y) ^ d = 1
      · rw [if_pos hxy, if_pos (by simp [hB, hy, hxy])]
      · rw [if_neg hxy, if_neg (by simp [hB, hy, hxy])]
  have hcount : (t : ℂ) * B.card = ((Fintype.card F - 1 : ℕ) : ℂ) := by
    have hswap : ∑ y : F, ∑ j ∈ Finset.range t, (χ ^ (d * j)) y
        = ∑ j ∈ Finset.range t, ∑ y : F, (χ ^ (d * j)) y := Finset.sum_comm
    have hleft : ∑ y : F, ∑ j ∈ Finset.range t, (χ ^ (d * j)) y
        = (t : ℂ) * B.card := by
      rw [Finset.sum_congr rfl fun y _ => hpoint y, Finset.sum_ite_mem,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hright : ∑ j ∈ Finset.range t, ∑ y : F, (χ ^ (d * j)) y
        = ((Fintype.card F - 1 : ℕ) : ℂ) := by
      refine (Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr ht0)
        (fun j hj hj0 => ?_)).trans ?_
      · refine MulChar.sum_eq_zero_of_ne_one (chi_pow_ne_one hord ?_ ?_)
        · exact Nat.mul_pos hd0 (Nat.pos_of_ne_zero hj0)
        · calc d * j < d * t := (Nat.mul_lt_mul_left hd0).mpr (Finset.mem_range.mp hj)
            _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
      · simp only [mul_zero, pow_zero]
        exact sum_one_mulChar
    rw [← hleft, hswap, hright]
  have hBcard : B.card = d := by
    have hcast : (t * B.card : ℕ) = Fintype.card F - 1 := by exact_mod_cast hcount
    have htdd : t * B.card = t * d := by omega
    exact Nat.eq_of_mul_eq_mul_left ht0 htdd
  have hsub : torsion F d ⊆ B := by
    intro y hy
    have hy0 := ne_zero_of_mem_torsion hd0 hy
    rw [mem_torsion] at hy
    rw [hB, Finset.mem_filter]
    exact ⟨Finset.mem_univ y, hy0, by rw [← map_pow, hy, map_one]⟩
  have hAB : torsion F d = B :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hBcard, card_torsion hd hd0])
  constructor
  · intro hchi
    rw [hAB, hB, Finset.mem_filter]
    exact ⟨Finset.mem_univ z, hz, hchi⟩
  · intro hmem
    rw [hAB, hB, Finset.mem_filter] at hmem
    exact hmem.2.2

/-- Inverse-character evaluation through powers, valid for ALL exponents (including
`0`) at nonzero arguments: `((χ^n)⁻¹) y = ((χ y)^n)⁻¹`. -/
theorem inv_pow_apply (χ : MulChar F ℂ) {y : F} (hy : y ≠ 0) (n : ℕ) :
    ((χ ^ n)⁻¹) y = ((χ y) ^ n)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [pow_zero, pow_zero, inv_one, MulChar.one_apply (isUnit_iff_ne_zero.mpr hy),
      inv_one]
  · rw [MulChar.inv_apply_eq_inv' (χ ^ n) y, MulChar.pow_apply' χ hn.ne' y]

/-- **The Gauss-phase autocorrelation identity**: for lag `0 < h < t`,

  `∑_{j<t} τ(χ^{d(j+h)}, ψ) · conj(τ(χ^{dj}, ψ))
      = t · τ(χ^{dh}, ψ) · ∑_{r ∈ torsion \ {1}} (χ^{dh})⁻¹(r − 1)`.

The autocorrelation hierarchy of the Gauss-phase vector is exactly the shifted
thin-subgroup character-sum family. -/
theorem autocorr_identity {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) {h : ℕ} (hh0 : 0 < h)
    (hht : h < (Fintype.card F - 1) / d) :
    ∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
        gaussSum (χ ^ (d * (j + h))) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) ψ)
      = ((Fintype.card F - 1) / d : ℕ) * gaussSum (χ ^ (d * h)) ψ
          * ∑ r ∈ (torsion F d).erase 1, ((χ ^ (d * h))⁻¹) (r - 1) := by
  classical
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hdh0 : 0 < d * h := Nat.mul_pos hd0 hh0
  have hdhlt : d * h < Fintype.card F - 1 := by
    calc d * h < d * t := (Nat.mul_lt_mul_left hd0).mpr hht
      _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
  have hχdh : (χ ^ (d * h)) ≠ 1 := chi_pow_ne_one hord hdh0 hdhlt
  -- Step 1: expand each product of Gauss sums as a double sum and swap the j-sum inside
  have hexpand : ∀ j : ℕ,
      gaussSum (χ ^ (d * (j + h))) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) ψ)
        = ∑ x : F, ∑ y : F,
            (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) y * ψ⁻¹ y) := by
    intro j
    rw [conj_gaussSum]
    unfold gaussSum
    rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun j _ => hexpand j]
  rw [Finset.sum_comm]
  -- now: ∑_x ∑_j ∑_y …; swap once more to get ∑_x ∑_y ∑_j
  have hswap2 : ∀ x : F, ∑ j ∈ Finset.range t, ∑ y : F,
      (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) y * ψ⁻¹ y)
      = ∑ y : F, ∑ j ∈ Finset.range t,
      (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) y * ψ⁻¹ y) := fun x =>
    Finset.sum_comm
  rw [Finset.sum_congr rfl fun x _ => hswap2 x]
  -- Step 2: pointwise collapse of the j-sum
  have hcollapse : ∀ x y : F, y ≠ 0 →
      ∑ j ∈ Finset.range t, (χ ^ (d * (j + h))) x * (((χ ^ (d * j))⁻¹) y)
        = (χ ^ (d * h)) x * (if x * y⁻¹ ∈ torsion F d then (t : ℂ) else 0) := by
    intro x y hy
    by_cases hx : x = 0
    · subst hx
      rw [Finset.sum_congr rfl fun j _ =>
          by rw [MulChar.map_nonunit _ (by simp), zero_mul],
        Finset.sum_const, smul_zero, MulChar.map_nonunit _ (by simp), zero_mul]
    · have hterm : ∀ j : ℕ, (χ ^ (d * (j + h))) x * (((χ ^ (d * j))⁻¹) y)
          = (χ x) ^ (d * h) * ((χ x) ^ d * ((χ y) ^ d)⁻¹) ^ j := by
        intro j
        rw [MulChar.pow_apply' χ (by positivity) x, inv_pow_apply χ hy (d * j)]
        rw [mul_add, pow_add, pow_mul (χ x) d j, pow_mul (χ y) d j, mul_pow, inv_pow]
        ring
      rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum]
      have hxq : (χ x) ^ (Fintype.card F - 1) = 1 := by
        rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one]
      have hyq : (χ y) ^ (Fintype.card F - 1) = 1 := by
        rw [← map_pow, FiniteField.pow_card_sub_one_eq_one y hy, map_one]
      have hut : ((χ x) ^ d * ((χ y) ^ d)⁻¹) ^ t = 1 := by
        rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm d t, htd, hxq, hyq,
          inv_one, mul_one]
      rw [geom_indicator hut]
      have hyunit : IsUnit (χ y) := by
        refine isUnit_iff_ne_zero.mpr fun h0 => ?_
        have hn := norm_mulChar_apply_unit χ hy
        rw [h0, norm_zero] at hn
        norm_num at hn
      have hinvy : χ y⁻¹ = (χ y)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_mul, inv_mul_cancel₀ hy, map_one]
      have hcond : ((χ x) ^ d * ((χ y) ^ d)⁻¹ = 1) ↔ x * y⁻¹ ∈ torsion F d := by
        have hrewrite : (χ x) ^ d * ((χ y) ^ d)⁻¹ = (χ (x * y⁻¹)) ^ d := by
          rw [map_mul, hinvy, mul_pow, inv_pow]
        rw [hrewrite]
        exact chiPow_eq_one_iff_torsion hd hd0 hord
          (mul_ne_zero hx (inv_ne_zero hy))
      by_cases hc : (χ x) ^ d * ((χ y) ^ d)⁻¹ = 1
      · rw [if_pos hc, if_pos (hcond.mp hc),
          MulChar.pow_apply' χ (by positivity) x]
      · rw [if_neg hc, if_neg (fun hmem => hc (hcond.mpr hmem)),
          MulChar.pow_apply' χ (by positivity) x, mul_zero]
  -- Step 3: rearrange each (x, y)-term to isolate the j-sum, apply the collapse,
  -- and evaluate. First kill y = 0.
  have hy0 : ∀ x : F, ∑ j ∈ Finset.range t,
      (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) (0 : F) * ψ⁻¹ 0)
        = 0 := by
    intro x
    rw [Finset.sum_congr rfl fun j _ => by
      rw [MulChar.map_nonunit ((χ ^ (d * j))⁻¹) (by simp), zero_mul, mul_zero],
      Finset.sum_const, smul_zero]
  -- Reorganize the full double sum with x = r·y on the torsion fiber.
  have hinner : ∀ y : F, y ≠ 0 → ∀ x : F,
      ∑ j ∈ Finset.range t, (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) y * ψ⁻¹ y)
        = ψ x * ψ⁻¹ y * ((χ ^ (d * h)) x
            * (if x * y⁻¹ ∈ torsion F d then (t : ℂ) else 0)) := by
    intro y hy x
    have : ∑ j ∈ Finset.range t,
        (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) y * ψ⁻¹ y)
        = ψ x * ψ⁻¹ y * ∑ j ∈ Finset.range t,
            (χ ^ (d * (j + h))) x * (((χ ^ (d * j))⁻¹) y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hcollapse x y hy]
  -- Step 4: for fixed y ≠ 0, sum over x via the bijection r ↦ r·y from torsion.
  have hfiber : ∀ y : F, y ≠ 0 →
      ∑ x : F, ψ x * ψ⁻¹ y * ((χ ^ (d * h)) x
          * (if x * y⁻¹ ∈ torsion F d then (t : ℂ) else 0))
        = (t : ℂ) * ∑ r ∈ torsion F d, (χ ^ (d * h)) y * ψ ((r - 1) * y) := by
    intro y hy
    have himage : Finset.univ.filter (fun x : F => x * y⁻¹ ∈ torsion F d)
        = (torsion F d).image (fun r => r * y) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hx
        exact ⟨x * y⁻¹, hx, by field_simp⟩
      · rintro ⟨r, hr, rfl⟩
        rwa [mul_assoc, mul_inv_cancel₀ hy, mul_one]
    calc ∑ x : F, ψ x * ψ⁻¹ y * ((χ ^ (d * h)) x
            * (if x * y⁻¹ ∈ torsion F d then (t : ℂ) else 0))
        = ∑ x ∈ Finset.univ.filter (fun x : F => x * y⁻¹ ∈ torsion F d),
            ψ x * ψ⁻¹ y * ((χ ^ (d * h)) x * t) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x * y⁻¹ ∈ torsion F d
          · rw [if_pos hx, if_pos hx]
          · rw [if_neg hx, if_neg hx, mul_zero, mul_zero]
      _ = ∑ r ∈ torsion F d, ψ (r * y) * ψ⁻¹ y * ((χ ^ (d * h)) (r * y) * t) := by
          rw [himage]
          exact Finset.sum_image fun a _ b _ hab => mul_right_cancel₀ hy hab
      _ = (t : ℂ) * ∑ r ∈ torsion F d, (χ ^ (d * h)) y * ψ ((r - 1) * y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          have hr0 : r ≠ 0 := ne_zero_of_mem_torsion hd0 hr
          have hrd : r ^ d = 1 := mem_torsion.mp hr
          have hchir : (χ ^ (d * h)) (r * y)
              = (χ ^ (d * h)) r * (χ ^ (d * h)) y := map_mul _ r y
          have hchir1 : (χ ^ (d * h)) r = 1 := by
            rw [MulChar.pow_apply' χ (by positivity) r, pow_mul, ← map_pow, hrd,
              map_one, one_pow]
          have hpsi : ψ (r * y) * ψ⁻¹ y = ψ ((r - 1) * y) := by
            rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul]
            congr 1
            ring
          rw [hchir, hchir1, one_mul]
          calc ψ (r * y) * ψ⁻¹ y * ((χ ^ (d * h)) y * t)
              = (ψ (r * y) * ψ⁻¹ y) * (χ ^ (d * h)) y * t := by ring
            _ = ψ ((r - 1) * y) * (χ ^ (d * h)) y * t := by rw [hpsi]
            _ = (t : ℂ) * ((χ ^ (d * h)) y * ψ ((r - 1) * y)) := by ring
  -- Step 5: assemble — swap x ↔ y roles, evaluate the r-sum via Gauss sums.
  -- Current shape after rewriting: ∑_x ∑_y ∑_j …  — convert to ∑_y ∑_x …
  rw [Finset.sum_comm]
  have hcombine : ∑ y : F, ∑ x : F, ∑ j ∈ Finset.range t,
      (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) y * ψ⁻¹ y)
      = ∑ y ∈ Finset.univ.erase (0 : F), (t : ℂ)
          * ∑ r ∈ torsion F d, (χ ^ (d * h)) y * ψ ((r - 1) * y) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : F))]
    have hzero : ∑ x : F, ∑ j ∈ Finset.range t,
        (χ ^ (d * (j + h))) x * ψ x * (((χ ^ (d * j))⁻¹) (0 : F) * ψ⁻¹ 0) = 0 := by
      rw [Finset.sum_congr rfl fun x _ => hy0 x, Finset.sum_const, smul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyne : y ≠ 0 := Finset.ne_of_mem_erase hy
    rw [Finset.sum_congr rfl fun x _ => hinner y hyne x]
    exact hfiber y hyne
  rw [hcombine]
  -- Step 6: swap the y-sum and r-sum, evaluate inner y-sums as shifted Gauss sums.
  have hswap3 : ∑ y ∈ Finset.univ.erase (0 : F), (t : ℂ)
        * ∑ r ∈ torsion F d, (χ ^ (d * h)) y * ψ ((r - 1) * y)
      = (t : ℂ) * ∑ r ∈ torsion F d, ∑ y ∈ Finset.univ.erase (0 : F),
          (χ ^ (d * h)) y * ψ ((r - 1) * y) := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [hswap3]
  have hysum : ∀ r : F, ∑ y ∈ Finset.univ.erase (0 : F),
        (χ ^ (d * h)) y * ψ ((r - 1) * y)
      = gaussSum (χ ^ (d * h)) (AddChar.mulShift ψ (r - 1)) := by
    intro r
    unfold gaussSum
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : F))]
    have h0 : (χ ^ (d * h)) (0 : F) * (AddChar.mulShift ψ (r - 1)) 0 = 0 := by
      rw [MulChar.map_nonunit _ (by simp), zero_mul]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun y _ => by rw [AddChar.mulShift_apply]
  rw [Finset.sum_congr rfl fun r _ => hysum r]
  -- Step 7: split off r = 1 (vanishes: trivial shift, nontrivial character).
  have h1mem : (1 : F) ∈ torsion F d := mem_torsion.mpr (one_pow d)
  rw [← Finset.add_sum_erase _ _ h1mem]
  have hr1 : gaussSum (χ ^ (d * h)) (AddChar.mulShift ψ ((1 : F) - 1)) = 0 := by
    rw [sub_self, AddChar.mulShift_zero]
    unfold gaussSum
    have : ∀ y : F, (χ ^ (d * h)) y * (1 : AddChar F ℂ) y = (χ ^ (d * h)) y :=
      fun y => by rw [AddChar.one_apply, mul_one]
    rw [Finset.sum_congr rfl fun y _ => this y]
    exact MulChar.sum_eq_zero_of_ne_one hχdh
  rw [hr1, zero_add]
  -- Step 8: twist each remaining shifted Gauss sum.
  have htwist : ∀ r ∈ (torsion F d).erase 1,
      gaussSum (χ ^ (d * h)) (AddChar.mulShift ψ (r - 1))
        = ((χ ^ (d * h))⁻¹) (r - 1) * gaussSum (χ ^ (d * h)) ψ := by
    intro r hr
    have hrne : r - 1 ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hr)
    exact gaussSum_mulShift_twist (χ ^ (d * h)) ψ hrne
  rw [Finset.sum_congr rfl htwist, ← Finset.sum_mul]
  ring

#print axioms chiPow_eq_one_iff_torsion
#print axioms inv_pow_apply
#print axioms autocorr_identity

end ArkLib.ProximityGap.R340GaussPhaseAutocorr
