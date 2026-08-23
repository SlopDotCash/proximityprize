/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The worst-case `√q` anchor for the subgroup Gauss sum (#357, item 7)

Item 7 of the 26-thread review: wire Mathlib's `GaussSum` against the character-sum
kernel.  The landed kernel lane (`SubgroupGaussSumSecondMoment` → Markov → energy) is
entirely **average-case** (Parseval).  This file supplies the missing **worst-case
per-frequency** bound — classical Gauss-sum completion, NO Weil input:

For the `d`-torsion subgroup `G = {y : y^d = 1}` of `F*` (`d ∣ q−1`; the smooth
`2`-power subgroups are the case `d = 2^m`) and EVERY nonzero frequency `b`:

  `t · ‖η_b‖ = ‖∑_{j<t} τ(χ^{dj}, ψ_b)‖ ≤ (t−1)·√q + 1`,  hence  `‖η_b‖ ≤ √q`,

where `t = (q−1)/d` and `χ` has full order `q−1`.

Route: the geometric indicator `∑_{j<t} (χ(y)^d)^j = t·[χ(y)^d = 1]`; the count
`#{y ≠ 0 : χ(y)^d = 1} = d` by character orthogonality, which equals the torsion
count `d` (`IsPrimitiveRoot.card_nthRootsFinset`) — the two sets coincide by
cardinality, so no kernel-triviality argument is ever needed; the completion identity
`t·η_b = ∑_{j<t} gaussSum (χ^{dj}) (ψ_b)`; and `‖τ‖ = √q` for the `t−1` nontrivial
terms (`gaussSum_mul_gaussSum_eq_card` + conjugation), `‖τ‖ = 1` for the trivial one.

Together with the second-moment lane this closes the kernel at the `√q` quality level:
the average frequency sits at scale `√|G|`, every frequency at scale `≤ √q`, and the
open core is exactly beating `√q` per-frequency on smooth subgroups (the incomplete
character-sum wall).
-/

open Finset AddChar Polynomial

namespace ArkLib.ProximityGap.SubgroupGaussSumWorstCase

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Conjugation and the Gauss-sum norm -/

/-- A multiplicative character has unit norm on units. -/
theorem norm_mulChar_apply_unit (χ : MulChar F ℂ) {y : F} (hy : y ≠ 0) : ‖χ y‖ = 1 := by
  have hcard : Fintype.card F - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have h1 : ‖χ y‖ ^ (Fintype.card F - 1) = 1 := by
    rw [← norm_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one y hy, map_one,
      norm_one]
  rcases lt_trichotomy ‖χ y‖ 1 with h | h | h
  · have := pow_lt_one₀ (norm_nonneg (χ y)) h hcard
    linarith
  · exact h
  · have := one_lt_pow₀ h hcard
    linarith

/-- Conjugation inverts a multiplicative character pointwise. -/
theorem conj_mulChar_apply (χ : MulChar F ℂ) (y : F) :
    (starRingEnd ℂ) (χ y) = χ⁻¹ y := by
  by_cases hy : y = 0
  · subst hy
    rw [χ.map_nonunit (by simp), χ⁻¹.map_nonunit (by simp), map_zero]
  · rw [MulChar.inv_apply_eq_inv' χ y,
      ← Complex.inv_eq_conj (norm_mulChar_apply_unit χ hy)]

/-- Conjugation inverts an additive character pointwise (finite domain). -/
theorem conj_addChar_apply (ψ : AddChar F ℂ) (a : F) :
    (starRingEnd ℂ) (ψ a) = ψ⁻¹ a := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [AddChar.starComp_apply hchar]

/-- The conjugate of a Gauss sum is the Gauss sum of the inverted characters. -/
theorem conj_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (starRingEnd ℂ) (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
  unfold gaussSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, conj_mulChar_apply, conj_addChar_apply]

/-- **The Gauss-sum norm: `‖τ(χ,ψ)‖² = q`** for `χ ≠ 1`, `ψ` primitive. -/
theorem norm_gaussSum_sq {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = Fintype.card F := by
  have hprod : gaussSum χ ψ * (starRingEnd ℂ) (gaussSum χ ψ)
      = (Fintype.card F : ℂ) := by
    rw [conj_gaussSum]
    exact gaussSum_mul_gaussSum_eq_card hχ hψ
  have hnorms := congrArg norm hprod
  rw [Complex.norm_mul, Complex.norm_conj, Complex.norm_natCast] at hnorms
  rw [sq]
  exact hnorms

/-- The Gauss-sum norm: `‖τ(χ,ψ)‖ = √q`. -/
theorem norm_gaussSum_eq_sqrt {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  rw [← norm_gaussSum_sq hχ hψ, Real.sqrt_sq (norm_nonneg _)]

/-! ## The torsion subgroup and its character description -/

/-- The `d`-torsion subgroup of `F*`, as a finset of `F` (excludes `0` since
`0^d = 0 ≠ 1` for `d > 0`). -/
def torsion (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) : Finset F :=
  univ.filter fun y => y ^ d = 1

theorem mem_torsion {d : ℕ} {y : F} : y ∈ torsion F d ↔ y ^ d = 1 := by
  simp [torsion]

theorem ne_zero_of_mem_torsion {d : ℕ} (hd : 0 < d) {y : F} (hy : y ∈ torsion F d) :
    y ≠ 0 := by
  intro h
  rw [mem_torsion, h, zero_pow hd.ne'] at hy
  exact one_ne_zero hy.symm

/-- The torsion count: `|{y : y^d = 1}| = d` for `d ∣ q − 1`. -/
theorem card_torsion {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d) :
    (torsion F d).card = d := by
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have horder : orderOf g = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  set k := (Fintype.card F - 1) / d with hk
  have hkd : k * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hkd
      omega
    · exact h
  have hζord : orderOf (g ^ k) = d := by
    rw [orderOf_pow, horder]
    have hkdvd : k ∣ Fintype.card F - 1 := ⟨d, hkd.symm⟩
    have hgcd : Nat.gcd (Fintype.card F - 1) k = k := Nat.gcd_eq_right hkdvd
    rw [hgcd]
    exact Nat.div_eq_of_eq_mul_left hk0 ((mul_comm d k).trans hkd).symm
  have hζ : IsPrimitiveRoot ((g ^ k : Fˣ) : F) d := by
    rw [← hζord]
    exact (IsPrimitiveRoot.coe_units_iff).mpr (IsPrimitiveRoot.orderOf _)
  have hEq : torsion F d = Polynomial.nthRootsFinset d (1 : F) := by
    ext y
    rw [mem_torsion, Polynomial.mem_nthRootsFinset hd0]
  rw [hEq, hζ.card_nthRootsFinset]

/-! ## The completion identity -/

/-- Powers `χ^m` with `0 < m < q−1` of a full-order character are nontrivial. -/
theorem chi_pow_ne_one {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {m : ℕ} (hm0 : 0 < m) (hm : m < Fintype.card F - 1) :
    χ ^ m ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hord] at this
  exact absurd (Nat.le_of_dvd hm0 this) (not_le.mpr hm)

/-- The trivial character sums to `q − 1` over `F`. -/
theorem sum_one_mulChar : ∑ y : F, (1 : MulChar F ℂ) y = (Fintype.card F - 1 : ℕ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : F => y = 0)]
  have h0 : ∑ y ∈ Finset.univ.filter (fun y : F => y = 0), (1 : MulChar F ℂ) y = 0 := by
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [(Finset.mem_filter.mp hy).2]
    exact MulChar.map_nonunit _ (by simp)
  have h1 : ∑ y ∈ Finset.univ.filter (fun y : F => ¬ y = 0), (1 : MulChar F ℂ) y
      = (Finset.univ.filter (fun y : F => ¬ y = 0)).card := by
    rw [Finset.sum_congr rfl fun y hy =>
      MulChar.one_apply (isUnit_iff_ne_zero.mpr (Finset.mem_filter.mp hy).2)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h0, h1, zero_add]
  congr 1
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset F)) (p := fun y : F => y = 0)
  have hzero : (Finset.univ.filter (fun y : F => y = 0)).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨0, by ext y; simp⟩
  have hcardF : (Finset.univ : Finset F).card = Fintype.card F := rfl
  omega

/-- The geometric indicator: for `x` with `x^t = 1`, `∑_{j<t} x^j = t·[x = 1]`. -/
theorem geom_indicator {t : ℕ} {x : ℂ} (hx : x ^ t = 1) :
    ∑ j ∈ Finset.range t, x ^ j = if x = 1 then (t : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp
  · rw [geom_sum_eq h, hx, sub_self, zero_div]

open Classical in
/-- **The completion identity**: `t` times the torsion Gauss sum is the sum of `t`
complete Gauss sums, `t·η_b = ∑_{j<t} τ(χ^{dj}, ψ_b)`. -/
theorem completion_identity {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) (b : F) :
    ((Fintype.card F - 1) / d : ℕ) * eta ψ (torsion F d) b
      = ∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
          gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b) := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd
      omega
    · exact h
  set B : Finset F := Finset.univ.filter (fun y => y ≠ 0 ∧ (χ y) ^ d = 1) with hB
  -- pointwise collapse: ∑_{j<t} (χ^{dj}) y = t·[y ∈ B]
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
  -- orthogonality count: t·|B| = q − 1
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
    have hcast : (t * B.card : ℕ) = Fintype.card F - 1 := by
      exact_mod_cast hcount
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
  calc (t : ℂ) * eta ψ (torsion F d) b
      = ∑ y ∈ torsion F d, (t : ℂ) * ψ (b * y) := by
        have heta : eta ψ (torsion F d) b = ∑ y ∈ torsion F d, ψ (b * y) := rfl
        rw [heta, Finset.mul_sum]
    _ = ∑ y ∈ B, (t : ℂ) * ψ (b * y) := by rw [hAB]
    _ = ∑ y : F, (if y ∈ B then (t : ℂ) else 0) * ψ (b * y) := by
        symm
        calc ∑ y : F, (if y ∈ B then (t : ℂ) else 0) * ψ (b * y)
            = ∑ y : F, (if y ∈ B then (t : ℂ) * ψ (b * y) else 0) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [ite_mul, zero_mul]
          _ = ∑ y ∈ B, (t : ℂ) * ψ (b * y) := by
              rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ y : F, (∑ j ∈ Finset.range t, (χ ^ (d * j)) y) * ψ (b * y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hpoint y]
    _ = ∑ y : F, ∑ j ∈ Finset.range t, (χ ^ (d * j)) y * ψ (b * y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold gaussSum
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [AddChar.mulShift_apply]

/-! ## The worst-case bound -/

/-- The trivial-character Gauss sum at a nonzero shift is `−1`. -/
theorem gaussSum_one_mulShift {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F}
    (hb : b ≠ 0) :
    gaussSum (1 : MulChar F ℂ) (AddChar.mulShift ψ b) = -1 := by
  have hne0 : AddChar.mulShift ψ b ≠ 0 := by
    have h1 := hψ hb
    simpa using h1
  have hsum : ∑ y : F, (AddChar.mulShift ψ b) y = 0 :=
    AddChar.sum_eq_zero_iff_ne_zero.mpr hne0
  have h1 : ∑ y ∈ Finset.univ.erase (0 : F),
        (1 : MulChar F ℂ) y * (AddChar.mulShift ψ b) y
      = ∑ y ∈ Finset.univ.erase (0 : F), (AddChar.mulShift ψ b) y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (Finset.ne_of_mem_erase hy)), one_mul]
  have h2 : ∑ y ∈ Finset.univ.erase (0 : F), (AddChar.mulShift ψ b) y
      = - (AddChar.mulShift ψ b) 0 := by
    refine eq_neg_of_add_eq_zero_left ?_
    rw [Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : F))]
    exact hsum
  have h0 : (AddChar.mulShift ψ b) 0 = 1 := by
    rw [AddChar.mulShift_apply, mul_zero, AddChar.map_zero_eq_one]
  unfold gaussSum
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : F)), h1, h2,
    MulChar.map_nonunit _ (by simp), zero_mul, add_zero, h0]

/-- **The worst-case per-frequency bound, sharp form**: for the `d`-torsion subgroup
and every `b ≠ 0`, `t·‖η_b‖ ≤ (t−1)·√q + 1` with `t = (q−1)/d`. -/
theorem mul_norm_eta_torsion_le {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ((Fintype.card F - 1) / d : ℕ) * ‖eta ψ (torsion F d) b‖
      ≤ ((Fintype.card F - 1) / d - 1 : ℕ) * Real.sqrt (Fintype.card F) + 1 := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd
      omega
    · exact h
  -- the full-order character
  have hcardu : (Fintype.card Fˣ : ℕ) ≠ 0 := Fintype.card_ne_zero
  obtain ⟨χ, hχord⟩ := MulChar.exists_mulChar_orderOf_eq_card_units F
    (Complex.isPrimitiveRoot_exp (Fintype.card Fˣ) hcardu)
  have hord : orderOf χ = Fintype.card F - 1 := by
    rw [hχord, Fintype.card_units]
  have hkey := completion_identity hd hd0 hord ψ b
  have hnorm : (t : ℝ) * ‖eta ψ (torsion F d) b‖
      = ‖∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ := by
    rw [← hkey, norm_mul, Complex.norm_natCast]
  rw [hnorm]
  calc ‖∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖
      ≤ ∑ j ∈ Finset.range t, ‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ :=
        norm_sum_le _ _
    _ = ‖gaussSum (χ ^ (d * 0)) (AddChar.mulShift ψ b)‖
        + ∑ j ∈ (Finset.range t).erase 0,
            ‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ :=
        (Finset.add_sum_erase _ _ (Finset.mem_range.mpr ht0)).symm
    _ ≤ 1 + ((t - 1 : ℕ)) * Real.sqrt (Fintype.card F) := by
        refine add_le_add ?_ ?_
        · rw [mul_zero, pow_zero, gaussSum_one_mulShift hψ hb]
          simp
        · have hbound : ∀ j ∈ (Finset.range t).erase 0,
              ‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖
                = Real.sqrt (Fintype.card F) := by
            intro j hj
            have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
            have hjt : j < t := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
            have hχ' : χ ^ (d * j) ≠ 1 := by
              refine chi_pow_ne_one hord ?_ ?_
              · exact Nat.mul_pos hd0 (Nat.pos_of_ne_zero hj0)
              · calc d * j < d * t := (Nat.mul_lt_mul_left hd0).mpr hjt
                  _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
            set bu : Fˣ := Units.mk0 b hb with hbu
            have hshift := gaussSum_mulShift (χ ^ (d * j)) ψ bu
            have hnorms := congrArg norm hshift
            rw [Complex.norm_mul,
              norm_mulChar_apply_unit _ (show ((bu : F)) ≠ 0 from hb), one_mul]
              at hnorms
            rw [show AddChar.mulShift ψ b = AddChar.mulShift ψ ((bu : F)) from rfl,
              hnorms, norm_gaussSum_eq_sqrt hχ' hψ]
          rw [Finset.sum_congr rfl hbound, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_range.mpr ht0),
            Finset.card_range, nsmul_eq_mul]
    _ = ((t - 1 : ℕ)) * Real.sqrt (Fintype.card F) + 1 := by ring

/-- **THE WORST-CASE `√q` ANCHOR** (#357 item 7): for the `d`-torsion subgroup
`G = {y : y^d = 1}` of any finite field (`d ∣ q−1`) and EVERY nonzero frequency `b`,

  `‖∑_{y∈G} ψ(b·y)‖ ≤ √q`.

Classical Gauss-sum completion — no Weil input.  Complements the average-case
Parseval lane: the open core is exactly beating `√q` on smooth subgroups. -/
theorem norm_eta_torsion_le {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖eta ψ (torsion F d) b‖ ≤ Real.sqrt (Fintype.card F) := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd
      omega
    · exact h
  have hmain := mul_norm_eta_torsion_le hd hd0 hψ hb
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    refine Real.sqrt_le_sqrt ?_
    have := Fintype.one_lt_card (α := F)
    exact_mod_cast this.le
  have htcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht0]
    norm_num
  rw [htcast] at hmain
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  refine le_of_mul_le_mul_left ?_ ht0R
  calc (t : ℝ) * ‖eta ψ (torsion F d) b‖
      ≤ ((t : ℝ) - 1) * Real.sqrt (Fintype.card F) + 1 := hmain
    _ ≤ ((t : ℝ) - 1) * Real.sqrt (Fintype.card F) + Real.sqrt (Fintype.card F) :=
        by linarith
    _ = (t : ℝ) * Real.sqrt (Fintype.card F) := by ring

end ArkLib.ProximityGap.SubgroupGaussSumWorstCase

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.norm_gaussSum_sq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.card_torsion
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.completion_identity
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.norm_eta_torsion_le
