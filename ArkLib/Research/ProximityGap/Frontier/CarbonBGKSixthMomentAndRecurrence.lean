/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Production Sixth-Moment Laws, Cross-Coset Sextuples, and Holonomic Recurrence Bounds

This module formalizes four analytic and algebraic results on the sixth Gauss-period moment
(`r = 3`) over dyadic multiplicative subgroups `H = μ_n ⊂ F_p^×` (`n = 2^30`):

1. **Normalized-pair decomposition of `rEnergy H 3`, subgroup divisibility, DC-moment equivalence,
   and exact `u = 1` multiplicity (`§1`):**
   Connects `SubgroupGaussSumMoment.rEnergy H 3` directly to the normalized pair-signature
   histogram `normProfile H n u`, deduces `H.card ∣ rEnergy H 3`, proves that
   `∑_{b ≠ 0} ‖η_b‖^6 ≤ 15 * |F| * n^3 ↔ rEnergy H 3 ≤ 15 * n^3` whenever `n^5 < |F|`, and proves
   `3 * H.card - 3 ≤ normProfile H n 1` unconditionally (with exact equality under weak Sidon).

2. **`2.5×` sharper unconditional production occupied-bin floor via `u = 1` puncturing (`§2`):**
   Applying Cauchy–Schwarz on `(occupiedBins H n).erase 1` after isolating the `u = 1` spike
   `m(1) ≥ 3n - 3` upgrades the production occupied-bin lower bound under `rEnergy H 3 ≤ 15 * n^3`
   from `76,861,433,640,456,466` (`≈ n^2 / 15`) to `192,153,582,490,528,435` (`≈ n^2 / 6`) with
   no additional four-term hypotheses.

3. **Finite-window polynomial-coefficient (holonomic) recurrence lower bound (`§3`):**
   Proves via `Polynomial.aeval` of the left-shift endomorphism, binomial finite differencing,
   monic propagation, and arithmetic-progression Vandermonde reduction that any nonzero family of
   polynomials `A_0, ..., A_r ∈ (ZMod p)[X]` of degree `≤ b < p` annihilating the weighted trace
   `S_k = ∑_{u ∈ U} w(u) u^k` on the finite window `0 ≤ j < |U| * (b + 1)` must have order
   `r ≥ |U|`, yielding `r ≥ 192,153,582,490,528,434` at `n = 2^30` under the sixth-moment bound.

4. **Cross-coset `2+2+2` S-unit / Sidon reduction and `μ_4`-coset occupancy elimination (`§4`):**
   Reduces cross-coset `2+2+2` zero-sum sextuples to normalized two-root lines, bounds equal- or
   conjugate-gap cross-coset placements by at most `2` under weak Sidon, and proves that every
   antipode-free 6-element zero-sum subset of `μ_n` avoiding two disjoint `μ_4`-coset pairs
   occupies at least `5` distinct `μ_4`-cosets (`2+1+1+1+1` or `1+1+1+1+1+1`).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonBGKSixthMomentAndRecurrence

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

/-! ## §1. Normalized-pair decomposition of `rEnergy H 3`, DC equivalence, and `u = 1` floor -/

/-- Number of ordered pairs `(x, y) ∈ H × H` with normalized signature `(1 + x + y)^n = u`. -/
def normProfile {F : Type*} [Field F] [DecidableEq F] (H : Finset F) (n : ℕ) (u : F) : ℕ :=
  ((H ×ˢ H).filter (fun P => (1 + P.1 + P.2) ^ n = u)).card

/-- Set of signature bins `u` occupied by `(1 + x + y)^n` as `(x, y)` ranges over `H × H`. -/
def occupiedBins {F : Type*} [Field F] [DecidableEq F] (H : Finset F) (n : ℕ) : Finset F :=
  (H ×ˢ H).image (fun P => (1 + P.1 + P.2) ^ n)

private theorem pow_eq_iff_div_mem {F : Type*} [Field F] {H : Finset F} {n : ℕ}
    (hH : ∀ x, x ∈ H ↔ x ^ n = 1) {x y : F} (hy : y ≠ 0) :
    x ^ n = y ^ n ↔ x / y ∈ H := by
  rw [hH, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hy)]

private def tripleWeight {F : Type*} [Field F] (H : Finset F) (f : F → ℕ) : ℕ :=
  ∑ a ∈ H, ∑ b ∈ H, ∑ c ∈ H, f (a + b + c)

private theorem normalized_weight {F : Type*} [Field F] {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x ^ n = 1) (f : F → ℕ) :
    tripleWeight H f = ∑ P ∈ H ×ˢ H, ∑ a ∈ H, f (a * (1 + P.1 + P.2)) := by
  rw [sum_product]
  conv_rhs => rw [Finset.sum_comm]; enter [2, y]; rw [Finset.sum_comm]
  unfold tripleWeight
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl (fun a ha => ?_)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simpa only [zero_pow hn.ne', zero_ne_one] using (hH 0).mp ha
  have hreindex (w : F → ℕ) : ∑ j ∈ H, w (a * j) = ∑ j ∈ H, w j := by
    apply sum_nbij' (i := fun j => a * j) (j := fun j => a⁻¹ * j)
    · intro x hx
      exact (hH _).mpr (by rw [mul_pow, (hH _).mp ha, (hH _).mp hx, one_mul])
    · intro x hx
      exact (hH _).mpr (by rw [mul_pow, inv_pow, (hH _).mp ha, (hH _).mp hx, inv_one, one_mul])
    · intro x _
      exact inv_mul_cancel_left₀ ha0 x
    · intro x _
      exact mul_inv_cancel_left₀ ha0 x
    · intro _ _
      rfl
  rw [← hreindex (fun b => ∑ c ∈ H, f (a + b + c))]
  refine sum_congr rfl (fun b _ => ?_)
  rw [← hreindex (fun c => f (a + a * b + c))]
  exact sum_congr rfl (fun c _ => congrArg f (by ring))

private theorem scale_count {F : Type*} [Field F] [DecidableEq F] {H : Finset F} {n : ℕ}
    (hn : 0 < n) (hH : ∀ x, x ∈ H ↔ x ^ n = 1) (c z : F) :
    (∑ a ∈ H, if c = a * z then 1 else 0) =
      if c = 0 then (if z ^ n = 0 then H.card else 0)
      else (if z ^ n = c ^ n then 1 else 0) := by
  by_cases hz : z = 0
  · subst z
    by_cases hc : c = 0
    · simp [hc, hn.ne']
    · simp [hc, hn.ne', (pow_ne_zero n hc).symm]
  · have he (a : F) : c = a * z ↔ a = c / z := by
      rw [eq_div_iff hz, eq_comm]
    simp_rw [he]
    rw [sum_ite_eq' H _ (fun _ => (1 : ℕ))]
    simp only [← pow_eq_iff_div_mem hH hz]
    by_cases hc : c = 0
    · simp [hc, hn.ne', pow_ne_zero n hz, (pow_ne_zero n hz).symm]
    · simp [hc, eq_comm]

private theorem profile_weight {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (H : Finset F) (n : ℕ) (f : F → ℕ) :
    (∑ P ∈ H ×ˢ H, f ((1 + P.1 + P.2) ^ n)) = ∑ u : F, normProfile H n u * f u := by
  simpa only [normProfile, sum_const, nsmul_eq_mul, Nat.cast_id] using
    (sum_fiberwise' (H ×ˢ H) (fun P => (1 + P.1 + P.2) ^ n) f).symm

private theorem tripleWeight_eq_piSum {F : Type*} [Field F] (H : Finset F) (f : F → ℕ) :
    tripleWeight H f = ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => H), f (∑ i, v i) := by
  unfold tripleWeight
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ![p.1.1, p.1.2, p.2]) (fun v => ((v 0, v 1), v 2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i <;> simp [hp.1.1, hp.1.2, hp.2]
  · intro v hv
    rw [Fintype.mem_piFinset] at hv
    simp [hv 0, hv 1, hv 2]
  · intro _ _
    rfl
  · intro v _
    funext i
    fin_cases i <;> rfl
  · intro _ _
    simp [Fin.sum_univ_three]

/-- **Exact normalized-pair histogram identity for `rEnergy H 3`.** -/
theorem rEnergy_three_eq_normProfile {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {H : Finset F} {n : ℕ} (hn : 0 < n) (hH : ∀ x, x ∈ H ↔ x ^ n = 1) :
    rEnergy H 3 = (H.card * normProfile H n 0) ^ 2 +
      H.card * ∑ u ∈ (Finset.univ : Finset F).erase 0, (normProfile H n u) ^ 2 := by
  let tc (c : F) : ℕ := ∑ a ∈ H, ∑ b ∈ H, ∑ d ∈ H, if c = a + b + d then 1 else 0
  let f (u : F) : ℕ := if u = 0 then H.card * normProfile H n 0 else normProfile H n u
  have htc (c : F) : tc c = f (c ^ n) := by
    change tripleWeight H (fun z => if c = z then 1 else 0) = f (c ^ n)
    rw [normalized_weight hn hH]
    simp_rw [scale_count hn hH]
    by_cases hc : c = 0
    · subst c
      simp only [f, zero_pow hn.ne', ite_true]
      rw [profile_weight H n (fun u => if u = 0 then H.card else 0)]
      simp [mul_ite, Nat.mul_comm]
    · simp only [f, hc, pow_ne_zero _ hc, ite_false]
      rw [profile_weight H n (fun u => if u = c ^ n then 1 else 0)]
      simp [mul_ite]
  have hpi (z : F) : (∑ w ∈ Fintype.piFinset (fun _ : Fin 3 => H),
      if z = ∑ i, w i then 1 else 0) = tc z :=
    (tripleWeight_eq_piSum H (fun c => if z = c then 1 else 0)).symm
  unfold rEnergy
  simp_rw [hpi]
  rw [← tripleWeight_eq_piSum H tc, show tc = (fun c => f (c ^ n)) by funext c; exact htc c]
  rw [normalized_weight hn hH]
  have hscale (P : F × F) :
      (∑ a ∈ H, f ((a * (1 + P.1 + P.2)) ^ n)) = H.card * f ((1 + P.1 + P.2) ^ n) := by
    apply sum_const_nat
    intro a ha
    rw [mul_pow, (hH _).mp ha, one_mul]
  simp_rw [hscale]
  rw [← Finset.mul_sum, profile_weight H n f,
    ← Finset.add_sum_erase (Finset.univ : Finset F) (fun u => normProfile H n u * f u)
      (Finset.mem_univ 0)]
  have hnonzero : (∑ u ∈ (Finset.univ : Finset F).erase 0, normProfile H n u * f u) =
      ∑ u ∈ (Finset.univ : Finset F).erase 0, (normProfile H n u) ^ 2 := by
    apply sum_congr rfl
    intro u hu
    simp [f, (Finset.mem_erase.mp hu).1, pow_two]
  rw [hnonzero]
  simp only [f, ite_true]
  ring

/-- **Subgroup cardinality divides the sixth-moment energy `rEnergy H 3`.** -/
theorem card_dvd_rEnergy_three {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {H : Finset F} {n : ℕ} (hn : 0 < n) (hH : ∀ x, x ∈ H ↔ x ^ n = 1) :
    H.card ∣ rEnergy H 3 := by
  rw [rEnergy_three_eq_normProfile hn hH]
  refine ⟨H.card * (normProfile H n 0) ^ 2 +
    ∑ u ∈ (Finset.univ : Finset F).erase 0, (normProfile H n u) ^ 2, ?_⟩
  ring

/-- **Equivalence between the DC-subtracted sixth-moment Wick bound and `rEnergy H 3 ≤ 15 * n^3`.**
Whenever `n^5 < |F|` (satisfied by `2^150 < P₁, P₂`), subgroup divisibility `n ∣ rEnergy H 3`
upgrades `∑_{b ≠ 0} ‖η_b‖^6 ≤ 15 * |F| * n^3` to the integer bound `rEnergy H 3 ≤ 15 * n^3`. -/
theorem dcSixthMoment_le_wick_iff_rEnergy_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {H : Finset F} {n : ℕ}
    (hn : 0 < n) (hcard : H.card = n) (hH : ∀ x, x ∈ H ↔ x ^ n = 1)
    (hlarge : n ^ 5 < Fintype.card F) :
    (∑ b ∈ (Finset.univ : Finset F).erase 0, ‖eta ψ H b‖ ^ 6
        ≤ 15 * (Fintype.card F : ℝ) * (n : ℝ) ^ 3) ↔
      rEnergy H 3 ≤ 15 * n ^ 3 := by
  have hmom := sum_nonzero_moment hψ H 3
  simp only [show 2 * 3 = 6 by rfl, hcard] at hmom
  rw [hmom]
  constructor
  · intro hle
    obtain ⟨k, hk⟩ := card_dvd_rEnergy_three hn hH
    rw [hcard] at hk
    by_contra hgt
    push Not at hgt
    have hk_gt : 15 * n ^ 2 < k := by
      have hmul : n * (15 * n ^ 2) < n * k := by
        calc n * (15 * n ^ 2) = 15 * n ^ 3 := by ring
          _ < rEnergy H 3 := hgt
          _ = n * k := hk
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hk_ge : (15 * (n : ℝ) ^ 2 + 1) ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hk_gt
    have hn6 : (n : ℝ) ^ 6 < (Fintype.card F : ℝ) * (n : ℝ) := by
      have h5 : (n : ℝ) ^ 5 < (Fintype.card F : ℝ) := by exact_mod_cast hlarge
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      calc (n : ℝ) ^ 6 = (n : ℝ) ^ 5 * (n : ℝ) := by ring
        _ < (Fintype.card F : ℝ) * (n : ℝ) := mul_lt_mul_of_pos_right h5 hn0
    have hE_ge : 15 * (Fintype.card F : ℝ) * (n : ℝ) ^ 3 + (Fintype.card F : ℝ) * (n : ℝ)
        ≤ (Fintype.card F : ℝ) * (rEnergy H 3 : ℝ) := by
      have hFn : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (n : ℝ) := by positivity
      calc 15 * (Fintype.card F : ℝ) * (n : ℝ) ^ 3 + (Fintype.card F : ℝ) * (n : ℝ)
          = ((Fintype.card F : ℝ) * (n : ℝ)) * (15 * (n : ℝ) ^ 2 + 1) := by ring
        _ ≤ ((Fintype.card F : ℝ) * (n : ℝ)) * (k : ℝ) := mul_le_mul_of_nonneg_left hk_ge hFn
        _ = (Fintype.card F : ℝ) * ((n : ℝ) * (k : ℝ)) := by ring
        _ = (Fintype.card F : ℝ) * (rEnergy H 3 : ℝ) := by
            rw [show ((n : ℝ) * (k : ℝ)) = ((n * k : ℕ) : ℝ) by push_cast; ring, ← hk]
    linarith
  · intro hle
    have hleR : (rEnergy H 3 : ℝ) ≤ 15 * (n : ℝ) ^ 3 := by exact_mod_cast hle
    have hF0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
    have hn6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hleR hF0]

/-- **Unconditional `u = 1` bin lower bound `3 * H.card - 3 ≤ normProfile H n 1`.**
In odd characteristic at even order `n > 0`, the three antipodal families `(-1, y)`, `(x, -1)`,
and `(x, -x)` supply `3 * H.card - 3` distinct pairs in `normProfile H n 1`. -/
theorem normProfile_one_ge_three_card_sub_three {F : Type*} [Field F] [DecidableEq F]
    {H : Finset F} {n : ℕ} (_hn : 0 < n) (heven : Even n) (htwo : (2 : F) ≠ 0)
    (hH : ∀ x, x ∈ H ↔ x ^ n = 1) :
    3 * H.card - 3 ≤ normProfile H n 1 := by
  have h1H : (1 : F) ∈ H := (hH 1).mpr (one_pow n)
  have hm1H : (-1 : F) ∈ H := (hH (-1)).mpr ((heven.neg_pow 1).trans (one_pow n))
  have h1_ne : (1 : F) ≠ -1 := by
    intro h
    apply htwo
    linear_combination h
  have hcard2 : 2 ≤ H.card := Finset.one_lt_card.mpr ⟨1, h1H, -1, hm1H, h1_ne⟩
  let A : Finset (F × F) := H.image (fun y => (-1, y))
  let B : Finset (F × F) := (H.erase (-1)).image (fun x => (x, -1))
  let C : Finset (F × F) := ((H.erase (-1)).erase 1).image (fun x => (x, -x))
  have hA_card : A.card = H.card :=
    Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
  have hB_card : B.card = H.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_erase_of_mem hm1H]
  have h1_mem_erase : (1 : F) ∈ H.erase (-1) := Finset.mem_erase.mpr ⟨h1_ne, h1H⟩
  have hC_card : C.card = H.card - 2 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_erase_of_mem h1_mem_erase, Finset.card_erase_of_mem hm1H]
    omega
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hpA
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hpB
    exact (Finset.mem_erase.mp hx).1 (Prod.mk.inj heq).1
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro p hpAB hpC
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpC
    obtain ⟨hx1, hx2⟩ := Finset.mem_erase.mp hx
    have hxm1 : x ≠ -1 := (Finset.mem_erase.mp hx2).1
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · obtain ⟨y, -, heq⟩ := Finset.mem_image.mp hpA
      exact hxm1 (Prod.mk.inj heq).1.symm
    · obtain ⟨y, -, heq⟩ := Finset.mem_image.mp hpB
      have hneg : -x = -1 := (Prod.mk.inj heq).2.symm
      exact hx1 (neg_inj.mp hneg)
  have hsub : (A ∪ B) ∪ C ⊆ (H ×ˢ H).filter (fun P => (1 + P.1 + P.2) ^ n = 1) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpAB | hpC
    · rcases Finset.mem_union.mp hpAB with hpA | hpB
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hpA
        simp only [Finset.mem_filter, Finset.mem_product, hm1H, hy, and_self, true_and,
          add_neg_cancel, zero_add]
        exact (hH y).mp hy
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpB
        have hxH : x ∈ H := Finset.mem_of_mem_erase hx
        simp only [Finset.mem_filter, Finset.mem_product, hxH, hm1H, and_self, true_and]
        rw [show (1 + x + -1 : F) = x by ring]
        exact (hH x).mp hxH
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpC
      have hxH : x ∈ H := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hnxH : -x ∈ H := (hH (-x)).mpr ((heven.neg_pow x).trans ((hH x).mp hxH))
      simp only [Finset.mem_filter, Finset.mem_product, hxH, hnxH, and_self, true_and]
      rw [show (1 + x + -x : F) = 1 by ring, one_pow]
  have hcard_union : ((A ∪ B) ∪ C).card = 3 * H.card - 3 := by
    rw [Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB,
      hA_card, hB_card, hC_card]
    omega
  rw [← hcard_union]
  exact Finset.card_le_card hsub

/-- **Exact `u = 1` multiplicity `normProfile H n 1 = 3 * H.card - 3` under weak Sidon.** -/
theorem normProfile_one_eq_of_sidon {F : Type*} [Field F] [DecidableEq F]
    {H : Finset F} {n : ℕ} (hn : 0 < n) (heven : Even n) (htwo : (2 : F) ≠ 0)
    (hH : ∀ x, x ∈ H ↔ x ^ n = 1)
    (hsidon : ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, ∀ d ∈ H,
      a + b = c + d → a + b = 0 ∨ a = c ∨ a = d) :
    normProfile H n 1 = 3 * H.card - 3 := by
  apply le_antisymm _ (normProfile_one_ge_three_card_sub_three hn heven htwo hH)
  have h1H : (1 : F) ∈ H := (hH 1).mpr (one_pow n)
  have hm1H : (-1 : F) ∈ H := (hH (-1)).mpr ((heven.neg_pow 1).trans (one_pow n))
  have h1_ne : (1 : F) ≠ -1 := by
    intro h
    apply htwo
    linear_combination h
  have hcard2 : 2 ≤ H.card := Finset.one_lt_card.mpr ⟨1, h1H, -1, hm1H, h1_ne⟩
  let A : Finset (F × F) := H.image (fun y => (-1, y))
  let B : Finset (F × F) := (H.erase (-1)).image (fun x => (x, -1))
  let C : Finset (F × F) := ((H.erase (-1)).erase 1).image (fun x => (x, -x))
  have hsub : (H ×ˢ H).filter (fun P => (1 + P.1 + P.2) ^ n = 1) ⊆ (A ∪ B) ∪ C := by
    intro p hp
    obtain ⟨hpH, hp1⟩ := Finset.mem_filter.mp hp
    obtain ⟨hxH, hyH⟩ := Finset.mem_product.mp hpH
    have hzH : 1 + p.1 + p.2 ∈ H := (hH _).mpr hp1
    have hrel : p.1 + p.2 = (1 + p.1 + p.2) + (-1) := by ring
    by_cases hx : p.1 = -1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨p.2, hyH, Prod.ext hx.symm rfl⟩))
    by_cases hy : p.2 = -1
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨p.1, Finset.mem_erase.mpr ⟨hx, hxH⟩, Prod.ext rfl hy.symm⟩))
    rcases hsidon p.1 hxH p.2 hyH (1 + p.1 + p.2) hzH (-1) hm1H hrel with h0 | heq | heq
    · have hy_eq : p.2 = -p.1 := eq_neg_of_add_eq_zero_right h0
      have hx1 : p.1 ≠ 1 := by
        intro h1
        exact hy (by rw [hy_eq, h1])
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨p.1, Finset.mem_erase.mpr ⟨hx1, Finset.mem_erase.mpr ⟨hx, hxH⟩⟩,
          Prod.ext rfl hy_eq.symm⟩)
    · exfalso
      apply hy
      linear_combination -heq
    · exact absurd heq hx
  have hA : A.card ≤ H.card := Finset.card_image_le
  have hB : B.card ≤ H.card - 1 :=
    le_trans Finset.card_image_le (le_of_eq (Finset.card_erase_of_mem hm1H))
  have h1_mem_erase : (1 : F) ∈ H.erase (-1) := Finset.mem_erase.mpr ⟨h1_ne, h1H⟩
  have hC : C.card ≤ H.card - 2 := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_erase_of_mem h1_mem_erase, Finset.card_erase_of_mem hm1H]
    omega
  calc normProfile H n 1
      ≤ ((A ∪ B) ∪ C).card := Finset.card_le_card hsub
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ A.card + B.card + C.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ H.card + (H.card - 1) + (H.card - 2) := by omega
    _ = 3 * H.card - 3 := by omega

/-! ## §2. `2.5×` sharper production occupied-bin floor via `u = 1` puncturing -/

/-- **Punctured `u = 1` Cauchy–Schwarz occupancy inequality.**
Isolating the `u = 1` bin from `occupiedBins H n` yields
`H.card * (H.card^2 - normProfile H n 1)^2 ≤ ((occupiedBins H n).card - 1) *
  (rEnergy H 3 - H.card * (normProfile H n 1)^2)`. -/
theorem punctured_one_occupancy_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {H : Finset F} {n : ℕ} (hn : 0 < n) (heven : Even n) (hH : ∀ x, x ∈ H ↔ x ^ n = 1) :
    1 ∈ occupiedBins H n ∧
      H.card * (normProfile H n 1) ^ 2 ≤ rEnergy H 3 ∧
      H.card * (H.card ^ 2 - normProfile H n 1) ^ 2
        ≤ ((occupiedBins H n).erase 1).card *
            (rEnergy H 3 - H.card * (normProfile H n 1) ^ 2) := by
  let U := occupiedBins H n
  let U₁ := U.erase 1
  let m := normProfile H n
  have h1H : (1 : F) ∈ H := (hH 1).mpr (one_pow n)
  have hm1H : (-1 : F) ∈ H := (hH (-1)).mpr ((heven.neg_pow 1).trans (one_pow n))
  have h1U : (1 : F) ∈ U := by
    refine Finset.mem_image.mpr ⟨(-1, 1), Finset.mem_product.mpr ⟨hm1H, h1H⟩, ?_⟩
    rw [show (1 + (-1 : F) + 1) = 1 by ring, one_pow]
  have hpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨1, h1H⟩
  have hmass : ∑ u ∈ U, m u = H.card ^ 2 := by
    simpa only [U, occupiedBins, m, normProfile, pow_two, Finset.card_product] using
      (Finset.card_eq_sum_card_image (fun P : F × F => (1 + P.1 + P.2) ^ n) (H ×ˢ H)).symm
  have hmass1 : m 1 + ∑ u ∈ U₁, m u = H.card ^ 2 := by
    rw [← hmass]
    exact Finset.add_sum_erase U m h1U
  have hmass_sub : ∑ u ∈ U₁, m u = H.card ^ 2 - m 1 := by omega
  have hcs : (H.card ^ 2 - m 1) ^ 2 ≤ U₁.card * ∑ u ∈ U₁, (m u) ^ 2 := by
    simpa only [one_mul, hmass_sub, one_pow, mul_one, Finset.sum_const, smul_eq_mul] using
      Finset.sum_mul_sq_le_sq_mul_sq U₁ (fun _ => (1 : ℕ)) m
  have h1_erase0 : (1 : F) ∈ (Finset.univ : Finset F).erase 0 :=
    Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ 1⟩
  have hU1_sub : U₁ ⊆ insert (0 : F) (((Finset.univ : Finset F).erase 0).erase 1) := by
    intro u hu
    have hu1 : u ≠ 1 := (Finset.mem_erase.mp hu).1
    by_cases hu0 : u = 0
    · subst hu0
      exact Finset.mem_insert_self (0 : F) _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hu1, Finset.mem_erase.mpr ⟨hu0, Finset.mem_univ u⟩⟩)
  have h0_notmem : (0 : F) ∉ ((Finset.univ : Finset F).erase 0).erase 1 := by
    intro h0
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp h0).2).1 rfl
  have hsq_le : ∑ u ∈ U₁, (m u) ^ 2 ≤ (m 0) ^ 2 +
      ∑ u ∈ ((Finset.univ : Finset F).erase 0).erase 1, (m u) ^ 2 := by
    calc ∑ u ∈ U₁, (m u) ^ 2
        ≤ ∑ u ∈ insert (0 : F) (((Finset.univ : Finset F).erase 0).erase 1), (m u) ^ 2 :=
          Finset.sum_le_sum_of_subset hU1_sub
      _ = (m 0) ^ 2 + ∑ u ∈ ((Finset.univ : Finset F).erase 0).erase 1, (m u) ^ 2 :=
          Finset.sum_insert h0_notmem
  have henergy : H.card * (m 1) ^ 2 + H.card * ∑ u ∈ U₁, (m u) ^ 2 ≤ rEnergy H 3 := by
    rw [rEnergy_three_eq_normProfile hn hH]
    change H.card * (m 1) ^ 2 + H.card * ∑ u ∈ U₁, (m u) ^ 2 ≤
      (H.card * m 0) ^ 2 + H.card * ∑ u ∈ (Finset.univ : Finset F).erase 0, (m u) ^ 2
    rw [← Finset.add_sum_erase ((Finset.univ : Finset F).erase 0) (fun u => (m u) ^ 2) h1_erase0]
    have hm0 : H.card * (m 0) ^ 2 ≤ (H.card * m 0) ^ 2 := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right ((m 0) ^ 2) (by nlinarith)
    have hmul := Nat.mul_le_mul_left H.card hsq_le
    linarith
  refine ⟨h1U, le_trans (Nat.le_add_right _ _) henergy, ?_⟩
  have hrem : H.card * ∑ u ∈ U₁, (m u) ^ 2 ≤ rEnergy H 3 - H.card * (m 1) ^ 2 := by omega
  calc H.card * (H.card ^ 2 - m 1) ^ 2
      ≤ H.card * (U₁.card * ∑ u ∈ U₁, (m u) ^ 2) := Nat.mul_le_mul_left H.card hcs
    _ = U₁.card * (H.card * ∑ u ∈ U₁, (m u) ^ 2) := by ring
    _ ≤ U₁.card * (rEnergy H 3 - H.card * (m 1) ^ 2) := Nat.mul_le_mul_left U₁.card hrem

/-- **`2.5×` sharper unconditional production occupied-bin bound (`192,153,582,490,528,435`).**
Under the exact same hypotheses `H.card = 2^30`, `H = μ_{2^30}`, `rEnergy H 3 ≤ 15 * (2^30)^3`
(in odd characteristic), puncturing `u = 1` improves `76,861,433,640,456,466` by `2.5×` with
zero additional four-term or Sidon assumptions. -/
theorem production_punctured_min_bins {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {H : Finset F} (htwo : (2 : F) ≠ 0) (hcard : H.card = 2 ^ 30)
    (hroots : ∀ x, x ∈ H ↔ x ^ (2 ^ 30 : ℕ) = 1)
    (henergy : rEnergy H 3 ≤ 15 * (2 ^ 30) ^ 3) :
    192153582490528435 ≤ (occupiedBins H (2 ^ 30)).card ∧
      192153582490528434 ≤ ((occupiedBins H (2 ^ 30)).erase 0).card := by
  have hn : 0 < (2 ^ 30 : ℕ) := by decide
  have heven : Even (2 ^ 30 : ℕ) := by decide
  obtain ⟨h1U, hm1_sq, hpunc⟩ := punctured_one_occupancy_bound hn heven hroots
  have hm1_lo := normProfile_one_ge_three_card_sub_three hn heven htwo hroots
  rw [hcard] at hm1_sq hpunc hm1_lo
  set t : ℕ := normProfile H (2 ^ 30) 1
  set d₁ : ℕ := ((occupiedBins H (2 ^ 30)).erase 1).card
  have ht_sq : t ^ 2 ≤ 15 * (2 ^ 30) ^ 2 := by
    have hmul : 2 ^ 30 * t ^ 2 ≤ 2 ^ 30 * (15 * (2 ^ 30) ^ 2) := by
      calc 2 ^ 30 * t ^ 2 ≤ rEnergy H 3 := hm1_sq
        _ ≤ 15 * (2 ^ 30) ^ 3 := henergy
        _ = 2 ^ 30 * (15 * (2 ^ 30) ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hn
  have ht_hi : t ≤ 4158584202 := by
    by_contra hgt
    push Not at hgt
    have hge : 4158584203 ≤ t := hgt
    have hsq : 4158584203 ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hge 2
    have hbad : 4158584203 ^ 2 ≤ 15 * (2 ^ 30) ^ 2 := le_trans hsq ht_sq
    norm_num at hbad
  have hpunc_step : ((2 ^ 30) ^ 2 - t) ^ 2 ≤ d₁ * (15 * (2 ^ 30) ^ 2 - t ^ 2) := by
    have hrem : rEnergy H 3 - 2 ^ 30 * t ^ 2 ≤ 2 ^ 30 * (15 * (2 ^ 30) ^ 2 - t ^ 2) := by omega
    have hmul : 2 ^ 30 * ((2 ^ 30) ^ 2 - t) ^ 2 ≤ 2 ^ 30 * (d₁ * (15 * (2 ^ 30) ^ 2 - t ^ 2)) := by
      calc 2 ^ 30 * ((2 ^ 30) ^ 2 - t) ^ 2
          ≤ d₁ * (rEnergy H 3 - 2 ^ 30 * t ^ 2) := hpunc
        _ ≤ d₁ * (2 ^ 30 * (15 * (2 ^ 30) ^ 2 - t ^ 2)) := Nat.mul_le_mul_left d₁ hrem
        _ = 2 ^ 30 * (d₁ * (15 * (2 ^ 30) ^ 2 - t ^ 2)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hn
  have hd1_ge : 192153582490528434 ≤ d₁ := by
    let N : ℤ := 2 ^ 30
    let tZ : ℤ := t
    let t₀ : ℤ := 3 * N - 3
    let A : ℤ := 6 * N ^ 2 + 18 * N - 9
    let B : ℤ := N ^ 2 - 3 * N + 3
    have ht_le_N2 : t ≤ (2 ^ 30) ^ 2 := le_trans ht_hi (by decide)
    have hZ_cs : (N ^ 2 - tZ) ^ 2 ≤ (d₁ : ℤ) * (15 * N ^ 2 - tZ ^ 2) := by
      have hcast : (((2 ^ 30) ^ 2 - t : ℕ) : ℤ) ^ 2 ≤
          (d₁ : ℤ) * ((15 * (2 ^ 30) ^ 2 - t ^ 2 : ℕ) : ℤ) := by exact_mod_cast hpunc_step
      rwa [Nat.cast_sub ht_le_N2, Nat.cast_sub ht_sq] at hcast
    have htZ_lo : t₀ ≤ tZ := by
      dsimp only [t₀, N, tZ]
      have hlo' : (3 * 2 ^ 30 - 3 : ℕ) ≤ t := hm1_lo
      omega
    have htZ_hi : tZ ≤ 4158584202 := by
      dsimp only [tZ]
      exact_mod_cast ht_hi
    have hdenom_pos : 0 < 15 * N ^ 2 - tZ ^ 2 := by
      have hZ_sq : tZ ^ 2 ≤ 4158584202 ^ 2 := by
        nlinarith [(Nat.cast_nonneg t : (0 : ℤ) ≤ tZ)]
      dsimp only [N]
      linarith [show (4158584202 : ℤ) ^ 2 < 15 * (2 ^ 30 : ℤ) ^ 2 by norm_num]
    have hid : A * (N ^ 2 - tZ) ^ 2 - B ^ 2 * (15 * N ^ 2 - tZ ^ 2) =
        (tZ - t₀) * (6 * N ^ 2 * (N - 6) * B + (A + B ^ 2) * (tZ - t₀)) := by
      dsimp only [A, B, t₀]
      ring
    have hA_pos : 0 < A := by dsimp only [A, N]; norm_num
    have hB_pos : 0 < B := by dsimp only [B, N]; norm_num
    have hN6 : 0 < 6 * N ^ 2 * (N - 6) * B := by dsimp only [N, B]; norm_num
    have hdiff_nonneg : 0 ≤ A * (N ^ 2 - tZ) ^ 2 - B ^ 2 * (15 * N ^ 2 - tZ ^ 2) := by
      rw [hid]
      exact mul_nonneg (sub_nonneg.mpr htZ_lo)
        (add_nonneg hN6.le (mul_nonneg (by positivity) (sub_nonneg.mpr htZ_lo)))
    have hmul_le : B ^ 2 * (15 * N ^ 2 - tZ ^ 2) ≤ (A * (d₁ : ℤ)) * (15 * N ^ 2 - tZ ^ 2) := by
      calc B ^ 2 * (15 * N ^ 2 - tZ ^ 2)
          ≤ A * (N ^ 2 - tZ) ^ 2 := by linarith
        _ ≤ A * ((d₁ : ℤ) * (15 * N ^ 2 - tZ ^ 2)) := mul_le_mul_of_nonneg_left hZ_cs hA_pos.le
        _ = (A * (d₁ : ℤ)) * (15 * N ^ 2 - tZ ^ 2) := by ring
    have hBA : B ^ 2 ≤ A * (d₁ : ℤ) := le_of_mul_le_mul_right hmul_le hdenom_pos
    dsimp only [A, B, N] at hBA
    norm_num at hBA
    omega
  have hcard_occ : d₁ + 1 = (occupiedBins H (2 ^ 30)).card :=
    Finset.card_erase_add_one h1U
  have hcard_erase0 : (occupiedBins H (2 ^ 30)).card - 1 ≤
      ((occupiedBins H (2 ^ 30)).erase 0).card := Finset.pred_card_le_card_erase
  omega

/-! ## §3. Finite-window polynomial-coefficient (holonomic) recurrence lower bound -/

/-- Weighted exponential trace `S_k = ∑_{u ∈ U} w(u) * u^k`. -/
def expTrace {F : Type*} [CommRing F] (U : Finset F) (w : F → F) (k : ℕ) : F :=
  ∑ u ∈ U, w u * u ^ k

/-- Left-shift linear endomorphism `f ↦ (j ↦ f (j + 1))` on sequences `ℕ → F`. -/
def shiftEnd (F : Type*) [CommRing F] : Module.End F (ℕ → F) where
  toFun f j := f (j + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shiftEnd_pow_apply {F : Type*} [CommRing F] (k : ℕ) (f : ℕ → F) (j : ℕ) :
    ((shiftEnd F ^ k) f) j = f (j + k) := by
  induction k generalizing j with
  | zero => simp only [pow_zero, Module.End.one_apply, Nat.add_zero]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change ((shiftEnd F ^ k) f) (j + 1) = f (j + (k + 1))
    rw [ih (j + 1)]
    exact congrArg f (by omega)

private theorem aeval_shiftEnd_X_sub_C {F : Type*} [CommRing F] (u : F) (f : ℕ → F) (j : ℕ) :
    ((Polynomial.aeval (shiftEnd F) (X - C u)) f) j = f (j + 1) - u * f j := by
  simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

private theorem aeval_X_sub_C_pow_monomial {F : Type*} [CommRing F] (u : F) (m : ℕ) :
    Polynomial.aeval (shiftEnd F) ((X - C u) ^ (m + 1))
      (fun j : ℕ => u ^ j * (j : F) ^ m) = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    let g (s : ℕ) : ℕ → F := fun j => u ^ j * (j : F) ^ s
    have hstep : Polynomial.aeval (shiftEnd F) (X - C u) (g m) =
        ∑ s ∈ Finset.range m, ((m.choose s : F) * u) • g s := by
      ext j
      rw [aeval_shiftEnd_X_sub_C, Finset.sum_apply]
      simp only [g, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
      have hbinom : ((j : F) + 1) ^ m - (j : F) ^ m =
          ∑ s ∈ Finset.range m, (j : F) ^ s * (m.choose s : F) := by
        rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self,
          Nat.cast_one, mul_one, add_sub_cancel_right]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [one_pow, mul_one]
      calc u ^ (j + 1) * ((j : F) + 1) ^ m - u * (u ^ j * (j : F) ^ m)
          = u * u ^ j * (((j : F) + 1) ^ m - (j : F) ^ m) := by rw [pow_succ']; ring
        _ = u * u ^ j * ∑ s ∈ Finset.range m, (j : F) ^ s * (m.choose s : F) := by rw [hbinom]
        _ = ∑ s ∈ Finset.range m, (m.choose s : F) * u * (u ^ j * (j : F) ^ s) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun s _ => by ring)
    change Polynomial.aeval (shiftEnd F) ((X - C u) ^ (m + 1)) (g m) = 0
    rw [pow_succ, map_mul, Module.End.mul_apply, hstep, map_sum]
    refine Finset.sum_eq_zero (fun s hs => ?_)
    rw [map_smul]
    have hsm : s < m := Finset.mem_range.mp hs
    have hsplit : m = (m - (s + 1)) + (s + 1) := by omega
    rw [hsplit, pow_add, map_mul, Module.End.mul_apply, ih s hsm, map_zero, smul_zero]

private theorem aeval_X_sub_C_pow_poly {F : Type*} [CommRing F] (u : F) {Q : F[X]} {b : ℕ}
    (hQ : Q.natDegree ≤ b) :
    Polynomial.aeval (shiftEnd F) ((X - C u) ^ (b + 1))
      (fun j : ℕ => u ^ j * Q.eval (j : F)) = 0 := by
  have hexp : (fun j : ℕ => u ^ j * Q.eval (j : F)) =
      ∑ s ∈ Finset.range (b + 1), Q.coeff s • (fun j : ℕ => u ^ j * (j : F) ^ s) := by
    ext j
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ) (j : F), Finset.mul_sum,
      Finset.sum_apply]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexp, map_sum]
  refine Finset.sum_eq_zero (fun s hs => ?_)
  rw [map_smul]
  have hsb : s + 1 ≤ b + 1 := Finset.mem_range.mp hs
  have hsplit : b + 1 = (b + 1 - (s + 1)) + (s + 1) := by omega
  rw [hsplit, pow_add, map_mul, Module.End.mul_apply, aeval_X_sub_C_pow_monomial u s,
    map_zero, smul_zero]

private theorem monic_shift_propagate {F : Type*} [CommRing F] {M : F[X]} (hM : M.Monic)
    {f : ℕ → F} (hann : Polynomial.aeval (shiftEnd F) M f = 0)
    (hinit : ∀ j < M.natDegree, f j = 0) :
    ∀ n : ℕ, f n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < M.natDegree
    · exact hinit n hlt
    · let j := n - M.natDegree
      have hjn : j + M.natDegree = n := by omega
      have hj0 : ((Polynomial.aeval (shiftEnd F) M) f) j = 0 := by rw [hann]; rfl
      rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply] at hj0
      have hterms : ∀ k ∈ Finset.range (M.natDegree + 1),
          ((M.coeff k • shiftEnd F ^ k) f) j = M.coeff k * f (j + k) := by
        intro k _
        rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, shiftEnd_pow_apply]
      rw [Finset.sum_congr rfl hterms, Finset.sum_range_succ] at hj0
      have hlow : ∑ k ∈ Finset.range M.natDegree, M.coeff k * f (j + k) = 0 := by
        refine Finset.sum_eq_zero (fun k hk => ?_)
        have hklt : j + k < n := by
          have := Finset.mem_range.mp hk
          omega
        rw [ih (j + k) hklt, mul_zero]
      rw [hlow, zero_add, hM.coeff_natDegree, one_mul, hjn] at hj0
      exact hj0

/-- **Finite-window polynomial-coefficient (holonomic) recurrence lower bound.**
Let `U ⊆ (ZMod p)^×` be nonzero nodes with nonzero weights `w u ≠ 0`, and let
`A : Fin (r + 1) → (ZMod p)[X]` have `natDegree ≤ b < p` with some `A i₀ ≠ 0`.
If `∑_{i=0}^r A_i(j) * expTrace U w (j + i) = 0` on the finite window `0 ≤ j < |U| * (b + 1)`,
then `|U| ≤ r`. -/
theorem finite_window_poly_recurrence_degree {p r b : ℕ} [Fact p.Prime]
    (U : Finset (ZMod p)) (w : ZMod p → ZMod p)
    (hw : ∀ u ∈ U, w u ≠ 0) (hu : ∀ u ∈ U, u ≠ 0)
    (A : Fin (r + 1) → (ZMod p)[X])
    (hdeg : ∀ i, (A i).natDegree ≤ b) (hb : b < p)
    (hne : ∃ i, A i ≠ 0)
    (hwin : ∀ j < U.card * (b + 1),
      ∑ i : Fin (r + 1), (A i).eval (j : ZMod p) * expTrace U w (j + i.val) = 0) :
    U.card ≤ r := by
  classical
  let T : ℕ → ZMod p := fun j =>
    ∑ i : Fin (r + 1), (A i).eval (j : ZMod p) * expTrace U w (j + i.val)
  let Q (u : ZMod p) : (ZMod p)[X] :=
    ∑ i : Fin (r + 1), C (w u * u ^ i.val) * A i
  have hQ_deg (u : ZMod p) : (Q u).natDegree ≤ b := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (hdeg i)
  have hT_eq : T = ∑ u ∈ U, (fun j : ℕ => u ^ j * (Q u).eval (j : ZMod p)) := by
    ext j
    simp only [T, expTrace, Finset.mul_sum, Finset.sum_apply, Q, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    exact Finset.sum_congr rfl (fun i _ => by rw [pow_add]; ring)
  let M : (ZMod p)[X] := ∏ u ∈ U, (X - C u) ^ (b + 1)
  have hM_monic : M.Monic :=
    Polynomial.monic_prod_of_monic U _ (fun u _ => (Polynomial.monic_X_sub_C u).pow (b + 1))
  have hM_deg : M.natDegree = U.card * (b + 1) := by
    rw [Polynomial.natDegree_prod_of_monic U _
      (fun u _ => (Polynomial.monic_X_sub_C u).pow (b + 1))]
    have h1 : ∀ u ∈ U, ((X - C u) ^ (b + 1)).natDegree = b + 1 := by
      intro u _
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul]
  have hM_ann : Polynomial.aeval (shiftEnd (ZMod p)) M T = 0 := by
    rw [hT_eq, map_sum]
    refine Finset.sum_eq_zero (fun u huU => ?_)
    obtain ⟨K, hK⟩ := Finset.dvd_prod_of_mem (fun v => (X - C v) ^ (b + 1)) huU
    dsimp only [M]
    rw [hK, mul_comm, map_mul, Module.End.mul_apply,
      aeval_X_sub_C_pow_poly u (hQ_deg u), map_zero]
  have hT_all : ∀ n : ℕ, T n = 0 :=
    monic_shift_propagate hM_monic hM_ann (by rwa [hM_deg])
  obtain ⟨i₀, hi₀⟩ := hne
  have hex_a : ∃ a : ZMod p, (A i₀).eval a ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hi₀
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (A i₀) Finset.univ
      (fun a _ => hall a) (by rw [Finset.card_univ, ZMod.card]; exact lt_of_le_of_lt (hdeg i₀) hb)
  obtain ⟨a, ha0⟩ := hex_a
  let Pa : (ZMod p)[X] := ∑ i : Fin (r + 1), C ((A i).eval a) * X ^ i.val
  have hPa_ne : Pa ≠ 0 := by
    intro h0
    apply ha0
    have hc := congrArg (fun P => P.coeff i₀.val) h0
    simp only [Pa, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Polynomial.coeff_zero] at hc
    have huniq : (∑ x : Fin (r + 1), if i₀.val = x.val then (A x).eval a else 0) =
        (A i₀).eval a := by
      have heq : ∀ x : Fin (r + 1),
          (if i₀.val = x.val then (A x).eval a else 0) =
            (if i₀ = x then (A x).eval a else 0) := by
        intro x
        by_cases h : i₀ = x
        · subst h
          simp only [ite_true]
        · have hv : i₀.val ≠ x.val := fun hv => h (Fin.ext hv)
          simp only [h, hv, ite_false]
      rw [Finset.sum_congr rfl (fun x _ => heq x),
        Finset.sum_ite_eq Finset.univ i₀ (fun x => (A x).eval a)]
      simp only [Finset.mem_univ, ite_true]
    exact huniq.symm.trans hc
  have hPa_deg : Pa.natDegree ≤ r := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    calc (C ((A i).eval a) * X ^ i.val).natDegree
        ≤ (C ((A i).eval a)).natDegree + (X ^ i.val : (ZMod p)[X]).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 0 + i.val := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      _ ≤ r := by omega
  have hPa_roots : ∀ u ∈ U, Pa.eval u = 0 := by
    let e : Fin U.card ≃ U := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
    let nd (m : Fin U.card) : ZMod p := (e m).val
    let cf (m : Fin U.card) : ZMod p := w (nd m) * (nd m) ^ a.val * Pa.eval (nd m)
    have hvand (k : Fin U.card) : ∑ m : Fin U.card, cf m * (nd m) ^ k.val = 0 := by
      have hTk := hT_all (a.val + p * k.val)
      have hmod : ((a.val + p * k.val : ℕ) : ZMod p) = a := by
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
          ZMod.natCast_zmod_val]
      have hexpand : T (a.val + p * k.val) =
          ∑ u ∈ U, (w u * u ^ a.val * Pa.eval u) * u ^ k.val := by
        simp only [T, hmod, expTrace, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        simp only [Pa, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hpow : u ^ (a.val + p * k.val + i.val) = u ^ a.val * u ^ i.val * u ^ k.val := by
          rw [show a.val + p * k.val + i.val = a.val + i.val + p * k.val by omega,
            pow_add, pow_add, pow_mul, ZMod.pow_card]
        rw [hpow]
        ring
      rw [hexpand, ← Finset.sum_coe_sort U] at hTk
      exact (e.sum_comp
        (fun u : U => (w u.val * u.val ^ a.val * Pa.eval u.val) * u.val ^ k.val)).trans hTk
    have hcf0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := nd) (v := cf) (Subtype.val_injective.comp e.injective) hvand
    intro u huU
    let m := e.symm ⟨u, huU⟩
    have hnd : nd m = u := by simp [nd, m]
    have hzero : cf m = 0 := congrFun hcf0 m
    have hw_ne : w u * u ^ a.val ≠ 0 := mul_ne_zero (hw u huU) (pow_ne_zero _ (hu u huU))
    exact (mul_eq_zero.mp (by simpa only [cf, hnd] using hzero)).resolve_left hw_ne
  by_contra hlt
  push Not at hlt
  exact hPa_ne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Pa U hPa_roots
    (lt_of_le_of_lt hPa_deg hlt))

/-- **Production finite-window holonomic recurrence lower bound (`r ≥ 192,153,582,490,528,434`).**
For any prime `p > 2^60` (in particular both `P₁` and `P₂`), if `H = μ_{2^30} ⊂ ZMod p` satisfies
`rEnergy H 3 ≤ 15 * (2^30)^3`, then every nonzero polynomial-coefficient recurrence of coefficient
degree `≤ b < p` annihilating the nonzero-bin normalized trace on its initial `|U| * (b + 1)`
samples must have recurrence order `r ≥ 192,153,582,490,528,434`. -/
theorem production_holonomic_window_recurrence_degree {p r b : ℕ} [Fact p.Prime]
    (hp : 2 ^ 60 < p) {H : Finset (ZMod p)} (hcard : H.card = 2 ^ 30)
    (hroots : ∀ x, x ∈ H ↔ x ^ (2 ^ 30 : ℕ) = 1)
    (henergy : rEnergy H 3 ≤ 15 * (2 ^ 30) ^ 3)
    (A : Fin (r + 1) → (ZMod p)[X])
    (hdeg : ∀ i, (A i).natDegree ≤ b) (hb : b < p) (hne : ∃ i, A i ≠ 0)
    (hwin : ∀ j < ((occupiedBins H (2 ^ 30)).erase 0).card * (b + 1),
      ∑ i : Fin (r + 1), (A i).eval (j : ZMod p) *
        expTrace ((occupiedBins H (2 ^ 30)).erase 0)
          (fun u => (normProfile H (2 ^ 30) u : ZMod p)) (j + i.val) = 0) :
    192153582490528434 ≤ r := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  have hbins := (production_punctured_min_bins htwo hcard hroots henergy).2
  refine le_trans hbins ?_
  refine finite_window_poly_recurrence_degree ((occupiedBins H (2 ^ 30)).erase 0)
    (fun u => (normProfile H (2 ^ 30) u : ZMod p)) ?_ ?_ A hdeg hb hne hwin
  · intro u hu hzero
    have hu_occ : u ∈ occupiedBins H (2 ^ 30) := Finset.mem_of_mem_erase hu
    obtain ⟨P, hP, hPu⟩ := Finset.mem_image.mp hu_occ
    have hpos : 0 < normProfile H (2 ^ 30) u :=
      Finset.card_pos.mpr ⟨P, Finset.mem_filter.mpr ⟨hP, hPu⟩⟩
    have hmax : normProfile H (2 ^ 30) u ≤ 2 ^ 60 := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Finset.card_product, hcard]
      decide
    have hdvd := (ZMod.natCast_eq_zero_iff _ p).mp hzero
    exact not_le_of_gt (lt_of_le_of_lt hmax hp) (Nat.le_of_dvd hpos hdvd)
  · intro u hu
    exact (Finset.mem_erase.mp hu).1

/-! ## §4. Cross-coset `2+2+2` S-unit / Sidon reduction and `μ_4`-coset occupancy `≥ 5` -/

/-- **Cross-coset `2+2+2` S-unit line reduction.** Any zero-sum sextuple formed by three pairs
`(a_j, a_j u_j)` with `a_j^n = 1` reduces via `z₁ = a₁ / a₃, z₂ = a₂ / a₃` to the normalized
two-root equation `(1 + u₁) z₁ + (1 + u₂) z₂ + (1 + u₃) = 0`. -/
theorem crossCoset_two_two_two_sunit {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0)
    {a₁ a₂ a₃ u₁ u₂ u₃ : F} (ha₁ : a₁ ^ n = 1) (ha₂ : a₂ ^ n = 1) (ha₃ : a₃ ^ n = 1)
    (hsum : a₁ + a₁ * u₁ + a₂ + a₂ * u₂ + a₃ + a₃ * u₃ = 0) :
    (a₁ / a₃) ^ n = 1 ∧ (a₂ / a₃) ^ n = 1 ∧
      (1 + u₁) * (a₁ / a₃) + (1 + u₂) * (a₂ / a₃) + (1 + u₃) = 0 := by
  have ha₃0 : a₃ ≠ 0 := by
    rintro rfl
    simp only [zero_pow hn, zero_ne_one] at ha₃
  refine ⟨by rw [div_pow, ha₁, ha₃, div_one], by rw [div_pow, ha₂, ha₃, div_one], ?_⟩
  field_simp [ha₃0]
  linear_combination hsum

/-- Conjugate / inverse subgroup ratios share the exact same projective pair signature:
`(1 + u⁻¹)^n = (1 + u)^n` for any `u^n = 1` (`n ≠ 0`). -/
theorem pair_signature_inv_eq {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0) {u : F}
    (hu : u ^ n = 1) :
    (1 + u⁻¹) ^ n = (1 + u) ^ n := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp only [zero_pow hn, zero_ne_one] at hu
  have hrel : 1 + u⁻¹ = (1 + u) / u := by
    field_simp [hu0]
    ring
  rw [hrel, div_pow, hu, div_one]

/-- **Sidon cap (`≤ 2` solutions) for equal- or conjugate-gap cross-coset `2+2+2` sextuples.**
Whenever `(1 + u₁)^n = (1 + u₂)^n` (including `u₂ = u₁` and `u₂ = u₁⁻¹`), `1 + u₁ ≠ 0`,
`1 + u₃ ≠ 0`, and `μ_n` satisfies the weak Sidon law, at most two normalized root pairs
`(z₁, z₂) ∈ μ_n × μ_n` can solve `(1 + u₁) z₁ + (1 + u₂) z₂ + (1 + u₃) = 0`. -/
theorem crossCoset_two_two_two_sidon_cap {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0)
    {u₁ u₂ u₃ z₁ z₂ w₁ w₂ : F}
    (hsig : (1 + u₁) ^ n = (1 + u₂) ^ n)
    (hu₁ : 1 + u₁ ≠ 0) (hu₃ : 1 + u₃ ≠ 0)
    (hsidon : ∀ a b c d : F, a ^ n = 1 → b ^ n = 1 → c ^ n = 1 → d ^ n = 1 →
      a + b = c + d → a + b = 0 ∨ a = c ∨ a = d)
    (hz₁ : z₁ ^ n = 1) (hz₂ : z₂ ^ n = 1) (hw₁ : w₁ ^ n = 1) (hw₂ : w₂ ^ n = 1)
    (hsol_z : (1 + u₁) * z₁ + (1 + u₂) * z₂ + (1 + u₃) = 0)
    (hsol_w : (1 + u₁) * w₁ + (1 + u₂) * w₂ + (1 + u₃) = 0) :
    let c := (1 + u₂) / (1 + u₁)
    (z₁ = w₁ ∧ z₂ = w₂) ∨ (z₁ = c * w₂ ∧ c * z₂ = w₁) := by
  dsimp only
  set c : F := (1 + u₂) / (1 + u₁)
  have hc_pow : c ^ n = 1 := by
    dsimp only [c]
    rw [div_pow, ← hsig, div_self (pow_ne_zero n hu₁)]
  have hcz : (c * z₂) ^ n = 1 := by rw [mul_pow, hc_pow, hz₂, one_mul]
  have hcw : (c * w₂) ^ n = 1 := by rw [mul_pow, hc_pow, hw₂, one_mul]
  have heq_sum : z₁ + c * z₂ = w₁ + c * w₂ := by
    dsimp only [c]
    field_simp [hu₁]
    linear_combination hsol_z - hsol_w
  have hnz_sum : z₁ + c * z₂ ≠ 0 := by
    intro h0
    apply hu₃
    have hmul : (1 + u₁) * (z₁ + c * z₂) = (1 + u₁) * z₁ + (1 + u₂) * z₂ := by
      dsimp only [c]
      field_simp [hu₁]
    rw [h0, mul_zero] at hmul
    linear_combination hsol_z + hmul
  rcases hsidon z₁ (c * z₂) w₁ (c * w₂) hz₁ hcz hw₁ hcw heq_sum with h0 | h1 | h2
  · exact absurd h0 hnz_sum
  · left
    have hc0 : c ≠ 0 := by
      intro h0
      have hu2 : 1 + u₂ = 0 := by
        dsimp only [c] at h0
        exact (div_eq_zero_iff.mp h0).resolve_right hu₁
      rw [hu2] at hsig
      exact pow_ne_zero n hu₁ (hsig.trans (zero_pow hn))
    exact ⟨h1, mul_left_cancel₀ hc0 (add_left_cancel (h1 ▸ heq_sum))⟩
  · right
    exact ⟨h2, add_left_cancel ((h2 ▸ heq_sum).trans (add_comm _ _))⟩

/-- Every antipode-free subset `S ⊆ μ_n` (`0 < n`) intersects each `μ_4`-coset (`x^4 = q`) in at
most `2` elements. -/
theorem quarterCoset_fiber_card_le_two {F : Type*} [Field F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {i : F} (hi : i ^ 2 = -1)
    {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) (hanti : ∀ x ∈ S, -x ∉ S) (q : F) :
    (S.filter (fun x => x ^ 4 = q)).card ≤ 2 := by
  set Fq := S.filter (fun x => x ^ 4 = q)
  by_cases hne : Fq.Nonempty
  · obtain ⟨a, haFq⟩ := hne
    obtain ⟨haS, haq⟩ := Finset.mem_filter.mp haFq
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hz := hS 0 haS
      simp only [zero_pow hn.ne', zero_ne_one] at hz
    by_cases hai : a * i ∈ S
    · have hsub : Fq ⊆ {a, a * i} := by
        intro x hxFq
        obtain ⟨hxS, hxq⟩ := Finset.mem_filter.mp hxFq
        have hrat : (x / a) ^ 4 = 1 := by
          rw [div_pow, hxq, ← haq, div_self (pow_ne_zero 4 ha0)]
        have hfac : (x / a - 1) * (x / a + 1) * (x / a - i) * (x / a + i) = 0 := by
          calc (x / a - 1) * (x / a + 1) * (x / a - i) * (x / a + i)
              = ((x / a) ^ 2 - 1) * ((x / a) ^ 2 - i ^ 2) := by ring
            _ = (x / a) ^ 4 - 1 := by rw [hi]; ring
            _ = 0 := sub_eq_zero.mpr hrat
        rcases mul_eq_zero.mp hfac with h123 | h4
        · rcases mul_eq_zero.mp h123 with h12 | h3
          · rcases mul_eq_zero.mp h12 with h1 | h2
            · have hx_eq : x = a := (div_eq_one_iff_eq ha0).mp (sub_eq_zero.mp h1)
              simp [hx_eq]
            · exfalso
              have hx_eq : x = -a := by
                have hd : x / a = -1 := eq_neg_of_add_eq_zero_left h2
                simpa using (div_eq_iff ha0).mp hd
              exact hanti a haS (hx_eq ▸ hxS)
          · have hx_eq : x = a * i := by
              have hd : x / a = i := sub_eq_zero.mp h3
              simpa [mul_comm] using (div_eq_iff ha0).mp hd
            simp [hx_eq]
        · exfalso
          have hx_eq : x = -(a * i) := by
            have hd : x / a = -i := eq_neg_of_add_eq_zero_left h4
            have hm := (div_eq_iff ha0).mp hd
            linear_combination hm
          exact hanti (a * i) hai (hx_eq ▸ hxS)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le a {a * i})
    · have hsub : Fq ⊆ {a, -(a * i)} := by
        intro x hxFq
        obtain ⟨hxS, hxq⟩ := Finset.mem_filter.mp hxFq
        have hrat : (x / a) ^ 4 = 1 := by
          rw [div_pow, hxq, ← haq, div_self (pow_ne_zero 4 ha0)]
        have hfac : (x / a - 1) * (x / a + 1) * (x / a - i) * (x / a + i) = 0 := by
          calc (x / a - 1) * (x / a + 1) * (x / a - i) * (x / a + i)
              = ((x / a) ^ 2 - 1) * ((x / a) ^ 2 - i ^ 2) := by ring
            _ = (x / a) ^ 4 - 1 := by rw [hi]; ring
            _ = 0 := sub_eq_zero.mpr hrat
        rcases mul_eq_zero.mp hfac with h123 | h4
        · rcases mul_eq_zero.mp h123 with h12 | h3
          · rcases mul_eq_zero.mp h12 with h1 | h2
            · have hx_eq : x = a := (div_eq_one_iff_eq ha0).mp (sub_eq_zero.mp h1)
              simp [hx_eq]
            · exfalso
              have hx_eq : x = -a := by
                have hd : x / a = -1 := eq_neg_of_add_eq_zero_left h2
                simpa using (div_eq_iff ha0).mp hd
              exact hanti a haS (hx_eq ▸ hxS)
          · exfalso
            have hx_eq : x = a * i := by
              have hd : x / a = i := sub_eq_zero.mp h3
              simpa [mul_comm] using (div_eq_iff ha0).mp hd
            exact hai (hx_eq ▸ hxS)
        · have hx_eq : x = -(a * i) := by
            have hd : x / a = -i := eq_neg_of_add_eq_zero_left h4
            have hm := (div_eq_iff ha0).mp hd
            linear_combination hm
          simp [hx_eq]
      exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le a {-(a * i)})
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    decide

/-- **Complete `μ_4`-coset occupancy elimination (`≥ 5` cosets for every nodup non-pairable
sextuple).** Rules out `6`, `5+1`, `4+2`, `4+1+1`, `3+3`, `3+2+1`, `2+2+2`, and `2+2+1+1`,
leaving only `2+1+1+1+1` and `1+1+1+1+1+1`. -/
theorem quarterCoset_occupancy_at_least_five {F : Type*} [Field F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {i : F} (hi : i ^ 2 = -1)
    {S : Finset F} (hcard : S.card = 6) (hS : ∀ x ∈ S, x ^ n = 1)
    (hanti : ∀ x ∈ S, -x ∉ S) (hsum : ∑ x ∈ S, x = 0)
    (htwoPairs : ∀ a b u v z w : F,
      a ^ n = 1 → b ^ n = 1 → u ^ 4 = 1 → v ^ 4 = 1 → z ^ n = 1 → w ^ n = 1 →
      a + a * u + z + (b + b * v + w) = 0 →
      ∃ p ∈ ({a, a * u, z, b, b * v, w} : Finset F),
        -p ∈ ({a, a * u, z, b, b * v, w} : Finset F)) :
    5 ≤ (S.image (fun x => x ^ 4)).card := by
  set Q := S.image (fun x => x ^ 4)
  let Fq (q : F) := S.filter (fun x => x ^ 4 = q)
  have hmax (q : F) : (Fq q).card ≤ 2 := quarterCoset_fiber_card_le_two hn hi hS hanti q
  have hat_most_one_two : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, 2 ≤ (Fq q₁).card → 2 ≤ (Fq q₂).card → q₁ = q₂ := by
    intro q₁ _ q₂ _ h2₁ h2₂
    by_contra hne
    have hc₁ : (Fq q₁).card = 2 := le_antisymm (hmax q₁) h2₁
    have hc₂ : (Fq q₂).card = 2 := le_antisymm (hmax q₂) h2₂
    obtain ⟨x₁, y₁, hxy₁, hF₁⟩ := Finset.card_eq_two.mp hc₁
    obtain ⟨x₂, y₂, hxy₂, hF₂⟩ := Finset.card_eq_two.mp hc₂
    have hdisj12 : Disjoint (Fq q₁) (Fq q₂) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hne (((Finset.mem_filter.mp hx₁).2).symm.trans (Finset.mem_filter.mp hx₂).2)
    have hsub12 : Fq q₁ ∪ Fq q₂ ⊆ S :=
      Finset.union_subset (Finset.filter_subset _ S) (Finset.filter_subset _ S)
    have hc12 : (Fq q₁ ∪ Fq q₂).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj12, hc₁, hc₂]
    set R := S \ (Fq q₁ ∪ Fq q₂)
    have hcR : R.card = 2 := by
      have hsdiff := Finset.card_sdiff_add_card_eq_card hsub12
      change R.card + (Fq q₁ ∪ Fq q₂).card = S.card at hsdiff
      omega
    obtain ⟨z, w, hzw, hR⟩ := Finset.card_eq_two.mp hcR
    have hunion : R ∪ (Fq q₁ ∪ Fq q₂) = S := Finset.sdiff_union_of_subset hsub12
    have hsum_parts : (z + w) + ((x₁ + y₁) + (x₂ + y₂)) = 0 := by
      rw [← hsum, ← hunion,
        Finset.sum_union (show Disjoint R (Fq q₁ ∪ Fq q₂) from Finset.sdiff_disjoint),
        Finset.sum_union hdisj12, hR, hF₁, hF₂,
        Finset.sum_pair hzw, Finset.sum_pair hxy₁, Finset.sum_pair hxy₂]
    have hx₁F : x₁ ∈ Fq q₁ := hF₁ ▸ Finset.mem_insert_self x₁ {y₁}
    have hy₁F : y₁ ∈ Fq q₁ := hF₁ ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y₁)
    have hx₂F : x₂ ∈ Fq q₂ := hF₂ ▸ Finset.mem_insert_self x₂ {y₂}
    have hy₂F : y₂ ∈ Fq q₂ := hF₂ ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y₂)
    have hzS : z ∈ S := Finset.sdiff_subset (hR ▸ Finset.mem_insert_self z {w})
    have hwS : w ∈ S := Finset.sdiff_subset
      (hR ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
    have hx₁S : x₁ ∈ S := (Finset.mem_filter.mp hx₁F).1
    have hy₁S : y₁ ∈ S := (Finset.mem_filter.mp hy₁F).1
    have hx₂S : x₂ ∈ S := (Finset.mem_filter.mp hx₂F).1
    have hy₂S : y₂ ∈ S := (Finset.mem_filter.mp hy₂F).1
    have hx₁0 : x₁ ≠ 0 := by
      rintro rfl
      have hz0 := hS 0 hx₁S
      simp only [zero_pow hn.ne', zero_ne_one] at hz0
    have hx₂0 : x₂ ≠ 0 := by
      rintro rfl
      have hz0 := hS 0 hx₂S
      simp only [zero_pow hn.ne', zero_ne_one] at hz0
    let u := y₁ / x₁
    let v := y₂ / x₂
    have hu4 : u ^ 4 = 1 := by
      dsimp only [u]
      rw [div_pow, (Finset.mem_filter.mp hy₁F).2, ← (Finset.mem_filter.mp hx₁F).2,
        div_self (pow_ne_zero 4 hx₁0)]
    have hv4 : v ^ 4 = 1 := by
      dsimp only [v]
      rw [div_pow, (Finset.mem_filter.mp hy₂F).2, ← (Finset.mem_filter.mp hx₂F).2,
        div_self (pow_ne_zero 4 hx₂0)]
    have hxu : x₁ * u = y₁ := mul_div_cancel₀ y₁ hx₁0
    have hxv : x₂ * v = y₂ := mul_div_cancel₀ y₂ hx₂0
    have hzero6 : x₁ + x₁ * u + z + (x₂ + x₂ * v + w) = 0 := by
      rw [hxu, hxv]
      linear_combination hsum_parts
    obtain ⟨p, hp_in, hnp_in⟩ := htwoPairs x₁ x₂ u v z w
      (hS x₁ hx₁S) (hS x₂ hx₂S) hu4 hv4 (hS z hzS) (hS w hwS) hzero6
    have hsub6 : ({x₁, x₁ * u, z, x₂, x₂ * v, w} : Finset F) ⊆ S := by
      rw [hxu, hxv]
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx₁S
      · exact hy₁S
      · exact hzS
      · exact hx₂S
      · exact hy₂S
      · exact hwS
    exact hanti p (hsub6 hp_in) (hsub6 hnp_in)
  have hpart : 6 = ∑ q ∈ Q, (Fq q).card := by
    rw [← hcard]
    exact Finset.card_eq_sum_card_image (fun x => x ^ 4) S
  by_cases hex2 : ∃ q₀ ∈ Q, 2 ≤ (Fq q₀).card
  · obtain ⟨q₀, hq₀Q, h2₀⟩ := hex2
    have hsplit := (Finset.add_sum_erase Q (fun q => (Fq q).card) hq₀Q).symm
    have herase_le : ∑ q ∈ Q.erase q₀, (Fq q).card ≤ (Q.erase q₀).card := by
      calc ∑ q ∈ Q.erase q₀, (Fq q).card
          ≤ ∑ _q ∈ Q.erase q₀, 1 := by
            refine Finset.sum_le_sum (fun q hq => ?_)
            obtain ⟨hq_ne, hqQ⟩ := Finset.mem_erase.mp hq
            by_contra hgt1
            push Not at hgt1
            exact hq_ne (hat_most_one_two q hqQ q₀ hq₀Q hgt1 h2₀)
        _ = (Q.erase q₀).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hcardQ : (Q.erase q₀).card + 1 = Q.card := Finset.card_erase_add_one hq₀Q
    have h2_le : (Fq q₀).card ≤ 2 := hmax q₀
    omega
  · push Not at hex2
    have hall_le : ∑ q ∈ Q, (Fq q).card ≤ Q.card := by
      calc ∑ q ∈ Q, (Fq q).card
          ≤ ∑ _q ∈ Q, 1 := Finset.sum_le_sum (fun q hq => Nat.le_of_lt_succ (hex2 q hq))
        _ = Q.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    omega

/-! ## §5. Coset-reduced sixth-moment period bound and designated-prime specializations -/

/-- **Coset-reduced sixth-moment period bound on `H = μ_n`.**
Whenever `rEnergy H 3 ≤ 15 * n^3`, every nonzero frequency `b₀ ≠ 0` satisfies
`‖eta ψ H b₀‖^6 ≤ 15 * |F| * n^2`. -/
theorem cosetReduced_sixthMoment_eta_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {H : Finset F} {n : ℕ}
    (hn : 0 < n) (hcard : H.card = n) (hH : ∀ x, x ∈ H ↔ x ^ n = 1)
    (henergy : rEnergy H 3 ≤ 15 * n ^ 3) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ H b₀‖ ^ 6 ≤ 15 * (Fintype.card F : ℝ) * (n : ℝ) ^ 2 := by
  have h0 : (0 : F) ∉ H := by
    intro hmem
    simpa only [zero_pow hn.ne', zero_ne_one] using (hH 0).mp hmem
  have hmul : ∀ a ∈ H, ∀ c ∈ H, a * c ∈ H := by
    intro a ha c hc
    exact (hH (a * c)).mpr (by rw [mul_pow, (hH a).mp ha, (hH c).mp hc, one_mul])
  have hbij : ∀ u ∈ H, H.image (fun y => u * y) = H :=
    fun u hu => image_mul_self_of_mem H hu hmul h0
  have hne : H.Nonempty := ⟨1, (hH 1).mpr (one_pow n)⟩
  have hcos := cosetReduced_eta_pow_le hψ hbij h0 hne 3 hb₀
  simp only [show 2 * 3 = 6 by rfl, hcard] at hcos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hleR : (rEnergy H 3 : ℝ) ≤ 15 * (n : ℝ) ^ 3 := by exact_mod_cast henergy
  have hnum : (Fintype.card F : ℝ) * (rEnergy H 3 : ℝ) - (n : ℝ) ^ 6
      ≤ (15 * (Fintype.card F : ℝ) * (n : ℝ) ^ 2) * (n : ℝ) := by
    have hF0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
    have hn6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hleR hF0]
  exact le_trans hcos ((div_le_iff₀ hn_pos).mpr hnum)

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30Second.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- **First designated prime (`P₁`) sixth-moment equivalence and `2.5×` occupied-bin floor.** -/
theorem firstPrime_sixthMoment_package
    {ψ : AddChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ℂ} (hψ : ψ.IsPrimitive)
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)}
    (hcard : H.card = 2 ^ 30)
    (hroots : ∀ x, x ∈ H ↔ x ^ (2 ^ 30 : ℕ) = 1) :
    let P₁ := ArkLib.ProximityGap.PrizeShapePrimeP30.P
    ((∑ b ∈ (Finset.univ : Finset (ZMod P₁)).erase 0, ‖eta ψ H b‖ ^ 6
        ≤ 15 * (P₁ : ℝ) * (2 ^ 30 : ℝ) ^ 3) ↔
      rEnergy H 3 ≤ 15 * (2 ^ 30) ^ 3) ∧
    (rEnergy H 3 ≤ 15 * (2 ^ 30) ^ 3 →
      192153582490528435 ≤ (occupiedBins H (2 ^ 30)).card) := by
  dsimp only
  have hcardF : Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) =
      ArkLib.ProximityGap.PrizeShapePrimeP30.P := ZMod.card _
  have hlarge : (2 ^ 30) ^ 5 < Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) := by
    rw [hcardF]
    decide
  have htwo : (2 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff 2 ArkLib.ProximityGap.PrizeShapePrimeP30.P).mp h0
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    unfold ArkLib.ProximityGap.PrizeShapePrimeP30.P at hle
    omega
  refine ⟨?_, fun hE => (production_punctured_min_bins htwo hcard hroots hE).1⟩
  have heq := dcSixthMoment_le_wick_iff_rEnergy_le hψ (by decide : 0 < 2 ^ 30) hcard hroots hlarge
  simpa only [hcardF, Nat.cast_pow, Nat.cast_ofNat] using heq

/-- **Second designated prime (`P₂`) sixth-moment equivalence and `2.5×` occupied-bin floor.** -/
theorem secondPrime_sixthMoment_package
    {ψ : AddChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ℂ} (hψ : ψ.IsPrimitive)
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hcard : H.card = 2 ^ 30)
    (hroots : ∀ x, x ∈ H ↔ x ^ (2 ^ 30 : ℕ) = 1) :
    let P₂ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
    ((∑ b ∈ (Finset.univ : Finset (ZMod P₂)).erase 0, ‖eta ψ H b‖ ^ 6
        ≤ 15 * (P₂ : ℝ) * (2 ^ 30 : ℝ) ^ 3) ↔
      rEnergy H 3 ≤ 15 * (2 ^ 30) ^ 3) ∧
    (rEnergy H 3 ≤ 15 * (2 ^ 30) ^ 3 →
      192153582490528435 ≤ (occupiedBins H (2 ^ 30)).card) := by
  dsimp only
  have hcardF : Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) =
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.P := ZMod.card _
  have hlarge : (2 ^ 30) ^ 5 <
      Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) := by
    rw [hcardF]
    decide
  have htwo : (2 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff 2 ArkLib.ProximityGap.PrizeShapePrimeP30Second.P).mp h0
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    unfold ArkLib.ProximityGap.PrizeShapePrimeP30Second.P at hle
    omega
  refine ⟨?_, fun hE => (production_punctured_min_bins htwo hcard hroots hE).1⟩
  have heq := dcSixthMoment_le_wick_iff_rEnergy_le hψ (by decide : 0 < 2 ^ 30) hcard hroots hlarge
  simpa only [hcardF, Nat.cast_pow, Nat.cast_ofNat] using heq

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms rEnergy_three_eq_normProfile
#print axioms card_dvd_rEnergy_three
#print axioms dcSixthMoment_le_wick_iff_rEnergy_le
#print axioms normProfile_one_ge_three_card_sub_three
#print axioms normProfile_one_eq_of_sidon
#print axioms punctured_one_occupancy_bound
#print axioms production_punctured_min_bins
#print axioms finite_window_poly_recurrence_degree
#print axioms production_holonomic_window_recurrence_degree
#print axioms crossCoset_two_two_two_sunit
#print axioms pair_signature_inv_eq
#print axioms crossCoset_two_two_two_sidon_cap
#print axioms quarterCoset_occupancy_at_least_five
#print axioms cosetReduced_sixthMoment_eta_le
#print axioms firstPrime_sixthMoment_package
#print axioms secondPrime_sixthMoment_package

end ArkLib.ProximityGap.Frontier.CarbonBGKSixthMomentAndRecurrence
