/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyHigherMoments
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# All-order higher-moment Paley discrepancy for multiplicative subgroups

Using the unconditional all-order `2r`-th moment (`PaleyHigherMoments.shifted_even_moment_le`)
and the ultra-sharp sixth moment (`PaleyHigherMoments.shifted_sixth_moment_ultra`), this file
breaks two major walls of the fourth-moment subgroup analysis (`PaleySubgroupTransversal.lean`
and `PaleySubgroupSignedEnergy.lean`), completely axiom-clean:

1. **All-polynomial-size power saving (`subgroup_all_poly_power_saving`)**:
   The fourth-moment analysis hit a hard `|H| ≥ q^{1/4}` barrier. Using the `2r`-th moment with
   sample size `⌊q^{1/(2r)}⌋`, we obtain an explicit relative power saving
   `|S(A, H)| ≤ q^{-(η / (2r))} · |A| · |H|` for **every** `r ≥ 1`, **every** subgroup `H` of
   arbitrary polynomial size `|H| ≥ q^{1/(2r)}` (`q^ε` for any `ε > 0`!), and **every** `A ⊆ Fˣ`
   with bounded coset occupancy `K` satisfying `2^r ((2r-1)!! + 9r) K q^{1/2 + η} ≤ |A| · |H|`.
2. **Signed `ℓ^{2r/(2r-1)}` Hölder theorem (`subgroup_even_moment_signed_holder`)**:
   Generalizes `PaleySubgroupSignedEnergy.fourth_signed_holder` from `4/3` to arbitrary `2r/(2r-1)`,
   tolerating unbounded coset occupancy whenever the signed coset energy is controlled.
3. **18-bit (`262,144×`) production-prime transversal record (`named_prime_half_sixth`)**:
   On **both** designated length-`2^30` production primes
   `p₁ = 365375409332725729550921208179070755120141565953` and
   `p₂ = 730750818665451459101842416358141509841924915201`,
   `2 |S(A, H)| ≤ |A| · |H|` holds unconditionally for EVERY partial transversal `A ⊆ Fˣ` of
   size **`|A| ≥ 2^59`** — improving `PaleySubgroupTransversal.named_prime_half` (`|A| ≥ 2^77`)
   by 18 bits.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.PaleySubgroupHigherMoment

open Finset ProximityGap.PaleyHigherMoments

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Multiplicative subgroups, cosets, and exact signed recovery -/

/-- A finite multiplicative subgroup of `Fˣ` represented as a `Finset F`. -/
structure IsMulSubgroup (H : Finset F) : Prop where
  zero_not_mem : (0 : F) ∉ H
  one_mem : (1 : F) ∈ H
  mul_mem : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H
  inv_mem : ∀ a ∈ H, a⁻¹ ∈ H

theorem IsMulSubgroup.ne_zero_of_mem {H : Finset F} (hH : IsMulSubgroup H) {u : F}
    (hu : u ∈ H) : u ≠ 0 :=
  fun h => hH.zero_not_mem (h ▸ hu)

theorem IsMulSubgroup.ofSubgroup (G : Subgroup Fˣ) [DecidablePred (· ∈ G)] :
    IsMulSubgroup (Finset.univ.image (fun u : G => (u.1 : F))) where
  zero_not_mem := by
    intro h
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
    exact u.1.ne_zero hu
  one_mem := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  mul_mem := by
    intro a ha b hb
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨u * v, Finset.mem_univ _, rfl⟩
  inv_mem := by
    intro a ha
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨u⁻¹, Finset.mem_univ _, by simp⟩

/-- Multiplicative coset `H · x` as a `Finset F`. -/
def coset (H : Finset F) (x : F) : Finset F :=
  H.image (· * x)

theorem mem_coset_symm {H : Finset F} (hH : IsMulSubgroup H) {a x : F}
    (hx : x ∈ coset H a) : a ∈ coset H x := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨u⁻¹, hH.inv_mem u hu, inv_mul_cancel_left₀ (hH.ne_zero_of_mem hu) a⟩

/-- Signed occupancy `∑ a ∈ A ∩ xH, χ(a)` of the coset `xH` by `A`. -/
def signedOccupancy (A H : Finset F) (x : F) : ℤ :=
  ∑ a ∈ A ∩ coset H x, quadraticChar F a

/-- Exact signed recovery of a subgroup row sum from any subsample `T ⊆ H`. -/
theorem sum_weighted_sample_rows (H T : Finset F) (hH : IsMulSubgroup H) (hT : T ⊆ H) (a : F) :
    ∑ u ∈ H, quadraticChar F u * shiftedCharSum T (u * a) =
      (T.card : ℤ) * shiftedCharSum H a := by
  classical
  simp_rw [shiftedCharSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ b ∈ T,
      ∑ u ∈ H, quadraticChar F u * quadraticChar F (u * a - b) =
        ∑ y ∈ H, quadraticChar F (a - y) := by
    intro b hb
    have hbH := hT hb
    have hb₀ := hH.ne_zero_of_mem hbH
    refine Finset.sum_nbij' (fun u => b / u) (fun y => b / y) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      exact div_eq_mul_inv b u ▸ hH.mul_mem _ hbH _ (hH.inv_mem u hu)
    · intro y hy
      exact div_eq_mul_inv b y ▸ hH.mul_mem _ hbH _ (hH.inv_mem y hy)
    · intro u hu
      field_simp [hb₀, hH.ne_zero_of_mem hu]
    · intro y hy
      field_simp [hb₀, hH.ne_zero_of_mem hy]
    · intro u hu
      have hu₀ := hH.ne_zero_of_mem hu
      rw [show u * a - b = u * (a - b / u) by field_simp [hu₀], map_mul,
        ← mul_assoc, ← pow_two, quadraticChar_sq_one hu₀, one_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]

/-- Grouping amplified subgroup rows by field element yields the signed-occupancy identity. -/
theorem signed_recovery (A H T : Finset F) (hH : IsMulSubgroup H) (hT : T ⊆ H)
    (hA : (0 : F) ∉ A) :
    (T.card : ℤ) * (∑ a ∈ A, shiftedCharSum H a) =
      ∑ x : F, signedOccupancy A H x * (quadraticChar F x * shiftedCharSum T x) := by
  classical
  have hflip (x a : F) : a ∈ coset H x ↔ x ∈ coset H a :=
    ⟨mem_coset_symm hH, mem_coset_symm hH⟩
  have hrow (a : F) (ha : a ∈ A) :
      (∑ u ∈ H, quadraticChar F u * shiftedCharSum T (u * a)) =
      ∑ x : F, if a ∈ coset H x then
        quadraticChar F a * (quadraticChar F x * shiftedCharSum T x) else 0 := by
    have ha₀ : a ≠ 0 := fun he => hA (he ▸ ha)
    simp_rw [hflip _ a]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    unfold coset
    rw [Finset.sum_image (mul_left_injective₀ ha₀).injOn]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, show ∀ v w t : ℤ, v * ((w * v) * t) = v ^ 2 * (w * t) by intros; ring,
      quadraticChar_sq_one ha₀, one_mul]
  rw [Finset.mul_sum]
  simp_rw [← sum_weighted_sample_rows H T hH hT]
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, signedOccupancy, Finset.sum_mul]

/-! ## 2. General `2r`-th moment subgroup inequalities (pointwise and signed-Hölder) -/

/-- For any subsample `T ⊆ H`, any `r ≥ 1`, and any bounded coset occupancy `K` (with optional
unit weights `w a ^ (2r) = 1`), the `2r`-th power of the subgroup Paley sum is controlled by the
`2r`-th moment of `W_T`. -/
theorem weighted_subgroup_even_moment_of_raw (A H T : Finset F)
    (hH : IsMulSubgroup H) (hT : T ⊆ H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) {r : ℕ} (hr : 1 ≤ r)
    (w : F → ℤ) (hw : ∀ a ∈ A, w a ^ (2 * r) = 1) :
    ((T.card : ℤ) * ∑ a ∈ A, w a * shiftedCharSum H a) ^ (2 * r) ≤
      ((A.card : ℤ) * H.card) ^ (2 * r - 1) * (K : ℤ) *
        ∑ x : F, (shiftedCharSum T x) ^ (2 * r) := by
  classical
  let D := A ×ˢ H
  let G (z : F × F) : ℤ := w z.1 * (quadraticChar F z.2 * shiftedCharSum T (z.2 * z.1))
  have hflip (x a : F) : a ∈ coset H x ↔ x ∈ coset H a :=
    ⟨mem_coset_symm hH, mem_coset_symm hH⟩
  have hrecover : (T.card : ℤ) * (∑ a ∈ A, w a * shiftedCharSum H a) = ∑ z ∈ D, G z := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [G, ← Finset.mul_sum]
    rw [mul_left_comm]
    congr 1
    exact (sum_weighted_sample_rows H T hH hT a).symm
  have heven : Even (2 * r) := even_two_mul r
  have hcover : ∑ z ∈ D, G z ^ (2 * r) ≤ (K : ℤ) * ∑ x : F, (shiftedCharSum T x) ^ (2 * r) := by
    calc ∑ z ∈ D, G z ^ (2 * r)
        = ∑ a ∈ A, ∑ u ∈ H, (shiftedCharSum T (u * a)) ^ (2 * r) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun u hu => ?_
          dsimp only [G]
          rw [mul_pow, hw a ha, one_mul, mul_pow]
          have hu₀ := hH.ne_zero_of_mem hu
          have hqpow : quadraticChar F u ^ (2 * r) = 1 := by
            rw [pow_mul, quadraticChar_sq_one hu₀, one_pow]
          rw [hqpow, one_mul]
      _ = ∑ a ∈ A, ∑ x : F, if a ∈ coset H x then (shiftedCharSum T x) ^ (2 * r) else 0 := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have ha₀ : a ≠ 0 := fun he => hA (he ▸ ha)
          simp_rw [hflip _ a]
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
          unfold coset
          rw [Finset.sum_image (mul_left_injective₀ ha₀).injOn]
      _ = ∑ x : F, ((A ∩ coset H x).card : ℤ) * (shiftedCharSum T x) ^ (2 * r) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ℤ) * ∑ x : F, (shiftedCharSum T x) ^ (2 * r) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_right (by exact_mod_cast hK x) (heven.pow_nonneg _)
  have hpow : (∑ z ∈ D, G z) ^ (2 * r) ≤ (D.card : ℤ) ^ (2 * r - 1) * ∑ z ∈ D, G z ^ (2 * r) := by
    have h1 := pow_sum_le_card_mul_sum_pow (s := D) (f := fun z => |G z|)
      (fun _ _ => abs_nonneg _) (2 * r - 1)
    have hidx : (2 * r - 1) + 1 = 2 * r := by omega
    rw [hidx] at h1
    calc (∑ z ∈ D, G z) ^ (2 * r)
        = |∑ z ∈ D, G z| ^ (2 * r) := (heven.pow_abs _).symm
      _ ≤ (∑ z ∈ D, |G z|) ^ (2 * r) :=
          pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (2 * r)
      _ ≤ (D.card : ℤ) ^ (2 * r - 1) * ∑ z ∈ D, |G z| ^ (2 * r) := h1
      _ = (D.card : ℤ) ^ (2 * r - 1) * ∑ z ∈ D, G z ^ (2 * r) := by
          simp only [heven.pow_abs]
  calc ((T.card : ℤ) * ∑ a ∈ A, w a * shiftedCharSum H a) ^ (2 * r)
      = (∑ z ∈ D, G z) ^ (2 * r) := by rw [hrecover]
    _ ≤ (D.card : ℤ) ^ (2 * r - 1) * ∑ z ∈ D, G z ^ (2 * r) := hpow
    _ ≤ (D.card : ℤ) ^ (2 * r - 1) * ((K : ℤ) * ∑ x : F, (shiftedCharSum T x) ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left hcover (by positivity)
    _ = ((A.card : ℤ) * H.card) ^ (2 * r - 1) * (K : ℤ) *
          ∑ x : F, (shiftedCharSum T x) ^ (2 * r) := by
        simp only [D, Finset.card_product, Nat.cast_mul]; ring

/-- **Unconditional all-order `2r`-th moment subgroup bound** (pointwise coset occupancy `K`):
combines `weighted_subgroup_even_moment_of_raw` with `PaleyHigherMoments.shifted_even_moment_le`. -/
theorem subgroup_even_moment_le (hF : ringChar F ≠ 2) (A H T : Finset F)
    (hH : IsMulSubgroup H) (hT : T ⊆ H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) {r : ℕ} (hr : 1 ≤ r) :
    ((T.card : ℝ) * |((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)|) ^ (2 * r) ≤
      ((A.card : ℝ) * H.card) ^ (2 * r - 1) * (K : ℝ) *
        ((doubleFact r : ℝ) * (T.card : ℝ) ^ r * Fintype.card F +
          (9 * r : ℝ) * (T.card : ℝ) ^ (2 * r) * Real.sqrt (Fintype.card F)) := by
  have hraw := weighted_subgroup_even_moment_of_raw A H T hH hT hA K hK hr (fun _ => 1) (by simp)
  have hrawR : ((T.card : ℝ) * ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)) ^ (2 * r) ≤
      ((A.card : ℝ) * H.card) ^ (2 * r - 1) * (K : ℝ) *
        ((∑ x : F, (shiftedCharSum T x) ^ (2 * r) : ℤ) : ℝ) := by
    have h1 : (((T.card : ℤ) * ∑ a ∈ A, (1 : ℤ) * shiftedCharSum H a : ℤ) : ℝ) ^ (2 * r) ≤
        ((((A.card : ℤ) * H.card) ^ (2 * r - 1) * (K : ℤ) *
          ∑ x : F, (shiftedCharSum T x) ^ (2 * r) : ℤ) : ℝ) := by exact_mod_cast hraw
    simpa only [one_mul, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using h1
  have heven : Even (2 * r) := even_two_mul r
  have hlhs : ((T.card : ℝ) * |((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)|) ^ (2 * r) =
      ((T.card : ℝ) * ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)) ^ (2 * r) := by
    rw [mul_pow, mul_pow, heven.pow_abs]
  rw [hlhs]
  exact hrawR.trans (mul_le_mul_of_nonneg_left (shifted_even_moment_le hF T hr) (by positivity))

private theorem even_holder {ι : Type*} (s : Finset ι) (d w : ι → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |∑ x ∈ s, d x * w x| ^ (2 * r) ≤
      (∑ x ∈ s, |d x| ^ (((2 * r : ℕ) : ℝ) / ((2 * r - 1 : ℕ) : ℝ))) ^ (2 * r - 1) *
        (∑ x ∈ s, w x ^ (2 * r)) := by
  set p : ℝ := ((2 * r : ℕ) : ℝ) / ((2 * r - 1 : ℕ) : ℝ)
  set q : ℝ := ((2 * r : ℕ) : ℝ)
  have h2r_pos : (0 : ℝ) < q := by dsimp [q]; exact_mod_cast (by omega : 0 < 2 * r)
  have h2rm1_pos : (0 : ℝ) < ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * r - 1)
  have h2rm1_eq : ((2 * r - 1 : ℕ) : ℝ) = q - 1 := by
    dsimp [q]; rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]; simp
  have hconj : Real.HolderConjugate p q := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · dsimp [p]
      rw [one_lt_div h2rm1_pos, h2rm1_eq]
      linarith
    · dsimp [p]
      rw [inv_div, h2rm1_eq]
      field_simp [h2r_pos.ne']
      ring
  have h := Real.inner_le_Lp_mul_Lq s (fun x => |d x|) (fun x => |w x|) hconj
  simp only [abs_abs, ← abs_mul] at h
  have habs := (Finset.abs_sum_le_sum_abs (fun i => d i * w i) s).trans h
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habs (2 * r)
  have hpower : ∀ (x : ℝ), 0 ≤ x → ∀ (c : ℝ), (x ^ c) ^ (2 * r) = x ^ (c * q) := by
    intro x hx c
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hp_exp : (1 / p) * q = ((2 * r - 1 : ℕ) : ℝ) := by
    dsimp [p, q]
    rw [one_div_div]
    field_simp [h2r_pos.ne']
  have hq_exp : (1 / q) * q = 1 := by field_simp [h2r_pos.ne']
  have heven : Even (2 * r) := even_two_mul r
  rw [mul_pow, hpower _ (by positivity), hpower _ (by positivity), hp_exp, hq_exp,
    Real.rpow_natCast, Real.rpow_one] at hpow
  refine hpow.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [q]
  rw [Real.rpow_natCast, heven.pow_abs]

/-- **All-order signed `ℓ^{2r/(2r-1)}` Hölder theorem**: generalizes
`PaleySubgroupSignedEnergy.fourth_signed_holder` to every even order `2r` (`r ≥ 1`), requiring no
pointwise cap on coset occupancy. -/
theorem subgroup_even_moment_signed_holder (hF : ringChar F ≠ 2) (A H T : Finset F)
    (hH : IsMulSubgroup H) (hT : T ⊆ H) (hA : (0 : F) ∉ A) {r : ℕ} (hr : 1 ≤ r) :
    ((T.card : ℝ) * |((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)|) ^ (2 * r) ≤
      (∑ x : F, |(signedOccupancy A H x : ℝ)| ^ (((2 * r : ℕ) : ℝ) / ((2 * r - 1 : ℕ) : ℝ))) ^
          (2 * r - 1) *
        ((doubleFact r : ℝ) * (T.card : ℝ) ^ r * Fintype.card F +
          (9 * r : ℝ) * (T.card : ℝ) ^ (2 * r) * Real.sqrt (Fintype.card F)) := by
  let d (x : F) : ℝ := (signedOccupancy A H x : ℝ)
  let w (x : F) : ℝ := ((quadraticChar F x * shiftedCharSum T x : ℤ) : ℝ)
  have hrec : (T.card : ℝ) * ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ) = ∑ x : F, d x * w x := by
    have h := signed_recovery A H T hH hT hA
    have hR : ((T.card : ℤ) * (∑ a ∈ A, shiftedCharSum H a) : ℝ) =
        ((∑ x : F, signedOccupancy A H x * (quadraticChar F x * shiftedCharSum T x) : ℤ) : ℝ) := by
      exact_mod_cast h
    simpa [d, w, Int.cast_sum, Int.cast_mul] using hR
  have heven : Even (2 * r) := even_two_mul r
  have htwist : ∑ x : F, w x ^ (2 * r) ≤
      ((∑ x : F, (shiftedCharSum T x) ^ (2 * r) : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_le_sum fun x _ => ?_
    dsimp only [w]
    push_cast
    rw [mul_pow]
    by_cases hx : x = 0
    · simp only [hx, MulChar.map_zero, Int.cast_zero, zero_pow (by omega : 2 * r ≠ 0), zero_mul]
      exact heven.pow_nonneg _
    · have hq1 : ((quadraticChar F x : ℤ) : ℝ) ^ (2 * r) = 1 := by
        have h1 : quadraticChar F x ^ (2 * r) = 1 := by
          rw [pow_mul, quadraticChar_sq_one hx, one_pow]
        exact_mod_cast h1
      rw [hq1, one_mul]
  have hD_nonneg : 0 ≤ ∑ x : F, |d x| ^ (((2 * r : ℕ) : ℝ) / ((2 * r - 1 : ℕ) : ℝ)) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  calc ((T.card : ℝ) * |((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)|) ^ (2 * r)
      = |(T.card : ℝ) * ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)| ^ (2 * r) := by
        congr 1
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (T.card : ℝ) by positivity)]
    _ = |∑ x : F, d x * w x| ^ (2 * r) := by rw [hrec]
    _ ≤ (∑ x : F, |d x| ^ (((2 * r : ℕ) : ℝ) / ((2 * r - 1 : ℕ) : ℝ))) ^ (2 * r - 1) *
          (∑ x : F, w x ^ (2 * r)) := even_holder Finset.univ d w hr
    _ ≤ (∑ x : F, |d x| ^ (((2 * r : ℕ) : ℝ) / ((2 * r - 1 : ℕ) : ℝ))) ^ (2 * r - 1) *
          ((doubleFact r : ℝ) * (T.card : ℝ) ^ r * Fintype.card F +
            (9 * r : ℝ) * (T.card : ℝ) ^ (2 * r) * Real.sqrt (Fintype.card F)) :=
        mul_le_mul_of_nonneg_left (htwist.trans (shifted_even_moment_le hF T hr))
          (pow_nonneg hD_nonneg _)

/-! ## 3. All-polynomial-size power saving (shattering the `|H| ≥ q^{1/4}` barrier) -/

/-- **All-polynomial-size subgroup power saving**:
For ANY `r ≥ 1` and ANY `η > 0`, ANY multiplicative subgroup `H` of size `|H| ≥ q^{1/(2r)}`
(arbitrarily small polynomial size `q^ε`!) and ANY `A ⊆ Fˣ` with coset occupancy `≤ K` satisfying
`2^r * ((2r - 1)!! + 9r) * K * q^{1/2 + η} ≤ |A| * |H|` has explicit power saving
`|S(A, H)| ≤ q^{-(η / (2r))} * |A| * |H|`. -/
theorem subgroup_all_poly_power_saving (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) {r : ℕ} (hr : 1 ≤ r)
    (η : ℝ) (hη : 0 < η)
    (hH_size : (Fintype.card F : ℝ) ^ (1 / (2 * r : ℝ)) ≤ H.card)
    (hprod : (2 : ℝ) ^ r * ((doubleFact r : ℝ) + 9 * r) * (K : ℝ) *
        (Fintype.card F : ℝ) ^ ((1 / 2 : ℝ) + η) ≤ (A.card : ℝ) * H.card) :
    |((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ) ^ (-(η / (2 * r : ℝ))) * ((A.card : ℝ) * H.card) := by
  let q : ℝ := Fintype.card F
  let m : ℝ := (A.card : ℝ) * H.card
  let S : ℝ := ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)
  have hq1 : (1 : ℝ) ≤ q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hqpos : 0 < q := by linarith
  have h2r_pos : (0 : ℝ) < (2 * r : ℝ) := by positivity
  let t : ℝ := q ^ (1 / (2 * r : ℝ))
  let s : ℕ := ⌊t⌋₊
  have ht1 : 1 ≤ t := Real.one_le_rpow hq1 (by positivity)
  have hs_pos : 0 < s := Nat.floor_pos.mpr ht1
  have hs_posR : (0 : ℝ) < s := by exact_mod_cast hs_pos
  have hs_le_t : (s : ℝ) ≤ t := Nat.floor_le (by linarith)
  have ht_le_2s : t ≤ 2 * (s : ℝ) := by
    have hlt : t < (s : ℝ) + 1 := Nat.lt_floor_add_one t
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs_pos
    linarith
  have hs_le_H : s ≤ H.card := by
    have : (s : ℝ) ≤ H.card := hs_le_t.trans hH_size
    exact_mod_cast this
  obtain ⟨T, hTH, hTcard⟩ := Finset.exists_subset_card_eq hs_le_H
  have ht_pow_r : t ^ r = Real.sqrt q := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le, Real.sqrt_eq_rpow]
    congr 1
    field_simp [show (r : ℝ) ≠ 0 by positivity]
  have hs_pow_r_le : (s : ℝ) ^ r ≤ Real.sqrt q := by
    calc (s : ℝ) ^ r ≤ t ^ r := pow_le_pow_left₀ hs_posR.le hs_le_t r
      _ = Real.sqrt q := ht_pow_r
  have hsqrt_le : Real.sqrt q ≤ (2 : ℝ) ^ r * (s : ℝ) ^ r := by
    rw [← ht_pow_r, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) ht_le_2s r
  have hmom := subgroup_even_moment_le hF A H T hH hTH hA K hK hr
  rw [hTcard] at hmom
  -- Bound `(s : ℝ)^(2*r) * √q ≤ (s : ℝ)^r * q` using `s^r ≤ √q`.
  have hterm2 : (s : ℝ) ^ (2 * r) * Real.sqrt q ≤ (s : ℝ) ^ r * q := by
    calc (s : ℝ) ^ (2 * r) * Real.sqrt q
        = (s : ℝ) ^ r * ((s : ℝ) ^ r * Real.sqrt q) := by
            rw [show 2 * r = r + r by omega, pow_add]; ring
      _ ≤ (s : ℝ) ^ r * (Real.sqrt q * Real.sqrt q) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hs_pow_r_le (Real.sqrt_nonneg q)) (by positivity)
      _ = (s : ℝ) ^ r * q := by rw [Real.mul_self_sqrt hqpos.le]
  have hmom2 : (s : ℝ) ^ (2 * r) * |S| ^ (2 * r) ≤
      m ^ (2 * r - 1) * (K : ℝ) * (((doubleFact r : ℝ) + 9 * r) * (s : ℝ) ^ r * q) := by
    have hcomb : (doubleFact r : ℝ) * (s : ℝ) ^ r * q + (9 * r : ℝ) * (s : ℝ) ^ (2 * r) * Real.sqrt q ≤
        ((doubleFact r : ℝ) + 9 * r) * (s : ℝ) ^ r * q := by
      have : (9 * r : ℝ) * ((s : ℝ) ^ (2 * r) * Real.sqrt q) ≤ (9 * r : ℝ) * ((s : ℝ) ^ r * q) :=
        mul_le_mul_of_nonneg_left hterm2 (by positivity)
      linarith
    have h1 : (s : ℝ) ^ (2 * r) * |S| ^ (2 * r) ≤
        m ^ (2 * r - 1) * (K : ℝ) *
          ((doubleFact r : ℝ) * (s : ℝ) ^ r * q + (9 * r : ℝ) * (s : ℝ) ^ (2 * r) * Real.sqrt q) := by
      simpa only [mul_pow, m, S, q] using hmom
    exact h1.trans (mul_le_mul_of_nonneg_left hcomb (by positivity))
  -- Cancel `s^r > 0`:
  have hcancel_sr : (s : ℝ) ^ r * |S| ^ (2 * r) ≤
      m ^ (2 * r - 1) * (K : ℝ) * ((doubleFact r : ℝ) + 9 * r) * q := by
    apply le_of_mul_le_mul_left (a := (s : ℝ) ^ r) _ (pow_pos hs_posR r)
    calc (s : ℝ) ^ r * ((s : ℝ) ^ r * |S| ^ (2 * r))
        = (s : ℝ) ^ (2 * r) * |S| ^ (2 * r) := by
            rw [show 2 * r = r + r by omega, pow_add]; ring
      _ ≤ m ^ (2 * r - 1) * (K : ℝ) * (((doubleFact r : ℝ) + 9 * r) * (s : ℝ) ^ r * q) := hmom2
      _ = (s : ℝ) ^ r * (m ^ (2 * r - 1) * (K : ℝ) * ((doubleFact r : ℝ) + 9 * r) * q) := by ring
  -- Multiply by `2^r` and use `√q ≤ 2^r * s^r`, then cancel `√q > 0`:
  have hS_pow : |S| ^ (2 * r) ≤
      (2 : ℝ) ^ r * ((doubleFact r : ℝ) + 9 * r) * (K : ℝ) * q ^ (1 / 2 : ℝ) * m ^ (2 * r - 1) := by
    have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
    apply le_of_mul_le_mul_left (a := Real.sqrt q) _ hsqrt_pos
    calc Real.sqrt q * |S| ^ (2 * r)
        ≤ ((2 : ℝ) ^ r * (s : ℝ) ^ r) * |S| ^ (2 * r) :=
          mul_le_mul_of_nonneg_right hsqrt_le (by positivity)
      _ = (2 : ℝ) ^ r * ((s : ℝ) ^ r * |S| ^ (2 * r)) := by ring
      _ ≤ (2 : ℝ) ^ r * (m ^ (2 * r - 1) * (K : ℝ) * ((doubleFact r : ℝ) + 9 * r) * q) :=
          mul_le_mul_of_nonneg_left hcancel_sr (by positivity)
      _ = Real.sqrt q *
            ((2 : ℝ) ^ r * ((doubleFact r : ℝ) + 9 * r) * (K : ℝ) * q ^ (1 / 2 : ℝ) *
              m ^ (2 * r - 1)) := by
          rw [← Real.sqrt_eq_rpow]
          have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hqpos.le
          calc (2 : ℝ) ^ r * (m ^ (2 * r - 1) * (K : ℝ) * ((doubleFact r : ℝ) + 9 * r) * q)
              = (2 : ℝ) ^ r * (m ^ (2 * r - 1) * (K : ℝ) * ((doubleFact r : ℝ) + 9 * r) *
                  (Real.sqrt q * Real.sqrt q)) := by rw [hsq]
            _ = _ := by ring
  -- Finish by multiplying by `q^η = (q^(η/(2r)))^(2r)` and taking the `2r`-th root:
  change |S| ≤ q ^ (-(η / (2 * r : ℝ))) * m
  rw [Real.rpow_neg hqpos.le, inv_mul_eq_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hqpos _)).mpr
  apply le_of_pow_le_pow_left₀ (n := 2 * r) (by omega) (by positivity)
  have hpow_eta : (q ^ (η / (2 * r : ℝ))) ^ (2 * r) = q ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    congr 1
    push_cast
    field_simp [h2r_pos.ne']
  have hqadd : q ^ (1 / 2 : ℝ) * q ^ η = q ^ ((1 / 2 : ℝ) + η) := (Real.rpow_add hqpos _ _).symm
  have hm_pow : m * m ^ (2 * r - 1) = m ^ (2 * r) := by
    rw [← pow_succ', show (2 * r - 1) + 1 = 2 * r by omega]
  calc (|S| * q ^ (η / (2 * r : ℝ))) ^ (2 * r)
      = |S| ^ (2 * r) * (q ^ (η / (2 * r : ℝ))) ^ (2 * r) := mul_pow _ _ _
    _ = |S| ^ (2 * r) * q ^ η := by rw [hpow_eta]
    _ ≤ ((2 : ℝ) ^ r * ((doubleFact r : ℝ) + 9 * r) * (K : ℝ) * q ^ (1 / 2 : ℝ) *
          m ^ (2 * r - 1)) * q ^ η :=
        mul_le_mul_of_nonneg_right hS_pow (Real.rpow_nonneg hqpos.le _)
    _ = ((2 : ℝ) ^ r * ((doubleFact r : ℝ) + 9 * r) * (K : ℝ) * (q ^ (1 / 2 : ℝ) * q ^ η)) *
          m ^ (2 * r - 1) := by ring
    _ = ((2 : ℝ) ^ r * ((doubleFact r : ℝ) + 9 * r) * (K : ℝ) * q ^ ((1 / 2 : ℝ) + η)) *
          m ^ (2 * r - 1) := by rw [hqadd]
    _ ≤ m * m ^ (2 * r - 1) := mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = m ^ (2 * r) := hm_pow

/-! ## 4. Production-prime 6th-moment transversal record (`|A| ≥ 2^59`, 18-bit win!) -/

/-- Half-discrepancy bound on a partial transversal from the ultra-sharp 6th moment
(`q ≥ 10^7 + 1`), expressed with an integer upper bound `S_q` on `√q` (`q ≤ S_q^2`) so
instantiation at concrete production primes reduces to exact integer arithmetic. -/
theorem transversal_half_sixth_bound (hF : ringChar F ≠ 2) (hq : 10 ^ 7 + 1 ≤ Fintype.card F)
    (A H : Finset F) (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A)
    (htrans : ∀ x : F, (A ∩ coset H x).card ≤ 1)
    (Sq : ℕ) (hSq : Fintype.card F ≤ Sq ^ 2)
    (hsize : 9600 * H.card ^ 3 * Fintype.card F +
        (86400 * H.card ^ 5 + 7104 * H.card ^ 6) * Sq ≤ 10 * A.card * H.card ^ 7) :
    2 * |∑ a ∈ A, shiftedCharSum H a| ≤ (A.card : ℤ) * H.card := by
  have hraw := weighted_subgroup_even_moment_of_raw A H H hH (Finset.Subset.refl H) hA 1 htrans
    (r := 3) (by decide) (fun _ => 1) (by simp)
  have hrawR : ((H.card : ℝ) * ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)) ^ 6 ≤
      ((A.card : ℝ) * H.card) ^ 5 * ((∑ x : F, (shiftedCharSum H x) ^ 6 : ℤ) : ℝ) := by
    have h1 : (((H.card : ℤ) * ∑ a ∈ A, (1 : ℤ) * shiftedCharSum H a : ℤ) : ℝ) ^ 6 ≤
        ((((A.card : ℤ) * H.card) ^ 5 * (1 : ℤ) *
          ∑ x : F, (shiftedCharSum H x) ^ 6 : ℤ) : ℝ) := by exact_mod_cast hraw
    simpa only [one_mul, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one, mul_one] using h1
  have h6 := shifted_sixth_moment_ultra hF hq H
  have hsqrt_le : Real.sqrt (Fintype.card F) ≤ (Sq : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨Nat.cast_nonneg Sq, by exact_mod_cast hSq⟩
  have h6_int : 10 * ((∑ x : F, (shiftedCharSum H x) ^ 6 : ℤ) : ℝ) ≤
      150 * (H.card : ℝ) ^ 3 * Fintype.card F +
        (1350 * (H.card : ℝ) ^ 5 + 111 * (H.card : ℝ) ^ 6) * (Sq : ℝ) := by
    have h1 : (135 * (H.card : ℝ) ^ 5 + (111 / 10 : ℝ) * (H.card : ℝ) ^ 6) *
          Real.sqrt (Fintype.card F) ≤
        (135 * (H.card : ℝ) ^ 5 + (111 / 10 : ℝ) * (H.card : ℝ) ^ 6) * (Sq : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
    linarith
  have hsizeR : 9600 * (H.card : ℝ) ^ 3 * Fintype.card F +
      (86400 * (H.card : ℝ) ^ 5 + 7104 * (H.card : ℝ) ^ 6) * (Sq : ℝ) ≤
      10 * (A.card : ℝ) * (H.card : ℝ) ^ 7 := by exact_mod_cast hsize
  have hHpos : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hH.one_mem⟩
  let S : ℝ := ((∑ a ∈ A, shiftedCharSum H a : ℤ) : ℝ)
  have hS_real : 2 * |S| ≤ (A.card : ℝ) * H.card := by
    apply le_of_pow_le_pow_left₀ (n := 6) (by decide) (by positivity)
    apply le_of_mul_le_mul_right (a := (10 : ℝ) * (H.card : ℝ) ^ 6) _ (by positivity)
    have hcomb : 64 * (10 * ((∑ x : F, (shiftedCharSum H x) ^ 6 : ℤ) : ℝ)) ≤
        10 * (A.card : ℝ) * (H.card : ℝ) ^ 7 := by linarith
    calc (2 * |S|) ^ 6 * (10 * (H.card : ℝ) ^ 6)
        = 640 * ((H.card : ℝ) * S) ^ 6 := by
            rw [mul_pow, (show Even 6 by decide).pow_abs, mul_pow]; ring
      _ ≤ 640 * (((A.card : ℝ) * H.card) ^ 5 * ((∑ x : F, (shiftedCharSum H x) ^ 6 : ℤ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hrawR (by norm_num)
      _ = ((A.card : ℝ) * H.card) ^ 5 * (64 * (10 * ((∑ x : F, (shiftedCharSum H x) ^ 6 : ℤ) : ℝ))) := by
            ring
      _ ≤ ((A.card : ℝ) * H.card) ^ 5 * (10 * (A.card : ℝ) * (H.card : ℝ) ^ 7) :=
            mul_le_mul_of_nonneg_left hcomb (by positivity)
      _ = ((A.card : ℝ) * H.card) ^ 6 * (10 * (H.card : ℝ) ^ 6) := by ring
  dsimp only [S] at hS_real
  exact_mod_cast hS_real

/-- Exact arithmetic certificate for the 6th-moment half-discrepancy bound at `|A| = 2^59` and
`|H| = 2^30` on both designated length-`2^30` production moduli. -/
theorem named_prime_sixth_sizes {q : ℕ}
    (hp : q = 365375409332725729550921208179070755120141565953 ∨
          q = 730750818665451459101842416358141509841924915201) :
    ∃ Sq : ℕ, 10 ^ 7 + 1 ≤ q ∧ q ≤ Sq ^ 2 ∧
      9600 * (2 ^ 30) ^ 3 * q + (86400 * (2 ^ 30) ^ 5 + 7104 * (2 ^ 30) ^ 6) * Sq ≤
        10 * 2 ^ 59 * (2 ^ 30) ^ 7 := by
  rcases hp with rfl | rfl
  · exact ⟨604463 * 10 ^ 18, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨854840 * 10 ^ 18, by norm_num, by norm_num, by norm_num⟩

/-- **18-bit (`262,144×`) production-prime record**:
On both designated length-`2^30` production primes (`p₁ ≈ 2^158` and `p₂ ≈ 2^159`), EVERY partial
transversal `A ⊆ Fˣ` of size **`|A| ≥ 2^59`** satisfies `2 |S(A, H)| ≤ |A| · |H|` (improving
`PaleySubgroupTransversal.named_prime_half` from `2^77` down to `2^59`). -/
theorem named_prime_half_sixth (hF : ringChar F ≠ 2)
    (hp : Fintype.card F = 365375409332725729550921208179070755120141565953 ∨
          Fintype.card F = 730750818665451459101842416358141509841924915201)
    (A H : Finset F) (hH : IsMulSubgroup H) (hh : H.card = 2 ^ 30)
    (hA : (0 : F) ∉ A) (ha : 2 ^ 59 ≤ A.card)
    (htrans : ∀ x : F, (A ∩ coset H x).card ≤ 1) :
    2 * |∑ a ∈ A, shiftedCharSum H a| ≤ (A.card : ℤ) * H.card := by
  obtain ⟨Sq, hq, hSq, hsize⟩ := named_prime_sixth_sizes hp
  refine transversal_half_sixth_bound hF hq A H hH hA htrans Sq hSq ?_
  rw [hh]
  exact hsize.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 ha))

end ProximityGap.PaleySubgroupHigherMoment

#print axioms ProximityGap.PaleySubgroupHigherMoment.signed_recovery
#print axioms ProximityGap.PaleySubgroupHigherMoment.subgroup_even_moment_le
#print axioms ProximityGap.PaleySubgroupHigherMoment.subgroup_even_moment_signed_holder
#print axioms ProximityGap.PaleySubgroupHigherMoment.subgroup_all_poly_power_saving
#print axioms ProximityGap.PaleySubgroupHigherMoment.transversal_half_sixth_bound
#print axioms ProximityGap.PaleySubgroupHigherMoment.named_prime_sixth_sizes
#print axioms ProximityGap.PaleySubgroupHigherMoment.named_prime_half_sixth
