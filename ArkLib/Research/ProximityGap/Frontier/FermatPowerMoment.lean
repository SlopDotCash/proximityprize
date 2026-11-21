/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Fermat point counts as lower bounds for complete power sums -/
namespace ArkLib.ProximityGap.Frontier.FermatPowerMoment
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Complete additive-character sum of a function. -/
noncomputable def completeSum (ψ : AddChar F ℂ) (u : F → F) (b : F) : ℂ :=
  ∑ x : F, ψ (b*u x)

/-- Number of ordered equal-value pairs of the map. -/
def equalPairs (u : F → F) : ℕ := ∑ x : F, ∑ y : F, if u x=u y then 1 else 0

/-- Number of ordered additive zero triples of values of the map, with fiber multiplicities. -/
def zeroTriples (u : F → F) : ℕ := ∑ x : F, ∑ y : F, ∑ z : F,
  if u x+u y+u z=0 then 1 else 0

theorem nonzero_cubic {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (u : F → F) :
    ∑ b ∈ (univ : Finset F).erase 0, completeSum ψ u b^3 =
      (Fintype.card F : ℂ) * zeroTriples u - (Fintype.card F : ℂ)^3 := by
  classical
  have hc (b : F) : completeSum ψ u b^3 =
      ∑ x : F, ∑ y : F, ∑ z : F, ψ (b*(u x+u y+u z)) := by
    rw [show completeSum ψ u b^3=completeSum ψ u b*(completeSum ψ u b*completeSum ψ u b) by ring]
    simp only [completeSum]
    rw [sum_mul_sum, sum_mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    rw [mul_sum]
    apply sum_congr rfl
    intro z _
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hall : (∑ b : F, completeSum ψ u b^3) = (Fintype.card F : ℂ) * zeroTriples u := by
    simp_rw [hc]
    calc
      _ = ∑ x : F, ∑ y : F, ∑ z : F, ∑ b : F, ψ (b*(u x+u y+u z)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        rw [sum_comm]
      _ = _ := by
        simp only [zeroTriples, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          mul_sum, AddChar.sum_mulShift _ hψ, mul_ite, mul_one, mul_zero]
  have hz : completeSum ψ u 0 = (Fintype.card F : ℂ) := by simp [completeSum]
  have he := sum_erase_add (univ : Finset F) (fun b ↦ completeSum ψ u b^3) (mem_univ 0)
  rw [hz,hall] at he
  linear_combination he

theorem nonzero_square {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (u : F → F) :
    ∑ b ∈ (univ : Finset F).erase 0, ‖completeSum ψ u b‖^2 =
      (Fintype.card F : ℝ)*equalPairs u - (Fintype.card F : ℝ)^2 := by
  classical
  have hchar : 0 < ringChar F := by
    have := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hc (b : F) : ((‖completeSum ψ u b‖^2 : ℝ) : ℂ) =
      ∑ x : F, ∑ y : F, ψ (b*(u x-u y)) := by
    calc
      _ = (completeSum ψ u b) * (starRingEnd ℂ) (completeSum ψ u b) := by
        rw [RCLike.mul_conj]; norm_cast
      _ = _ := by
        simp only [completeSum, map_sum, sum_mul_sum]
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        rw [AddChar.starComp_apply hchar, AddChar.inv_apply, ← AddChar.map_add_eq_mul]
        congr 1
        ring
  have hall : (∑ b : F, ‖completeSum ψ u b‖^2) = (Fintype.card F : ℝ)*equalPairs u := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [← Complex.ofReal_pow, hc]
    calc
      _ = ∑ x : F, ∑ y : F, ∑ b : F, ψ (b*(u x-u y)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [sum_comm]
      _ = _ := by
        simp only [equalPairs, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          mul_sum, AddChar.sum_mulShift _ hψ, mul_ite, mul_one, mul_zero, sub_eq_zero]
  have hz : ‖completeSum ψ u 0‖ = (Fintype.card F : ℝ) := by simp [completeSum]
  have he := sum_erase_add (univ : Finset F) (fun b ↦ ‖completeSum ψ u b‖^2) (mem_univ 0)
  rw [hz,hall] at he
  linarith

/-- A Fermat cone point count far from the random value forces a large nonzero frequency. -/
theorem discrepancy_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (u : F → F)
    (M : ℝ) (hM : ∀ b ≠ 0, ‖completeSum ψ u b‖ ≤ M) :
    ‖(Fintype.card F : ℂ) * zeroTriples u - (Fintype.card F : ℂ)^3‖ ≤
      M * ((Fintype.card F : ℝ)*equalPairs u - (Fintype.card F : ℝ)^2) := by
  rw [← nonzero_cubic hψ u, ← nonzero_square hψ u, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b hb
  rw [norm_pow, show (3 : ℕ)=1+2 by decide, pow_add, pow_one]
  exact mul_le_mul_of_nonneg_right (hM b (mem_erase.mp hb).1) (sq_nonneg _)


/-- The affine slice of the homogeneous cone at the last coordinate. -/
def affineSlice (k : ℕ) (t : F) : ℕ := ∑ x : F, ∑ y : F,
  if x^k+y^k+t^k=0 then 1 else 0

/-- The points at infinity, normalized to middle coordinate one. -/
def infinityChart (k : ℕ) : ℕ := ∑ x : F, if x^k+1=0 then 1 else 0

/-- The homogeneous Fermat equation has two affine charts when the exponent is positive. -/
def fermatPoints (k : ℕ) : ℕ := affineSlice k (1 : F) + infinityChart (F := F) k

private theorem sum_offzero_constant {v : F → ℕ} {c : ℕ} (h : ∀ t ≠ 0, v t = c) :
    ∑ t : F, v t = v 0 + (Fintype.card F - 1)*c := by
  have he := sum_erase_add (univ : Finset F) v (mem_univ 0)
  rw [← he]
  rw [sum_congr rfl (fun t ht ↦ h t (mem_erase.mp ht).1)]
  simp [add_comm]

private theorem affineSlice_nonzero (k : ℕ) (t : F) (ht : t ≠ 0) :
    affineSlice k t = affineSlice k (1 : F) := by
  let s := Equiv.mulLeft₀ t ht
  have h (x y : F) : (t*x)^k+(t*y)^k+t^k=0 ↔ x^k+y^k+(1:F)^k=0 := by
    rw [mul_pow,mul_pow,one_pow,
      show t^k*x^k+t^k*y^k+t^k=t^k*(x^k+y^k+1) by ring, mul_eq_zero]
    simp [pow_ne_zero _ ht]
  unfold affineSlice
  rw [← Equiv.sum_comp s (fun x : F ↦ ∑ y : F, if x^k+y^k+t^k=0 then (1:ℕ) else 0)]
  apply sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp s (fun y : F ↦ if (s x)^k+y^k+t^k=0 then (1:ℕ) else 0)]
  apply sum_congr rfl
  intro y _
  exact if_congr (h x y) rfl rfl

theorem affineSlice_zero (k : ℕ) (hk : k ≠ 0) :
    affineSlice k (0 : F) = 1+(Fintype.card F-1)*infinityChart (F := F) k := by
  classical
  unfold affineSlice
  simp only [zero_pow hk, add_zero]
  rw [sum_comm]
  have hz : (∑ x : F, if x^k+(0 : F)^k=0 then (1:ℕ) else 0)=1 := by
    simp [zero_pow hk, pow_eq_zero_iff hk]
  convert sum_offzero_constant (c := infinityChart (F := F) k) (v := fun y : F ↦
    ∑ x : F, if x^k+y^k=0 then (1:ℕ) else 0) ?_ using 1
  · rw [hz]
  · intro y hy
    let s := Equiv.mulLeft₀ y hy
    rw [← Equiv.sum_comp s (fun x : F ↦ if x^k+y^k=0 then (1:ℕ) else 0)]
    unfold infinityChart
    apply sum_congr rfl
    intro x _
    apply if_congr _ rfl rfl
    change (y*x)^k+y^k=0 ↔ _
    rw [mul_pow, show y^k*x^k+y^k=y^k*(x^k+1) by ring, mul_eq_zero]
    simp [pow_ne_zero _ hy]

theorem cone_count (k : ℕ) (hk : k ≠ 0) :
    zeroTriples (fun x : F ↦ x^k) = 1+(Fintype.card F-1)*fermatPoints (F := F) k := by
  have hz : zeroTriples (fun x : F ↦ x^k) = ∑ z : F, affineSlice k z := by
    unfold zeroTriples affineSlice
    symm
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [sum_comm]
  rw [hz, sum_offzero_constant (fun t ht ↦ affineSlice_nonzero k t ht), affineSlice_zero k hk,
    fermatPoints]
  ring

theorem homogeneous_pairs (k : ℕ) (hk : Odd k) :
    equalPairs (fun x : F ↦ x^k) = 1+(Fintype.card F-1)*infinityChart (F := F) k := by
  have hk0 : k ≠ 0 := by obtain ⟨l,hl⟩ := hk; omega
  rw [← affineSlice_zero k hk0]
  unfold equalPairs affineSlice
  apply sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (Equiv.neg F) (fun y : F ↦ if x^k+y^k+(0:F)^k=0 then (1:ℕ) else 0)]
  apply sum_congr rfl
  intro y _
  simp [zero_pow hk0, hk.neg_pow, ← sub_eq_add_neg, sub_eq_zero]

/-- The projective point-count discrepancy is bounded by the largest nonzero-frequency
complete sum times the number of points at infinity less one. -/
theorem fermat_discrepancy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (k : ℕ) (hk : Odd k)
    (M : ℝ) (hM : ∀ b ≠ 0, ‖completeSum ψ (fun x : F ↦ x^k) b‖ ≤ M) :
    |(fermatPoints (F := F) k : ℝ) - Fintype.card F - 1| ≤
      M*((infinityChart (F := F) k : ℝ)-1) := by
  have hk0 : k ≠ 0 := by obtain ⟨l,hl⟩ := hk; omega
  have hp : 1 < Fintype.card F := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have he := discrepancy_le hψ (fun x : F ↦ x^k) M hM
  rw [cone_count k hk0, homogeneous_pairs k hk] at he
  push_cast [Nat.cast_sub hp.le] at he
  let q : ℝ := Fintype.card F
  let C : ℝ := fermatPoints (F := F) k
  let B : ℝ := infinityChart (F := F) k
  have hq : 1 < q := by dsimp [q]; exact_mod_cast hp
  have hpos : 0 < q*(q-1) := by positivity
  have hl : (Fintype.card F : ℂ)*(1+((Fintype.card F : ℂ)-1)*fermatPoints (F := F) k)
      -(Fintype.card F : ℂ)^3 = ((q*(q-1)*(C-q-1) : ℝ) : ℂ) := by
    dsimp [q,C]
    push_cast
    ring
  rw [hl, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hpos] at he
  change |C-q-1| ≤ M*(B-1)
  apply (mul_le_mul_iff_right₀ hpos).mp
  apply he.trans_eq
  change M*(q*(1+(q-1)*B)-q^2) = q*(q-1)*(M*(B-1))
  ring

/-- An exact one-sided third-moment test. Weighting the observations by a shifted square
keeps their order and recovers the sharp fixed-index extremum at the Fermat identity. -/
theorem signed_weighted_test {ι : Type*} (s : Finset ι) (y : ι → ℝ) (a L : ℝ)
    (hL : ∀ i ∈ s, L ≤ y i) (hcenter : ∑ i ∈ s, y i = 0) :
    L*((∑ i ∈ s, y i^2) + s.card*a^2) ≤ (∑ i ∈ s, y i^3) - 2*a*(∑ i ∈ s, y i^2) := by
  have h := sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_right (hL i hi) (sq_nonneg (y i-a)))
  have hl (i : ι) : L*(y i-a)^2 = L*y i^2 - (2*L*a)*y i + L*a^2 := by ring
  have hr (i : ι) : y i*(y i-a)^2 = y i^3 - (2*a)*y i^2 + a^2*y i := by ring
  simp only [hl, hr, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_const, nsmul_eq_mul, hcenter, mul_zero, add_zero, sub_zero] at h
  linarith only [h, show L*((∑ i ∈ s,y i^2) + s.card*a^2) =
      L*(∑ i ∈ s,y i^2)+s.card*(L*a^2) by ring]

omit [DecidableEq F] in
theorem power_real {ψ : AddChar F ℂ} (k : ℕ) (hk : Odd k) (b : F) :
    (((completeSum ψ (fun x : F ↦ x^k) b).re : ℝ) : ℂ) =
      completeSum ψ (fun x : F ↦ x^k) b := by
  have hchar : 0 < ringChar F := by
    have := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : (starRingEnd ℂ) (completeSum ψ (fun x : F ↦ x^k) b) =
      completeSum ψ (fun x : F ↦ x^k) b := by
    unfold completeSum
    rw [map_sum, ← Equiv.sum_comp (Equiv.neg F) (fun x : F ↦ ψ (b*x^k))]
    apply sum_congr rfl
    intro x _
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
    simp [hk.neg_pow]
  apply Complex.ext
  · simp
  · simpa using (Complex.conj_eq_iff_im.mp hconj).symm

theorem nonzero_center {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {k : ℕ} (hk : k ≠ 0) :
    ∑ b ∈ (univ : Finset F).erase 0, completeSum ψ (fun x : F ↦ x^k) b = 0 := by
  classical
  have ha : (∑ b : F, completeSum ψ (fun x : F ↦ x^k) b) = (Fintype.card F : ℂ) := by
    unfold completeSum
    rw [sum_comm]
    simp [AddChar.sum_mulShift _ hψ, pow_eq_zero_iff hk]
  have hz : completeSum ψ (fun x : F ↦ x^k) 0 = Fintype.card F := by simp [completeSum]
  have he := sum_erase_add (univ : Finset F) (fun b ↦ completeSum ψ (fun x : F ↦ x^k) b) (mem_univ 0)
  rw [ha,hz] at he
  linear_combination he

/-- A lower bound for all real power sums gives the exact signed Fermat point-count
inequality, with the shift chosen as the square root of the field size. -/
theorem fermat_signed_discrepancy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (k : ℕ) (hk : Odd k)
    (L : ℝ) (hL : ∀ b ≠ 0, L ≤ (completeSum ψ (fun x : F ↦ x^k) b).re) :
    L*(infinityChart (F := F) k : ℝ) ≤ (fermatPoints (F := F) k : ℝ) - Fintype.card F - 1
      - 2*Real.sqrt (Fintype.card F)*((infinityChart (F := F) k : ℝ)-1) := by
  let q : ℝ := Fintype.card F
  let B : ℝ := infinityChart (F := F) k
  let C : ℝ := fermatPoints (F := F) k
  let y (b : F) := (completeSum ψ (fun x : F ↦ x^k) b).re
  let T := (univ : Finset F).erase 0
  have hp : 1 < Fintype.card F := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hq : 1 < q := by dsimp [q]; exact_mod_cast hp
  have hk0 : k ≠ 0 := by obtain ⟨l,hl⟩ := hk; omega
  have hy (b : F) : ((y b : ℝ) : ℂ) = completeSum ψ (fun x : F ↦ x^k) b := power_real k hk b
  have hcenter : ∑ b ∈ T, y b = 0 := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [hy]
    exact nonzero_center hψ hk0
  have h2 : ∑ b ∈ T, y b^2 = q*(q-1)*(B-1) := by
    have hs (b : F) : y b^2 = ‖completeSum ψ (fun x : F ↦ x^k) b‖^2 := by
      rw [← hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [hs]
    rw [show T = _ from rfl, nonzero_square hψ, homogeneous_pairs k hk]
    push_cast [Nat.cast_sub hp.le]
    dsimp [q,B]
    ring
  have h3 : ∑ b ∈ T, y b^3 = q*(q-1)*(C-q-1) := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [hy]
    rw [show T = _ from rfl, nonzero_cubic hψ, cone_count k hk0]
    dsimp [q,C]
    push_cast [Nat.cast_sub hp.le]
    ring
  have ht : (T.card : ℝ) = q-1 := by
    simp [T,q,Nat.cast_sub hp.le,card_erase_of_mem (mem_univ (0 : F))]
  have hw := signed_weighted_test T y (Real.sqrt q) L (fun b hb ↦ hL b (mem_erase.mp hb).1) hcenter
  rw [h2,h3,ht,Real.sq_sqrt (by linarith)] at hw
  change L*B ≤ C-q-1-2*Real.sqrt q*(B-1)
  apply (mul_le_mul_iff_right₀ (show 0 < q*(q-1) by positivity)).mp
  linarith only [hw, show L*(q*(q-1)*(B-1)+(q-1)*q)=q*(q-1)*(L*B) by ring,
    show q*(q-1)*(C-q-1)-2*Real.sqrt q*(q*(q-1)*(B-1)) =
      q*(q-1)*(C-q-1-2*Real.sqrt q*(B-1)) by ring]

/-- At a split prime, the odd-degree Fermat curve has exactly the degree many points at
infinity. A primitive root supplies the complete set of roots. -/
theorem infinityChart_eq_degree {k : ℕ} (hk : Odd k) {ζ : F} (hζ : IsPrimitiveRoot ζ k) :
    infinityChart (F := F) k = k := by
  classical
  have hkpos : 0 < k := by obtain ⟨r,hr⟩ := hk; omega
  have hs : (univ.filter fun x : F ↦ x^k=1) = Polynomial.nthRootsFinset k (1 : F) := by
    ext x
    simp [Polynomial.mem_nthRootsFinset hkpos]
  unfold infinityChart
  rw [← Equiv.sum_comp (Equiv.neg F) (fun x : F ↦ if x^k+1=0 then (1:ℕ) else 0)]
  calc
    _ = ∑ x : F, if x^k=1 then (1:ℕ) else 0 := by
      apply sum_congr rfl
      intro x _
      apply if_congr _ rfl rfl
      change (-x)^k+1=0 ↔ x^k=1
      rw [hk.neg_pow]
      constructor <;> intro h <;> linear_combination -h
    _ = _ := by rw [← card_filter,hs,hζ.card_nthRootsFinset]

/-- Exact one-sided Fermat bound at a split odd index. -/
theorem split_signed_discrepancy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {k : ℕ} (hk : Odd k)
    {ζ : F} (hζ : IsPrimitiveRoot ζ k) (L : ℝ)
    (hL : ∀ b ≠ 0, L ≤ (completeSum ψ (fun x : F ↦ x^k) b).re) :
    L*(k : ℝ) ≤ (fermatPoints (F := F) k : ℝ) - Fintype.card F - 1
      - 2*Real.sqrt (Fintype.card F)*((k : ℝ)-1) := by
  simpa only [infinityChart_eq_degree hk hζ] using fermat_signed_discrepancy hψ k hk L hL

#print axioms split_signed_discrepancy
#print axioms fermat_signed_discrepancy

#print axioms signed_weighted_test
#print axioms fermat_discrepancy
#print axioms cone_count
#print axioms homogeneous_pairs
#print axioms discrepancy_le
end ArkLib.ProximityGap.Frontier.FermatPowerMoment
