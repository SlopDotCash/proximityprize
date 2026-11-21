/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._EtaRealNegClosed
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Binary digit changes bound the mean over consecutive doubled frequencies. -/

namespace ArkLib.ProximityGap.PrimeFieldDoublingChain

open Finset
variable {p : ℕ} [Fact p.Prime]

private def iter (j : ℕ) (x : ZMod p) := (2 : ZMod p) ^ j * x
private def digit (j : ℕ) (x : ZMod p) : Bool := decide (p ≤ 2 * (iter j x).val)

/-- Binary expansion recurrence for a residue under doubling. -/
private theorem step (j : ℕ) (x : ZMod p) :
    (iter (j+1) x).val + (if digit j x then p else 0) = 2 * (iter j x).val := by
  have h : iter (j+1) x = iter j x + iter j x := by simp [iter, pow_succ]; ring
  rw [h, ZMod.val_add]
  have hlt := (iter j x).val_lt
  unfold digit
  split_ifs with ht
  · simp only [decide_eq_true_eq] at ht
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [decide_eq_true_eq] at ht
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

private def code {m : ℕ} (ref : Fin m → Bool) (x : ZMod p) : Bool × Finset (Fin m) :=
  (digit 0 x, univ.filter fun j ↦ Bool.xor (digit j x) (digit (j+1 : ℕ) x) ≠ ref j)

private theorem code_injective {m : ℕ} (ref : Fin m → Bool) (hp : p ≤ 2 ^ (m+1)) :
    Function.Injective (code (p := p) ref) := by
  intro x y he
  have hd : ∀ j ≤ m, digit j x = digit j y := by
    intro j hj
    induction j with
    | zero => exact congrArg Prod.fst he
    | succ j ih =>
      have hj' : j < m := by omega
      let i : Fin m := ⟨j, hj'⟩
      have hmem : i ∈ (code ref x).2 ↔ i ∈ (code ref y).2 := by rw [he]
      simp only [code, mem_filter, mem_univ, true_and] at hmem
      change (Bool.xor (digit j x) (digit (j+1) x) ≠ ref i) ↔
        (Bool.xor (digit j y) (digit (j+1) y) ≠ ref i) at hmem
      rw [ih hj'.le] at hmem
      cases digit j y <;> cases hx : digit (j+1) x <;> cases hy : digit (j+1) y <;>
        cases hr : ref i <;> simp_all
  have hdiff : ∀ j ≤ m + 1,
      (iter j x).val + 2^j * y.val = (iter j y).val + 2^j * x.val := by
    intro j hj
    induction j with
    | zero => simp [iter, Nat.add_comm]
    | succ j ih =>
      have h₁ := step j x
      have h₂ := step j y
      rw [hd j (by omega)] at h₁
      have hprev := ih (by omega)
      rw [pow_succ, Nat.mul_right_comm (2^j) 2, Nat.mul_right_comm (2^j) 2]
      omega
  have hr := hdiff (m+1) le_rfl
  have hx := (iter (m+1) x).val_lt
  have hy := (iter (m+1) y).val_lt
  apply ZMod.val_injective
  rcases lt_trichotomy x.val y.val with h | h | h
  · have hmul := Nat.mul_le_mul_left (2 ^ (m+1)) (show x.val+1 ≤ y.val by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · exact h
  · have hmul := Nat.mul_le_mul_left (2 ^ (m+1)) (show y.val+1 ≤ x.val by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

/-- An injection into an initial digit and a transition-error set bounds total errors
from below by the binomial Hamming layer counts. -/
theorem hamming_floor {α : Type*} [DecidableEq α] (D : Finset α) {m : ℕ}
    (f : α → Bool × Finset (Fin m)) (hf : Function.Injective f) (t : ℕ) :
    t * D.card ≤ (∑ x ∈ D, (f x).2.card) +
      2 * ∑ j ∈ range (m+1), m.choose j * (t - j) := by
  classical
  let v (z : Bool × Finset (Fin m)) := t - z.2.card
  have hfloor : t * D.card ≤ (∑ x ∈ D, (f x).2.card) + ∑ x ∈ D, v (f x) := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _x ∈ D, t := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum fun x _ ↦ by dsimp [v]; omega
  apply hfloor.trans <| Nat.add_le_add_left _ _
  calc
    (∑ x ∈ D, v (f x)) = ∑ z ∈ D.image f, v z := (sum_image (f := v) (g := f) hf.injOn).symm
    _ ≤ ∑ z : Bool × Finset (Fin m), v z := sum_le_univ_sum_of_nonneg (fun _ ↦ Nat.zero_le _)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [v, Fintype.sum_bool, ← two_mul]
      rw [← Finset.powerset_univ, sum_powerset_apply_card]
      simp

private theorem truncate_layers (m : ℕ) (hm : 5 ≤ m+1) :
    (∑ j ∈ range (m+1), m.choose j * (5-j)) = ∑ j ∈ range 5, m.choose j * (5-j) := by
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro j _ hj
  simp only [mem_range, not_lt] at hj
  simp [Nat.sub_eq_zero_of_le hj]

private lemma cos_expression (z : ZMod p) :
    (ZMod.stdAddChar z).re = Real.cos (2 * Real.pi * z.val / p) := by
  have hz : ((z.val : ℤ) : ZMod p) = z := by simp
  conv_lhs => rw [← hz, ZMod.stdAddChar_coe]
  have heq : (2 * Real.pi * Complex.I * (z.val : ℤ) / p : ℂ) =
      ((2 * Real.pi * z.val / p : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_re]

private lemma sign_bound (j : ℕ) (x : ZMod p) (negative : Bool) :
    (if negative then -(ZMod.stdAddChar (iter j x)).re else (ZMod.stdAddChar (iter j x)).re)
      + (if Bool.xor (digit j x) (digit (j+1) x) ≠ negative then (1:ℝ) else 0) ≤ 1 := by
  let a := (iter j x).val
  let a' := (iter (j+1) x).val
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hl := (iter j x).val_lt
  have hstep := step j x
  change a' + (if digit j x then p else 0) = 2*a at hstep
  have hsign (n : Bool) (hn : Bool.xor (digit j x) (digit (j+1) x) = n) :
      if n then (ZMod.stdAddChar (iter j x)).re ≤ 0 else 0 ≤ (ZMod.stdAddChar (iter j x)).re := by
    rw [cos_expression]
    change (if n then Real.cos (2 * Real.pi * a / p) ≤ 0 else 0 ≤ Real.cos (2 * Real.pi * a / p))
    have hmid (h₀ : p ≤ 4*a) (h₁ : 4*a ≤ 3*p) :
        Real.cos (2 * Real.pi * a / p) ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · apply (le_div_iff₀ hp).2
        have hr : (p : ℝ) ≤ 4*a := by exact_mod_cast h₀
        nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)]
      · apply (div_le_iff₀ hp).2
        have hr : 4*(a : ℝ) ≤ 3*p := by exact_mod_cast h₁
        nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)]
    have hlow (h : 4*a ≤ p) : 0 ≤ Real.cos (2 * Real.pi * a / p) := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · linarith [show (0:ℝ) ≤ 2 * Real.pi * a / p by positivity, Real.pi_pos]
      · apply (div_le_iff₀ hp).2
        have hr : 4*(a : ℝ) ≤ p := by exact_mod_cast h
        nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)]
    have hhigh (h : 3*p ≤ 4*a) : 0 ≤ Real.cos (2 * Real.pi * a / p) := by
      rw [← Real.cos_two_pi_sub]
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · have hr : (a : ℝ) ≤ p := by exact_mod_cast hl.le
        have hu : 2*Real.pi*a / p ≤ 2*Real.pi := (div_le_iff₀ hp).mpr
          (by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)])
        linarith [Real.pi_pos]
      · have hr : 3*(p:ℝ) ≤ 4*a := by exact_mod_cast h
        have hu : 3*Real.pi / 2 ≤ 2*Real.pi*a / p := (le_div_iff₀ hp).mpr
          (by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)])
        linarith
    change Bool.xor (decide (p ≤ 2*a)) (decide (p ≤ 2*a')) = n at hn
    change a' + (if decide (p ≤ 2*a) then p else 0) = 2*a at hstep
    by_cases m₁ : p ≤ 2*a <;> by_cases m₂ : p ≤ 2*a' <;> simp [m₁, m₂] at hn hstep <;>
      subst n <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hlow (by omega) | exact hhigh (by omega) | exact hmid (by omega) (by omega)
  have hbound := hsign _ rfl
  have hu : (ZMod.stdAddChar (iter j x)).re ≤ 1 := by rw [cos_expression]; exact Real.cos_le_one _
  have hl' : -1 ≤ (ZMod.stdAddChar (iter j x)).re := by rw [cos_expression]; exact Real.neg_one_le_cos _
  cases negative <;> cases h : Bool.xor (digit j x) (digit (j+1) x) <;> simp_all
  linarith

open SubgroupGaussSumSecondMoment

/-- For any antipodal domain and any nonzero starting frequency, the sum of consecutive
doubling-period norms is bounded by the binomial weight deficit. -/
theorem doubling_chain (D : Finset (ZMod p)) (hneg : ∀ x ∈ D, -x ∈ D)
    {m : ℕ} (hp : p ≤ 2 ^ (m+1)) (b : ZMod p) (hb : b ≠ 0) (t : ℕ) :
    (∑ j : Fin m, ‖eta ZMod.stdAddChar D ((2 : ZMod p)^j.val * b)‖) + t * (D.card : ℝ) ≤
      m * (D.card : ℝ) + (2 * ∑ j ∈ range (m+1), m.choose j * (t-j) : ℕ) := by
  classical
  let a (j : Fin m) := eta ZMod.stdAddChar D ((2 : ZMod p)^j.val * b)
  let ref (j : Fin m) := decide ((a j).re < 0)
  let f (x : ZMod p) := code ref (b*x)
  have hfloor := hamming_floor D f ((code_injective ref hp).comp (mul_right_injective₀ hb)) t
  have hcol (j : Fin m) : ‖a j‖ + (∑ x ∈ D, if j ∈ (f x).2 then (1:ℝ) else 0) ≤ D.card := by
    have hre : (a j).re = ∑ x ∈ D, (ZMod.stdAddChar (iter j (b*x))).re := by
      simp [a, eta, iter, mul_assoc, Complex.re_sum]
    have hn : ‖a j‖ = |(a j).re| :=
      _root_.ProximityGap.Frontier.EtaRealNegClosed.eta_norm_eq_abs_re hneg _
    have hid : ‖a j‖ = ∑ x ∈ D, if ref j then -(ZMod.stdAddChar (iter j (b*x))).re
        else (ZMod.stdAddChar (iter j (b*x))).re := by
      rw [hn]
      by_cases h : (a j).re < 0
      · rw [abs_of_neg h]
        have hbit : ref j = true := decide_eq_true h
        simp only [hbit, ↓reduceIte, sum_neg_distrib, hre]
      · rw [abs_of_nonneg (le_of_not_gt h)]
        have hbit : ref j = false := decide_eq_false h
        simp only [hbit, Bool.false_eq_true, ↓reduceIte, hre]
    rw [hid, ← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _x ∈ D, (1 : ℝ) := by
        apply sum_le_sum
        intro x _
        simpa only [f, code, mem_filter, mem_univ, true_and] using sign_bound j (b*x) (ref j)
      _ = _ := by simp
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin m))) (fun j _ ↦ hcol j)
  rw [sum_add_distrib, sum_comm] at hsum
  simp only [sum_boole, filter_mem_eq_inter, univ_inter, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hf' : (t : ℝ)*D.card ≤ ∑ x ∈ D, ((f x).2.card : ℝ) +
      (2 * ∑ j ∈ range (m+1), m.choose j * (t-j) : ℕ) := by exact_mod_cast hfloor
  change (∑ j, ‖a j‖) + _ ≤ _
  linarith

/-- Exact production-length average upper bounds over the first 158 consecutive doublings. -/
theorem production_first_chain (D : Finset (ZMod p)) (hD : D.card = 2^30)
    (hneg : ∀ x ∈ D, -x ∈ D) (hp : p ≤ 2^159) (b : ZMod p) (hb : b ≠ 0) :
    (∑ j : Fin 158, ‖eta ZMod.stdAddChar D ((2 : ZMod p)^j.val * b)‖) ≤
      158 * (2^30 : ℝ) - 5316069514 := by
  have h := doubling_chain D hneg (m := 158) hp b hb 5
  rw [hD, truncate_layers _ (by decide)] at h
  have hc : (∑ j ∈ range 5, Nat.choose 158 j * (5-j)) = 26319803 := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  rw [hc] at h
  norm_num at h ⊢
  linarith

/-- Exact production-length average upper bounds over the first 159 consecutive doublings. -/
theorem production_second_chain (D : Finset (ZMod p)) (hD : D.card = 2^30)
    (hneg : ∀ x ∈ D, -x ∈ D) (hp : p ≤ 2^160) (b : ZMod p) (hb : b ≠ 0) :
    (∑ j : Fin 159, ‖eta ZMod.stdAddChar D ((2 : ZMod p)^j.val * b)‖) ≤
      159 * (2^30 : ℝ) - 5314729034 := by
  have h := doubling_chain D hneg (m := 159) hp b hb 5
  rw [hD, truncate_layers _ (by decide)] at h
  have hc : (∑ j ∈ range 5, Nat.choose 159 j * (5-j)) = 26990043 := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  rw [hc] at h
  norm_num at h ⊢
  linarith

private theorem period_double_of_closed (D : Finset (ZMod p)) (h₂ : (2 : ZMod p) ≠ 0)
    (hclosed : ∀ x ∈ D, 2*x ∈ D) (b : ZMod p) :
    eta ZMod.stdAddChar D (2*b) = eta ZMod.stdAddChar D b := by
  have himg : D.image (fun x ↦ 2*x) = D := by
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.image_subset_iff] using hclosed
    · rw [Finset.card_image_of_injective _ (mul_right_injective₀ h₂)]
  calc
    eta ZMod.stdAddChar D (2*b) = ∑ x ∈ D, ZMod.stdAddChar (b*(2*x)) := by
      simp only [eta, mul_left_comm, mul_assoc]
    _ = ∑ y ∈ D.image (fun x ↦ 2*x), ZMod.stdAddChar (b*y) :=
      (Finset.sum_image (f := fun y ↦ ZMod.stdAddChar (b*y))
        (g := fun x ↦ 2*x) (mul_right_injective₀ h₂).injOn).symm
    _ = _ := by rw [himg]; rfl

/-- When multiplication by two preserves the domain the chain bound applies to each
individual nonzero frequency. -/
theorem pointwise_of_double_closed (D : Finset (ZMod p)) (hneg : ∀ x ∈ D, -x ∈ D)
    (h₂ : (2 : ZMod p) ≠ 0) (hclosed : ∀ x ∈ D, 2*x ∈ D)
    {m : ℕ} (hp : p ≤ 2 ^ (m+1)) (b : ZMod p) (hb : b ≠ 0) (t : ℕ) :
    m * ‖eta ZMod.stdAddChar D b‖ + t * (D.card : ℝ) ≤
      m * (D.card : ℝ) + (2 * ∑ j ∈ range (m+1), m.choose j * (t-j) : ℕ) := by
  have hpows (j : ℕ) : eta ZMod.stdAddChar D (2^j*b) = eta ZMod.stdAddChar D b := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_assoc, period_double_of_closed D h₂ hclosed, ih]
  simpa only [hpows, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
    doubling_chain D hneg hp b hb t

#print axioms pointwise_of_double_closed
#print axioms doubling_chain
#print axioms production_first_chain
#print axioms production_second_chain

end ArkLib.ProximityGap.PrimeFieldDoublingChain
