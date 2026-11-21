/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.Fermat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import ArkLib.Research.ProximityGap.Frontier._AvX_AntipodalTransversalEvenCardLe
import ArkLib.Data.CodingTheory.ProximityGap.Round8CosetConcentration

/-!
# Simultaneous alignment of prime-field Gaussian periods

A six-bin pigeonhole on a signed cover produces a nonzero frequency at which every
summand has real part greater than one half. When the prime may vary this gives an
obstruction to uniform square-root cancellation even on cyclic subgroups of dyadic order.
-/

namespace ArkLib.ProximityGap.PrimeFieldPeriodAlignment

open Finset SubgroupGaussSumSecondMoment

variable {p : ℕ} [Fact p.Prime]

private lemma re_gt_half_of_short {z : ℤ}
    (h₁ : -(p : ℤ) < 6 * z) (h₂ : 6 * z < (p : ℤ)) :
    1 / 2 < (ZMod.stdAddChar (z : ZMod p)).re := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h₁' : -(p : ℝ) < 6 * z := by exact_mod_cast h₁
  have h₂' : 6 * (z : ℝ) < p := by exact_mod_cast h₂
  have hθ : |2 * Real.pi * z / p| < Real.pi / 3 := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hp).2
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr h₁')]
    · apply (div_lt_iff₀ hp).2
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr h₂')]
  rw [ZMod.stdAddChar_coe]
  have heq : (2 * Real.pi * Complex.I * z / p : ℂ) =
      ((2 * Real.pi * z / p : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs, ← Real.cos_pi_div_three]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hθ

private def bin (a : ZMod p) : Fin 6 :=
  ⟨6 * a.val / p, (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).2 (by
    have := a.val_lt
    omega)⟩

private lemma lift_diff_of_bin_eq {a c : ZMod p} (h : bin a = bin c) :
    ∃ z : ℤ, (z : ZMod p) = a - c ∧ -(p : ℤ) < 6 * z ∧ 6 * z < (p : ℤ) := by
  have heq : 6 * a.val / p = 6 * c.val / p := congrArg Fin.val h
  have h₁ := Nat.div_add_mod (6 * a.val) p
  have h₂ := Nat.div_add_mod (6 * c.val) p
  rw [heq] at h₁
  have h₃ := Nat.mod_lt (6 * a.val) (Fact.out : p.Prime).pos
  have h₄ := Nat.mod_lt (6 * c.val) (Fact.out : p.Prime).pos
  refine ⟨(a.val : ℤ) - c.val, by simp, ?_, ?_⟩ <;> omega

/-- A small signed cover forces a nonzero frequency with every phase in the open arc
with real part greater than one half. -/
theorem exists_frequency_of_signed_cover (T D : Finset (ZMod p))
    (hcover : ∀ x ∈ D, x ∈ T ∨ -x ∈ T) (hsize : 6 ^ T.card < p) :
    ∃ b : ZMod p, b ≠ 0 ∧ ∀ x ∈ D, 1 / 2 < (ZMod.stdAddChar (b * x)).re := by
  classical
  let f (a : ZMod p) (x : T) : Fin 6 := bin (a * (x : ZMod p))
  obtain ⟨a, c, hac, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hsize)
  have hT (x : ZMod p) (hx : x ∈ T) :
      ∃ z : ℤ, (z : ZMod p) = (a - c) * x ∧ -(p : ℤ) < 6 * z ∧ 6 * z < (p : ℤ) := by
    rw [sub_mul]
    exact lift_diff_of_bin_eq (congrFun heq ⟨x, hx⟩)
  refine ⟨a - c, sub_ne_zero.mpr hac, fun x hx ↦ ?_⟩
  rcases hcover x hx with ht | ht
  · obtain ⟨z, hz, h₁, h₂⟩ := hT x ht
    rw [← hz]
    exact re_gt_half_of_short h₁ h₂
  · obtain ⟨z, hz, h₁, h₂⟩ := hT (-x) ht
    have hz' : ((-z : ℤ) : ZMod p) = (a - c) * x := by simp [hz]
    rw [← hz']
    apply re_gt_half_of_short <;> omega

/-- The Gaussian period exceeds half the domain cardinality at a nonzero frequency. -/
theorem exists_large_period (T D : Finset (ZMod p)) (hD : D.Nonempty)
    (hcover : ∀ x ∈ D, x ∈ T ∨ -x ∈ T) (hsize : 6 ^ T.card < p) :
    ∃ b : ZMod p, b ≠ 0 ∧ D.card / 2 < ‖eta ZMod.stdAddChar D b‖ := by
  obtain ⟨b, hb, hphase⟩ := exists_frequency_of_signed_cover T D hcover hsize
  refine ⟨b, hb, lt_of_lt_of_le ?_ (Complex.re_le_norm _)⟩
  rw [eta, Complex.re_sum]
  simpa [div_eq_mul_inv] using Finset.sum_lt_sum_of_nonempty hD hphase

/-- For a negation-closed domain, one digit per antipodal pair suffices. -/
theorem large_period_of_antipodal (D : Finset (ZMod p)) (hne : D.Nonempty)
    (h₂ : (2 : ZMod p) ≠ 0) (h₀ : (0 : ZMod p) ∉ D)
    (hneg : ∀ x ∈ D, -x ∈ D) (hsize : 6 ^ (D.card / 2) < p) :
    ∃ b : ZMod p, b ≠ 0 ∧ D.card / 2 < ‖eta ZMod.stdAddChar D b‖ := by
  obtain ⟨T, _, _, hcov, hcard⟩ :=
    Frontier.AntipodalTransversal.exists_neg_transversal D h₂ h₀ hneg
  apply exists_large_period T D hne
  · intro x hx
    rw [← hcov, Finset.mem_union] at hx
    refine hx.imp_right ?_
    intro hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    simpa using hy
  · rwa [show T.card = D.card / 2 by omega]

open Round8CosetConcentration
open scoped Classical

/-- Once the order divides the prime minus one, its subgroup can be chosen in the field. -/
theorem exists_subgroup_of_order {n : ℕ} (hdiv : n ∣ p - 1) :
    ∃ H : Subgroup (ZMod p)ˣ, (sgFinset H).card = n := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hu' : orderOf u = p - 1 := by
    rw [hu, Nat.card_eq_fintype_card]
    exact (Nat.prime_iff_card_units p).mp Fact.out
  let H := Subgroup.zpowers (u ^ (orderOf u / n))
  refine ⟨H, ?_⟩
  rw [sgFinset_card, ← Nat.card_eq_fintype_card, Nat.card_zpowers]
  apply orderOf_pow_orderOf_div
  · rw [hu']
    have := (Fact.out : p.Prime).two_le
    omega
  · rwa [hu']

/-- For every prescribed positive order and every lower cutoff, there is a prime field
with a subgroup of that order and a nonzero frequency realizing more than half its size.
The prime also satisfies the sparsity hypothesis of the prime-field Shaw question. -/
theorem prime_witness_for_order (n cutoff : ℕ) (hn : 0 < n) :
    ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      cutoff < p ∧ n ^ 2 ≤ p ∧ ∃ H : Subgroup (ZMod p)ˣ, (sgFinset H).card = n ∧
        ∃ b : ZMod p, b ≠ 0 ∧ (n : ℝ) / 2 < ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  obtain ⟨p, hp, hgt, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (max cutoff (max (n ^ 2) (6 ^ n))) hn.ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := exists_subgroup_of_order ((Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm)
  have hne : (sgFinset H).Nonempty := Finset.card_pos.mp (hH.symm ▸ hn)
  have hsize : 6 ^ (sgFinset H).card < p := by rw [hH]; omega
  obtain ⟨b, hb, hlarge⟩ :=
    exists_large_period (sgFinset H) (sgFinset H) hne (fun _ hx ↦ Or.inl hx) hsize
  exact ⟨p, hp, by omega, by omega, H, hH, b, hb, by simpa only [hH] using hlarge⟩

/-- No absolute square-root constant works on dyadic subgroups in the sparse prime-field
range. The prime field and the order may both grow. -/
theorem dyadic_sqrt_counterexample (C : ℝ) (cutoff : ℕ) :
    ∃ (k p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      cutoff < p ∧ (2 ^ k) ^ 2 ≤ p ∧ ∃ H : Subgroup (ZMod p)ˣ,
        (sgFinset H).card = 2 ^ k ∧ ∃ b : ZMod p, b ≠ 0 ∧
          C * Real.sqrt ((2 : ℝ) ^ k) < ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 * C) (by norm_num : (1 : ℝ) < 2)
  let k := m + m
  obtain ⟨p, hp, hcut, hsparse, H, hH, b, hb, hlarge⟩ :=
    prime_witness_for_order (2 ^ k) cutoff (by positivity)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨k, p, hp, hcut, hsparse, H, hH, b, hb, lt_trans ?_ hlarge⟩
  have hpow : (2 : ℝ) ^ k = (2 ^ m) ^ 2 := by dsimp [k]; rw [pow_add, sq]
  push_cast
  rw [hpow, Real.sqrt_sq (by positivity)]
  nlinarith [mul_pos (show (0 : ℝ) < 2 ^ m by positivity) (sub_pos.mpr hm)]

/-- Fermat-number divisors supply arbitrarily large dyadic orders with a controlled
upper bound for the prime. This needs no estimate for primes in arithmetic progressions. -/
theorem dyadic_prime_window (m : ℕ) :
    ∃ k p : ℕ, m ≤ k ∧ p.Prime ∧ 2 ^ k ∣ p - 1 ∧
      6 ^ (2 ^ k) < p ∧ p ≤ 6 ^ (2 * 2 ^ k) := by
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (6 ^ (2 ^ m)) (by decide : 1 < (2 : ℕ))
  let j := t + 2
  let p := (Nat.fermatNumber j).minFac
  have hp : p.Prime := Nat.minFac_prime (Nat.fermatNumber_ne_one j)
  have hpf : p ∣ Nat.fermatNumber j := Nat.minFac_dvd _
  obtain ⟨v, hv⟩ := Nat.fermat_primeFactors_one_lt j p (by dsimp [j]; omega) hp hpf
  have hvpos : 0 < v := by
    by_contra! h
    have := hp.two_le
    simp [Nat.eq_zero_of_le_zero h] at hv
    omega
  have hplower : 2 ^ (j + 2) < p := by
    have := Nat.le_mul_of_pos_left (2 ^ (j + 2)) hvpos
    omega
  have hstart : 6 ^ (2 ^ m) < p := ht.trans <| lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide) (show t ≤ j + 2 by dsimp [j]; omega)) hplower
  have hstop : p ≤ 6 ^ (2 ^ (j + 2)) := calc
    p ≤ Nat.fermatNumber j := Nat.le_of_dvd (by have := Nat.three_le_fermatNumber j; omega) hpf
    _ ≤ 6 ^ (2 ^ j) := Nat.pow_lt_pow_left (by decide) (by positivity)
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
  let P (k : ℕ) := 6 ^ (2 ^ k) < p
  let k := Nat.findGreatest P (j + 2)
  have hexp := (Nat.pow_lt_pow_iff_right (by decide : 1 < 6)).mp (hstart.trans_le hstop)
  have hmj := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hexp
  have hmk : m ≤ k := Nat.le_findGreatest hmj.le hstart
  have hpk : P k := Nat.findGreatest_spec hmj.le hstart
  have hkj : k ≤ j + 2 := Nat.findGreatest_le _
  have hklt : k < j + 2 := lt_of_le_of_ne hkj (fun h ↦ (not_lt_of_ge hstop) (h ▸ hpk))
  have hnext := Nat.findGreatest_is_greatest (P := P)
    (show k < k + 1 by omega) (show k + 1 ≤ j + 2 by omega)
  refine ⟨k, p, hmk, hp, ?_, hpk, ?_⟩
  · have hdvd : 2 ^ (j + 2) ∣ p - 1 := ⟨v, by rw [hv, Nat.add_sub_cancel, Nat.mul_comm]⟩
    exact (pow_dvd_pow 2 hkj).trans hdvd
  · have h := le_of_not_gt hnext
    simpa [pow_succ, Nat.mul_comm] using h

/-- Arbitrarily large dyadic subgroups realize a linear-size period while the prime
lies between six to the order and six to twice the order. In particular the logarithm
in the Shaw bound has the necessary asymptotic order along this sequence. -/
theorem dyadic_log_scale_witness (m : ℕ) :
    ∃ (k p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      m ≤ k ∧ (2 ^ k) ^ 2 ≤ p ∧ 6 ^ (2 ^ k) < p ∧ p ≤ 6 ^ (2 * 2 ^ k) ∧
        ∃ H : Subgroup (ZMod p)ˣ, (sgFinset H).card = 2 ^ k ∧ ∃ b : ZMod p, b ≠ 0 ∧
          (2 : ℝ) ^ k / 2 < ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  obtain ⟨k, p, hmk, hp, hdiv, hlo, hhi⟩ := dyadic_prime_window m
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := exists_subgroup_of_order hdiv
  have hne : (sgFinset H).Nonempty := Finset.card_pos.mp (by rw [hH]; positivity)
  obtain ⟨b, hb, hsum⟩ := exists_large_period _ _ hne (fun _ hx ↦ Or.inl hx) (by simpa [hH] using hlo)
  refine ⟨k, p, hp, hmk, ?_, hlo, hhi, H, hH, b, hb, by simpa [hH] using hsum⟩
  apply le_trans ?_ hlo.le
  calc
    ((2 : ℕ) ^ k) ^ 2 = 4 ^ k := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ ≤ 6 ^ k := Nat.pow_le_pow_left (by decide) _
    _ ≤ 6 ^ (2 ^ k) := Nat.pow_le_pow_right (by decide) (Nat.lt_two_pow_self.le)

/-- At arbitrarily large dyadic orders, a nonzero period exceeds one fifth of
the precise square-root logarithmic scale of the prime-field Shaw bound. -/
theorem shaw_scale_lower (m : ℕ) :
    ∃ (k p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      m ≤ k ∧ (2 ^ k) ^ 2 ≤ p ∧ ∃ H : Subgroup (ZMod p)ˣ,
        (sgFinset H).card = 2 ^ k ∧ ∃ b : ZMod p, b ≠ 0 ∧
          Real.sqrt ((2 : ℝ) ^ k * Real.logb 2 (p / (2 : ℝ) ^ k)) / 5 <
            ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  obtain ⟨k, p, hp, hmk, hsp, _, hhi, H, hH, b, hb, hlarge⟩ := dyadic_log_scale_witness m
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨k, p, hp, hmk, hsp, H, hH, b, hb, lt_of_le_of_lt ?_ hlarge⟩
  let n : ℝ := 2 ^ k
  have h₁ : 1 ≤ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have h₂ : 0 < (p : ℝ) / n := div_pos (by exact_mod_cast hp.pos) (by linarith)
  have h₃ : (p : ℝ) / n ≤ (6 : ℝ) ^ (2 * 2 ^ k) :=
    (div_le_self (by positivity) h₁).trans (by exact_mod_cast hhi)
  have hc : Real.logb 2 6 ≤ 3 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 2 ^ 3)
    simpa [Real.logb_pow] using h
  have hlog : Real.logb 2 (p / n) ≤ 6 * n := calc
    _ ≤ Real.logb 2 ((6 : ℝ) ^ (2 * 2 ^ k)) :=
      Real.logb_le_logb_of_le (by norm_num) h₂ h₃
    _ = (2 * n) * Real.logb 2 6 := by rw [Real.logb_pow]; push_cast; rfl
    _ ≤ 6 * n := by nlinarith [mul_nonneg (by linarith : 0 ≤ n) (sub_nonneg.mpr hc)]
  change Real.sqrt (n * Real.logb 2 (p / n)) / 5 ≤ n / 2
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [mul_nonneg (by linarith : 0 ≤ n) (sub_nonneg.mpr hlog), sq_nonneg n]

#print axioms shaw_scale_lower
#print axioms dyadic_log_scale_witness
#print axioms exists_frequency_of_signed_cover
#print axioms large_period_of_antipodal
#print axioms prime_witness_for_order
#print axioms dyadic_sqrt_counterexample

end ArkLib.ProximityGap.PrimeFieldPeriodAlignment
