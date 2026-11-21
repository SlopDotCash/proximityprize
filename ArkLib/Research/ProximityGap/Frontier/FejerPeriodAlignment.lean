/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldPeriodAlignment
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Positive kernels for partially aligned periods

The squared norm of a sum of characters is nonnegative at every site. A lower
bound at a subset of sites consequently gives a lower bound for some nonzero
frequency on the whole domain. Taking an arithmetic progression of frequencies
recovers the finite Fejér kernel.
-/

namespace ArkLib.ProximityGap.Frontier.FejerPeriodAlignment

open Finset SubgroupGaussSumSecondMoment ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- Squared length of the sum of the characters with frequencies in `B`. -/
noncomputable def kernelValue (B : Finset (ZMod p)) (x : ZMod p) : ℝ :=
  Complex.normSq (∑ i ∈ B, ZMod.stdAddChar (i*x))

/-- Expanding the squared norm expresses the kernel as a sum over differences. -/
theorem kernelValue_eq (B : Finset (ZMod p)) (x : ZMod p) :
    kernelValue B x = ∑ i ∈ B, ∑ j ∈ B, (ZMod.stdAddChar ((i-j)*x)).re := by
  have h : (∑ i ∈ B, ZMod.stdAddChar (i*x)) * conj (∑ i ∈ B, ZMod.stdAddChar (i*x)) =
      ∑ i ∈ B, ∑ j ∈ B, ZMod.stdAddChar ((i-j)*x) := by
    rw [map_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simpa only [kernelValue, Complex.mul_conj, Complex.ofReal_re, Complex.re_sum] using
    congrArg Complex.re h

/-- The complete positive-kernel mass is a sum of ordinary Gaussian periods. -/
theorem kernel_mass (D B : Finset (ZMod p)) :
    ∑ x ∈ D, kernelValue B x = ∑ i ∈ B, ∑ j ∈ B, (eta ZMod.stdAddChar D (i-j)).re := by
  simp_rw [kernelValue_eq, eta, Complex.re_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]

/-- If the aligned sites contribute more mass than the diagonal and all the proposed
nonzero-frequency bounds can account for, a nonzero difference violates the bound. -/
theorem exists_large_period (D B T : Finset (ZMod p)) (hTD : T ⊆ D) (s r : ℝ)
    (halign : ∀ x ∈ T, s ≤ kernelValue B x)
    (hmass : (B.card : ℝ)*D.card + B.card*(B.card-1 : ℝ)*r < T.card*s) :
    ∃ i ∈ B, ∃ j ∈ B, i ≠ j ∧ r < (eta ZMod.stdAddChar D (i-j)).re := by
  classical
  by_contra! h
  have hl : (T.card : ℝ)*s ≤ ∑ x ∈ D, kernelValue B x := calc
    _ = ∑ _x ∈ T, s := by simp
    _ ≤ ∑ x ∈ T, kernelValue B x := sum_le_sum halign
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hTD (fun _ _ _ => Complex.normSq_nonneg _)
  rw [kernel_mass] at hl
  have hi (i : ZMod p) (hi : i ∈ B) :
      ∑ j ∈ B, (eta ZMod.stdAddChar D (i-j)).re ≤ D.card+(B.card-1 : ℝ)*r := by
    rw [← add_sum_erase B (fun j => (eta ZMod.stdAddChar D (i-j)).re) hi]
    simp only [sub_self, eta, zero_mul, AddChar.map_zero_eq_one, sum_const,
      nsmul_eq_mul, mul_one, Complex.natCast_re]
    apply add_le_add_right
    calc
      _ ≤ ∑ _j ∈ B.erase i, r := by
        apply sum_le_sum
        intro j hj
        exact h i hi j (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, card_erase_of_mem hi, Nat.cast_sub (card_pos.mpr ⟨i,hi⟩)]
        simp
  have hu := sum_le_sum hi
  simp only [sum_const, nsmul_eq_mul] at hu
  linarith only [hmass, hl, hu, mul_add (B.card : ℝ) (D.card : ℝ) ((B.card-1 : ℝ)*r),
    mul_assoc (B.card : ℝ) (B.card-1 : ℝ) r]

private theorem short_multiple {n : ℕ} (hn : 0 < n) (z : ℤ)
    (hshort : |(z : ℝ)| * (n : ℝ)^2 ≤ p) {j : ℕ} (hj : j < n) :
    1 - 20 / (n : ℝ)^2 ≤ (ZMod.stdAddChar ((j : ZMod p)*(z : ZMod p))).re := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj.le
  have ha : |(j : ℝ)*z| * n ≤ p := calc
    _ = ((j : ℝ)*n)* |(z : ℝ)| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]; ring
    _ ≤ ((n : ℝ)*n)* |(z : ℝ)| := by gcongr
    _ ≤ _ := by convert hshort using 1; ring
  have ha' : |(j : ℝ)*z/(p : ℝ)| ≤ (n : ℝ)⁻¹ := by
    rw [abs_div, abs_of_pos hp, inv_eq_one_div, div_le_div_iff₀ hp hn']; simpa using ha
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha' 2
  rw [sq_abs, inv_pow] at hs
  have hpi : 2*Real.pi^2 ≤ 20 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2, mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
  have hu : 2*Real.pi^2*((j : ℝ)*z/p)^2 ≤ 20*((n : ℝ)^2)⁻¹ := by gcongr
  have hz : (j : ZMod p)*(z : ZMod p) = ((j*z : ℤ) : ZMod p) := by push_cast; rfl
  rw [hz, ZMod.stdAddChar_coe]
  have he : (2*Real.pi*Complex.I*((j*z : ℤ) : ℂ)/p : ℂ) =
      ((2*Real.pi*((j : ℝ)*z/p) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I_re]
  apply le_trans _ Real.one_sub_sq_div_two_le_cos
  rw [div_eq_mul_inv (20 : ℝ)]
  nlinarith only [hu]

/-- Partial alignment suffices. On any domain of at least 64 sites, every subset whose
standard lifts have absolute value at most `p / |D|²` gives an actual nonprincipal
period with real part greater than `|T| - 2`. -/
theorem period_of_short_sites (D T : Finset (ZMod p)) (hTD : T ⊆ D) (hn : 64 ≤ D.card)
    (hshort : ∀ x ∈ T, ∃ z : ℤ, (z : ZMod p) = x ∧ |(z : ℝ)| * D.card^2 ≤ p) :
    ∃ b : ZMod p, b ≠ 0 ∧ (T.card : ℝ)-2 < (eta ZMod.stdAddChar D b).re := by
  classical
  let n := D.card
  let B := (univ : Finset (Fin n)).image (fun i => (i.val : ZMod p))
  have hnp : n ≤ p := by simpa [n, ZMod.card] using D.card_le_univ
  have hB : B.card = n := by
    dsimp only [B]
    rw [card_image_of_injOn, card_univ, Fintype.card_fin]
    intro i _ j _ h
    apply Fin.ext
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans_le hnp),
      Nat.mod_eq_of_lt (j.isLt.trans_le hnp)] using congrArg ZMod.val h
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have hc : 0 ≤ 1 - 20 / (n : ℝ)^2 := by
    rw [sub_nonneg, div_le_one hn2]; nlinarith only [hnR, sq_nonneg ((n : ℝ)-64)]
  have hk (x : ZMod p) (hx : x ∈ T) : (n : ℝ)^2-40 ≤ kernelValue B x := by
    obtain ⟨z, rfl, hz⟩ := hshort x hx
    let W := ∑ i ∈ B, ZMod.stdAddChar (i*(z : ZMod p))
    have hRe : (n : ℝ)*(1-20/(n : ℝ)^2) ≤ W.re := calc
      _ = ∑ _i ∈ B, (1-20/(n : ℝ)^2) := by simp [hB, mul_sub]
      _ ≤ _ := by
        change _ ≤ (∑ i ∈ B, ZMod.stdAddChar (i*(z : ZMod p))).re
        rw [Complex.re_sum]
        apply sum_le_sum
        intro i hi
        obtain ⟨j, _, rfl⟩ := mem_image.mp hi
        exact short_multiple (by omega : 0 < n) z hz j.isLt
    have hs := pow_le_pow_left₀ (mul_nonneg hn0.le hc) hRe 2
    have he : ((n : ℝ)*(1-20/(n : ℝ)^2))^2 = (n : ℝ)^2-40+(20/(n : ℝ))^2 := by
      field_simp; ring
    rw [he] at hs
    change _ ≤ Complex.normSq W
    rw [Complex.normSq_apply]
    nlinarith only [hs, sq_nonneg W.im, sq_nonneg (20/(n : ℝ))]
  have hmass : (B.card : ℝ)*D.card+B.card*(B.card-1 : ℝ)*((T.card : ℝ)-2) <
      T.card*((n : ℝ)^2-40) := by
    rw [hB]; change (n : ℝ)*n+_ < _
    have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ n-40 by linarith) ht,
      mul_pos hn0 (show (0 : ℝ) < n-2 by linarith)]
  obtain ⟨i, _, j, _, hij, hp⟩ := exists_large_period D B T hTD _ _ hk hmass
  exact ⟨i-j, sub_ne_zero.mpr hij, hp⟩

/-- For an integral base of even order, the two signed initial blocks give a lower
bound on a period of the entire cyclic subgroup, including at proper prime factors. -/
theorem integral_base_period (a m L : ℕ) (ha : 1 ≤ a)
    (hg : IsPrimitiveRoot (a : ZMod p) (2*m)) (hm : 64 ≤ 2*m)
    (hL : L ≤ m) (hsize : a^L*(2*m)^2 ≤ p) :
    ∃ b : ZMod p, b ≠ 0 ∧ ((2*L : ℕ) : ℝ)-2 <
      (eta ZMod.stdAddChar ((range (2*m)).image fun i => (a : ZMod p)^i) b).re := by
  classical
  let D := (range (2*m)).image fun i => (a : ZMod p)^i
  let e := fun j : ℕ => if j < L then j else m + (j-L)
  let T := (range (2*L)).image fun j => (a : ZMod p)^(e j)
  have hD : D.card = 2*m := by
    dsimp only [D]
    rw [card_image_of_injOn, card_range]
    exact fun _ hi _ hj => hg.pow_inj (mem_range.mp hi) (mem_range.mp hj)
  have hbound (i : ℕ) (hi : i < 2*L) : e i < 2*m := by dsimp [e]; split <;> omega
  have hT : T.card = 2*L := by
    dsimp only [T]
    rw [card_image_of_injOn, card_range]
    intro i hi j hj heq
    have h := hg.pow_inj (hbound _ (mem_range.mp hi)) (hbound _ (mem_range.mp hj)) heq
    dsimp [e] at h
    split at h <;> split at h <;> omega
  have hTD : T ⊆ D := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨e i, mem_range.mpr (hbound i (mem_range.mp hi)), rfl⟩
  have hmneg : (a : ZMod p)^m = -1 := by
    have hs : ((a : ZMod p)^m)^2 = 1 := by simpa [←pow_mul, mul_comm] using hg.pow_eq_one
    apply (sq_eq_one_iff.mp hs).resolve_left
    intro he
    have hl := Nat.le_of_dvd (show 0 < m by omega) (hg.dvd_of_pow_eq_one m he)
    omega
  have ha' (j : ℕ) (hj : j ≤ L) : (a^j : ℕ)*(2*m)^2 ≤ p :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right ha hj)).trans hsize
  have hsmall (x : ZMod p) (hx : x ∈ T) :
      ∃ z : ℤ, (z : ZMod p) = x ∧ |(z : ℝ)| * D.card^2 ≤ p := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    have hj' := mem_range.mp hj
    rw [hD]
    by_cases hh : j < L
    · refine ⟨(a^j : ℕ), ?_, ?_⟩
      · simp [e, hh]
      · push_cast
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast ha' j hh.le
    · refine ⟨-((a^(j-L) : ℕ) : ℤ), ?_, ?_⟩
      · simp [e, hh, pow_add, hmneg]
      · push_cast
        rw [abs_neg, abs_of_nonneg (by positivity)]
        exact_mod_cast ha' (j-L) (by omega)
  obtain ⟨b, hb, h⟩ := period_of_short_sites D T hTD (by simpa [hD] using hm) hsmall
  exact ⟨b, hb, by simpa [hT] using h⟩

/-- A multiplicative domain containing `r` distinct rational primes contains a box of
short ordinary integers. Every exponent ranges over `0, …, L-1`, giving a real
nonprincipal period greater than `L^r-2`. -/
theorem period_of_rational_primes (D : Finset (ZMod p)) (r L : ℕ) (q : Fin r → ℕ)
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hone : 1 ∈ D) (hmul : ∀ x ∈ D, ∀ y ∈ D, x*y ∈ D) (hqD : ∀ i, (q i : ZMod p) ∈ D)
    (hn : 64 ≤ D.card) (hsize : (∏ i, q i)^L*D.card^2 ≤ p) :
    ∃ b : ZMod p, b ≠ 0 ∧ ((L^r : ℕ) : ℝ)-2 < (eta ZMod.stdAddChar D b).re := by
  classical
  let H : Submonoid (ZMod p) := {
    carrier := (D : Set (ZMod p))
    one_mem' := hone
    mul_mem' := fun hx hy => hmul _ hx _ hy }
  let z (e : Fin r → Fin L) : ℕ := ∏ i, (q i)^(e i : ℕ)
  let T := (univ : Finset (Fin r → Fin L)).image fun e => (z e : ZMod p)
  have hz (e : Fin r → Fin L) : z e * D.card^2 ≤ p := by
    apply le_trans _ hsize
    apply Nat.mul_le_mul_right
    rw [←prod_pow]
    exact prod_le_prod fun i _ => Nat.pow_le_pow_right (hq i).one_le (e i).isLt.le
  have hlt (e : Fin r → Fin L) : z e < p := by
    have he : 0 < z e := prod_pos fun i _ => pow_pos (hq i).pos _
    have hcard : 1 < D.card^2 := by nlinarith [hn]
    exact (lt_mul_of_one_lt_right he hcard).trans_le (hz e)
  have hval (e : Fin r → Fin L) (j : Fin r) : (z e).factorization (q j) = e j := by
    dsimp only [z]
    rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hq i).ne_zero), Finsupp.finsetSum_apply]
    rw [sum_eq_single j]
    · exact Nat.factorization_pow_self (hq j)
    · intro i _ hi
      rw [(hq i).factorization_pow, Finsupp.single_eq_of_ne (fun h => hi (hinj h.symm))]
    · simp
  have hcard : T.card = L^r := by
    dsimp only [T]
    rw [card_image_of_injOn, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    intro e _ f _ he
    have h := congrArg ZMod.val he
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt e), Nat.mod_eq_of_lt (hlt f)] at h
    funext i
    apply Fin.ext
    rw [←hval e i, h, hval f i]
  have hTD : T ⊆ D := by
    intro x hx
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    change (z e : ZMod p) ∈ H
    simp only [z, Nat.cast_prod, Nat.cast_pow]
    exact H.prod_mem fun i _ => H.pow_mem (hqD i) _
  have hsmall (x : ZMod p) (hx : x ∈ T) :
      ∃ t : ℤ, (t : ZMod p) = x ∧ |(t : ℝ)| * D.card^2 ≤ p := by
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    refine ⟨(z e : ℕ), by simp, ?_⟩
    push_cast
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hz e
  obtain ⟨b, hb, h⟩ := period_of_short_sites D T hTD hn hsmall
  exact ⟨b, hb, by simpa [hcard] using h⟩

/-- A prime divisor shared by `2^N-1` and `3^N-1` yields a large period on the
actual `N`th roots of unity. If `N` is dyadic, their order is also dyadic. -/
theorem common_prime_period (N L : ℕ) (hN : 0 < N) (hL : 64 ≤ L)
    (h₂ : p ∣ 2^N-1) (h₃ : p ∣ 3^N-1) (hsize : 6^L*N^2 ≤ p) :
    let D := Polynomial.nthRootsFinset N (1 : ZMod p)
    D.card ≤ N ∧ ∃ b : ZMod p, b ≠ 0 ∧ ((L^2 : ℕ) : ℝ)-2 < (eta ZMod.stdAddChar D b).re := by
  classical
  let D := Polynomial.nthRootsFinset N (1 : ZMod p)
  change D.card ≤ N ∧ _
  have hn : D.card ≤ N := by
    dsimp only [D]
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots N _)
  have hr {a : ℕ} (ha : 0 < a) (hd : p ∣ a^N-1) : (a : ZMod p)^N = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff (a^N-1) p).mpr hd
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ ha.ne')), Nat.cast_pow,
      Nat.cast_one, sub_eq_zero] at hz
    exact hz
  have h2 : (2 : ZMod p)^N = 1 := hr (by decide : 0 < 2) h₂
  have h3 : (3 : ZMod p)^N = 1 := hr (by decide : 0 < 3) h₃
  have hp : (2 : ℕ)^64 ≤ p := calc
    _ ≤ 6^64 := Nat.pow_le_pow_left (by decide) _
    _ ≤ 6^L := Nat.pow_le_pow_right (by decide) hL
    _ ≤ _ := (Nat.le_mul_of_pos_right _ (pow_pos hN 2)).trans hsize
  have hlt {i : ℕ} (hi : i < 64) : 2^i < p :=
    (Nat.pow_lt_pow_right (by decide : 1 < 2) hi).trans_le hp
  let A := (range 64).image fun i => ((2^i : ℕ) : ZMod p)
  have hA : A.card = 64 := by
    dsimp only [A]
    rw [card_image_of_injOn, card_range]
    intro i hi j hj he
    have he' := congrArg ZMod.val he
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt (mem_range.mp hi)),
      Nat.mod_eq_of_lt (hlt (mem_range.mp hj))] at he'
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he'
  have hAD : A ⊆ D := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    apply (Polynomial.mem_nthRootsFinset hN _).mpr
    push_cast
    rw [←pow_mul, mul_comm i N, pow_mul, h2, one_pow]
  let q : Fin 2 → ℕ := ![2,3]
  have hq (i : Fin 2) : (q i).Prime := by fin_cases i <;> decide
  have hqi : Function.Injective q := by decide
  have hqD (i : Fin 2) : (q i : ZMod p) ∈ D := by
    apply (Polynomial.mem_nthRootsFinset hN _).mpr
    fin_cases i
    · exact h2
    · exact h3
  have hQ : ∏ i, q i = 6 := by decide
  have hDsize : (∏ i, q i)^L*D.card^2 ≤ p := by
    rw [hQ]; exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)) hsize
  refine ⟨hn, period_of_rational_primes D 2 L q hq hqi ?_ ?_ hqD
    (by rw [←hA]; exact card_le_card hAD) hDsize⟩
  · exact (Polynomial.mem_nthRootsFinset hN _).mpr (one_pow _)
  · intro x hx y hy
    simpa only [one_mul] using Polynomial.mul_mem_nthRootsFinset hx hy

#print axioms kernelValue_eq
#print axioms exists_large_period
#print axioms period_of_short_sites
#print axioms integral_base_period
#print axioms period_of_rational_primes
#print axioms common_prime_period

end ArkLib.ProximityGap.Frontier.FejerPeriodAlignment
