/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonPuncture

/-! # A full safe error count beyond Johnson by omitting several coordinates

Count all `r`-sets disjoint from each selected agreement support. At any fixed
omission set, the supports live on just `n-r` coordinates, so the strict
Johnson rank bound applies on that smaller universe.
-/

set_option autoImplicit false
namespace ProximityGap.MultipleOmissionJohnson
open Finset Code InterleavedListJohnsonRank
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
  (card_le_universe_of_equal_card_pair_inter_le)
open scoped ENNReal

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Each block omits exactly `choose (n-t) r` samples and each sample
can occur in at most `n-r` blocks. -/
theorem block_omissions {m t s r : ℕ} (S : Fin m → Finset I) (ht : 1 ≤ t)
    (hw : ∀ i, (S i).card = t) (hp : Pairwise fun i j => (S i ∩ S j).card ≤ s)
    (hs : (Fintype.card I - r) * s < t ^ 2) :
    m * (Fintype.card I - t).choose r ≤ (Fintype.card I).choose r * (Fintype.card I - r) := by
  classical
  let samples := (univ : Finset I).powersetCard r
  let cond (i : Fin m) (R : Finset I) := Disjoint R (S i)
  have above (i : Fin m) : (samples.bipartiteAbove cond i).card =
      (Fintype.card I - t).choose r := by
    have he : samples.bipartiteAbove cond i = ((S i)ᶜ).powersetCard r := by
      ext R
      simp [samples, cond, mem_powersetCard, subset_compl_iff_disjoint_right, and_comm]
    rw [he, card_powersetCard, card_compl, hw]
  have below (R : Finset I) (hR : R ∈ samples) :
      (univ.bipartiteBelow cond R).card ≤ Fintype.card I - r := by
    let T := univ.bipartiteBelow cond R
    let A (i : T) := (S i.val).subtype (· ∈ Rᶜ)
    have ha (i : T) : (A i).card = t := by
      have hdis : Disjoint R (S i.val) := (mem_filter.mp i.property).2
      have hf : ((S i.val).filter (· ∈ Rᶜ)) = S i.val :=
        filter_true_of_mem fun _ hx => subset_compl_iff_disjoint_right.mpr hdis.symm hx
      rw [show (A i).card = ((S i.val).filter (· ∈ Rᶜ)).card from card_subtype _ _, hf, hw]
    have hpair : Pairwise fun i j => (A i ∩ A j).card ≤ s := by
      intro i j hij
      have he : A i ∩ A j = (S i.val ∩ S j.val).subtype (· ∈ Rᶜ) := by ext; simp [A]
      rw [he, card_subtype]
      exact (card_filter_le _ _).trans (hp (fun h => hij (Subtype.ext h)))
    have hnn : Fintype.card ↥(Rᶜ) = Fintype.card I - r := by
      rw [Fintype.card_coe, card_compl, (mem_powersetCard.mp hR).2]
    have h := card_le_universe_of_equal_card_pair_inter_le A _ t s hnn ht ha hpair (by omega)
    exact (Fintype.card_coe T) ▸ h
  have h := card_mul_le_card_mul (s := (univ : Finset (Fin m))) (t := samples) cond
    (fun i _ => (above i).ge) below
  simpa [samples] using h

omit [DecidableEq I] in
/-- Any field and interleaving width obey the simultaneous-omission list cap. -/
theorem list_le_of_omissions {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k t width r B : ℕ) (δ : ℝ) (ht : 1 ≤ t)
    (hδ : δ * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1)
    (hs : (Fintype.card I - r) * (k - 1) < t ^ 2)
    (hbudget : (Fintype.card I).choose r * (Fintype.card I - r) <
      (B + 1) * (Fintype.card I - t).choose r) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F))) δ ≤ B := by
  classical
  apply interleaved_lambda_le_of_block_bound D k t width B δ hδ
  intro m S hw hp
  have h := (block_omissions S ht hw hp hs).trans_lt hbudget
  by_contra! hm
  exact h.not_ge (Nat.mul_le_mul_right _ hm)


private def fall (x step : ℤ) : ℕ → ℤ
  | 0 => 1
  | r + 1 => fall x step r * (x - step * r)

private theorem fall_cast (x r : ℕ) (h : r ≤ x) :
    fall (x : ℤ) 1 r = x.descFactorial r := by
  induction r with
  | zero => simp [fall]
  | succ r ih =>
    rw [fall, ih (by omega), Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
    ring

private theorem fall_scale (c x : ℤ) (r : ℕ) :
    fall (c * x) c r = c ^ r * fall x 1 r := by
  induction r with
  | zero => simp [fall]
  | succ r ih => rw [fall, ih, fall, pow_succ]; ring

private theorem fall_mono {x y c : ℤ} (r : ℕ) (hc : 0 ≤ c) (h : c * r ≤ x) (hxy : x ≤ y) :
    0 ≤ fall x c r ∧ fall x c r ≤ fall y c r := by
  induction r with
  | zero => simp [fall]
  | succ r ih =>
    have hl : c * (r : ℤ) ≤ x := by push_cast at h; nlinarith
    obtain ⟨ha, hb⟩ := ih hl
    simpa only [fall] using And.intro (mul_nonneg ha (by omega : 0 ≤ x - c * r))
      (mul_le_mul hb (by omega : x - c * r ≤ y - c * r) (by omega) (ha.trans hb))

private theorem budget_of_fall {n t r C c a b : ℕ} (hr : r < n) (ht : t + r ≤ n)
    (hc : 0 < c) (hmin : c * r ≤ a * n + b) (htan : a * n + b ≤ c * (n - t))
    (hpoly : (c : ℤ) ^ r * fall ((n : ℤ) - 1) 1 r ≤
      C * fall ((a : ℤ) * n + b) c r) :
    n.choose r * (n - r) ≤ (C * n) * (n - t).choose r := by
  have hh := (fall_mono (x := (a : ℤ) * n + b) (y := (c : ℤ) * (n - t : ℕ)) r
    (by positivity : 0 ≤ (c : ℤ)) (by exact_mod_cast hmin) (by exact_mod_cast htan)).2
  have hboth := hpoly.trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg C))
  rw [fall_scale, show (n : ℤ) - 1 = (↑(n - 1) : ℤ) by omega, fall_cast _ _ (by omega),
    fall_cast _ _ (by omega), ← mul_left_comm] at hboth
  have hdesc : (n - 1).descFactorial r ≤ C * (n - t).descFactorial r := by
    exact_mod_cast le_of_mul_le_mul_left hboth (by positivity : (0 : ℤ) < (c : ℤ) ^ r)
  have he : n * (n - 1).descFactorial r = (n - r) * n.descFactorial r := by
    cases n with
    | zero => omega
    | succ n =>
      simpa [Nat.descFactorial_succ] using (Nat.succ_descFactorial_succ n r).symm
  apply Nat.le_of_mul_le_mul_left _ (Nat.factorial_pos r)
  calc r.factorial * (n.choose r * (n - r)) = n * (n - 1).descFactorial r := by
         rw [he, Nat.descFactorial_eq_factorial_mul_choose]; ring
    _ ≤ n * (C * (n - t).descFactorial r) := Nat.mul_le_mul_left n hdesc
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose]; ring

/-- Denominators of the four challenge rates, in decreasing rate order. -/
def divisor : Fin 4 → ℕ := ![2, 4, 8, 16]

/-- Simultaneous omissions needed uniformly over the length. -/
def omissions : Fin 4 → ℕ := ![3, 5, 6, 9]

/-- A sufficient multiple of block length for one integer strictly beyond Johnson. -/
def multiple : Fin 4 → ℕ := ![40, 32, 14, 14]

private def scale : Fin 4 → ℕ := ![140, 2, 280, 4]
private def slope : Fin 4 → ℕ := ![41, 1, 181, 3]
private def intercept : Fin 4 → ℕ := ![98, 4, 392, 12]

private theorem poly_table (j : Fin 4) (n : ℕ) (hn : 256 ≤ n) :
    (scale j : ℤ) ^ omissions j * fall ((n : ℤ) - 1) 1 (omissions j) ≤
      multiple j * fall ((slope j : ℤ) * n + intercept j) (scale j) (omissions j) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hu : (0 : ℤ) ≤ u := Nat.cast_nonneg _
  fin_cases j <;>
    norm_num [scale, slope, intercept, multiple, omissions, fall] <;>
    apply sub_nonneg.mp <;> ring_nf <;> positivity


private def weight : Fin 4 → ℤ := ![140, 1, 280, 1]
private def topSlope : Fin 4 → ℤ := ![198, 2, 792, 4]
private def shift : Fin 4 → ℤ := ![98, 1, 392, 2]

private theorem weight_tangent (j : Fin 4) (k t : ℤ) (hn : 256 ≤ divisor j * k)
    (hlo : t ^ 2 < divisor j * k * (k - 1)) :
    weight j * t < topSlope j * k - shift j := by
  by_contra! h
  have hn' : 0 ≤ topSlope j * k - shift j := by
    fin_cases j <;> norm_num [topSlope, divisor, shift] at * <;> omega
  have hs := mul_self_le_mul_self hn' h
  fin_cases j <;> norm_num [weight, divisor, topSlope, shift] at * <;> nlinarith [sq_nonneg k]

private theorem bounds_int (j : Fin 4) (k t : ℤ) (hn : 256 ≤ divisor j * k) (ht : 0 ≤ t)
    (hlo : t ^ 2 < divisor j * k * (k - 1)) (hhi : divisor j * k * (k - 1) ≤ (t + 1) ^ 2) :
    let n := (divisor j : ℤ) * k
    1 ≤ t ∧ t + omissions j ≤ n ∧ (n - omissions j) * (k - 1) < t ^ 2 ∧
      scale j * omissions j ≤ (slope j : ℤ) * n + intercept j ∧
      (slope j : ℤ) * n + intercept j ≤ scale j * (n - t) := by
  have htan := weight_tangent j k t hn hlo
  have hk : 16 ≤ k := by fin_cases j <;> norm_num [divisor] at hn <;> omega
  have hpos : 1 ≤ t := by
    by_contra! h
    have : t = 0 := by omega
    subst t
    fin_cases j <;> norm_num [divisor] at hhi <;> nlinarith [sq_nonneg (k - 8)]
  fin_cases j <;>
    norm_num [divisor, omissions, scale, slope, intercept, topSlope, weight, shift] at * <;>
    refine ⟨hpos, by omega, ?_, by omega, by omega⟩ <;> nlinarith

/-- The agreement count at the first integer error strictly above finite-length Johnson.
Subtracting one before the square root also handles a square radicand. -/
def agreements (n k : ℕ) : ℕ := (n * (k - 1) - 1).sqrt

private theorem grid_sq {n k : ℕ} (hp : 0 < n * (k - 1)) :
    (agreements n k) ^ 2 < n * (k - 1) ∧ n * (k - 1) ≤ (agreements n k + 1) ^ 2 := by
  have h1 := Nat.sqrt_le' (n * (k - 1) - 1)
  have h2 := Nat.succ_le_succ_sqrt' (n * (k - 1) - 1)
  unfold agreements
  omega

omit [DecidableEq I] in
/-- One full grid point beyond Johnson is safe at length `n ≥ 256` for arbitrary fields,
domains, and widths when the list budget is respectively at least `40n, 32n, 14n, 14n`. -/
theorem four_rate_safe {F : Type*} [Field F] [Nonempty I] (D : I ↪ F) (j : Fin 4) (k width : ℕ)
    (hn : Fintype.card I = divisor j * k) (hlarge : 256 ≤ Fintype.card I) :
    let n := Fintype.card I
    let t := agreements n k
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ ((multiple j * n : ℕ) : ℕ∞) := by
  classical
  dsimp only
  let n := Fintype.card I
  let t := agreements n k
  have hk : 16 ≤ k := by
    fin_cases j <;> norm_num [divisor] at hn <;> omega
  have hp : 0 < n * (k - 1) := Nat.mul_pos (by dsimp [n]; omega) (by omega)
  obtain ⟨hlo, hhi⟩ := grid_sq hp
  have hn' : (n : ℤ) = divisor j * (k : ℤ) := by exact_mod_cast hn
  have hpred : (↑(k - 1) : ℤ) = (k : ℤ) - 1 := by omega
  have hzlo : (t : ℤ) ^ 2 < n * ((k : ℤ) - 1) := by rw [← hpred]; exact_mod_cast hlo
  have hzhi : (n : ℤ) * (k - 1) ≤ ((t : ℤ) + 1) ^ 2 := by
    rw [← hpred]; exact_mod_cast hhi
  have hnz : (256 : ℤ) ≤ n := by exact_mod_cast hlarge
  have hb := bounds_int j (k : ℤ) (t : ℤ) (hn' ▸ hnz) (Nat.cast_nonneg _) (hn' ▸ hzlo) (hn' ▸ hzhi)
  dsimp only at hb
  rw [← hn'] at hb
  obtain ⟨ht, htr, hs, hmin, htan⟩ := hb
  have hrn : omissions j < n := by omega
  have htn : t + omissions j ≤ n := by omega
  have ht' : t ≤ n := by omega
  have hsN : (n - omissions j) * (k - 1) < t ^ 2 := by
    rw [← hpred, ← Nat.cast_sub (le_of_lt hrn)] at hs
    exact_mod_cast hs
  have htanN : slope j * n + intercept j ≤ scale j * (n - t) := by
    rw [← Nat.cast_sub ht'] at htan
    exact_mod_cast htan
  have hsc : 0 < scale j := by fin_cases j <;> decide
  have cap := budget_of_fall hrn htn hsc (by exact_mod_cast hmin) htanN (poly_table j n hlarge)
  apply list_le_of_omissions D k t width (omissions j) (multiple j * n) _ (by omega)
  · change ((n - t : ℕ) : ℝ) / n * n < (n : ℝ) - t + 1
    rw [div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0), Nat.cast_sub ht']
    linarith
  · exact hsN
  · exact cap.trans_lt
      (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.choose_pos (by omega)))

/-- The displayed error count is the very first integral count strictly above the
real Johnson radius. Its predecessor is still at or below Johnson. -/
theorem johnson_grid {n k : ℕ} (hk : 1 < k) (hkn : k ≤ n) :
    let t := agreements n k
    (((n - (t + 1) : ℕ) : ℝ) / n ≤ 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n)) ∧
      1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n) < ((n - t : ℕ) : ℝ) / n := by
  let t := agreements n k
  have hn : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by positivity
  obtain ⟨hlo, hhi⟩ := grid_sq (Nat.mul_pos hn (by omega : 0 < k - 1))
  have ht : t < n := by
    by_contra! hf
    have := Nat.mul_le_mul_left n (show k - 1 ≤ n by omega)
    have := Nat.mul_self_le_mul_self hf
    change t ^ 2 < _ at hlo
    nlinarith
  let x := (n : ℝ) * Real.sqrt (((k - 1 : ℕ) : ℝ) / n)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hex : x ^ 2 = n * ((k - 1 : ℕ) : ℝ) := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have l : (t : ℝ) ^ 2 < x ^ 2 := by rw [hex]; exact_mod_cast hlo
  have h : x ^ 2 ≤ ((t : ℝ) + 1) ^ 2 := by rw [hex]; exact_mod_cast hhi
  have ha : (t : ℝ) < x := by
    by_contra! hc
    nlinarith [mul_self_le_mul_self hx hc]
  have hb : x ≤ (t : ℝ) + 1 := by
    by_contra! hc
    nlinarith [mul_self_lt_mul_self (by positivity : 0 ≤ (t : ℝ) + 1) hc]
  dsimp only
  change ↑(n - (t + 1)) / (n : ℝ) ≤ _ ∧ _ < ↑(n - t) / (n : ℝ)
  rw [div_le_iff₀ hnr, lt_div_iff₀ hnr, Nat.cast_sub (by omega : t + 1 ≤ n),
    Nat.cast_sub ht.le, Nat.cast_add, Nat.cast_one]
  dsimp [x] at ha hb
  constructor <;> nlinarith

/-- The numerical test using one choice of omission size and the smaller-universe rank cap. -/
def OmissionCertificate (n k t B : ℕ) : Prop :=
  ∃ r : ℕ, (n - r) * (k - 1) < t ^ 2 ∧ n.choose r * (n - r) < (B + 1) * (n - t).choose r

private theorem ratio_propagates {u v l n i : ℕ} (huv : u ≤ v)
    (hinit : l * u.choose i ≤ n * v.choose i) {r : ℕ} (hr : i ≤ r) :
    l * u.choose r ≤ n * v.choose r := by
  induction r, hr using Nat.le_induction with
  | base => exact hinit
  | succ r _ ih =>
    apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos r)
    calc l * u.choose (r + 1) * (r + 1) = l * u.choose r * (u - r) := by
           rw [mul_assoc, Nat.choose_succ_right_eq]; ring
      _ ≤ n * v.choose r * (v - r) := Nat.mul_le_mul ih (Nat.sub_le_sub_right huv _)
      _ = n * v.choose (r + 1) * (r + 1) := by
        rw [mul_assoc n _ (r + 1), Nat.choose_succ_right_eq]; ring

private theorem optimal_omission {n k t r cap : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hr : 0 < r) (strict : (n - r) * (k - 1) < t ^ 2)
    (prev : t ^ 2 ≤ (n - (r - 1)) * (k - 1))
    (lo : cap * (n - t).choose r ≤ n * (n - 1).choose r)
    (hi : n * (n - 1).choose r < (cap + 1) * (n - t).choose r) (B : ℕ) :
    OmissionCertificate n k t B ↔ cap ≤ B := by
  have he (x : ℕ) : n.choose x * (n - x) = n * (n - 1).choose x := by
    cases n with
    | zero => omega
    | succ n => simpa [Nat.mul_comm] using (Nat.choose_mul_succ_eq n x).symm
  constructor
  · rintro ⟨s, hstrict, htest⟩
    have hmin : r ≤ s := by
      by_contra! hs
      exact hstrict.not_ge (prev.trans (Nat.mul_le_mul_right _ (by omega)))
    rw [he] at htest
    by_contra! hB
    exact htest.not_ge ((Nat.mul_le_mul_right _ hB).trans (ratio_propagates (by omega) lo hmin))
  · intro h
    refine ⟨r, strict, ?_⟩
    rw [he]
    exact hi.trans_le (Nat.mul_le_mul_right _ (by omega))

/-- The exact minimum budgets attainable by this omission test on the first open list
steps for the nominated primes. Both candidates share the half, quarter, and sixteenth
steps. At eighth rate, the second nominated prime already passes the earlier step. -/
theorem named_omission_budgets (B : ℕ) :
    (OmissionCertificate 1073741824 536870912 759250124 B ↔ 3665983882 ≤ B) ∧
    (OmissionCertificate 1073741824 268435456 536870910 B ↔ 34359737888 ≤ B) ∧
    (OmissionCertificate 1073741824 134217728 379625061 B ↔ 1660990722 ≤ B) ∧
    (OmissionCertificate 1073741824 134217728 379625060 B ↔ 22759945996 ≤ B) ∧
    (OmissionCertificate 1073741824 67108864 268435453 B ↔ 10725307448 ≤ B) := by
  refine ⟨optimal_omission (r := 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ B,
    optimal_omission (r := 5) ?_ ?_ ?_ ?_ ?_ ?_ ?_ B,
    optimal_omission (r := 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ B,
    optimal_omission (r := 7) ?_ ?_ ?_ ?_ ?_ ?_ ?_ B,
    optimal_omission (r := 8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ B⟩
  all_goals try simp only [Nat.choose_eq_descFactorial_div_factorial]
  all_goals decide

end ProximityGap.MultipleOmissionJohnson

#print axioms ProximityGap.MultipleOmissionJohnson.block_omissions
#print axioms ProximityGap.MultipleOmissionJohnson.four_rate_safe
#print axioms ProximityGap.MultipleOmissionJohnson.johnson_grid
#print axioms ProximityGap.MultipleOmissionJohnson.named_omission_budgets
