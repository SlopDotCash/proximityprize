/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Q1 at `d = 16` via the DIRECT resultant/norm route (#407, lane LB2)

Continuation of lane `wf-LB`.  `wf-LB` REFUTED the Chai–Fan Q1 (Conj 4.12) **route (i)**
self-similarity bootstrap in char-`p` at `d = 32` (`(∗)_d : x₁ = 0 ⟹ x_a = 0` fails;
explicit `Y ⊂ ℤ/32`, `p = 1048609`, `p₁ = 0` but `p₃ ≠ 0`).  It noted `d = 16` is the last
clean dyadic level, and that closing Q1 at `d ≥ 16` needs *either* the full odd-symmetric
hypothesis *or* the **resultant form `R_d ≠ 0` directly**.

For a nonempty antipodal-free set of 16th roots, `v16PrimEmptyCharP_of_prime`
proves that one of its first eight odd power sums is nonzero, in every prime
characteristic. More generally, `exists_nonzero_odd_power_sum` detects a
missing opposite in a set of `(2*m)`th roots when the scalar `m` is nonzero.
The proof uses a finite geometric sum to isolate the chosen root.

The historical single-moment probes reported the entry primes
`{17, 97, 113, 193, 241, 337, 353, 401, 433, 577, 881}` among the scanned
primes below 40000 that split the 16th roots. The companion `OrderSixteenEntryPrimes.hasSignedEntry_iff` now certifies this
list in signed coordinates by norm descent. The arithmetic comparison `881 < 16^4` is checked here. The full odd-window theorem uses none
of those numerical observations. Production cancellation and the passage
from a single moment to the full window remain separate obligations.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.Q1DirectD16

/-! ## Even locator polynomials and antipodality -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- A polynomial all of whose odd coefficients vanish evaluates evenly: `P(-z) = P(z)`. -/
theorem eval_neg_eq_eval_of_oddCoeffZero {P : F[X]}
    (hOddCoeff : ∀ i : ℕ, Odd i → P.coeff i = 0) (z : F) :
    P.eval (-z) = P.eval z := by
  classical
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hiOdd : Odd i
  · simp [hOddCoeff i hiOdd]
  · have hiEven : Even i := Nat.not_odd_iff_even.mp hiOdd
    rw [hiEven.neg_pow z]

/-- **The full odd-descent forces antipodality (char-free).**

If the locator of a finite set has vanishing odd coefficients, its roots
are closed under negation. -/
theorem oddSymmetricVanishing_imp_antipodal_d16 (Y : Finset F)
    (hOddCoeff : ∀ i : ℕ, Odd i → (∏ y ∈ Y, (X - C y)).coeff i = 0) :
    Y.image (fun x => -x) = Y := by
  classical
  set P := ∏ y ∈ Y, (X - C y) with hPdef
  have heven : ∀ z : F, P.eval (-z) = P.eval z :=
    eval_neg_eq_eval_of_oddCoeffZero hOddCoeff
  have hclosed : ∀ x ∈ Y, -x ∈ Y := by
    intro x hx
    have hx0 : P.eval x = 0 := by
      rw [hPdef, eval_prod]; exact Finset.prod_eq_zero hx (by simp)
    have hnegroot : P.eval (-x) = 0 := by rw [heven x, hx0]
    rw [hPdef, eval_prod, Finset.prod_eq_zero_iff] at hnegroot
    obtain ⟨y, hy, hzero⟩ := hnegroot
    simp only [eval_sub, eval_X, eval_C] at hzero
    rw [sub_eq_zero.mp hzero]; exact hy
  have hsub : Y.image (fun x => -x) ⊆ Y := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hclosed x hx
  have hcard : (Y.image (fun x => -x)).card = Y.card :=
    Finset.card_image_of_injective Y neg_injective
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/-! ## Comparison with the reported single-moment threshold -/

/-- Largest prime in the historical single-moment probe's output. -/
def badReductionThresholdD16 : ℕ := 881

/-- The prize floor at `n = 16`, `β = 4`: `p ≥ 16⁴ = 65536`. -/
def prizeFloorD16 : ℕ := 16 ^ 4

/-- The reported threshold is below the prize floor at d=16. -/
theorem q1_d16_badReduction_threshold_below_prize :
    badReductionThresholdD16 < prizeFloorD16 := by
  unfold badReductionThresholdD16 prizeFloorD16; norm_num

/-- Comparison at any prime at or above the prize floor. -/
theorem prize_prime_above_badReduction {p : ℕ} (hp : prizeFloorD16 ≤ p) :
    badReductionThresholdD16 < p :=
  lt_of_lt_of_le q1_d16_badReduction_threshold_below_prize hp

/-! ## The full odd power-sum window -/

/-- No nonempty antipodal-free set of 16th roots has every odd moment below
16 equal to zero. The declaration below proves this over every prime field. -/
def V16PrimEmptyCharP (p : ℕ) : Prop :=
  ∀ Y : Finset (ZMod p), Y.Nonempty → (∀ y ∈ Y, y ^ 16 = 1) → (∀ y ∈ Y, -y ∉ Y) →
    ¬ ∀ a : ℕ, Odd a → a < 16 → ∑ y ∈ Y, y ^ a = 0

/-- Original consumer of the full-window emptiness predicate. -/
theorem q1_d16_prize_clean {p : ℕ} (hp : prizeFloorD16 ≤ p)
    (hV : V16PrimEmptyCharP p) :
    badReductionThresholdD16 < p ∧ V16PrimEmptyCharP p :=
  ⟨prize_prime_above_badReduction hp, hV⟩

/-- The complete odd Fourier window on a set of roots of unity detects each
antipodal imbalance. At a present root whose opposite is absent it recovers
the nonzero scalar m times that root. -/
theorem exists_nonzero_odd_power_sum {m : ℕ} (hm : (m : F) ≠ 0)
    (Y : Finset F) {y : F} (hy : y ∈ Y) (hneg : -y ∉ Y)
    (hroot : ∀ x ∈ Y, x ^ (2 * m) = 1) :
    ∃ r < m, ∑ x ∈ Y, x ^ (2 * r + 1) ≠ 0 := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => hm (by simp [h]))
  have hy0 : y ≠ 0 := by
    intro h
    have h1 := hroot y hy
    rw [h, zero_pow (by positivity : 2 * m ≠ 0)] at h1
    exact zero_ne_one h1
  by_contra! hall
  have filterSum (x : F) (hx : x ∈ Y) (hne : x ≠ y) :
      ∑ r ∈ range m, ((x/y)^2) ^ r = 0 := by
    have hsq : (x/y)^2 ≠ 1 := by
      intro heq
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hy0), one_mul] at heq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
      · exact hne h
      · exact hneg (h ▸ hx)
    have hpow : ((x/y)^2)^m = 1 := by
      rw [← pow_mul, div_pow, hroot x hx, hroot y hy, div_one]
    have h := geom_sum_mul ((x/y)^2) m
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hsq)
  have isolated :
      (∑ x ∈ Y, x * ∑ r ∈ range m, ((x/y)^2)^r) = y * (m : F) := by
    rw [sum_eq_single_of_mem y hy (fun x hx hne => by simp [filterSum x hx hne])]
    simp [hy0]
  have hz :
      (∑ x ∈ Y, x * ∑ r ∈ range m, ((x/y)^2)^r) = 0 := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro r hr
    calc
      (∑ x ∈ Y, x * ((x/y)^2)^r) =
          ∑ x ∈ Y, (y ^ (2*r))⁻¹ * x ^ (2*r+1) := by
        apply sum_congr rfl
        intro x _
        rw [← pow_mul, div_pow, div_eq_mul_inv, pow_succ]
        ring
      _ = 0 := by rw [← mul_sum, hall r (mem_range.mp hr), mul_zero]
  exact (mul_ne_zero hy0 hm) (isolated.symm.trans hz)

/-- The fixed-d predicate holds in every prime characteristic. -/
theorem v16PrimEmptyCharP_of_prime (p : ℕ) [hp : Fact p.Prime] : V16PrimEmptyCharP p := by
  intro Y hY hroot hanti hall
  obtain ⟨y, hy⟩ := hY
  by_cases h2 : p = 2
  · subst p
    exact (hanti y hy) (by simpa only [ZMod.neg_eq_self_mod_two] using hy)
  have h8 : ((8 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hd : p ∣ 2 ^ 3 := by simpa using hdvd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow hd))
  obtain ⟨r, hr, h⟩ := exists_nonzero_odd_power_sum h8 Y hy (hanti y hy) hroot
  exact h (hall (2*r+1) ⟨r, rfl⟩ (by omega))

/-- The existing d=16 gate with its full-window emptiness input discharged. -/
theorem q1_d16_prize_clean_of_prime (p : ℕ) [Fact p.Prime] (hp : prizeFloorD16 ≤ p) :
    badReductionThresholdD16 < p ∧ V16PrimEmptyCharP p :=
  q1_d16_prize_clean hp (v16PrimEmptyCharP_of_prime p)

/-- The increment in one statement: the structural antipodality lemma (char-free) AND the
arithmetic gate (`881 < 16⁴`).  This is the precise, honest content of the direct route at the
last clean dyadic level — Q1's char-free input plus the proven sub-prize bad-reduction bound. -/
theorem direct_route_d16_increment :
    (∀ Y : Finset ℚ, (∀ i : ℕ, Odd i → (∏ y ∈ Y, (X - C y)).coeff i = 0) →
        Y.image (fun x => -x) = Y) ∧
    badReductionThresholdD16 < prizeFloorD16 :=
  ⟨fun Y h => oddSymmetricVanishing_imp_antipodal_d16 Y h,
   q1_d16_badReduction_threshold_below_prize⟩

end ProximityGap.Frontier.Q1DirectD16

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.Q1DirectD16.eval_neg_eq_eval_of_oddCoeffZero
#print axioms ProximityGap.Frontier.Q1DirectD16.oddSymmetricVanishing_imp_antipodal_d16
#print axioms ProximityGap.Frontier.Q1DirectD16.q1_d16_badReduction_threshold_below_prize
#print axioms ProximityGap.Frontier.Q1DirectD16.prize_prime_above_badReduction
#print axioms ProximityGap.Frontier.Q1DirectD16.q1_d16_prize_clean
#print axioms ProximityGap.Frontier.Q1DirectD16.direct_route_d16_increment
#print axioms ProximityGap.Frontier.Q1DirectD16.exists_nonzero_odd_power_sum
#print axioms ProximityGap.Frontier.Q1DirectD16.v16PrimEmptyCharP_of_prime
#print axioms ProximityGap.Frontier.Q1DirectD16.q1_d16_prize_clean_of_prime
