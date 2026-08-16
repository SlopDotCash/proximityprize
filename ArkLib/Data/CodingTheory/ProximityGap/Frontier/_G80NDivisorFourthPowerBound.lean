/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80N (#466, 2026-07-10): the DIVISOR fourth-power bound `d(y)⁴ ≤ 19680·y` —
  the PURE-Nat input that fires G80O, fully proven (axiom-clean, no named hypotheses).

## Content

`card_divisors_pow_four_le : ∀ y ≥ 1, (#y.divisors)⁴ ≤ 19680·y` — the classical
constant-exponent divisor bound `d(y) = O(y^{1/4})` with the explicit constant
`19680 = 41·10·4·3·2·2`. Mechanism: `d` is multiplicative with `d(p^a) = a+1`; per prime,
`(a+1)⁴ ≤ c(p)·p^a` where `c(2)=41, c(3)=10, c(5)=4, c(7)=3, c(11)=c(13)=2, c(p≥17)=1`
(the `p ≥ 17` case is the clean ratio induction `(a+2)⁴ ≤ 16(a+1)⁴ < 17·(a+1)⁴`); the
product of the `c`'s over any set of distinct primes is at most `19680`.

## Consequence (with G80O)

`intervalCount_sq_le_of_divisorBound` + this lemma give the UNCONDITIONAL
`T(W)² ≤ 19680^{1/4}·√W·... ` — concretely `T(W)⁸ ≤ 19680·W²·n⁴`, i.e.
`T(W) = O(n^{1/2}·W^{1/4})`, strictly below `min(n, W)` throughout `n^{2/3} ≪ W ≪ n²`
(e.g. `T(n) = O(n^{3/4})`): the first machine-checked nontrivial subgroup-interval
concentration bound. Fenced from the prize saddle by G80P regime disjointness (`W < √p`);
no prize claim. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound

/-- Per-prime constant: `41, 10, 4, 3, 2, 2` at `2, 3, 5, 7, 11, 13`, else `1`. -/
def cpr (q : ℕ) : ℕ :=
  if q = 2 then 41 else if q = 3 then 10 else if q = 5 then 4
  else if q = 7 then 3 else if q = 11 then 2 else if q = 13 then 2 else 1

theorem one_le_cpr (q : ℕ) : 1 ≤ cpr q := by
  unfold cpr
  split_ifs <;> norm_num

/-- The generic ratio step: `(a+2)⁴ ≤ 2·(a+1)⁴` for `a ≥ 8`. -/
theorem ratio_step {a : ℕ} (ha : 8 ≤ a) : (a + 2) ^ 4 ≤ 2 * (a + 1) ^ 4 := by
  nlinarith [sq_nonneg a, sq_nonneg (a + 1), pow_pos (Nat.succ_pos a) 4]

/-- Large primes: `(a+1)⁴ ≤ p^a` for `p ≥ 17`, `a ≥ 1` — ratio `≤ 16 < 17`. -/
theorem pow_four_le_large_prime {p : ℕ} (hp : 17 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    (a + 1) ^ 4 ≤ p ^ a := by
  induction a with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le ha with h1 | h2
    · -- a = 1
      have hb : b = 0 := by omega
      subst hb
      calc (1 + 1 : ℕ) ^ 4 = 16 := by norm_num
        _ ≤ p := by omega
        _ = p ^ 1 := (pow_one p).symm
    · -- b ≥ 1
      have hb1 : 1 ≤ b := by omega
      have hstep : (b + 2) ^ 4 ≤ 16 * (b + 1) ^ 4 := by
        have h2b : b + 2 ≤ 2 * (b + 1) := by omega
        calc (b + 2) ^ 4 ≤ (2 * (b + 1)) ^ 4 := Nat.pow_le_pow_left h2b 4
          _ = 16 * (b + 1) ^ 4 := by ring
      calc (b + 1 + 1) ^ 4 = (b + 2) ^ 4 := by ring_nf
        _ ≤ 16 * (b + 1) ^ 4 := hstep
        _ ≤ 16 * p ^ b := Nat.mul_le_mul_left 16 (ih hb1)
        _ ≤ p * p ^ b := Nat.mul_le_mul_right (p ^ b) (by omega)
        _ = p ^ (b + 1) := by rw [pow_succ]; ring

/-- The per-prime inequality: `(a+1)⁴ ≤ cpr(p)·p^a` for every prime `p` and `a ≥ 1`. -/
theorem pow_four_le_cpr_mul {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    (a + 1) ^ 4 ≤ cpr p * p ^ a := by
  rcases Nat.lt_or_ge p 17 with hsmall | hbig
  case inr =>
    -- p ≥ 17: cpr = 1
    have hc : cpr p = 1 := by
      unfold cpr
      split_ifs <;> omega
    rw [hc, one_mul]
    exact pow_four_le_large_prime hbig ha
  case inl =>
    -- p ∈ {2,3,5,7,11,13}
    have hp2 : 2 ≤ p := hp.two_le
    -- reduce a ≥ 9 to a = 8 via the ratio step and p ≥ 2
    induction a with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_or_ge 8 (b + 1) with hgt | hle
      case inr =>
        -- a = b+1 ≤ 8: finite check over p prime < 17 and a ≤ 8
        have hb7 : b ≤ 7 := by omega
        interval_cases p <;> first
          | (exact absurd hp (by decide))
          | (interval_cases b <;> simp [cpr] <;> norm_num)
      case inl =>
        -- a = b+1 ≥ 9: b ≥ 8
        have hb8 : 8 ≤ b := by omega
        have hb1 : 1 ≤ b := by omega
        have hih := ih hb1
        calc (b + 1 + 1) ^ 4 = (b + 2) ^ 4 := by ring_nf
          _ ≤ 2 * (b + 1) ^ 4 := ratio_step hb8
          _ ≤ 2 * (cpr p * p ^ b) := Nat.mul_le_mul_left 2 hih
          _ ≤ p * (cpr p * p ^ b) := Nat.mul_le_mul_right _ hp2
          _ = cpr p * p ^ (b + 1) := by ring

/-- Product of the per-prime constants over ANY finset of naturals is at most `19680`. -/
theorem prod_cpr_le (S : Finset ℕ) : ∏ q ∈ S, cpr q ≤ 19680 := by
  classical
  set small : Finset ℕ := {2, 3, 5, 7, 11, 13} with hsmall
  have hsub : ∏ q ∈ S, cpr q ≤ ∏ q ∈ S ∪ small, cpr q :=
    Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
      (fun q _ _ => one_le_cpr q)
  have hval : ∏ q ∈ S ∪ small, cpr q = ∏ q ∈ small, cpr q := by
    refine (Finset.prod_subset Finset.subset_union_right ?_).symm
    intro q _ hq
    have : q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 11 ∧ q ≠ 13 := by
      rw [hsmall] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      tauto
    unfold cpr
    obtain ⟨h2, h3, h5, h7, h11, h13⟩ := this
    split_ifs <;> first | rfl | omega
  have hsmallval : ∏ q ∈ small, cpr q = 19680 := by
    rw [hsmall]
    decide
  omega

/-- **CAPSTONE — the divisor fourth-power bound**: `d(y)⁴ ≤ 19680·y` for every `y ≥ 1`.
Pure Nat; fires G80O's `DivisorBound` unconditionally at exponent `1/4`. -/
theorem card_divisors_pow_four_le {y : ℕ} (hy : y ≠ 0) :
    y.divisors.card ^ 4 ≤ 19680 * y := by
  classical
  rw [Nat.card_divisors hy, ← Finset.prod_pow]
  have hfac : ∀ p ∈ y.primeFactors,
      (y.factorization p + 1) ^ 4 ≤ cpr p * p ^ (y.factorization p) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpos : 1 ≤ y.factorization p := by
      rw [← Nat.support_factorization] at hp
      have := Finsupp.mem_support_iff.mp hp
      omega
    exact pow_four_le_cpr_mul hprime hpos
  have hprod : ∏ p ∈ y.primeFactors, p ^ (y.factorization p) = y := by
    rw [← Nat.support_factorization]
    exact Nat.factorization_prod_pow_eq_self hy
  calc ∏ p ∈ y.primeFactors, (y.factorization p + 1) ^ 4
      ≤ ∏ p ∈ y.primeFactors, cpr p * p ^ (y.factorization p) :=
        Finset.prod_le_prod' hfac
    _ = (∏ p ∈ y.primeFactors, cpr p) *
          ∏ p ∈ y.primeFactors, p ^ (y.factorization p) := by
        rw [Finset.prod_mul_distrib]
    _ ≤ 19680 * ∏ p ∈ y.primeFactors, p ^ (y.factorization p) :=
        Nat.mul_le_mul_right _ (prod_cpr_le _)
    _ = 19680 * y := by rw [hprod]

end ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound.pow_four_le_cpr_mul
#print axioms
  ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound.prod_cpr_le
#print axioms
  ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound.card_divisors_pow_four_le
