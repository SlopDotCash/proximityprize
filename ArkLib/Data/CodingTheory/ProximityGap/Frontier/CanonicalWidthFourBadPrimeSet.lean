/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2W4CyclotomicNonCollision
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AlmostAllPrimesWick

/-!
# Canonical width-four bad-prime set for the resultant lane (#464)

The canonical width-four finite-field obstruction was reduced in
`E2W4CyclotomicNonCollision` to one integer resultant:

`Res(Φ_n, (X^4 + 1)^n - (X^2 + 1)^n)`.

This file packages the corresponding **finite bad-prime set**.  It is the prime-factor set of
that resultant.  A prime outside this set cannot support the canonical literal width-four
`≤ n` budget.  This is weaker than a prize proof: the missing step is still a prime-supply
statement producing a primitive-root prime outside the finite set in the desired range.  The
point of the packaging is to make that remaining arithmetic input explicit and countable.

## Main statements

* `canonicalRatioBadPrimes` — prime factors of the canonical obstruction resultant.
* `mem_canonicalRatioBadPrimes_of_e2BadScalarSet_mu_card_le_n_zmod` — any surviving canonical
  literal budget over `ZMod p` puts `p` in the finite bad-prime set.
* `not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes` — outside that set,
  the canonical lane refutes the literal budget.
* `canonicalRatioBadPrimes_card_le_crude` and
  `canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp` — divisor-count bounds from the crude and
  sharp resultant envelopes.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset
open ArkLib.ProximityGap.Frontier.AlmostAllPrimesWick
open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet

/-- The integer resultant carrying the denominator-cleared canonical width-four obstruction. -/
noncomputable def canonicalRatioResultant (n : ℕ) : ℤ :=
  Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
    (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree

/-- The finite bad-prime set for the canonical width-four resultant lane. -/
noncomputable def canonicalRatioBadPrimes (n : ℕ) : Finset ℕ :=
  (canonicalRatioResultant n).natAbs.primeFactors

/-- Membership in the canonical bad-prime set is exactly prime divisibility of the nonzero
canonical obstruction resultant. -/
theorem mem_canonicalRatioBadPrimes {n p : ℕ} :
    p ∈ canonicalRatioBadPrimes n ↔
      p.Prime ∧ (p : ℤ) ∣ canonicalRatioResultant n ∧ canonicalRatioResultant n ≠ 0 := by
  classical
  unfold canonicalRatioBadPrimes
  rw [Nat.mem_primeFactors]
  have hdvd_iff : (p ∣ (canonicalRatioResultant n).natAbs)
      ↔ ((p : ℤ) ∣ canonicalRatioResultant n) := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  rw [hdvd_iff, Int.natAbs_ne_zero]

/-- The canonical bad-prime set has at most `log₂ |Res|` elements. -/
theorem canonicalRatioBadPrimes_card_le_natLog {n : ℕ} (hn : 0 < n) (hn8 : 8 < n) :
    (canonicalRatioBadPrimes n).card ≤ Nat.log 2 (canonicalRatioResultant n).natAbs := by
  have hN0 : canonicalRatioResultant n ≠ 0 := by
    unfold canonicalRatioResultant
    exact resultant_canonicalRatioPoly_ne_zero hn hn8
  exact card_primeFactors_le_natLog (Int.natAbs_pos.mpr hN0)

/-- Crude divisor-count bound from the elementary archimedean resultant envelope. -/
theorem canonicalRatioBadPrimes_card_le_crude {n : ℕ} (hn : 0 < n) (hn8 : 8 < n) :
    (canonicalRatioBadPrimes n).card ≤ n.totient * (n + 1) := by
  have hcard := canonicalRatioBadPrimes_card_le_natLog hn hn8
  have hNle :
      (canonicalRatioResultant n).natAbs ≤ (2 ^ (n + 1)) ^ n.totient := by
    unfold canonicalRatioResultant
    exact natAbs_resultant_canonicalRatioPoly_le_two_pow_succ_totient hn.ne'
  have hlogmono :
      Nat.log 2 (canonicalRatioResultant n).natAbs
        ≤ Nat.log 2 ((2 ^ (n + 1)) ^ n.totient) :=
    Nat.log_mono_right hNle
  have hlog : Nat.log 2 ((2 ^ (n + 1)) ^ n.totient) = n.totient * (n + 1) := by
    rw [← pow_mul, Nat.log_pow (by norm_num : 1 < 2)]
    ring
  exact hcard.trans (hlogmono.trans_eq hlog)

/-- If the literal canonical width-four budget survives over `ZMod p`, then `p` belongs to the
finite canonical bad-prime set. -/
theorem mem_canonicalRatioBadPrimes_of_e2BadScalarSet_mu_card_le_n_zmod
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ZMod p)) 4).card ≤ n) :
    p ∈ canonicalRatioBadPrimes n := by
  rw [mem_canonicalRatioBadPrimes]
  refine ⟨Fact.out, ?_, ?_⟩
  · unfold canonicalRatioResultant
    exact prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
      hn heven hn8 hζ hbudget
  · unfold canonicalRatioResultant
    exact resultant_canonicalRatioPoly_ne_zero hn hn8

/-- Scanner-facing finite-set form: any prime outside the canonical resultant's prime-factor set
refutes the literal width-four `≤ n` budget in the fixed primitive-root lane. -/
theorem not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n) (hgood : p ∉ canonicalRatioBadPrimes n) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ZMod p)) 4).card ≤ n := by
  intro hbudget
  exact hgood
    (mem_canonicalRatioBadPrimes_of_e2BadScalarSet_mu_card_le_n_zmod
      hn heven hn8 hζ hbudget)

/-- Sharp two-power divisor-count bound from the Landau/Mahler squared resultant envelope. -/
theorem canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp {m : ℕ} (hm : 4 ≤ m) :
    (canonicalRatioBadPrimes (2 ^ m)).card ≤ Nat.log 2 (canonicalRatioPolySharpBound m) := by
  have hm1 : 1 ≤ m := by omega
  have hn : 0 < 2 ^ m := by positivity
  have hn8 : 8 < 2 ^ m := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 3 < m)
  have hcard := canonicalRatioBadPrimes_card_le_natLog hn hn8
  have hsq :
      (canonicalRatioResultant (2 ^ m)).natAbs ^ 2 ≤ canonicalRatioPolySharpBound m := by
    unfold canonicalRatioResultant
    exact natAbs_resultant_canonicalRatioPoly_twoPow_sq_le hm1
  have hN0 : canonicalRatioResultant (2 ^ m) ≠ 0 := by
    unfold canonicalRatioResultant
    exact resultant_canonicalRatioPoly_ne_zero hn hn8
  have hNpos : 1 ≤ (canonicalRatioResultant (2 ^ m)).natAbs :=
    Int.natAbs_pos.mpr hN0
  have hNleSq :
      (canonicalRatioResultant (2 ^ m)).natAbs
        ≤ (canonicalRatioResultant (2 ^ m)).natAbs ^ 2 := by
    rw [pow_two]
    nth_rewrite 1 [← Nat.mul_one (canonicalRatioResultant (2 ^ m)).natAbs]
    exact Nat.mul_le_mul_left _ hNpos
  have hNle : (canonicalRatioResultant (2 ^ m)).natAbs ≤ canonicalRatioPolySharpBound m :=
    hNleSq.trans hsq
  have hlogmono :
      Nat.log 2 (canonicalRatioResultant (2 ^ m)).natAbs
        ≤ Nat.log 2 (canonicalRatioPolySharpBound m) :=
    Nat.log_mono_right hNle
  exact hcard.trans hlogmono

/-- Named arithmetic supply for this lane: a primitive-root prime outside the finite canonical
bad-prime set.  This is deliberately a hypothesis, not a theorem; producing such primes in the
prize range is the remaining Linnik/Chebotarev-style arithmetic input. -/
def CanonicalWidthFourGoodPrimeSupply (m : ℕ) : Prop :=
  ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ ζ : ZMod p,
    IsPrimitiveRoot ζ (2 ^ m) ∧ p ∉ canonicalRatioBadPrimes (2 ^ m)

/-- If the canonical good-prime supply holds at `2^m`, the literal width-four `≤ 2^m` budget is
refuted for one supplied prime. -/
theorem refuter_of_canonicalWidthFourGoodPrimeSupply {m : ℕ} (hm : 4 ≤ m)
    (hgood : CanonicalWidthFourGoodPrimeSupply m) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      IsPrimitiveRoot ζ (2 ^ m) ∧
        ¬ (e2BadScalarSet (Polynomial.nthRootsFinset (2 ^ m) (1 : ZMod p)) 4).card
          ≤ 2 ^ m := by
  obtain ⟨p, hpfact, ζ, hζ, hpnot⟩ := hgood
  have hn : 0 < 2 ^ m := by positivity
  have heven : 2 ∣ 2 ^ m := by
    exact dvd_pow_self 2 (by omega : m ≠ 0)
  have hn8 : 8 < 2 ^ m := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 3 < m)
  exact ⟨p, hpfact, ζ, hζ,
    not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes
      hn heven hn8 hζ hpnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet

#print axioms mem_canonicalRatioBadPrimes
#print axioms canonicalRatioBadPrimes_card_le_crude
#print axioms not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes
#print axioms canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp
#print axioms refuter_of_canonicalWidthFourGoodPrimeSupply

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet
