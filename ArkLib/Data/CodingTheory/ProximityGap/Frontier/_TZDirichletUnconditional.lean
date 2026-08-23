/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling

/-!
# Dirichlet ⟹ UNCONDITIONAL good prime for KKH26 (no `TZPrimeSupply`) — #334 B3 pivot

The s=128 (and every `μ`) `δ*` ceiling `kkh26_mcaDeltaStar_le_of_TZ` is complete **modulo the one
named analytic hypothesis** `TZPrimeSupply n β supply` (Thorner–Zaman PNT-in-APs), which gives
`~n^{β−1}` primes `p ≡ 1 (mod n)` in the short window `[n^β, 2n^β]`. That strong supply is needed
only to out-count the `~10^{26}` *bad* primes (divisors of the collision resultants ≤ `s^{s/2}`)
inside a polynomial window.

**The observation that removes the analytic hypothesis (at the cost of the polynomial field bound).**
Every collision resultant is a *nonzero* integer of absolute value `≤ s^{s/2} = (2^μ)^{2^{μ-1}}`. A
prime `p > s^{s/2}` therefore divides **none** of them (a prime exceeding a nonzero integer cannot
divide it) — so it is automatically a *good* prime, with **zero** budget condition and **no** supply
count. And such a prime `p ≡ 1 (mod n)` exists **unconditionally** by Dirichlet's theorem on primes
in arithmetic progressions, which IS in mathlib (`Nat.forall_exists_prime_gt_and_modEq`).

So the good-prime existence — the only place `TZPrimeSupply` was consumed — is discharged
unconditionally. What is given up versus [TZ24] is the *polynomial* field-size bound `p = Θ(n^β)`:
Dirichlet gives no size bound, so `p` may be large. Recovering the polynomial bound is exactly the
remaining **Linnik / effective-PNT-in-APs** gap (`∃` a prime `≡ 1 (mod n)` in `(s^{s/2}, poly(n)]`),
the *weakest* prime-in-AP statement, far below the strong `n^{β−1}` supply.

## Results
* `exists_good_prime_dirichlet` — generic: for `n ≠ 0` and any finite family of nonzero integers
  bounded by `M`, a prime `p ≡ 1 (mod n)` with `p > M` divides none of them (axiom-clean, Dirichlet).
* `kkh26_good_prime_avoids_collisions_unconditional` — the KKH26 instantiation: unconditionally a
  prime `p ≡ 1 (mod n)` with `p > s^{s/2}` divides no collision resultant — the exact divisibility
  hypothesis of `kkh26_lemma1_of_not_dvd`, now with **no `TZPrimeSupply`**.

## Honest scope (#334)
This removes the named hypothesis for the *existence* of the good prime / the `δ*` separation, NOT
the polynomial field-size refinement (that stays the Linnik gap). It does not touch the Paley/BGK
sup-norm cone. Real, unconditional, Mathlib-backed progress on the B3 thread.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.KKH26

open Finset
open scoped NNReal ENNReal

/-- **Dirichlet ⟹ good prime (generic).** For a modulus `n ≠ 0` and a finite family `R` of nonzero
integers each with `|R i| ≤ M`, there is a prime `p ≡ 1 (mod n)` with `p > M` dividing none of the
`R i`. Pure consequence of mathlib's Dirichlet theorem (`Nat.forall_exists_prime_gt_and_modEq`):
`p > M ≥ |R i| > 0` and `p` prime force `p ∤ R i`. -/
theorem exists_good_prime_dirichlet (n : ℕ) (hn : n ≠ 0) {k : ℕ} (R : Fin k → ℤ)
    (hR : ∀ i, R i ≠ 0) (M : ℕ) (hM : ∀ i, (R i).natAbs ≤ M) :
    ∃ p : ℕ, M < p ∧ p.Prime ∧ p ≡ 1 [MOD n] ∧ ∀ i, ¬ (p : ℤ) ∣ R i := by
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq M (q := n) (a := 1) hn (Nat.coprime_one_left n)
  refine ⟨p, hpgt, hp, hpmod, fun i hdvd => ?_⟩
  have hpd : p ∣ (R i).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using h
  have hle : p ≤ (R i).natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr (hR i)) hpd
  have : p ≤ M := hle.trans (hM i)
  omega

/-- **KKH26 good prime, UNCONDITIONAL (no `TZPrimeSupply`).** For any modulus `n ≠ 0` with
`1 ≤ μ` and `r ≤ 2^{μ-1}`, there is a prime `p ≡ 1 (mod n)` with `p > s^{s/2} = (2^μ)^{2^{μ-1}}`
that divides **no** collision resultant of distinct signed data — exactly the divisibility
hypothesis of `kkh26_lemma1_of_not_dvd`, discharged unconditionally by Dirichlet. Note
`p > (2^μ)^{2^{μ-1}} ≥ 2^μ`, so the prime-threshold hypothesis `2^μ < p` of Lemma 1 also holds. -/
theorem kkh26_good_prime_avoids_collisions_unconditional {n : ℕ} (hn : n ≠ 0) {μ r : ℕ}
    (hμ : 1 ≤ μ) (hr : r ≤ 2 ^ (μ - 1)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1)) < p ∧
      ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r, d₁ ≠ d₂ →
        ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂ := by
  classical
  obtain ⟨p, hpgt, hp, hmod, hgood⟩ :=
    exists_good_prime_dirichlet n hn
      (R := fun i : Fin (collisionPairs μ r).card =>
        collisionResultant μ ((collisionPairs μ r).equivFin.symm i).1.1
          ((collisionPairs μ r).equivFin.symm i).1.2)
      (fun i => by
        obtain ⟨h1, h2, h3⟩ :=
          mem_collisionPairs.mp ((collisionPairs μ r).equivFin.symm i).2
        exact collisionResultant_ne_zero hμ h1 h2 h3)
      (M := (((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1)))
      (fun i => by
        obtain ⟨h1, h2, _⟩ :=
          mem_collisionPairs.mp ((collisionPairs μ r).equivFin.symm i).2
        exact natAbs_collisionResultant_le hμ h1 h2 hr)
  refine ⟨p, hp, hmod, hpgt, fun d₁ hd₁ d₂ hd₂ hne => ?_⟩
  have hq : (d₁, d₂) ∈ collisionPairs μ r := mem_collisionPairs.mpr ⟨hd₁, hd₂, hne⟩
  have h := hgood ((collisionPairs μ r).equivFin ⟨(d₁, d₂), hq⟩)
  rwa [Equiv.symm_apply_apply] at h

/-- A prime `p ≡ 1 (mod n)` carries an element of multiplicative order `n` in `F_p`
(`(ZMod p)ˣ` is cyclic of order `p − 1`, and `n ∣ p − 1`). Inlined from
`KKH26PolyFieldCeiling` (where it is `private`). -/
private lemma exists_orderOf_eq_of_modEq' {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 0 < n)
    (hmod : p ≡ 1 [MOD n]) : ∃ g : ZMod p, orderOf g = n := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdvd : n ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf u = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units]
  have hdvd' : n ∣ orderOf u := hord ▸ hdvd
  have hne : orderOf u ≠ 0 := by omega
  refine ⟨((u ^ (orderOf u / n) : (ZMod p)ˣ) : ZMod p), ?_⟩
  rw [orderOf_units, orderOf_pow_orderOf_div hne hdvd']

/-- **The [KKH26] `δ*` ceiling, UNCONDITIONAL** (no `TZPrimeSupply`, #334 B3 pivot). For the
smooth modulus `n = 2^μ·m` (`1 ≤ μ`, `1 ≤ m`) and `2 ≤ r ≤ 2^{μ-1}`, there is a prime
`p ≡ 1 (mod n)` (with `p > s^{s/2}`, hence `> 2^μ`) and a smooth evaluation domain `⟨g⟩ ⊆ F_p^×`
of order `n` such that for every `ε* < 2^r·(2^{μ-1}).choose r / p` the explicit evaluation code of
degree `≤ (r-2)m` satisfies `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ` — strictly below capacity. The good
prime is supplied UNCONDITIONALLY by Dirichlet (no analytic hypothesis); the price is that `p` is
not proven polynomial in `n` (that is the remaining Linnik / effective-PNT-in-APs gap). -/
theorem kkh26_mcaDeltaStar_le_unconditional {n : ℕ} (hn0' : n ≠ 0) [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1)) < p ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  obtain ⟨p, hp, hmod, hpgt, hndvd⟩ :=
    kkh26_good_prime_avoids_collisions_unconditional hn0' hμ hr
  haveI hfact : Fact p.Prime := ⟨hp⟩
  have hplp : (2 : ℕ) ^ μ < p :=
    lt_of_le_of_lt (Nat.le_self_pow (by positivity) ((2 : ℕ) ^ μ)) hpgt
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn0'
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_modEq' hn0 hmod
  refine ⟨p, hp, hmod, hpgt, hfact, g, hg, fun εstar hεstar => ?_⟩
  exact kkh26_mcaDeltaStar_le_of_not_dvd hμ hm hn (hn ▸ hg) hplp hr2 hr hndvd εstar hεstar

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.KKH26.exists_good_prime_dirichlet
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_avoids_collisions_unconditional
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_unconditional
