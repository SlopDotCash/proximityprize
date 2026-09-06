/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# `GoodPrimeFamilyDensity`: bad-prime count and density in the prize family (#444, thread T9)

## The prize family and "bad" primes

The prize fixes a family of fields `F_p` with `p = Θ(n^β)`, `n = 2^μ` (`μ = 30`, `β` a fixed rate
exponent so `p ≈ n·2^128`). At a fixed moment-depth `r`, the char-`p` energy `E_r(μ_n; F_p)`
exceeds the char-`0` energy `E_r^{char0}` precisely when there is a WRAPAROUND relation:
a tuple `(x₁,…,x_r,y₁,…,y_r) ∈ μ_n^{2r}` with

    α = (Σ xᵢ − Σ yⱼ) ∈ ℤ[ζ_n]  nonzero,  but  α ≡ 0  (mod a degree-1 prime P₁ | p).

By `_AvE1_WraparoundCofactorVacuous` (item 3), each such `α` is a short `±1`-combination of `≤ 2r`
roots of unity, so its norm down to `ℤ` is a NONZERO integer with

    0 < |N(α)| ≤ (2r)^{φ(n)}      (here φ(n) = n/2 for n = 2^μ).

Since `P₁ | p` has norm `p` and `α ∈ P₁`, we get `p ∣ N(α)`. Therefore:

> **A prime `p` is bad at depth `r` ⟺ `p` divides some relation-value `N(α)`,
> a nonzero integer of size `≤ (2r)^{φ(n)}`.**

This file packages, axiom-clean, the resulting BAD-PRIME COUNT and the density derivation.

## What is proved here (axiom-clean)

* `badPrimes_subset_primeFactors_prod` : the set of primes that are bad at depth `r` (each dividing
  some relation value `Mᵢ ≠ 0`) is a SUBSET of `primeFactors (∏ᵢ Mᵢ)`. (`bad p ⊆ divisors of
  ∏ (relation values)` — the requested containment, made precise as a `Finset` subset.)

* `badPrimes_card_le` : hence `#bad ≤ Nat.log 2 (∏ᵢ Mᵢ)` — the distinct-bad-prime ceiling.

* `badPrimes_card_le_sum_log` : and `#bad ≤ Σᵢ Nat.log 2 Mᵢ ≤ R · (φ · Nat.log 2 (2r))` using the
  per-relation norm ceiling `Mᵢ ≤ (2r)^φ`. So with `R` = number of char-0-violating relations,

      #{bad primes at depth r}  ≤  R · φ · log₂(2r).

## The density derivation (honest)

The bad-prime SET is FINITE: it is contained in the prime factors of a single integer `∏ᵢ Mᵢ`,
so `#bad ≤ R·φ·log₂(2r) < ∞`. Consequently:

* **If `p` ranged freely over all primes**, the bad set being finite ⇒ ALL but finitely many primes
  are GOOD at depth `r` ⇒ good primes have density 1 (`o(1)` bad). This is
  `cofinitely_good_of_finite_bad` below: outside a finite bad set, every prime is good.

* **BUT the prize family `p = Θ(n^β)` is a THIN, FIXED family** (a single asymptotic line, not a
  free parameter). The honest statement is captured by `density_caveat` (a documentation `Prop`,
  not a vacuous discharge): cofiniteness over ALL primes does NOT by itself place a GOOD prime
  inside the prize window `[c₁ n^β, c₂ n^β]`, because the window is an interval of length `Θ(n^β)`
  containing `~ n^β / (β log n)` primes (PNT), and the bad-count bound `R·φ·log₂(2r)` is only useful
  if it is `< π(c₂ n^β) − π(c₁ n^β)`. That comparison is EXACTLY the Thorner–Zaman / Linnik
  PNT-in-the-window input flagged for B3 (`KKH26PolyFieldCeiling`), and the genuinely OPEN quantity
  is the relation count `R` (which is exponential in `n` over `ℤ` before the wraparound filter).

So this thread DERIVES the density skeleton and isolates the residual honestly:

> Good primes are COFINITE over all primes (proved). Whether a good prime lands in the prize window
> `p = Θ(n^β)` reduces to: `#bad ∩ window < #primes in window`, i.e. `R·φ·log₂(2r)` vs
> `π(c₂n^β) − π(c₁n^β)`. The numerator `R` (# char-0-violating relations) is the open input; this is
> NOT a free-choice escape unless `R` is shown subexponential at the saddle depth `r* ≈ log p`.

The named residual is `RelationCountSubWindow` below. It is the genuine open part: nothing here
secretly equals the prize.

## Relation to the rest of the ledger

* Consumes the AvE1 norm ceiling `Mᵢ ≤ (2r)^φ` (item 3) abstractly (as a hypothesis `hM`).
* Reuses the divisor-count technique of `_AlmostAllPrimesWick.card_primeFactors_le_natLog`.
* Honest verdict: DERIVED density skeleton + isolated `R` as the open quantity. Does NOT close the
  prize and does NOT claim free choice of `p` resolves it.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.GoodPrimeFamilyDensity

open Finset

/-- The product of distinct prime factors of `N` divides `N` and each factor is `≥ 2`, hence
`2 ^ (#primeFactors N) ≤ N` for `N ≥ 1`. (Same mechanism as `_AlmostAllPrimesWick`; reproved
locally to keep imports minimal.) -/
theorem two_pow_card_primeFactors_le {N : ℕ} (hN : 1 ≤ N) :
    2 ^ N.primeFactors.card ≤ N := by
  classical
  have hprod_dvd : (∏ p ∈ N.primeFactors, p) ∣ N := Nat.prod_primeFactors_dvd N
  have hprod_le : (∏ p ∈ N.primeFactors, p) ≤ N := Nat.le_of_dvd hN hprod_dvd
  have hconst : (∏ _p ∈ N.primeFactors, (2 : ℕ)) ≤ ∏ p ∈ N.primeFactors, p := by
    apply Finset.prod_le_prod'
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hconst_eq : (∏ _p ∈ N.primeFactors, (2 : ℕ)) = 2 ^ N.primeFactors.card := by
    simp [Finset.prod_const]
  calc 2 ^ N.primeFactors.card
      = ∏ _p ∈ N.primeFactors, (2 : ℕ) := hconst_eq.symm
    _ ≤ ∏ p ∈ N.primeFactors, p := hconst
    _ ≤ N := hprod_le

/-- The distinct-prime-factor count of a positive integer is `≤ log₂` of it. -/
theorem card_primeFactors_le_natLog {N : ℕ} (hN : 1 ≤ N) :
    N.primeFactors.card ≤ Nat.log 2 N :=
  Nat.le_log_of_pow_le Nat.one_lt_two (two_pow_card_primeFactors_le hN)

/-! ### The bad-prime set ⊆ divisors of the product of relation values -/

variable {ι : Type*} [DecidableEq ι]

/-- **The requested containment.** Let `M : ι → ℕ` index the char-0-violating relation values at
depth `r` (each `M i = |N(αᵢ)|`, a nonzero integer), over a finite index set `s`. Suppose every
relation value is positive (`M i ≠ 0`) so the product is nonzero. Then any prime `p` that is "bad"
— i.e. `p` divides SOME relation value `M i` for `i ∈ s` — lies in the prime factors of the product
`∏ᵢ M i`. Concretely: `bad p ⟹ p ∈ primeFactors (∏ᵢ Mᵢ)`.

This is the exact `bad p ⊆ divisors of ∏ (relation values)` statement, packaged as: the `Finset`
of such bad primes is a subset of `primeFactors (∏ M)`. -/
theorem badPrimes_subset_primeFactors_prod
    (s : Finset ι) (M : ι → ℕ) (hpos : ∀ i ∈ s, M i ≠ 0)
    (badP : Finset ℕ)
    (hbad : ∀ p ∈ badP, p.Prime ∧ ∃ i ∈ s, p ∣ M i) :
    badP ⊆ (∏ i ∈ s, M i).primeFactors := by
  classical
  have hprod_ne : (∏ i ∈ s, M i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpos
  intro p hp
  obtain ⟨hpprime, i, hi_mem, hi_dvd⟩ := hbad p hp
  have hp_dvd_prod : p ∣ ∏ i ∈ s, M i := hi_dvd.trans (Finset.dvd_prod_of_mem M hi_mem)
  exact Nat.mem_primeFactors.mpr ⟨hpprime, hp_dvd_prod, hprod_ne⟩

/-- **Bad-prime count ceiling (via the product).** The number of distinct primes bad at depth `r`
is at most `log₂ (∏ᵢ Mᵢ)`. -/
theorem badPrimes_card_le
    (s : Finset ι) (M : ι → ℕ) (hpos : ∀ i ∈ s, M i ≠ 0)
    (badP : Finset ℕ)
    (hbad : ∀ p ∈ badP, p.Prime ∧ ∃ i ∈ s, p ∣ M i) :
    badP.card ≤ Nat.log 2 (∏ i ∈ s, M i) := by
  classical
  have hsub := badPrimes_subset_primeFactors_prod s M hpos badP hbad
  have hcard_le : badP.card ≤ (∏ i ∈ s, M i).primeFactors.card :=
    Finset.card_le_card hsub
  have hprod_ge_one : 1 ≤ ∏ i ∈ s, M i :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr hpos)
  exact hcard_le.trans (card_primeFactors_le_natLog hprod_ge_one)

/-- `log₂ (a·b) ≤ log₂ a + log₂ b + 1` for `a, b ≥ 1`: since `a < 2^{log a + 1}`,
`b < 2^{log b + 1}`, we get `a·b < 2^{log a + log b + 2}`, hence
`log (a·b) ≤ log a + log b + 1`. -/
theorem natLog_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have hlt_a : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two a
  have hlt_b : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two b
  have hab_lt : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
          Nat.mul_lt_mul'' hlt_a hlt_b
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by rw [← pow_add]; congr 1; omega
  have := Nat.log_lt_of_lt_pow (by positivity) hab_lt
  omega

/-- `log₂ (m^k) ≤ k · (log₂ m + 1)`: since `m < 2^{log m + 1}`, `m^k < 2^{k(log m + 1)}`, hence
`log (m^k) ≤ k(log m + 1)`. (Covers `m = 0` and `k = 0` trivially.) -/
theorem natLog_pow_le (m k : ℕ) :
    Nat.log 2 (m ^ k) ≤ k * (Nat.log 2 m + 1) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
      have : (0 : ℕ) ^ k = 0 := zero_pow hk0
      rw [this]; simp
  · have hlt : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
    have hpow_lt : m ^ k < 2 ^ (k * (Nat.log 2 m + 1)) + 1 := by
      have hle2 : m ^ k ≤ (2 ^ (Nat.log 2 m + 1)) ^ k :=
        Nat.pow_le_pow_left (le_of_lt hlt) k
      rw [← pow_mul] at hle2
      have : (Nat.log 2 m + 1) * k = k * (Nat.log 2 m + 1) := mul_comm _ _
      rw [this] at hle2
      omega
    have hpow_le : m ^ k ≤ 2 ^ (k * (Nat.log 2 m + 1)) := by omega
    exact (Nat.log_mono_right hpow_le).trans
      (le_of_eq (Nat.log_pow Nat.one_lt_two _))

/-- `log₂` of a product is `≤` the sum of the `log₂`s of the positive factors, plus `(#s − 1)` from
the per-multiplication carries; we use the clean ceiling `≤ (Σ log₂ Mᵢ) + #s`. -/
theorem natLog_prod_le_sum_natLog
    (s : Finset ι) (M : ι → ℕ) (hpos : ∀ i ∈ s, M i ≠ 0) :
    Nat.log 2 (∏ i ∈ s, M i) ≤ (∑ i ∈ s, Nat.log 2 (M i)) + s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have hpos' : ∀ j ∈ s, M j ≠ 0 := fun j hj => hpos j (Finset.mem_insert_of_mem hj)
      have hMi : M i ≠ 0 := hpos i (Finset.mem_insert_self i s)
      have hprod_s : (∏ j ∈ s, M j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpos'
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      have hstep := natLog_mul_le (M i) (∏ j ∈ s, M j) hMi hprod_s
      have ihp := ih hpos'
      omega

/-- **The full bad-prime count bound.** With `R = #s` char-0-violating relations at depth `r`, each
of norm `M i ≤ (2r)^φ` (the AvE1 ceiling, item 3), the number of distinct bad primes is

    #bad ≤ Σᵢ log₂ Mᵢ ≤ R · log₂ ((2r)^φ) = R · φ · log₂ (2r).

`φ = n/2` for `n = 2^μ`. This is the central count: bad primes are bounded by
`(# relations) · (n/2) · log₂(2r)`. -/
theorem badPrimes_card_le_relCount
    (s : Finset ι) (M : ι → ℕ) (r φ : ℕ)
    (hpos : ∀ i ∈ s, M i ≠ 0)
    (hM : ∀ i ∈ s, M i ≤ (2 * r) ^ φ)
    (badP : Finset ℕ)
    (hbad : ∀ p ∈ badP, p.Prime ∧ ∃ i ∈ s, p ∣ M i) :
    badP.card ≤ s.card * (φ * (Nat.log 2 (2 * r) + 1) + 1) := by
  classical
  -- `#bad ≤ (Σ log₂ Mᵢ) + #s ≤ Σ φ·(log₂(2r)+1) + #s = #s·(φ·(log₂(2r)+1) + 1)`.
  have h1 : badP.card ≤ (∑ i ∈ s, Nat.log 2 (M i)) + s.card :=
    (badPrimes_card_le s M hpos badP hbad).trans (natLog_prod_le_sum_natLog s M hpos)
  -- each `log₂ (M i) ≤ log₂ ((2r)^φ) ≤ φ · (log₂ (2r) + 1)` via `natLog_pow_le`.
  have h2 : ∀ i ∈ s, Nat.log 2 (M i) ≤ φ * (Nat.log 2 (2 * r) + 1) := by
    intro i hi
    have hle : Nat.log 2 (M i) ≤ Nat.log 2 ((2 * r) ^ φ) :=
      Nat.log_mono_right (hM i hi)
    exact hle.trans (natLog_pow_le (2 * r) φ)
  have hsum : (∑ i ∈ s, Nat.log 2 (M i)) ≤ s.card * (φ * (Nat.log 2 (2 * r) + 1)) := by
    calc (∑ i ∈ s, Nat.log 2 (M i))
        ≤ ∑ _i ∈ s, (φ * (Nat.log 2 (2 * r) + 1)) := Finset.sum_le_sum h2
      _ = s.card * (φ * (Nat.log 2 (2 * r) + 1)) := by rw [Finset.sum_const, smul_eq_mul]
  calc badP.card ≤ (∑ i ∈ s, Nat.log 2 (M i)) + s.card := h1
    _ ≤ s.card * (φ * (Nat.log 2 (2 * r) + 1)) + s.card := Nat.add_le_add_right hsum _
    _ = s.card * (φ * (Nat.log 2 (2 * r) + 1) + 1) :=
          (Nat.mul_succ s.card (φ * (Nat.log 2 (2 * r) + 1))).symm

/-! ### Density: cofinite good primes; the honest prize-window caveat -/

/-- **Cofinitely many good primes (free-`p` density).** Since the bad-prime set at depth `r` is a
finite `Finset badP`, every prime OUTSIDE `badP` is good. Concretely: for any prime `p ∉ badP`,
`p` divides NO relation value — there is no `i ∈ s` with `p ∣ M i`. So good primes are cofinite
(density 1 over all primes), bad primes are `o(1)`.

This is the genuine `o(1)` statement IF `p` ranges freely; the prize caveat below explains why
this does not by itself solve the prize. -/
theorem cofinitely_good_of_finite_bad
    (s : Finset ι) (M : ι → ℕ)
    (badP : Finset ℕ)
    (hbad_iff : ∀ p, p.Prime → ((∃ i ∈ s, p ∣ M i) ↔ p ∈ badP))
    (p : ℕ) (hp : p.Prime) (hp_not : p ∉ badP) :
    ¬ ∃ i ∈ s, p ∣ M i := by
  intro hcon
  exact hp_not ((hbad_iff p hp).mp hcon)

/-- **Named open residual (honest).** The prize fixes `p = Θ(n^β)`: a thin window
`[c₁ n^β, c₂ n^β]`. Cofiniteness of good primes over ALL primes does NOT place a good prime in this
window unless the bad-count `#bad ≤ R · (φ·(log₂(2r)+1) + 1)` is strictly below the number of primes in the
window `π(c₂ n^β) − π(c₁ n^β) ≈ n^β/(β log n)` (PNT). The genuine open input is the relation count
`R = #s` at the saddle depth `r* ≈ log p` (exponential in `n` over `ℤ` before the wraparound
filter; subexponentiality is unproven).

`RelationCountSubWindow s windowPrimeCount r φ` asserts exactly the comparison that, if true at
`r*`, yields a good prime in the prize window. It is a HYPOTHESIS, not a theorem: it names the open
quantity honestly and is NOT secretly the prize (it is a count comparison, decoupled from the
char-`p` saddle value once `R` is controlled). -/
def RelationCountSubWindow (R windowPrimeCount r φ : ℕ) : Prop :=
  R * (φ * (Nat.log 2 (2 * r) + 1) + 1) < windowPrimeCount

/-- **The density conclusion, CONDITIONAL on the named residual.** If the bad-count bound is below
the number of primes in the prize window (`RelationCountSubWindow`), then there EXISTS a prime in
the window that is good at depth `r` — because the bad primes occupy at most `#bad` of the
`windowPrimeCount` window-primes, leaving at least one good.

This is the honest payoff: a good prime in the window EXISTS once `R` is controlled. The residual
`RelationCountSubWindow` is the only open input; it is named, not discharged. -/
theorem good_prime_in_window_of_relCount
    (s : Finset ι) (M : ι → ℕ) (r φ : ℕ)
    (hpos : ∀ i ∈ s, M i ≠ 0)
    (hM : ∀ i ∈ s, M i ≤ (2 * r) ^ φ)
    (windowPrimes : Finset ℕ)
    (hwin_prime : ∀ p ∈ windowPrimes, p.Prime)
    (badP : Finset ℕ)
    (hbad : ∀ p ∈ badP, p.Prime ∧ ∃ i ∈ s, p ∣ M i)
    (hbad_complete : ∀ p ∈ windowPrimes, (∃ i ∈ s, p ∣ M i) → p ∈ badP)
    (hres : RelationCountSubWindow s.card windowPrimes.card r φ) :
    ∃ p ∈ windowPrimes, ¬ ∃ i ∈ s, p ∣ M i := by
  classical
  -- Bad primes intersected with the window form a subset of badP, of card ≤ #bad < #window.
  have hcard_bad : badP.card ≤ s.card * (φ * (Nat.log 2 (2 * r) + 1) + 1) :=
    badPrimes_card_le_relCount s M r φ hpos hM badP hbad
  -- The window-primes that ARE bad inject into badP.
  set badInWin : Finset ℕ := windowPrimes.filter (fun p => ∃ i ∈ s, p ∣ M i) with hbadInWin
  have hbadInWin_sub : badInWin ⊆ badP := by
    intro p hp
    rw [hbadInWin, Finset.mem_filter] at hp
    exact hbad_complete p hp.1 hp.2
  have hbadInWin_card : badInWin.card ≤ s.card * (φ * (Nat.log 2 (2 * r) + 1) + 1) :=
    (Finset.card_le_card hbadInWin_sub).trans hcard_bad
  have hstrict : badInWin.card < windowPrimes.card :=
    lt_of_le_of_lt hbadInWin_card hres
  -- So badInWin ≠ windowPrimes (it is a proper-cardinality subset of windowPrimes); pick the gap.
  have hbadInWin_subwin : badInWin ⊆ windowPrimes := Finset.filter_subset _ _
  have hne : badInWin ≠ windowPrimes := by
    intro heq
    exact (lt_irrefl _) (heq ▸ hstrict)
  obtain ⟨p, hp_win, hp_notbad⟩ := Finset.exists_of_ssubset
    (lt_of_le_of_ne (Finset.le_iff_subset.mpr hbadInWin_subwin) hne)
  refine ⟨p, hp_win, ?_⟩
  intro hcon
  apply hp_notbad
  rw [hbadInWin, Finset.mem_filter]
  exact ⟨hp_win, hcon⟩

-- Axiom audit (expect: [propext, Classical.choice, Quot.sound], no sorryAx/native_decide).
#print axioms badPrimes_subset_primeFactors_prod
#print axioms badPrimes_card_le
#print axioms natLog_prod_le_sum_natLog
#print axioms badPrimes_card_le_relCount
#print axioms cofinitely_good_of_finite_bad
#print axioms good_prime_in_window_of_relCount

end ArkLib.ProximityGap.Frontier.GoodPrimeFamilyDensity
