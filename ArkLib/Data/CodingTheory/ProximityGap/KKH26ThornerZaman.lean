/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq

/-!
# KKH26 Lemma 2: the Thorner–Zaman reduction of the prime threshold (issue #334, K4)

The in-tree [KKH26] pipeline (`KKH26SumsOfRootsOfUnity.lean` → `KKH26WitnessSpread.lean`)
proves the witness-spread `ε_mca` lower bound `kkh26_epsMCA_lower_bound` and the `δ*` upper
bracket `kkh26_mcaDeltaStar_le` for explicit smooth-domain evaluation codes — but only above
the **explicit prime threshold** `p > (2^μ)^{2^{μ−1}} = s^{s/2}` (with `s = 2^μ`), which is
superpolynomial in the domain size `n = s·m`.  [KKH26] Lemma 2 removes this blemish: a
*good* prime `p ≡ 1 (mod n)` of size `p = Θ(n^β)` already exists, because

1. **(analytic input, [TZ24])** by Thorner–Zaman's refined prime number theorem in arithmetic
   progressions (Cor 3.1 of [TZ24], applied via partial summation to the short interval
   `[n^β, 2n^β]` with the smooth modulus `n = 2^μ·m`), the interval `[n^β, 2n^β]` contains
   `≥ n^{β−1−o(1)}` primes `p ≡ 1 (mod n)`, valid unconditionally for every fixed `β > 12/5`
   (and for every `β > 1` under Montgomery's conjecture); and
2. **(counting, THIS FILE, unconditional)** each collision resultant
   `Res_ℤ(P − Q, Φ_s)` is a nonzero integer of absolute value `≤ s^{s/2}`
   (`natAbs_resultant_cyclotomic_le` in-tree), so it has at most
   `log(s^{s/2}) / log(n^β)` prime divisors of size `≥ n^β`; with `≤ a²` pairs of
   sum-polynomials, at most `a² · log(s^{s/2}) / (β·log n)` primes in the window are *bad*.
   If the [TZ24] supply exceeds this count, a good prime survives, and the entire
   [KKH26] Lemma 1 separation argument runs at `p = Θ(n^β)`.

The analytic input (1) is far beyond present-day formalization (it relies on log-free
zero-density estimates for Dirichlet `L`-functions); following the `Hab25Johnson`
named-hypothesis pattern it is packaged as the `Prop`-valued structure `TZPrimeSupply`
— **never** an axiom — and every theorem consuming it takes it as an explicit hypothesis.
The counting step (2) is proven here unconditionally.

## Main definitions and results

* `tzWindow n β` — the `Finset` of primes `p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β`.
* `TZPrimeSupply n β supply` — the named [TZ24] hypothesis: `tzWindow n β` has
  `≥ supply` elements.  Instantiated (on paper) by [TZ24] Cor 3.1 with
  `supply ~ n^{β−1−o(1)}` for `β > 12/5`.
* `card_bigPrimeFactors_le` — **unconditional**: a nonzero integer of absolute value
  `≤ M` has at most `log M / log x` distinct prime divisors of size `≥ x` (any `x ≥ 2`).
* `card_biUnion_bigPrimeFactors_le` — **unconditional**: a family of `m` nonzero integers,
  each of absolute value `≤ M`, has at most `m · log M / log x` distinct prime divisors
  of size `≥ x` in total.
* `kkh26_good_prime_of_TZ` — **conditional headline** ([KKH26] Lemma 2): given
  `TZPrimeSupply n β supply` with `supply > m · log M / log(n^β)`, there is a prime
  `p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β` dividing none of the `m` given resultants.
* `kkh26_good_prime_paper_form` — the same with the [KKH26] parameters spelled out:
  `M = s^{s/2} = (2^μ)^{2^{μ−1}}` and `m = a²` resultants, and the bad-prime budget in
  the paper's `a² · 2^{μ−1}·μ·log 2 / (β·log n)` form.

## Wiring to the in-tree threshold

`KKH26SumsOfRootsOfUnity.lean` contains both routes through Lemma 1.  The explicit-threshold
route uses `not_isRoot_of_l1On_pow_lt`: if `p > s^{s/2}`, then `p` is larger than every
collision resultant and cannot divide one.  The polynomial-field-size route uses the
divisibility API added for issue #334: `collisionResultant` names
`R_{(d,d')} = Res_ℤ(sumPoly d − sumPoly d', Φ_{2^μ})`,
`not_isRoot_of_not_dvd_resultant` replaces the size contradiction by the hypothesis
`¬ (p : ℤ) ∣ collisionResultant m d d'`, and
`sVal_injOn_of_not_dvd` / `kkh26_lemma1_of_not_dvd` re-run the separation and counting chain
under that no-bad-resultant assumption.  This file supplies the matching good-prime source:
`kkh26_good_prime_of_TZ` and `kkh26_good_prime_paper_form` produce primes in the
Thorner--Zaman window that avoid any supplied finite family of nonzero, bounded resultants.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to
  capacity*, ePrint 2026/782 (Lemma 2).
* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Cor 3.1.
* [Jo26] ePrint 2026/891.  Issue #334.
-/

open Finset

namespace ArkLib.ProximityGap.KKH26

/-! ### The Thorner–Zaman prime window and the named [TZ24] hypothesis -/

/-- The Thorner–Zaman prime window: primes `p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β`
(as a `Finset` of naturals; the real-interval conditions are encoded by
`⌈n^β⌉₊ ≤ p ≤ ⌊2·n^β⌋₊`, see `mem_tzWindow`). -/
noncomputable def tzWindow (n : ℕ) (β : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈(n : ℝ) ^ β⌉₊ ⌊2 * (n : ℝ) ^ β⌋₊).filter
    (fun p => p.Prime ∧ p ≡ 1 [MOD n])

/-- Membership in the Thorner–Zaman window, in real-interval form. -/
lemma mem_tzWindow {n : ℕ} {β : ℝ} {p : ℕ} :
    p ∈ tzWindow n β ↔
      p.Prime ∧ p ≡ 1 [MOD n] ∧ (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β := by
  have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) ^ β := by positivity
  simp only [tzWindow, Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff h2]
  tauto

/-- **The named [TZ24] hypothesis** (`Hab25Johnson` pattern; never an axiom).
`TZPrimeSupply n β supply` asserts that the window `[n^β, 2·n^β]` contains at least
`supply` primes `p ≡ 1 (mod n)`.

On paper this is instantiated by [TZ24] (Thorner–Zaman, *Refinements to the prime number
theorem in arithmetic progressions*) Corollary 3.1, via partial summation over the short
interval: for the smooth modulus `n = 2^μ·m` and any fixed `β > 12/5` it holds
unconditionally with `supply ~ n^{β−1−o(1)}`; under Montgomery's conjecture it holds for
every `β > 1`.  The counting theorems below consume exactly this cardinality bound and
nothing else. -/
structure TZPrimeSupply (n : ℕ) (β : ℝ) (supply : ℕ) : Prop where
  /-- The window `[n^β, 2·n^β]` contains at least `supply` primes `≡ 1 (mod n)`. -/
  le_card : supply ≤ (tzWindow n β).card

/-! ### The prime-factor count ([KKH26] Lemma 2, counting step — unconditional) -/

/-- The distinct prime divisors of the integer `N` of size at least `x`. -/
noncomputable def bigPrimeFactors (x : ℝ) (N : ℤ) : Finset ℕ :=
  N.natAbs.primeFactors.filter (fun q => x ≤ (q : ℝ))

/-- Membership in `bigPrimeFactors`, unfolded. -/
lemma mem_bigPrimeFactors {x : ℝ} {N : ℤ} {q : ℕ} :
    q ∈ bigPrimeFactors x N ↔ q.Prime ∧ (q : ℤ) ∣ N ∧ N ≠ 0 ∧ x ≤ (q : ℝ) := by
  simp only [bigPrimeFactors, Finset.mem_filter, Nat.mem_primeFactors,
    ← Int.natCast_dvd_natCast, Int.dvd_natAbs, Int.natAbs_ne_zero]
  tauto

/-- **The prime-factor count** (pure number theory, unconditional): a nonzero integer of
absolute value at most `M` has at most `log M / log x` distinct prime divisors of size at
least `x`, for any `x ≥ 2`.  (If it had `k` of them, their product — which divides `N` —
would already be at least `x^k`, so `x^k ≤ M`.) -/
theorem card_bigPrimeFactors_le {N : ℤ} (hN : N ≠ 0) {M x : ℝ}
    (hM : (N.natAbs : ℝ) ≤ M) (hx : 2 ≤ x) :
    ((bigPrimeFactors x N).card : ℝ) ≤ Real.log M / Real.log x := by
  set S : Finset ℕ := bigPrimeFactors x N with hS
  have hsub : S ⊆ N.natAbs.primeFactors := Finset.filter_subset _ _
  -- the product of the big prime factors divides |N|
  have hdvd : (∏ q ∈ S, q) ∣ N.natAbs :=
    (Finset.prod_dvd_prod_of_subset S N.natAbs.primeFactors _ hsub).trans
      (Nat.prod_primeFactors_dvd N.natAbs)
  have hpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hprod_le : (∏ q ∈ S, q) ≤ N.natAbs := Nat.le_of_dvd hpos hdvd
  have hx0 : (0 : ℝ) < x := by linarith
  -- hence x^|S| ≤ M
  have hpow : x ^ S.card ≤ M := by
    calc x ^ S.card = ∏ _q ∈ S, x := (Finset.prod_const x).symm
      _ ≤ ∏ q ∈ S, (q : ℝ) :=
          Finset.prod_le_prod (fun _ _ => hx0.le)
            (fun q hq => (Finset.mem_filter.mp hq).2)
      _ = ((∏ q ∈ S, q : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (N.natAbs : ℝ) := by exact_mod_cast hprod_le
      _ ≤ M := hM
  -- take logarithms
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : (S.card : ℝ) * Real.log x ≤ Real.log M := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  exact (le_div_iff₀ hlogx).mpr hlog

/-- **The union count** (unconditional): a family of `m` nonzero integers, each of
absolute value at most `M`, has at most `m · (log M / log x)` distinct prime divisors of
size at least `x` in total. -/
theorem card_biUnion_bigPrimeFactors_le {m : ℕ} {R : Fin m → ℤ} (hR : ∀ i, R i ≠ 0)
    {M x : ℝ} (hM : ∀ i, ((R i).natAbs : ℝ) ≤ M) (hx : 2 ≤ x) :
    ((Finset.univ.biUnion (fun i : Fin m => bigPrimeFactors x (R i))).card : ℝ)
      ≤ m * (Real.log M / Real.log x) := by
  have h1 : (Finset.univ.biUnion (fun i : Fin m => bigPrimeFactors x (R i))).card
      ≤ ∑ i : Fin m, (bigPrimeFactors x (R i)).card := Finset.card_biUnion_le
  calc ((Finset.univ.biUnion (fun i : Fin m => bigPrimeFactors x (R i))).card : ℝ)
      ≤ ((∑ i : Fin m, (bigPrimeFactors x (R i)).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ i : Fin m, ((bigPrimeFactors x (R i)).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _i : Fin m, (Real.log M / Real.log x) :=
        Finset.sum_le_sum (fun i _ => card_bigPrimeFactors_le (hR i) (hM i) hx)
    _ = m * (Real.log M / Real.log x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The good-prime existence ([KKH26] Lemma 2 — conditional headline) -/

/-- **[KKH26] Lemma 2 (good-prime existence), conditional on the named [TZ24] supply.**
Given `TZPrimeSupply n β supply` and a family of `m` nonzero integers `R i` (the collision
resultants) of absolute value at most `M`, if the supply strictly exceeds the bad-prime
budget `m · log M / log(n^β)`, then some prime `p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β`
divides **none** of the `R i`.  (Pigeonhole: the window minus the bad set is nonempty.) -/
theorem kkh26_good_prime_of_TZ {n : ℕ} {β : ℝ} {supply : ℕ}
    (hTZ : TZPrimeSupply n β supply) {m : ℕ} {R : Fin m → ℤ}
    (hR : ∀ i, R i ≠ 0) {M : ℝ} (hM : ∀ i, ((R i).natAbs : ℝ) ≤ M)
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hcount : (m : ℝ) * (Real.log M / Real.log ((n : ℝ) ^ β)) < supply) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∀ i, ¬ (p : ℤ) ∣ R i := by
  classical
  set B : Finset ℕ :=
    Finset.univ.biUnion (fun i : Fin m => bigPrimeFactors ((n : ℝ) ^ β) (R i)) with hB
  -- the bad set is strictly smaller than the window
  have hBcard : (B.card : ℝ) < (supply : ℝ) :=
    lt_of_le_of_lt (card_biUnion_bigPrimeFactors_le hR hM hx) hcount
  have hcard : B.card < (tzWindow n β).card := by
    have h : (B.card : ℝ) < ((tzWindow n β).card : ℝ) :=
      lt_of_lt_of_le hBcard (by exact_mod_cast hTZ.le_card)
    exact_mod_cast h
  -- pigeonhole: a window prime outside the bad set
  have hne : (tzWindow n β \ B).Nonempty := by
    rw [← Finset.card_pos]
    have h := Finset.le_card_sdiff B (tzWindow n β)
    omega
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hpW, hpB⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hprime, hmod, hlb, hub⟩ := mem_tzWindow.mp hpW
  refine ⟨p, hprime, hmod, hlb, hub, fun i hdvd => hpB ?_⟩
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, mem_bigPrimeFactors.mpr ⟨hprime, hdvd, hR i, hlb⟩⟩

/-- **[KKH26] Lemma 2 in the paper's parameters.**  With `s = 2^μ`, the in-tree resultant
bound `natAbs_resultant_cyclotomic_le` gives `|Res_ℤ(P − Q, Φ_s)| ≤ s^{s/2} = (2^μ)^{2^{μ−1}}`
for each of the `m = a²` pairs of sum-polynomials (`a = 2^r·(2^{μ−1}).choose r` signed data),
and `log(s^{s/2}) = 2^{μ−1}·μ·log 2`.  If the [TZ24] supply exceeds the resulting bad-prime
budget `a²·2^{μ−1}·μ·log 2 / (β·log n)`, a good prime `p ≡ 1 (mod n)`, `p ∈ [n^β, 2n^β]`,
avoids every resultant — so [KKH26] Lemma 1's separation argument runs at `p = Θ(n^β)`
instead of `p > s^{s/2}` (see the module docstring for the remaining in-tree re-plumbing). -/
theorem kkh26_good_prime_paper_form {n : ℕ} {β : ℝ} {supply : ℕ}
    (hTZ : TZPrimeSupply n β supply) {μ a : ℕ} {R : Fin (a ^ 2) → ℤ}
    (hR : ∀ i, R i ≠ 0)
    (hM : ∀ i, ((R i).natAbs : ℝ) ≤ ((2 : ℝ) ^ μ) ^ 2 ^ (μ - 1))
    (hn : 1 < n) (hx : 2 ≤ (n : ℝ) ^ β)
    (hcount : ((a ^ 2 : ℕ) : ℝ) *
        ((((2 ^ (μ - 1) : ℕ) : ℝ) * ((μ : ℝ) * Real.log 2)) / (β * Real.log n))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∀ i, ¬ (p : ℤ) ∣ R i := by
  refine kkh26_good_prime_of_TZ hTZ hR hM hx ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn.le
  rw [Real.log_rpow hn0, Real.log_pow, Real.log_pow]
  exact hcount

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.card_bigPrimeFactors_le
#print axioms ArkLib.ProximityGap.KKH26.card_biUnion_bigPrimeFactors_le
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_of_TZ
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_paper_form
