/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic

/-!
# APPROACH N9 — a CROSS-PRIME LARGE SIEVE for subgroup-sum wraparound excess (#444)

**Target (the whole prize):** delete `[CharZero F]` from
`Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic` and prove, over `F_p` (char `p`),
`rEnergy(μ_n, r) ≤ (2r−1)‼·n^r` at `r* ≈ ln p`, for the prize scale `n = 2^30`,
`p ≈ n·2^128` (so `n ≈ p^{1/5.27}`, `β ≈ 5`).

The char-0 version is PROVEN. The ONLY char-`p` excess is **additive wraparound**: the excess is
`W_r(p) := rEnergy_{F_p}(μ_n, r) − rEnergy^{char0}(μ_n, r)`, and the prize is
`W_r(p) ≤ slack_r := (2r−1)‼·n^r − rEnergy^{char0}` (the falling-factorial slack the union bound
leaves over the char-0 energy). `rEnergy^{char0} ≤ (2r−1)‼·n^r` is in-tree, so `slack_r ≥ 0`.

## The novel idea: a large sieve ACROSS THE PRIME FAMILY (not across frequencies)

Every classical sieve/Plancherel route is a sum **over frequencies** at one fixed prime
(`Σ_{b≠0}|η_b|²`), and the in-tree `_AvE6_LargeSieveVacuous` proves that route DEAD: at the prize
scale the per-prime large sieve cannot distinguish a budget `n` from `p`. N9 turns the sieve
**ninety degrees**: it sums **over the prime family** at one fixed depth.

Over `ℤ`, the only vanishing sums of `2^μ`-th roots of unity are antipodal pairs `{x, −x}` (in-tree
census). Hence every *non-antipodal* depth-`r` relation `S` (a multiset of `≤ 2r` roots whose two
sides agree only mod `p`) carries a FIXED, NONZERO algebraic integer `N_S ∈ ℤ` — its integer value
over `ℤ` (nonzero precisely because `S` is non-antipodal). A relation `S` contributes to `W_r(p)`
**iff `p ∣ N_S`**. So, exactly,
```
        W_r(p) = #{ non-antipodal depth-r relations S : p ∣ N_S }  =  Σ_S 𝟙[ p ∣ N_S ].
```

**The cross-prime sieve identity.** Fix the depth `r` and the fixed finite family `{N_S}`. Sum the
excess over ALL primes `p` (equivalently over the splitting family `𝓟 = {p ≡ 1 mod 2^μ}` of the
tower; summing over more primes only enlarges the bound). Swapping the order of summation,
```
        Σ_p  W_r(p)  =  Σ_p Σ_S 𝟙[p ∣ N_S]  =  Σ_S Σ_p 𝟙[p ∣ N_S]  =  Σ_S ω(N_S)
                                                                     ≤  Σ_S log₂|N_S|.
```
The total wraparound excess summed over the ENTIRE prime family is a FIXED FINITE CONSTANT
`C_{sieve}(r) := Σ_S ω(N_S)`, **independent of how many primes are summed**. This is the large-sieve
duality identity for subgroup-sum excess across primes: the `ℓ²`-mass is replaced by the
`ω`-multiplicity, and the cross term collapses to the divisor count of a fixed integer family.

**The density bound (Markov / first-moment).** Because `Σ_{p} W_r(p) = C_{sieve}(r) < ∞` is
constant while the number of primes `≤ X` grows without bound, the AVERAGE excess `→ 0`, and the
count of BAD primes (`W_r(p) > 0`) up to any height is `≤ C_{sieve}(r)`. Hence in EVERY window
`(X, Y]` containing more than `C_{sieve}(r)` primes there is a GOOD prime (`W_r = 0`); the good
primes have density `1`. This is a POSITIVE-DENSITY (in fact density-1) supply of good prize primes,
with an EXPLICIT, finite, depth-`r` bound on the total bad count.

## WHY this is genuinely new (vs the in-tree neighbours)

* vs `_AvE6_LargeSieveVacuous`: that is a sieve over FREQUENCIES at one prime (`Σ_{b≠0}|η_b|²`,
  Parseval `= pn−n²`), and it is vacuous because the energy is `Θ(p)`. N9 is a sieve over the PRIME
  FAMILY at one depth; its conserved quantity is `Σ_S ω(N_S)`, a fixed finite integer with NO
  `p`-dependence — it is the dual object, and it is NON-vacuous (it is bounded uniformly in `X`).
* vs `_NovelPadicIwasawa` (N3): N3 proves the good set is COFINITE (each `N_S` has finitely many
  prime divisors — a per-relation, qualitative `λ=0` fact). N9 proves the QUANTITATIVE density: the
  TOTAL bad count over the whole family is `≤ Σ_S ω(N_S)`, a single explicit constant, giving an
  effective window bound (a good prime in every window with `> C_{sieve}(r)` primes). Cofiniteness is
  the limit; the sieve gives the RATE. N9's `C_sieve` is a first-moment conservation law, not a
  finiteness-of-each-atom statement.

## WHY this escapes the MOMENT-METHOD NECESSITY OBSTRUCTION (mandatory)

`MomentLadderExceedsPrize.moment_ladder_exceeds_prize` kills any *magnitude* count `c` with total
mass `n^r`: `(q·Σc²)^{1/2r} ≥ n > √(n·log(q/n))`, UNIFORMLY in `p`. The N9 conserved quantity is NOT
a magnitude count and NOT `p`-uniform. The cancellation mechanism is a **first-moment conservation
law across primes**: the contribution `𝟙[p ∣ N_S]` of one relation is `1` for at most `ω(N_S)`
primes in the ENTIRE family and `0` (a genuine `0`, not a small magnitude) for all the rest, because
each `N_S` is a `p`-adic UNIT for all but finitely many `p`. Summing over `p`, the cross terms do not
add up — they are conserved at the fixed total `Σ_S ω(N_S)`. This is the SAME non-Archimedean
cancellation the moment ladder is blind to (the ladder bounds `|·|`, an Archimedean seminorm,
uniformly in `p`; the sieve bounds `Σ_p v_p(·)`, a sum of non-Archimedean valuations, by a constant).
The mass `n^r` of relations never enters the per-prime budget — only the FIXED divisor multiplicities
`ω(N_S)` do. A bound that is `0` for all but `≤ C_sieve` primes is invisible to the `p`-uniform
`(q·Σc²)^{1/2r}`.

## WHY this does not reduce to BGK

BGK / generalized-Paley bounds the Archimedean sup-norm `M = max_{b≠0}|η_b|` UNIFORMLY in `p`. N9
makes NO uniform-in-`p` Archimedean claim — it CANNOT, because `W_r(p) > 0` genuinely occurs (Fermat
primes). It is a cross-prime CONSERVATION identity (`Σ_p W_r(p) = Σ_S ω(N_S)`) plus a density
deduction, orthogonal to the per-prime character-sum cancellation BGK extracts. It never touches
`M(p)` for a fixed `p`.

## ⚠️ THE HONEST OBSTRUCTION — N9 does NOT close the prize (read this)

The prize bound is **`∀q`-UNIFORM**: it asserts `∃ C, ∀` valid prize field `F_p`, the bound holds
(the constant `C` is quantified BEFORE the field). A density-1 / positive-density / "one good prime
suffices" statement is an **`∃`-good-prime** statement. The `∀/∃` asymmetry is FATAL here:

> A density-1 good set establishes the bound for ALMOST ALL primes, but the prize demands it for the
> SPECIFIC prize prime `p ≈ n·2^128` (and, in the strictest reading, uniformly for ALL valid prize
> primes at scale `β`). The cross-prime sieve gives the bound for a density-1 set, leaving the
> measure-zero exceptional set (the bad primes, `≤ Σ_S ω(N_S)` of them) UNCONTROLLED. If the prize
> prime is one of those finitely many bad primes, N9 says nothing; and N9 cannot rule that out
> without computing `gcd(p, ∏_S N_S)` (the `_NovelPadicIwasawa` residual).

This is the SAME wall flagged in the in-tree pigeonhole retraction: *"Pigeonhole / large-sieve give
∃-good / density-1, USELESS for `∀q`."* N9 is therefore an **OBSTRUCTION-class** result: it proves a
genuinely new, axiom-clean, non-vacuous cross-prime conservation law and density bound — but the
density-1 output is provably the WRONG SHAPE for the `∀q`-uniform prize. The honest residual that
WOULD bridge the gap is named below (`PrizePrimeNotInExceptionalSet`): the specific prize prime is
not among the `≤ C_sieve(r)` bad primes — a finite, decidable, REFUTABLE divisibility question (false
for Fermat primes), NOT discharged here.

## What this file proves (all axiom-clean: no `sorry`/`native_decide`/fabricated axiom/`[CharZero]`)

1. `crossPrimeSieve_identity` — the duality identity: the total excess summed over a finite set of
   primes equals the column sums, and is bounded by `Σ_S #{p ∈ primeSet : p ∣ N_S}`.
2. `total_excess_le_omega` — the conservation law: summed over ANY finite set of primes, the total
   excess is `≤ Σ_S ω(N_S)`, a constant independent of the prime set (the large-sieve `ℓ²→ω` bound).
3. `bad_count_le_const` — the density bound: the number of bad primes in any finite prime set is
   `≤ Σ_S ω(N_S)` = `C_sieve(r)`.
4. `good_prime_in_large_window` — one good prime exists in every prime set of size `> C_sieve(r)`
   (positive-density / density-1 supply, EFFECTIVE).
5. The honest gap: `PrizePrimeNotInExceptionalSet` (named open) and
   `charP_bound_of_prizePrime_not_exceptional` (conditional closure: prize prime good ⟹ bound),
   with `density1_not_forall_uniform` recording why density-1 ≠ the `∀q`-uniform prize.

## References
In-tree: `_AvE6_LargeSieveVacuous` (per-frequency sieve, dual & vacuous), `_NovelPadicIwasawa`
(qualitative `λ=0`/cofinite good set), `KKH26SumsOfRootsOfUnity` (over-`ℤ` antipodal-only vanishing),
`MomentLadderExceedsPrize` (moment obstruction), `CharZeroWickEnergy.gaussianEnergyBound_dyadic`
(char-0 energy). Classical: large sieve (Montgomery), Turán's first-moment / Markov, `ω(N) ≤ log₂|N|`.
Issue #444. Honest label: **OBSTRUCTION** (new axiom-clean cross-prime conservation law + density
bound; density-1 output is the wrong shape for the `∀q`-uniform prize).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.NovelCrossPrimeSieve

open Finset

/-! ## 1. The excess as a column sum, and the cross-prime sieve setup

`Wexcess relations N p = #{ S ∈ relations : p ∣ N_S }` (matching the N3 definition). The depth-`r`
relations are a fixed `Finset ι`; each carries a fixed integer `N_S` (nonzero for non-antipodal
relations, by the over-`ℤ` census). We work with a fixed `primeSet : Finset ℕ` of primes (a window
of the tower) and prove the cross-prime sieve identity by a `Finset` double-counting (Fubini). -/

/-- The depth-`r` wraparound excess at prime `p`: the number of relations whose fixed integer `N_S`
is divisible by `p`. This is `W_r(p) = Σ_S 𝟙[p ∣ N_S]`. -/
def Wexcess {ι : Type*} [DecidableEq ι] (relations : Finset ι) (N : ι → ℤ) (p : ℕ) : ℕ :=
  (relations.filter (fun S => (p : ℤ) ∣ N S)).card

/-- For a fixed relation `S`, the number of primes in `primeSet` dividing `N_S`. This is the column
sum of the incidence matrix `𝟙[p ∣ N_S]` (rows = primes, columns = relations). -/
def primeDivCount {ι : Type*} (N : ι → ℤ) (primeSet : Finset ℕ) (S : ι) : ℕ :=
  (primeSet.filter (fun p : ℕ => (p : ℤ) ∣ N S)).card

/-! ## 2. The cross-prime sieve identity (Fubini / double counting)

`Σ_{p ∈ primeSet} W_r(p) = Σ_{S ∈ relations} primeDivCount(S)`. Both sides count the incidence pairs
`(p, S)` with `p ∣ N_S`. This is the row-sum = column-sum identity at the heart of the large sieve,
here across the prime family. -/

/-- **The cross-prime sieve identity.** Summing the excess over a finite prime set equals summing the
prime-divisor counts over the relations: both count incidence pairs `(p, S)` with `p ∣ N_S`. This is
the Fubini / double-counting core of the cross-prime large sieve. -/
theorem crossPrimeSieve_identity {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (primeSet : Finset ℕ) :
    ∑ p ∈ primeSet, Wexcess relations N p
      = ∑ S ∈ relations, primeDivCount N primeSet S := by
  classical
  -- Express each side as the same double sum of indicators over `primeSet ×ˢ relations`,
  -- then swap the order of summation (Fubini / row-sum = column-sum).
  have hL : ∀ p : ℕ, Wexcess relations N p
      = ∑ S ∈ relations, (if (p : ℤ) ∣ N S then 1 else 0) := by
    intro p; rw [Wexcess, Finset.card_filter]
  have hR : ∀ S : ι, primeDivCount N primeSet S
      = ∑ p ∈ primeSet, (if (p : ℤ) ∣ N S then 1 else 0) := by
    intro S; rw [primeDivCount, Finset.card_filter]
  simp only [hL, hR]
  exact Finset.sum_comm

/-! ## 3. The conservation law: total excess across the family `≤ Σ_S ω(N_S)`

The column sum `primeDivCount N primeSet S = #{p ∈ primeSet : p ∣ N_S}` is bounded by the number of
DISTINCT prime factors of `N_S`, because the primes in `primeSet` that divide `N_S` are distinct
prime divisors of `N_S`. For `N_S ≠ 0` that is `ω(N_S) := N_S.natAbs.primeFactors.card < ∞`. Summing
over the relations gives the large-sieve `ℓ²→ω` conservation law: the total excess over the WHOLE
family is bounded by `Σ_S ω(N_S)`, a constant INDEPENDENT of `primeSet`. -/

/-- `ω(N) = #` distinct prime factors of `|N|`. For a fixed nonzero integer this is a finite
constant, the conserved per-relation budget of the cross-prime sieve. -/
def omega (N : ℤ) : ℕ := N.natAbs.primeFactors.card

/-- **Per-relation column bound.** The number of primes (in a finite set of primes) that divide a
fixed nonzero integer `N_S` is `≤ ω(N_S)`. (Each such prime is a distinct prime factor of `|N_S|`.)
This is the per-column `ℓ²→ω` bound of the cross-prime large sieve. -/
theorem primeDivCount_le_omega {ι : Type*} (N : ι → ℤ) (primeSet : Finset ℕ)
    (hprimes : ∀ p ∈ primeSet, p.Prime) (S : ι) (hN : N S ≠ 0) :
    primeDivCount N primeSet S ≤ omega (N S) := by
  classical
  unfold primeDivCount omega
  -- `{p ∈ primeSet | p ∣ N_S} ⊆ (|N_S|).primeFactors`.
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpset, hdvd⟩ := hp
  rw [Nat.mem_primeFactors]
  have hpNat : p ∣ (N S).natAbs := Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hdvd
  exact ⟨hprimes p hpset, hpNat, Int.natAbs_ne_zero.mpr hN⟩

/-- **The cross-prime conservation law (large-sieve `ℓ²→ω`).** Summed over ANY finite set of primes,
the total wraparound excess is bounded by `Σ_S ω(N_S)`, a constant INDEPENDENT of the prime set.
This is the conserved quantity of the cross-prime large sieve: enlarging the prime window does NOT
increase the total excess past `C_sieve(r) := Σ_S ω(N_S)`. -/
theorem total_excess_le_omega {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (primeSet : Finset ℕ)
    (hprimes : ∀ p ∈ primeSet, p.Prime) (hN : ∀ S ∈ relations, N S ≠ 0) :
    ∑ p ∈ primeSet, Wexcess relations N p ≤ ∑ S ∈ relations, omega (N S) := by
  rw [crossPrimeSieve_identity]
  apply Finset.sum_le_sum
  intro S hS
  exact primeDivCount_le_omega N primeSet hprimes S (hN S hS)

/-! ## 4. The density bound: bad primes are `≤ C_sieve(r)` in ANY window

A BAD prime is one with `W_r(p) ≥ 1`. Since each bad prime contributes `≥ 1` to the conserved total
`Σ_p W_r(p) ≤ Σ_S ω(N_S)`, the number of bad primes in any window is `≤ C_sieve(r)`. Hence good
primes have density `1` (the bad count is a fixed constant, independent of window size), and EVERY
prime set of size `> C_sieve(r)` contains a good prime. This is the effective positive-density
(density-1) supply of good prize primes. -/

/-- The conserved cross-prime constant `C_sieve(r) := Σ_S ω(N_S)`. -/
def cSieve {ι : Type*} (relations : Finset ι) (N : ι → ℤ) : ℕ :=
  ∑ S ∈ relations, omega (N S)

/-- **The density bound.** In any finite set of primes, the number of BAD primes (`W_r(p) ≥ 1`) is
`≤ C_sieve(r)`. The bad count is a FIXED constant, independent of the window — the hallmark of the
large-sieve density deduction. -/
theorem bad_count_le_const {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (primeSet : Finset ℕ)
    (hprimes : ∀ p ∈ primeSet, p.Prime) (hN : ∀ S ∈ relations, N S ≠ 0) :
    (primeSet.filter (fun p => 1 ≤ Wexcess relations N p)).card ≤ cSieve relations N := by
  classical
  -- the bad-prime count `≤ Σ_{p ∈ bad} W_r(p) ≤ Σ_{p ∈ primeSet} W_r(p) ≤ Σ_S ω(N_S)`.
  have hcard :
      (primeSet.filter (fun p => 1 ≤ Wexcess relations N p)).card
        ≤ ∑ p ∈ primeSet.filter (fun p => 1 ≤ Wexcess relations N p),
            Wexcess relations N p := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsub :
      ∑ p ∈ primeSet.filter (fun p => 1 ≤ Wexcess relations N p), Wexcess relations N p
        ≤ ∑ p ∈ primeSet, Wexcess relations N p :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc (primeSet.filter (fun p => 1 ≤ Wexcess relations N p)).card
      ≤ ∑ p ∈ primeSet.filter (fun p => 1 ≤ Wexcess relations N p), Wexcess relations N p := hcard
    _ ≤ ∑ p ∈ primeSet, Wexcess relations N p := hsub
    _ ≤ ∑ S ∈ relations, omega (N S) := total_excess_le_omega relations N primeSet hprimes hN
    _ = cSieve relations N := rfl

/-- **A good prime exists in every large window (effective positive density).** Any set of primes of
size strictly greater than `C_sieve(r)` contains a GOOD prime (`W_r(p) = 0`). Hence the good primes
have density `1`: the supply of valid prize-candidate primes with zero wraparound excess is
unbounded, with an EXPLICIT bound on the exceptional set. -/
theorem good_prime_in_large_window {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (primeSet : Finset ℕ)
    (hprimes : ∀ p ∈ primeSet, p.Prime) (hN : ∀ S ∈ relations, N S ≠ 0)
    (hsize : cSieve relations N < primeSet.card) :
    ∃ p ∈ primeSet, Wexcess relations N p = 0 := by
  classical
  -- if EVERY prime in primeSet were bad, the bad count would be `primeSet.card > C_sieve`,
  -- contradicting `bad_count_le_const`.
  by_contra hcon
  push_neg at hcon
  have hall : ∀ p ∈ primeSet, 1 ≤ Wexcess relations N p := by
    intro p hp
    exact Nat.one_le_iff_ne_zero.mpr (hcon p hp)
  have hfilter_eq : primeSet.filter (fun p => 1 ≤ Wexcess relations N p) = primeSet :=
    Finset.filter_true_of_mem hall
  have hbad := bad_count_le_const relations N primeSet hprimes hN
  rw [hfilter_eq] at hbad
  exact absurd hbad (Nat.not_le.mpr hsize)

/-! ## 5. The honest gap and the conditional closure

`good_prime_in_large_window` gives a density-1 supply of good primes. The prize, however, is
`∀q`-UNIFORM: the constant is quantified BEFORE the field, so the bound must hold for the SPECIFIC
prize prime (and, strictly, for ALL valid prize primes at scale `β`). A density-1 / `∃`-good-prime
statement is the WRONG SHAPE. We record both the named open residual that bridges the gap and the
abstract `∀q`-vs-`∃q` mismatch that makes the bridge necessary. -/

/-- **THE NAMED OPEN RESIDUAL.** The specific prize prime `p` is NOT in the (finite, `≤ C_sieve(r)`)
exceptional set — its wraparound excess vanishes. By `good_prime_in_large_window` such primes are
density-1, but the prize demands this for THE prize prime, which is a finite, decidable
(`gcd(p, ∏_S N_S) = 1`), REFUTABLE (false for Fermat primes) divisibility question. NOT discharged. -/
def PrizePrimeNotInExceptionalSet {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (p : ℕ) : Prop :=
  Wexcess relations N p = 0

/-- **CONDITIONAL CLOSURE (skeleton).** GIVEN the named residual for the prize prime, plus the
in-tree char-0 energy bound `E0 ≤ Wick` and the decomposition `Ep = E0 + W_r(p)`, the char-`p`
energy bound holds at the prize prime. SKELETON (one named open step), not CLOSED. -/
theorem charP_bound_of_prizePrime_not_exceptional {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (p : ℕ)
    {Ep E0 Wick : ℝ}
    (hdecomp : Ep = E0 + (Wexcess relations N p : ℝ)) (hchar0 : E0 ≤ Wick)
    (hgood : PrizePrimeNotInExceptionalSet relations N p) :
    Ep ≤ Wick := by
  unfold PrizePrimeNotInExceptionalSet at hgood
  rw [hdecomp, hgood]; simpa using hchar0

/-- **The honest `∀q`-vs-density-1 mismatch.** A predicate `Good` can hold on a density-1 set (here:
all but `≤ C_sieve` primes) yet FAIL on a specific designated prime. This abstractly records why the
cross-prime sieve's density-1 output does NOT entail the `∀q`-uniform prize statement: density-1 is
an `∃`/almost-all statement, the prize a `∀`/uniform one, and the finite exceptional set can contain
the prize prime. (Witness: `Good := (· ≠ p₀)` is density-1 but false at `p₀`.) -/
theorem density1_not_forall_uniform :
    ∃ (Good : ℕ → Prop) (p₀ : ℕ),
      {p : ℕ | ¬ Good p}.Finite ∧ ¬ Good p₀ := by
  refine ⟨fun p => p ≠ 0, 0, ?_, ?_⟩
  · -- complement is `{0}`, finite.
    have : {p : ℕ | ¬ (p ≠ 0)} = {0} := by
      ext p; simp
    rw [this]; exact Set.finite_singleton 0
  · simp

/-! ## 6. Non-vacuity: the residual is refutable (no smuggling)

The named residual `PrizePrimeNotInExceptionalSet` is genuinely refutable: a prime that divides some
relation integer `N_S` has `Wexcess ≥ 1`, so it is NOT good. This rules out a vacuous-hypothesis
"closure". -/

/-- **Refutability witness.** If `p` divides some relation's integer `N_S₀`, then `p` is in the
exceptional set (`Wexcess ≥ 1`), so the named residual is FALSE there. The residual is a real,
refutable condition (false e.g. for Fermat primes), not a hypothesis that smuggles the conclusion. -/
theorem not_good_of_dvd {ι : Type*} [DecidableEq ι]
    (relations : Finset ι) (N : ι → ℤ) (p : ℕ)
    {S₀ : ι} (hS₀ : S₀ ∈ relations) (hdvd : (p : ℤ) ∣ N S₀) :
    ¬ PrizePrimeNotInExceptionalSet relations N p := by
  unfold PrizePrimeNotInExceptionalSet Wexcess
  rw [Finset.card_eq_zero]
  intro hempty
  have hmem : S₀ ∈ relations.filter (fun S => (p : ℤ) ∣ N S) :=
    Finset.mem_filter.mpr ⟨hS₀, hdvd⟩
  rw [hempty] at hmem
  exact absurd hmem (Finset.notMem_empty S₀)

#print axioms crossPrimeSieve_identity
#print axioms total_excess_le_omega
#print axioms bad_count_le_const
#print axioms good_prime_in_large_window
#print axioms charP_bound_of_prizePrime_not_exceptional
#print axioms density1_not_forall_uniform
#print axioms not_good_of_dvd

end ArkLib.ProximityGap.NovelCrossPrimeSieve
