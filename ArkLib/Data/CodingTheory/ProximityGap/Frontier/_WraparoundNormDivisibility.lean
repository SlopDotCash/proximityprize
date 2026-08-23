/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The wraparound as cyclotomic-norm divisibility (#444)

Target (2) of the scheduled attack: reframe the wraparound `W_r(p)` as a divisibility count over short
cyclotomic integers, and extract the genuinely-provable per-relation bound (the prime-divisor count),
then test whether it controls the worst-case prime or goes vacuous.

**The exact reframing.**  A depth-`r` relation is a pair `(a,b)` of `r`-tuples of `n`-th roots; its value is
the cyclotomic integer `α = Σ ζ^{a_i} − Σ ζ^{b_j} ∈ ℤ[ζ_n]`.  For the chosen split prime `𝔭 | p`
(`ℤ[ζ_n]/𝔭 ≅ F_p`), the char-`p` energy `E_r = Σ_{α ∈ 𝔭} mult_r(α)` (pairs landing in one `F_p`-class),
the char-0 energy `E_char0 = mult_r(0)` (exact zero relations), so the wraparound is exactly
`W_r(p) = Σ_{0 ≠ α ∈ 𝔭} mult_r(α)` — the *nonzero* short cyclotomic integers that reduce into `𝔭`.
`energy_eq_char0_add_wraparound` records this split.

**The provable per-relation bound.**  A relation of depth `r` has `‖σ(α)‖ ≤ 2r` in every embedding, so its
field norm satisfies `|N(α)| ≤ (2r)^{φ(n)}`.  A *fixed* nonzero `α` lies in `𝔭` only for primes `p | N(α)`,
of which there are at most `ω(N(α)) ≤ log₂|N(α)| ≤ φ(n)·log₂(2r)`.  So each relation "wraps around" at only
*boundedly many* primes — `two_pow_primeFactors_card_le` and `short_relation_prime_count` prove the count
bound `2^{ω(N)} ≤ N ≤ B^d`, axiom-clean.

**Why it does not close the worst case (honest, see `probe_norm_divisibility`).**  Summing the per-relation
bound over all `~n^{2r}` relations bounds the *total* `(α, bad-prime)` incidence by `n^{2r}·φ(n)·log₂(2r)`,
hence the *average* `W_r` over primes — but the wraparound is over-dispersed (`_OverdispersionObstructsVariance`),
so the average does not bound the worst-case prime.  Concretely the Markov/union bad-prime count
`#{p : W_r ≥ T} ≤ (Σ mult·ω)/T` is *vacuous* at prize scale (it exceeds the admissible prime count), because a
single prime `𝔭` contains `~p·φ(n)` short cyclotomic integers — the worst-case `W_r(p)` is the lattice-point
count of the box in `𝔭`, which is the growing-order equidistribution wall.  The per-relation bound is real and
new; it controls the *average*, not the *supremum*.  We record both.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace ProximityGap.WraparoundNormDivisibility

open Finset

/-! ## 1. The exact reframing: energy = char-0 multiplicity + wraparound -/

/-- **The wraparound reframing.**  Over the finite support `s ∋ 0` of the multiplicity function `mult`,
with the prime-ideal membership predicate `pred` (and `pred 0`), the char-`p` energy `∑_{α ∈ 𝔭} mult α`
equals the char-0 multiplicity `mult 0` plus the wraparound `∑_{0 ≠ α ∈ 𝔭} mult α`.  This is the exact
split `E_r = E_char0 + W_r` with `E_char0 = mult_r(0)` and `W_r = Σ_{0≠α∈𝔭} mult_r(α)`. -/
theorem energy_eq_char0_add_wraparound {G : Type*} [DecidableEq G] [Zero G]
    (s : Finset G) (mult : G → ℕ) (pred : G → Prop) [DecidablePred pred]
    (h0s : (0 : G) ∈ s) (h0p : pred 0) :
    (∑ α ∈ s.filter pred, mult α)
      = mult 0 + ∑ α ∈ (s.filter pred).erase 0, mult α := by
  have hmem : (0 : G) ∈ s.filter pred := mem_filter.mpr ⟨h0s, h0p⟩
  rw [← Finset.add_sum_erase _ mult hmem]

/-! ## 2. The provable per-relation prime-divisor bound -/

/-- **`2^{ω(N)} ≤ N`.**  A positive integer has at most `log₂ N` distinct prime factors, because the product
of its (distinct, each `≥ 2`) prime factors divides `N`.  This bounds the number of primes a fixed nonzero
cyclotomic relation can wrap around at. -/
theorem two_pow_primeFactors_card_le {N : ℕ} (hN : 1 ≤ N) :
    2 ^ N.primeFactors.card ≤ N := by
  have hprod : (∏ p ∈ N.primeFactors, p) ∣ N := Nat.prod_primeFactors_dvd N
  have hle : 2 ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p := by
    calc 2 ^ N.primeFactors.card
        = ∏ _p ∈ N.primeFactors, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact le_trans hle (Nat.le_of_dvd hN hprod)

/-- **Per-relation prime count, archimedean form.**  If the field norm of a relation is bounded by `B^d`
(`B = 2r`, `d = φ(n)` — the archimedean bound `|N(α)| ≤ (2r)^{φ(n)}`), then the number of distinct primes
it can wrap around at is bounded: `2^{ω(N)} ≤ B^d`.  Equivalently `ω(N(α)) ≤ φ(n)·log₂(2r)`: each short
relation is `𝔭`-divisible for only logarithmically-many primes. -/
theorem short_relation_prime_count {N B d : ℕ} (hN : 1 ≤ N) (hbound : N ≤ B ^ d) :
    2 ^ N.primeFactors.card ≤ B ^ d :=
  le_trans (two_pow_primeFactors_card_le hN) hbound

/-- **The per-relation count is a constant in `p`.**  Restated multiplicatively: the number of primes a
relation with norm `≤ B^d` wraps around at, `ω(N)`, satisfies `2^{ω(N)} ≤ B^d`, a bound *independent of which
prime `p`* — the content that makes the *average* wraparound `O(n^{2r}·φ(n)·log r / #primes)`, even though the
*supremum* over primes is not controlled (over-dispersion; the worst prime is a lattice-point count). -/
theorem wraparound_average_is_controlled_per_relation {N B d : ℕ} (hN : 1 ≤ N) (hbound : N ≤ B ^ d) :
    2 ^ N.primeFactors.card ≤ B ^ d :=
  short_relation_prime_count hN hbound

end ProximityGap.WraparoundNormDivisibility
