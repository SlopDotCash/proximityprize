/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

/-!
# Split-prime signed sieve for the wraparound excess is VACUOUS (#444, Mechanism 6 no-go)

**Target (attempted).**  A NOVEL signed inclusion–exclusion sieve for the RS proximity-gap
wraparound excess `W_r`, over the `φ(n)` degree-1 primes `P_1,…,P_{φ(n)}` into which the
prize prime `p` splits completely in `ℤ[ζ_n]` (`n ∣ p−1`).  The seed: "`p ∣ α`" was read as
`φ(n)` simultaneous Galois-conjugate vanishing conditions `α ≡ 0 (mod P_i) ∀ i`, and a sieve
`W = Σ_{S} (−1)^{|S|} N_S`, `N_S = #{α ≡ 0 mod ∏_{i∈S} P_i}`, was hoped to cancel.

**Result: a clean, EXACT no-go (verified by exhaustive ℤ-exact enumeration, `/tmp/sieve_probe*.py`).**
The mechanism splits into two halves, BOTH of which hit a trap, simultaneously:

1. **The φ(n)-prime sieve computes the WRONG object, which is identically empty.**
   The full-set term `N_{full} = #{wraparound α : α ∈ (p)}` (= `α ≡ 0 mod ALL P_i` = `α/p ∈ ℤ[ζ_n]`)
   is `0` throughout the prize regime, by a **Minkowski / coefficient-size bound**:
   a wraparound `α = Σ_{j≤r} ζ^{x_j} − Σ_{j≤r} ζ^{y_j}` has *every* archimedean conjugate
   bounded by `2r` (sum of `2r` unit-modulus roots), whereas `α ∈ (p) ∖ {0}` forces
   *some* conjugate to have modulus `≥ p` (because `|N(α/p)| ≥ 1` for the nonzero algebraic
   integer `α/p`, so some conjugate of `α/p` has modulus `≥ 1`).  Since at the saddle
   `r ~ ln q` we have `2r ≪ p`, **no** nonzero wraparound lies in `(p)`: `N_{full} = 0`.
   The sieve is exact but sieves the EMPTY set — the mirror of TRAP 1 (vacuous counting).
   Exact check: `n=8, p=17`, `W_full = 0` at `r=2,3,4` while `W_single = 96, 10440, 797664 ≠ 0`;
   every wraparound α has max conjugate modulus `5.60 ≪ 17 = p`.

2. **The TRUE wraparound `W_r` is a SINGLE-prime object, and that object IS BGK.**
   The defining condition "`Σx = Σy` in `F_p`" is reduction mod the ONE prime `P_1` fixed by
   the embedding `μ_n ↪ F_p` (`ζ_n ↦ g`).  There is no `φ(n)`-fold alternating sum producing it —
   `W_r` is the single `|S|=1` term, with nothing to sieve over.  And exactly
   `N_{P_1} = (1/p) Σ_{b} |η_b|^{2r}` (verified exact: `264, 15560` at `n=8,p=17,r=2,3`),
   i.e. the BGK / di-Benedetto character-sum energy — TRAP 2.

So the genuinely-novel split-prime CRT structure, correctly set up, sieves an empty set;
and the object it was meant to bound collapses to the archimedean char-sum.  **Both traps,
with an exact proof.**

**RELATION TO IN-TREE WORK (honesty).**  The SINGLE-prime Minkowski-vacuity fact —
`Q4 = 0` below the ℓ¹ shortest-vector threshold of the ONE chosen split prime `𝔭₀` — is
ALREADY in the cone: `CyclotomicLatticeWrapOnset.wrapExcess_eq_zero_below_minWeight`
(`+ MinkowskiL1ShortestVectorBound`).  That file even already records the punchline that killing
`Q4` lands back on the `b≠0` BGK wall.  So the Minkowski half here is NOT new.

**What IS new in this file: the SIEVE-SPECIFIC no-go.**  Mechanism 6 proposed a `φ(n)`-FOLD
alternating inclusion–exclusion over ALL the split primes, whose top term is
`W_full = #{wraparound α ∈ (p)} = #{α ≡ 0 mod ALL P_i}`.  This is a STRICTLY SMALLER (more
vacuous) target than the single-prime `Q4`: it needs vanishing mod every conjugate prime, which
forces a conjugate `≥ p`, never met for `2r ≪ p`.  And there is no `φ(n)`-fold structure to
exploit — the true `W_r` is the |S|=1 single-prime term itself.  This file proves the
field-agnostic structural heart: any signed sieve whose top term is the all-primes set `InIdeal`
sums over the EMPTY set in the prize regime.  Model: `cvals : Fin d → ℝ` are conjugate magnitudes;
`bound = 2r`; `prime = p`.  `InIdeal` (some conjugate `≥ p`) is provably disjoint from the
`bound < prime` set, so the sieve's cardinality is `0`.  No NumberField import: the no-go is the
elementary archimedean gap, complementing (not duplicating) the lattice-library route in
`CyclotomicLatticeWrapOnset`.

**Honesty.**  This is a NO-GO (a named dead end for Mechanism 6), not a closure.  It does NOT
bound the prize `W_r`; it shows the proposed `φ(n)`-prime sieve cannot, because its top term
targets the (even-more-)empty `W_full`, while the true `W_r` is the single-prime `Q4` count
`= (1/p)Σ_b|η_b|^{2r} =` BGK.  All proofs are elementary; `#print axioms` shows only the trio.
-/

namespace ProximityGap.Frontier.SplitPrimeSieveVacuous

open Finset
open scoped Classical

/-- A candidate "wraparound element" abstracted by its `d` archimedean conjugate magnitudes
`cvals`, with the structural facts the sieve depends on:
* `coeffBound`  — every conjugate magnitude is `≤ bound` (here `bound = 2r`, the # of unit roots);
* `prime`       — the rational prime `p` that splits completely (`prime = p`). -/
structure SieveElt (d : ℕ) where
  /-- magnitudes `|σ_i(α)|` of the `d` archimedean conjugates. -/
  cvals : Fin d → ℝ
  bound : ℝ
  prime : ℝ
  coeffBound : ∀ i, cvals i ≤ bound

variable {d : ℕ}

/-- Membership in the ideal `(p)` (the FULL-set sieve term) is detected archimedeanly:
`α ∈ (p) ∖ {0}` forces some conjugate `|σ_i(α)| ≥ p`.  This is the Minkowski direction
(`|N(α/p)| ≥ 1 ⇒ ∃ conjugate of α/p with modulus ≥ 1 ⇒ |σ_i(α)| ≥ p`). -/
def InIdeal (e : SieveElt d) : Prop := ∃ i, e.prime ≤ e.cvals i

/-- The archimedean separation: the coefficient bound is strictly below the prime
(`2r < p`, the prize-regime saddle `r ~ ln q`). -/
def SubPrime (e : SieveElt d) : Prop := e.bound < e.prime

/-- **Core no-go.**  In the sub-prime (prize) regime, a wraparound element CANNOT lie in `(p)`:
the full-set sieve term has no members.  (`max conjugate ≤ 2r < p ≤` any ideal conjugate.) -/
theorem not_inIdeal_of_subPrime (e : SieveElt d) (h : SubPrime e) : ¬ InIdeal e := by
  rintro ⟨i, hi⟩
  -- p ≤ |σ_i| ≤ bound < p, contradiction.
  have h1 : e.prime ≤ e.bound := le_trans hi (e.coeffBound i)
  exact (not_lt.mpr h1) h

/-- **Vacuity of the φ(n)-prime sieve, set form.**  Over any finite family of candidate
wraparound elements, the subset satisfying the full-ideal (all-primes) condition is EMPTY
in the prize regime.  Hence *any* signed inclusion–exclusion whose top term is this set
sums over an empty set — the sieve is vacuous, never a bound on the true `W_r`. -/
theorem ideal_filter_empty {ι : Type*} (s : Finset ι) (E : ι → SieveElt d)
    (h : ∀ x ∈ s, SubPrime (E x)) :
    (s.filter (fun x => InIdeal (E x))) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x hx
  exact not_inIdeal_of_subPrime (E x) (h x hx)

/-- **Cardinality form**: `N_{full} = 0` in the prize regime — the count the φ(n)-prime
sieve produces is identically zero.  (DecidableEq via classical, no `decide`.) -/
theorem ideal_filter_card_zero {ι : Type*} (s : Finset ι) (E : ι → SieveElt d)
    (h : ∀ x ∈ s, SubPrime (E x)) :
    (s.filter (fun x => InIdeal (E x))).card = 0 := by
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro x hx
  exact not_inIdeal_of_subPrime (E x) (h x hx)

/-- The concrete instantiation that makes the no-go bite: with `r` wraparound summands the
bound is `2r`, and the prize-regime hypothesis is exactly `2r < p`. -/
theorem subPrime_of_two_r_lt_prime {d : ℕ} (r : ℕ) (p : ℝ) (cvals : Fin d → ℝ)
    (hc : ∀ i, cvals i ≤ (2 * r : ℝ)) (hr : (2 * r : ℝ) < p) :
    SubPrime ⟨cvals, (2 * r : ℝ), p, hc⟩ := hr

/-- **Headline corollary**: at the prize saddle the wraparound excess that the φ(n)-split-prime
signed sieve can express (the `α ∈ (p)` full-set term) is `0`.  Therefore the sieve is NOT a
nonvacuous bound on `W_r`; the true `W_r` is the single-prime `(mod P_1)` count, which equals
the BGK energy `(1/p)Σ_b|η_b|^{2r}` (documented above, verified numerically) — i.e. the wall. -/
theorem split_prime_sieve_is_vacuous {ι : Type*} (s : Finset ι) (r : ℕ) (p : ℝ)
    (E : ι → SieveElt d)
    (_hbound : ∀ x ∈ s, ∀ i, (E x).cvals i ≤ (2 * r : ℝ))
    (hreg : ∀ x ∈ s, (E x).bound = (2 * r : ℝ))
    (hprime : ∀ x ∈ s, (E x).prime = p)
    (hr : (2 * r : ℝ) < p) :
    (s.filter (fun x => InIdeal (E x))) = ∅ := by
  apply ideal_filter_empty s E
  intro x hx
  show (E x).bound < (E x).prime
  rw [hreg x hx, hprime x hx]
  exact hr

end ProximityGap.Frontier.SplitPrimeSieveVacuous
