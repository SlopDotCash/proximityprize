/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# KKH26 at polynomial field size: the conditional Thorner–Zaman `δ*` ceiling (issue #334)

This file composes the two wave-1 lanes of issue #334 into the [KKH26] Lemma 2 endgame:

1. **the good-prime supply** (`KKH26ThornerZaman.lean`): conditionally on the named [TZ24]
   hypothesis `TZPrimeSupply n β supply` (Thorner–Zaman's refined PNT in arithmetic
   progressions — the `Hab25Johnson` named-hypothesis pattern, never an axiom), if the
   supply exceeds the bad-prime budget, some prime `p ≡ 1 (mod n)` with
   `n^β ≤ p ≤ 2·n^β` divides **none** of a given family of nonzero bounded integers
   (`kkh26_good_prime_of_TZ`); and
2. **the divisibility-route separation chain** (`KKH26SumsOfRootsOfUnity.lean` +
   `KKH26WitnessSpread.lean`, issue #334 additions): the entire [KKH26] Lemma 1 →
   witness-spread → `δ*`-ceiling pipeline re-plumbed through the hypothesis "`p` divides no
   collision resultant `collisionResultant μ d₁ d₂`" in place of the superpolynomial size
   threshold `p > (2^μ)^{2^{μ−1}}` (`kkh26_lemma1_of_not_dvd`,
   `kkh26_mcaDeltaStar_le_of_not_dvd`).

The composition instantiates the integer family of (1) with the collision resultants of
(2), indexed by the finite set `collisionPairs μ r` of ordered pairs of distinct signed
data.  The resultants are nonzero (`collisionResultant_ne_zero`) and bounded by
`s^{s/2} = (2^μ)^{2^{μ−1}}` (`natAbs_collisionResultant_le`), so the [TZ24] good prime
avoids all of them, and the whole separation argument runs at `p = Θ(n^β)` — polynomial
in the domain size `n = 2^μ·m`, as in [KKH26] Theorem 1 — instead of `p > s^{s/2}`.

**Honest conditionality.**  Everything here is unconditional *except* the single named
hypothesis `TZPrimeSupply n β supply`, which is the analytic [TZ24] input (log-free
zero-density estimates; far beyond present-day formalization) together with the numeric
budget hypothesis `hcount` comparing it to the bad-prime count.  On paper [TZ24] Cor 3.1
instantiates the supply with `~ n^{β−1−o(1)}` for every fixed `β > 12/5` (every `β > 1`
under Montgomery's conjecture), which dwarfs the budget
`|collisionPairs|·2^{μ−1}·μ·log 2/(β·log n)` for the [KKH26] parameter ranges.

## Main results

* `collisionPairs` — the index set of collision resultants (ordered pairs of distinct
  signed data).
* `card_collisionPairs` / `card_collisionPairs_le_square` — the exact `A(A - 1)` count and
  the coarse `A^2` upper bound for `A = 2^r * (2^(μ - 1)).choose r`.
* `coarseResultantLogRatio_nonneg` / `kkh26_mcaDeltaStar_le_of_TZ_square_bound` — a reusable
  square-budget consumer: it is enough for the prime supply to beat the common upper bound
  `A^2 * log((2^μ)^(2^(μ-1))) / log(n^β)`.
* `kkh26_good_prime_avoids_collisions_of_TZ` — **conditional [KKH26] Lemma 2,
  instantiated**: given the [TZ24] supply and the budget inequality, some prime
  `p ≡ 1 (mod n)`, `p ∈ [n^β, 2n^β]`, divides no collision resultant.
* `kkh26_mcaDeltaStar_le_of_TZ` — **conditional headline**: under the same hypotheses there
  is a prime `p = Θ(n^β)` and a smooth domain `⟨g⟩ ⊆ F_p^×` of order `n = 2^μ·m` such that
  the formal MCA threshold of the explicit evaluation code satisfies
  `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ` for every `ε* < 2^r·(2^{μ−1}).choose r / p` — the
  [KKH26] `δ*` ceiling at **polynomial field size**.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 (Lemma 2, Theorem 1).
* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Cor 3.1.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.  Issue #334.
-/

open Polynomial Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ### The collision-resultant family, enumerated for the good-prime supply -/

/-- The index set of collision resultants: ordered pairs of **distinct** signed data from
`sigData (2^{μ−1}) r`.  Its cardinality (`≤ (2^r·(2^{μ−1}).choose r)²`) is the `m` of the
bad-prime budget in `kkh26_good_prime_of_TZ`. -/
def collisionPairs (μ r : ℕ) :
    Finset (((_ : Finset ℕ) × Finset ℕ) × ((_ : Finset ℕ) × Finset ℕ)) :=
  ((sigData (2 ^ (μ - 1)) r) ×ˢ (sigData (2 ^ (μ - 1)) r)).filter fun q => q.1 ≠ q.2

lemma mem_collisionPairs {μ r : ℕ}
    {q : ((_ : Finset ℕ) × Finset ℕ) × ((_ : Finset ℕ) × Finset ℕ)} :
    q ∈ collisionPairs μ r ↔
      q.1 ∈ sigData (2 ^ (μ - 1)) r ∧ q.2 ∈ sigData (2 ^ (μ - 1)) r ∧ q.1 ≠ q.2 := by
  simp only [collisionPairs, Finset.mem_filter, Finset.mem_product]
  tauto

/-- The collision-pair index set is the off-diagonal of the signed-data set. -/
lemma collisionPairs_eq_offDiag (μ r : ℕ) :
    collisionPairs μ r = (sigData (2 ^ (μ - 1)) r).offDiag := by
  ext q
  rw [mem_collisionPairs, Finset.mem_offDiag]

/-- Exact cardinality of the collision-resultant family:
`|collisionPairs μ r| = A(A - 1)` with `A = 2^r * C(2^(μ-1), r)`. -/
lemma card_collisionPairs (μ r : ℕ) :
    (collisionPairs μ r).card =
      (2 ^ r * (2 ^ (μ - 1)).choose r) *
        (2 ^ r * (2 ^ (μ - 1)).choose r - 1) := by
  rw [collisionPairs_eq_offDiag, Finset.offDiag_card, card_sigData]
  rw [Nat.mul_sub_one]

/-- The coarse square upper bound on collision pairs used in the [KKH26] prime budget. -/
lemma card_collisionPairs_le_square (μ r : ℕ) :
    (collisionPairs μ r).card ≤ (2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 := by
  rw [card_collisionPairs, pow_two]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- The logarithmic resultant-budget factor used by the coarse KKH26 bound is nonnegative
whenever the prime window starts at `n^β ≥ 2`. -/
lemma coarseResultantLogRatio_nonneg {n : ℕ} {β : ℝ} (μ : ℕ)
    (hx : 2 ≤ (n : ℝ) ^ β) :
    0 ≤
      Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) /
        Real.log ((n : ℝ) ^ β) := by
  have hMpos : 0 < (((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1)) :=
    pow_pos (Nat.two_pow_pos μ) _
  have hMone : (1 : ℝ) ≤ (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_of_lt hMpos
  have hnum : 0 ≤ Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) :=
    Real.log_nonneg hMone
  have hden : 0 < Real.log ((n : ℝ) ^ β) := Real.log_pos (by linarith)
  exact div_nonneg hnum hden.le

/-- **Conditional [KKH26] Lemma 2, instantiated at the collision resultants.**  Given the
named [TZ24] supply `TZPrimeSupply n β supply` and the budget inequality (the supply
strictly exceeds `|collisionPairs μ r| · log(s^{s/2}) / log(n^β)` with `s = 2^μ`), some
prime `p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β` divides **no** collision resultant of
distinct signed data — exactly the divisibility hypothesis of `kkh26_lemma1_of_not_dvd`. -/
theorem kkh26_good_prime_avoids_collisions_of_TZ {n : ℕ} {β : ℝ} {supply : ℕ}
    (hTZ : TZPrimeSupply n β supply) {μ r : ℕ} (hμ : 1 ≤ μ) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hcount : ((collisionPairs μ r).card : ℝ) *
        (Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r, d₁ ≠ d₂ →
        ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂ := by
  classical
  obtain ⟨p, hp, hmod, hlb, hub, hgood⟩ :=
    kkh26_good_prime_of_TZ (M := ((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) hTZ
      (R := fun i : Fin (collisionPairs μ r).card =>
        collisionResultant μ ((collisionPairs μ r).equivFin.symm i).1.1
          ((collisionPairs μ r).equivFin.symm i).1.2)
      (fun i => by
        obtain ⟨h1, h2, h3⟩ :=
          mem_collisionPairs.mp ((collisionPairs μ r).equivFin.symm i).2
        exact collisionResultant_ne_zero hμ h1 h2 h3)
      (fun i => by
        obtain ⟨h1, h2, _⟩ :=
          mem_collisionPairs.mp ((collisionPairs μ r).equivFin.symm i).2
        exact_mod_cast natAbs_collisionResultant_le hμ h1 h2 hr)
      hx hcount
  refine ⟨p, hp, hmod, hlb, hub, fun d₁ hd₁ d₂ hd₂ hne => ?_⟩
  have hq : (d₁, d₂) ∈ collisionPairs μ r := mem_collisionPairs.mpr ⟨hd₁, hd₂, hne⟩
  have h := hgood ((collisionPairs μ r).equivFin ⟨(d₁, d₂), hq⟩)
  rwa [Equiv.symm_apply_apply] at h

/-- **Square-budget version of the conditional good-prime step.**  It is enough for the
Thorner-Zaman supply to beat the coarse paper budget
`(2^r * C(2^(μ-1), r))^2 * log((2^μ)^(2^(μ-1))) / log(n^β)`; the exact collision-pair
budget is smaller by `card_collisionPairs_le_square`. -/
theorem kkh26_good_prime_avoids_collisions_of_TZ_square_bound {n : ℕ} {β : ℝ} {supply : ℕ}
    (hTZ : TZPrimeSupply n β supply) {μ r : ℕ} (hμ : 1 ≤ μ) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hcount : (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        (Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) /
          Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r, d₁ ≠ d₂ →
        ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂ := by
  refine kkh26_good_prime_avoids_collisions_of_TZ hTZ hμ hr hx ?_
  have hcard : ((collisionPairs μ r).card : ℝ) ≤
      (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_collisionPairs_le_square μ r
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hcard (coarseResultantLogRatio_nonneg μ hx)) hcount

/-! ### A smooth domain inside the good prime field -/

/-- `p ≡ 1 (mod n)` gives an element of multiplicative order `n` in `F_p` (the unit group
is cyclic of order `p − 1` and `n ∣ p − 1`). -/
private lemma exists_orderOf_eq_of_modEq {p : ℕ} [Fact p.Prime] {n : ℕ} (_hn : 0 < n)
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

/-! ### The conditional headline -/

/-- **The [KKH26] `δ*` ceiling at polynomial field size, conditional on [TZ24]**
(issue #334).  Given the named Thorner–Zaman supply `TZPrimeSupply n β supply` for the
smooth modulus `n = 2^μ·m` and the bad-prime budget inequality, there is a prime
`p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β` — i.e. `p = Θ(n^β)`, polynomial in `n` — and a
smooth evaluation domain `⟨g⟩ ⊆ F_p^×` of order `n`, such that for every target error
`ε* < 2^r·(2^{μ−1}).choose r / p` the formal MCA threshold of the explicit evaluation
code of degree `≤ (r−2)m` satisfies

  `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ`,

strictly below the code's capacity.  This removes the superpolynomial field-size blemish
of `kkh26_mcaDeltaStar_le` exactly as [KKH26] Lemma 2 prescribes; the *only* unproven
input is the named analytic hypothesis `hTZ` (plus the numeric budget `hcount`, which the
paper's parameters satisfy with room to spare). -/
theorem kkh26_mcaDeltaStar_le_of_TZ {n : ℕ} {β : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : TZPrimeSupply n β supply) {μ m r : ℕ}
    (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ μ : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hcount : ((collisionPairs μ r).card : ℝ) *
        (Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  obtain ⟨p, hp, hmod, hlb, hub, hndvd⟩ :=
    kkh26_good_prime_avoids_collisions_of_TZ hTZ hμ hr hx hcount
  haveI hfact : Fact p.Prime := ⟨hp⟩
  have hplp : (2 : ℕ) ^ μ < p := by
    exact_mod_cast lt_of_lt_of_le hpl hlb
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_modEq hn0 hmod
  refine ⟨p, hp, hmod, hlb, hub, hfact, g, hg, fun εstar hεstar => ?_⟩
  exact kkh26_mcaDeltaStar_le_of_not_dvd hμ hm hn (hn ▸ hg) hplp hr2 hr hndvd
    εstar hεstar

/-- **The [KKH26] `δ*` ceiling at polynomial field size from the coarse square budget.**
This is the same conditional headline as `kkh26_mcaDeltaStar_le_of_TZ`, but callers may provide
the common paper-side upper bound
`(2^r * C(2^(μ-1), r))^2 * log((2^μ)^(2^(μ-1))) / log(n^β) < supply` directly. -/
theorem kkh26_mcaDeltaStar_le_of_TZ_square_bound {n : ℕ} {β : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : TZPrimeSupply n β supply) {μ m r : ℕ}
    (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ μ : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hcount : (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        (Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) /
          Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  refine kkh26_mcaDeltaStar_le_of_TZ hTZ hμ hm hn hr2 hr hx hpl ?_
  have hcard : ((collisionPairs μ r).card : ℝ) ≤
      (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_collisionPairs_le_square μ r
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hcard (coarseResultantLogRatio_nonneg μ hx)) hcount

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.collisionPairs_eq_offDiag
#print axioms ArkLib.ProximityGap.KKH26.card_collisionPairs
#print axioms ArkLib.ProximityGap.KKH26.card_collisionPairs_le_square
#print axioms ArkLib.ProximityGap.KKH26.coarseResultantLogRatio_nonneg
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_avoids_collisions_of_TZ
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_avoids_collisions_of_TZ_square_bound
#print axioms ArkLib.ProximityGap.KKH26.exists_orderOf_eq_of_modEq
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_of_TZ
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_of_TZ_square_bound
