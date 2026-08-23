/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Newton bridge: vanishing elementary symmetric window ⟹ vanishing power-sum window (#389)

The general-tower exact sub-Johnson list law needs: a `GapBand` solution (whose vanishing
polynomial has its top `m−1` non-leading coefficients zero, i.e. the first `m−1`
elementary symmetric functions of its roots vanish) has its **first `m−1` power sums
vanish** — feeding the in-tree 2-adic tower descent (`tower_closed_of_dyadic_sums_zero`)
the dyadic power sums it needs for order-`2^a` closure, hence the whole dyadic line.

> **`psum_window_zero_of_esymm_window_zero`** — for a finite family `f : σ → L` over a
> commutative ring, if `esymm` vanishes on `1..j−1`, then `∑ i, (f i)^k = 0` for
> `1 ≤ k < j` (`k ≤ card σ`).

Proof: specialize Newton's identity `psum_eq_mul_esymm_sub_sum` via `aeval f`, then strong
induction — every term of the recursion carries an `esymm a` with `1 ≤ a ≤ k < j`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open MvPolynomial Finset

namespace ArkLib.ProximityGap.KKH26

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {L : Type*} [CommRing L]

/-- `aeval f (psum σ ℤ k) = ∑ i, (f i)^k`. -/
private lemma aeval_psum (f : σ → L) (k : ℕ) :
    aeval f (psum σ ℤ k) = ∑ i, (f i) ^ k := by
  rw [psum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, aeval_X]

/-- `aeval f (esymm σ ℤ a) = (Finset.univ.val.map f).esymm a`. -/
private lemma aeval_esymm' (f : σ → L) (a : ℕ) :
    aeval f (esymm σ ℤ a) = (Finset.univ.val.map f).esymm a := by
  rw [aeval_esymm_eq_multiset_esymm]

/-- **THE NEWTON BRIDGE.**  If the elementary symmetric functions of `f` vanish on the
window `1 ≤ a < j`, then the power sums vanish on `1 ≤ k < j` (within `k ≤ card σ`). -/
theorem psum_window_zero_of_esymm_window_zero {L : Type*} [CommRing L] [CharZero L]
    (f : σ → L) {j : ℕ}
    (he : ∀ a, 1 ≤ a → a < j → aeval f (esymm σ ℤ a) = 0) :
    ∀ k, 1 ≤ k → k < j → ∑ i, (f i) ^ k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkj
    -- Newton's identity, aeval'd at f.
    have hnewton := congrArg (aeval f) (psum_eq_mul_esymm_sub_sum σ ℤ k hk1)
    rw [map_sub, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
      aeval_psum f k, aeval_esymm' f k] at hnewton
    -- the esymm k term vanishes (k in window)
    have hek : aeval f (esymm σ ℤ k) = 0 := he k hk1 hkj
    rw [aeval_esymm' f k] at hek
    -- the sum term: every entry has esymm a.1 with 1 ≤ a.1 < k < j → 0
    have hsum0 : aeval f (∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1) ^ a.fst * esymm σ ℤ a.1 * psum σ ℤ a.2) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun a ha => ?_
      obtain ⟨hmem, hioo⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha0, hak⟩ := hioo
      rw [map_mul, map_mul, map_pow, map_neg, map_one]
      have : aeval f (esymm σ ℤ a.1) = 0 := by
        rw [aeval_esymm' f a.1]
        have := he a.1 ha0 (lt_trans hak hkj)
        rwa [aeval_esymm' f a.1] at this
      rw [this, mul_zero, zero_mul]
    rw [hek, mul_zero] at hnewton
    rw [hsum0, sub_zero] at hnewton
    -- hnewton : ∑ (f i)^k = 0 (LHS already rewritten via aeval_psum above)
    exact hnewton

end ArkLib.ProximityGap.KKH26

#print axioms ArkLib.ProximityGap.KKH26.psum_window_zero_of_esymm_window_zero
