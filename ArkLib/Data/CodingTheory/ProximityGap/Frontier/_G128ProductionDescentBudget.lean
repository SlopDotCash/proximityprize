/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G126DisjointCensusGate

/-!
# G128: the production descent budget — unconditional through depth 102

The G126 gate charges `DCEnergyBound` with the descent overhead
`Σ_{s<r} (r)_{r−s}²·#G^{r−s}·E_s`.  This file quantifies that charge at the production
shape `(#G, r) = (2^30, 110)`, `q ≤ 2^160` (both certified prize primes qualify):

**With only the trivial in-tree energy bounds** (`E_0 = 1`, `E_s ≤ n^{2s−1}`), the overhead
through depth `102` fits inside the DC mass `n^{220}` outright:

```text
q · Σ_{s=0}^{102} (110)_{110−s}²·n^{110−s}·E_s ≤ n^{220}.
```

Engine: the term series `B k = q·(110)_k²·n^{219−k}` HALVES in `k` (`2·(110−k)² ≤ 2^30`), so
the whole tail `k ≥ 8` is at most `2·B 8`, and `2·B 8 + (s = 0 term) ≤ n^{220}` is one
kernel gate with `2^3` headroom.

**Consequence.**  In the G126 gate at production scale, only the SEVEN deepest sub-full
depths (`s = 103..109`) need true (conditional) lower-rung energy input; the remaining `103`
depths of descent are free.  The census obligation is therefore: the fully-disjoint census
plus seven near-full-depth energies against the Wick-plus-DC budget.

**Honest scope.**  Nothing here bounds the disjoint census or the seven deep energies (the
wall).  CORE remains OPEN.  Issue #466 (post-#505/#509 coordinates).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget

open Finset

/-- The trivial-energy descent term series at production shape. -/
def descB (q k : ℕ) : ℕ :=
  q * (Nat.descFactorial 110 k) ^ 2 * (2 ^ 30) ^ (219 - k)

/-- **Halving.**  Each step deeper into the series at least halves it:
`2·(110−k)² ≤ 2^30`. -/
theorem descB_halving (q : ℕ) {k : ℕ} (hk : k ≤ 109) :
    2 * descB q (k + 1) ≤ descB q k := by
  have hd : Nat.descFactorial 110 (k + 1) = (110 - k) * Nat.descFactorial 110 k :=
    Nat.descFactorial_succ 110 k
  have hpow : (2 ^ 30 : ℕ) ^ (219 - k) = 2 ^ 30 * (2 ^ 30) ^ (219 - (k + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsq : 2 * (110 - k) ^ 2 ≤ 2 ^ 30 := by
    have : (110 - k) ^ 2 ≤ 110 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  calc
    2 * descB q (k + 1)
        = (2 * (110 - k) ^ 2) *
            (q * (Nat.descFactorial 110 k) ^ 2 * (2 ^ 30) ^ (219 - (k + 1))) := by
      unfold descB
      rw [hd]
      ring
    _ ≤ 2 ^ 30 *
            (q * (Nat.descFactorial 110 k) ^ 2 * (2 ^ 30) ^ (219 - (k + 1))) :=
      Nat.mul_le_mul_right _ hsq
    _ = descB q k := by
      unfold descB
      rw [hpow]
      ring

/-- **Geometric tail.**  The whole tail of the series is at most twice its head. -/
theorem descB_tail (q : ℕ) :
    ∀ d, d ≤ 102 →
      ∑ j ∈ Finset.range (d + 1), descB q (110 - j) ≤ 2 * descB q (110 - d) := by
  intro d
  induction d with
  | zero =>
      intro _
      simp [Nat.two_mul]
  | succ d ih =>
      intro hd
      have hd' : d ≤ 102 := by omega
      have hstep : 110 - d = (110 - (d + 1)) + 1 := by omega
      calc
        ∑ j ∈ Finset.range (d + 2), descB q (110 - j)
            = (∑ j ∈ Finset.range (d + 1), descB q (110 - j))
                + descB q (110 - (d + 1)) := by
          rw [Finset.sum_range_succ]
        _ ≤ 2 * descB q (110 - d) + descB q (110 - (d + 1)) :=
          Nat.add_le_add_right (ih hd') _
        _ = 2 * descB q ((110 - (d + 1)) + 1) + descB q (110 - (d + 1)) := by
          rw [← hstep]
        _ ≤ descB q (110 - (d + 1)) + descB q (110 - (d + 1)) :=
          Nat.add_le_add_right (descB_halving q (by omega)) _
        _ = 2 * descB q (110 - (d + 1)) := (Nat.two_mul _).symm

/-- **The kernel gate**: head of the tail plus the depth-`0` term fit the DC mass, with
`q ≤ 2^160` (both certified prize primes qualify). -/
theorem production_gate :
    2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110
      + 2 * (2 ^ 160 * (Nat.descFactorial 110 8) ^ 2 * (2 ^ 30) ^ 211)
      ≤ (2 ^ 30 : ℕ) ^ 220 := by
  norm_num [Nat.factorial, Nat.descFactorial]

/-- **Production descent budget, unconditional through depth `102`.**  With only the trivial
energy bounds, the descent overhead over depths `0..102` fits inside the DC mass. -/
theorem production_shallow_descent_within_DC (q : ℕ) (hq : q ≤ 2 ^ 160)
    (E : ℕ → ℕ) (hE0 : E 0 ≤ 1)
    (hEs : ∀ s, 1 ≤ s → E s ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1)) :
    q * ∑ s ∈ Finset.range 103,
        (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s)
      ≤ (2 ^ 30 : ℕ) ^ 220 := by
  have hterm : ∀ i, i < 102 →
      q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
        ≤ descB q (109 - i) := by
    intro i hi
    have hidx : 110 - (i + 1) = 109 - i := by omega
    have hE := hEs (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
    have hpow : (2 ^ 30 : ℕ) ^ (109 - i) * (2 ^ 30) ^ (2 * (i + 1) - 1)
        = (2 ^ 30) ^ (219 - (109 - i)) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
          ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
          ≤ q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (110 - (i + 1)) * (2 ^ 30) ^ (2 * (i + 1) - 1))) := by
        gcongr
      _ = q * (Nat.descFactorial 110 (109 - i)) ^ 2 * (2 ^ 30) ^ (219 - (109 - i)) := by
        rw [hidx, hpow]
        ring
      _ = descB q (109 - i) := rfl
  -- peel the s = 0 term, bound the rest by the descB series
  rw [Finset.mul_sum, Finset.sum_range_succ']
  have h0 : q * ((Nat.descFactorial 110 (110 - 0)) ^ 2 *
      ((2 ^ 30) ^ (110 - 0) * E 0))
      ≤ 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110 := by
    have : Nat.descFactorial 110 110 = Nat.factorial 110 :=
      Nat.descFactorial_self 110
    calc
      q * ((Nat.descFactorial 110 (110 - 0)) ^ 2 *
          ((2 ^ 30) ^ (110 - 0) * E 0))
          ≤ 2 ^ 160 * ((Nat.factorial 110) ^ 2 * ((2 ^ 30) ^ 110 * 1)) := by
        simp only [Nat.sub_zero, this]
        gcongr
      _ = 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110 := by ring
  have htail : ∑ i ∈ Finset.range 102,
      q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
      ≤ 2 * descB q 8 := by
    calc
      ∑ i ∈ Finset.range 102,
          q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
          ≤ ∑ i ∈ Finset.range 102, descB q (109 - i) :=
        Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
      _ ≤ ∑ j ∈ Finset.range 103, descB q (110 - j) := by
        rw [Finset.sum_range_succ' (fun j => descB q (110 - j)) 102]
        exact Nat.le_add_right _ _
      _ ≤ 2 * descB q (110 - 102) := descB_tail q 102 (le_refl 102)
      _ = 2 * descB q 8 := by norm_num
  have hB8 : 2 * descB q 8 ≤
      2 * (2 ^ 160 * (Nat.descFactorial 110 8) ^ 2 * (2 ^ 30) ^ 211) := by
    unfold descB
    have : (219 - 8 : ℕ) = 211 := by norm_num
    rw [this]
    gcongr
  calc
    (∑ i ∈ Finset.range 102,
        q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
          ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1))))
      + q * ((Nat.descFactorial 110 (110 - 0)) ^ 2 *
          ((2 ^ 30) ^ (110 - 0) * E 0))
        ≤ 2 * (2 ^ 160 * (Nat.descFactorial 110 8) ^ 2 * (2 ^ 30) ^ 211)
          + 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110 :=
      Nat.add_le_add (htail.trans hB8) h0
    _ = 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110
          + 2 * (2 ^ 160 * (Nat.descFactorial 110 8) ^ 2 * (2 ^ 30) ^ 211) :=
      Nat.add_comm _ _
    _ ≤ (2 ^ 30 : ℕ) ^ 220 := production_gate

end ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget.descB_halving
#print axioms ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget.descB_tail
#print axioms ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget.production_gate
#print axioms
  ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget.production_shallow_descent_within_DC
