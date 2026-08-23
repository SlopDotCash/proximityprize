/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G133CensusTower

/-!
# G134: the production crossover pin — and the anchor-zone honesty audit

Two small but load-bearing records for the census-tower coordinates.

**The crossover pin.**  The DC-shape budget `q·Wick_t + n^{2t}` changes regime at the rung
where `n^t` crosses `q·(2t−1)!!`.  At production (`n = 2^30`, `2^158 ≤ q ≤ 2^160`) this
happens between rungs `5` and `6`, kernel-checked:

- `crossover_wick_side`: `n^5 ≤ q·9!!` for every `q ≥ 2^158` (rung 5 is Wick-dominated);
- `crossover_dc_side`: `q·11!! < n^6` for every `q ≤ 2^160` (rung 6 is DC-dominated).

The empirical bump analysis (regime scan + counterexample autopsy) identifies this exact
window as the razor-thin zone; the pin makes "the bump is at rungs 5–6" a theorem about the
production shape rather than a heuristic.

**The anchor-zone audit.**  The in-tree rung-2 anchor `dcEnergyBound_two_rootsOfUnity`
requires the Sidon threshold `12^φ(2^m) < p²`, which at production size demands
`p > 12^(2^29)` — astronomically false at `p ≈ 2^158`.  Kernel-checked here for the record
(`sidon_threshold_fails_at_production`, stated at the exponent level).  Consequently ALL
production anchors `t = 2..10` of the G133 tower are OPEN; no in-tree anchor covers any of
them at production shape.  Prior notes citing the rung-2 anchor as production-applicable
are corrected by this file.

**Honest scope.**  Arithmetic pins and an audit; no analytic progress.  CORE remains OPEN.
Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G134ProductionCrossoverPin

/-- Rung `5` is Wick-dominated at production: `n^5 ≤ q · 9!!` for every `q ≥ 2^158`. -/
theorem crossover_wick_side {q : ℕ} (hq : 2 ^ 158 ≤ q) :
    (2 ^ 30 : ℕ) ^ 5 ≤ q * Nat.doubleFactorial 9 := by
  calc
    (2 ^ 30 : ℕ) ^ 5 = 2 ^ 150 := by norm_num
    _ ≤ 2 ^ 158 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    _ ≤ q := hq
    _ ≤ q * Nat.doubleFactorial 9 := Nat.le_mul_of_pos_right _ (by norm_num [Nat.doubleFactorial])

/-- Rung `6` is DC-dominated at production: `q · 11!! < n^6` for every `q ≤ 2^160`. -/
theorem crossover_dc_side {q : ℕ} (hq : q ≤ 2 ^ 160) :
    q * Nat.doubleFactorial 11 < (2 ^ 30 : ℕ) ^ 6 := by
  calc
    q * Nat.doubleFactorial 11 ≤ 2 ^ 160 * Nat.doubleFactorial 11 :=
      Nat.mul_le_mul_right _ hq
    _ < (2 ^ 30 : ℕ) ^ 6 := by norm_num [Nat.doubleFactorial]

/-- **The Sidon threshold of the in-tree rung-2 anchor fails at production size**: the
anchor `dcEnergyBound_two_rootsOfUnity` needs `12^φ(2^30) = 12^(2^29) < p²`, but already
`2^(2^29)` dwarfs `p² ≤ 2^320` — stated at the exponent level (`320 < 2^29`). -/
theorem sidon_threshold_fails_at_production :
    (2 ^ 320 : ℕ) < 2 ^ (2 ^ 29) ∧ Nat.totient (2 ^ 30) = 2 ^ 29 := by
  constructor
  · exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  · rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 30)]
    norm_num

end ArkLib.ProximityGap.Frontier.G134ProductionCrossoverPin

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G134ProductionCrossoverPin.crossover_wick_side
#print axioms ArkLib.ProximityGap.Frontier.G134ProductionCrossoverPin.crossover_dc_side
#print axioms
  ArkLib.ProximityGap.Frontier.G134ProductionCrossoverPin.sidon_threshold_fails_at_production
