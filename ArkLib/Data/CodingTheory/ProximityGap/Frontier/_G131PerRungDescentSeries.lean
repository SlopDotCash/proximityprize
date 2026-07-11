/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G130UniformRungBudgets

/-!
# G131: the per-rung descent series — halving and geometric tail at every rung

Generalizes the G128 series machinery from the fixed rung `110` to an arbitrary rung
`t ≤ 110`: the trivial-energy descent term series

```text
descBT t q k = q · (t)_k² · n^(2t−1−k)
```

halves per step (`2·(t−k)² ≤ 2^30` uniformly for `t ≤ 110`), so every tail is at most twice
its head.  Together with the four uniform budget lemmas of G130 this supplies, at every rung
`11 ≤ t ≤ 110`, the shallow-descent bound the per-rung tower steps consume.

**Honest scope.**  Series arithmetic only; the assembly into per-rung tower steps and the
strong induction over rungs is the sequel.  CORE remains OPEN.  Issue #466 (G129/G130/G131).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G131PerRungDescentSeries

open Finset
open ArkLib.ProximityGap.Frontier.G130UniformRungBudgets

/-- The trivial-energy descent term series at rung `t`. -/
def descBT (t q k : ℕ) : ℕ :=
  q * (Nat.descFactorial t k) ^ 2 * (2 ^ 30) ^ (2 * t - 1 - k)

/-- **Per-rung halving.**  For `t ≤ 110` and `k + 1 ≤ t`, one step deeper at least halves
the series. -/
theorem descBT_halving {t : ℕ} (ht : t ≤ 110) (q : ℕ) {k : ℕ} (hk : k + 1 ≤ t) :
    2 * descBT t q (k + 1) ≤ descBT t q k := by
  have hd : Nat.descFactorial t (k + 1) = (t - k) * Nat.descFactorial t k :=
    Nat.descFactorial_succ t k
  have hpow : (2 ^ 30 : ℕ) ^ (2 * t - 1 - k) = 2 ^ 30 * (2 ^ 30) ^ (2 * t - 1 - (k + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsq : 2 * (t - k) ^ 2 ≤ 2 ^ 30 := by
    have h1 : t - k ≤ 110 := by omega
    have : (t - k) ^ 2 ≤ 110 ^ 2 := Nat.pow_le_pow_left h1 2
    omega
  calc
    2 * descBT t q (k + 1)
        = (2 * (t - k) ^ 2) *
            (q * (Nat.descFactorial t k) ^ 2 * (2 ^ 30) ^ (2 * t - 1 - (k + 1))) := by
      unfold descBT
      rw [hd]
      ring
    _ ≤ 2 ^ 30 *
            (q * (Nat.descFactorial t k) ^ 2 * (2 ^ 30) ^ (2 * t - 1 - (k + 1))) :=
      Nat.mul_le_mul_right _ hsq
    _ = descBT t q k := by
      unfold descBT
      rw [hpow]
      ring

/-- **Per-rung geometric tail.**  Summing the series downward from `k = t` (the deepest
term) through `k = t − d`, the total is at most twice the head `descBT t q (t − d)`,
whenever the window stays inside the rung (`d + 1 ≤ t`). -/
theorem descBT_tail {t : ℕ} (ht : t ≤ 110) (q : ℕ) :
    ∀ d, d + 1 ≤ t →
      ∑ j ∈ Finset.range (d + 1), descBT t q (t - j) ≤ 2 * descBT t q (t - d) := by
  intro d
  induction d with
  | zero =>
      intro _
      simp [Nat.two_mul]
  | succ d ih =>
      intro hd
      have hd' : d + 1 ≤ t := by omega
      have hstep : t - d = (t - (d + 1)) + 1 := by omega
      calc
        ∑ j ∈ Finset.range (d + 2), descBT t q (t - j)
            = (∑ j ∈ Finset.range (d + 1), descBT t q (t - j))
                + descBT t q (t - (d + 1)) := by
          rw [Finset.sum_range_succ]
        _ ≤ 2 * descBT t q (t - d) + descBT t q (t - (d + 1)) :=
          Nat.add_le_add_right (ih hd') _
        _ = 2 * descBT t q ((t - (d + 1)) + 1) + descBT t q (t - (d + 1)) := by
          rw [← hstep]
        _ ≤ descBT t q (t - (d + 1)) + descBT t q (t - (d + 1)) := by
          have hh := descBT_halving ht q (k := t - (d + 1)) (by omega)
          omega
        _ = 2 * descBT t q (t - (d + 1)) := (Nat.two_mul _).symm

end ArkLib.ProximityGap.Frontier.G131PerRungDescentSeries

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G131PerRungDescentSeries.descBT_halving
#print axioms ArkLib.ProximityGap.Frontier.G131PerRungDescentSeries.descBT_tail