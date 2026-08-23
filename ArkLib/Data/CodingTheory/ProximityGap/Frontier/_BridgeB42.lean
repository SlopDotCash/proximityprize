/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# B42 — `v₂(m)` controls the FFT-recursion descent depth (#444, target E6)

The E6 graded recursion `#bad_{2n}(k, 2m') = #bad_n(k/2, m')` and `#bad_{2n}(k, odd) = 0`
(spec `deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, line 66) means: starting
from a level with parameter `m`, each FFT-recursion step **halves `m` and `k`** and recurses;
once `m` becomes **odd** the recursion stops (the only nonvanishing graded piece at an even
level requires an even `m`, and the antipodal `−1` kills the odd piece).

So the *descent depth* — the number of halving steps the FFT recursion takes before it bottoms
out at an odd `m` — is governed purely by the 2-adic valuation of `m`. This file proves that
clean `Nat` fact, modelling one recursion step by the halving map `m ↦ m / 2` (valid while
`m` is even) and the stopping predicate by `Odd m`.

The two deliverables:

* `descentDepth_eq_padicValNat` — the number of halving steps `m ↦ m/2` from `m` (`m ≠ 0`)
  down to its odd core equals `padicValNat 2 m`; i.e. the descent depth is exactly `v₂(m)`.
* `descent_step_halves` / `descent_stops_iff_odd` — the per-step structure: one step halves
  `m` exactly when `m` is even, and the recursion has stopped (no further halving) iff `m`
  is odd. This is the `Nat` shadow of E6's "halves `m` and `k`, stops at odd `m`".

These are char-free `Nat`/`padicValNat` identities; combined with the E6 graded-vanishing core
(B05/B06, `_Bridge05`) they pin the recursion's termination level. The open content of E6 is the
bijection on graded vectors, NOT this valuation bookkeeping.

Issue #444.
-/

namespace ArkLib.ProximityGap.BridgeB42

open Nat

/-- **One FFT-recursion step is a halving, available exactly when `m` is even.**
The E6 step `#bad_{2n}(k,2m') = #bad_n(k/2,m')` reads, on the parameter `m = 2m'`, as the map
`m ↦ m/2`; it strictly decreases `m` precisely when `m` is even and positive. -/
theorem descent_step_halves {m : ℕ} (hm : 0 < m) (heven : Even m) : m / 2 < m ∧ 2 * (m / 2) = m := by
  obtain ⟨c, rfl⟩ := heven
  have hc : 0 < c := by omega
  constructor
  · omega
  · omega

/-- **The recursion stops iff `m` is odd.** A further halving step is *unavailable* (the
graded piece vanishes, E6 `#bad_{2n}(k, odd) = 0`) exactly when `m` is odd: there is no `m'`
with `m = 2m'`. -/
theorem descent_stops_iff_odd {m : ℕ} : Odd m ↔ ¬ Even m := by
  rw [Nat.not_even_iff_odd]

/-- The odd core `m / 2^{v₂(m)}` is odd (for `m ≠ 0`): the recursion genuinely terminates at an
odd level. This is the "stops at odd `m`" half of the spec. -/
theorem ordCompl_two_odd {m : ℕ} (hm : m ≠ 0) : Odd (ordCompl[2] m) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact Nat.not_dvd_ordCompl Nat.prime_two hm

/-- **Descent depth.** `descentDepth m` counts the number of halving FFT-recursion steps
`m ↦ m/2` performed before reaching an odd `m` (the stopping level). It is defined by the
exact recursion that E6 prescribes: halve while even, stop at odd. -/
def descentDepth : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
    if Even (n + 1) then descentDepth ((n + 1) / 2) + 1 else 0
  decreasing_by
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by omega)
    exact this

@[simp] theorem descentDepth_zero : descentDepth 0 = 0 := by
  rw [descentDepth.eq_def]

theorem descentDepth_odd {m : ℕ} (hm : Odd m) : descentDepth m = 0 := by
  cases m with
  | zero => simp
  | succ n =>
    conv_lhs => rw [descentDepth.eq_def]
    simp only []
    rw [if_neg]
    rwa [Nat.not_even_iff_odd]

theorem descentDepth_even {m : ℕ} (hm : 0 < m) (he : Even m) :
    descentDepth m = descentDepth (m / 2) + 1 := by
  cases m with
  | zero => omega
  | succ n =>
    conv_lhs => rw [descentDepth.eq_def]
    simp only []
    rw [if_pos he]

/-- **Main bridge fact: the descent depth equals the 2-adic valuation of `m`.**
The number of FFT-recursion halving steps from `m` (`m ≠ 0`) down to its odd core is exactly
`v₂(m)`. This is the `Nat` content of E6's "`v₂(m)` controls the FFT-recursion descent depth:
each step halves `m` and `k`, stops at odd `m`." -/
theorem descentDepth_eq_padicValNat {m : ℕ} (hm : m ≠ 0) :
    descentDepth m = padicValNat 2 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd m with he | ho
    · -- even, positive: peel one factor of 2 on both sides
      have hpos : 0 < m := Nat.pos_of_ne_zero hm
      obtain ⟨c, hc⟩ := he
      have hc' : m = 2 * c := by omega
      have hcpos : c ≠ 0 := by omega
      have hlt : c < m := by omega
      have hdiv : m / 2 = c := by omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [descentDepth_even hpos ⟨c, hc⟩, hdiv, ih c hlt hcpos]
      -- padicValNat 2 m = padicValNat 2 (c*2) = padicValNat 2 c + 1
      have h2 : m = c * 2 := by omega
      rw [h2, padicValNat.mul hcpos (by norm_num), padicValNat.self (by norm_num)]
    · rw [descentDepth_odd ho]
      rw [Nat.odd_iff] at ho
      have : ¬ (2 ∣ m) := by omega
      symm
      rw [padicValNat.eq_zero_iff]
      exact Or.inr (Or.inr this)

end ArkLib.ProximityGap.BridgeB42

#print axioms ArkLib.ProximityGap.BridgeB42.descentDepth_eq_padicValNat
#print axioms ArkLib.ProximityGap.BridgeB42.descent_step_halves
#print axioms ArkLib.ProximityGap.BridgeB42.ordCompl_two_odd
