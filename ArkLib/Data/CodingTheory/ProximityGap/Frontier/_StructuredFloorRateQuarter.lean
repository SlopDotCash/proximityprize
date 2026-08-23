/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.StructuredUncertaintySharpFloor

/-!
# The structured single-line floor at rate `rho = 1/4` is `5n/8`, for ALL `mu` (#407 / #444)

`StructuredUncertaintySharpFloor.card_witnessVal_zero_ge` proves the per-spike structured floor
`s*(2^mu, k) >= n/2 + 2^e` for every spike exponent `e <= mu-1` (the witness
`(x^{n/2}+1)*(x^{2^e} - (zeta^{j0})^{2^e})`, `j0` even, `j0 < 2^{mu-e}`).  At the prize-relevant
rate `rho = 1/4` (`k = n/4 = 2^{mu-2}`) the optimal spike is the largest power of two `<= k-1`,
namely `2^{mu-3}` (`e = mu-3`), and the floor closes to

> `s*(2^mu, 2^{mu-2}) >= n/2 + 2^{mu-3} = 5 * 2^{mu-3} = 5n/8`,    for ALL `mu >= 3`.

`FloorAsymptoticRadius.lean` certifies this only at `n = 8, 16` (by `decide`).  This file lifts it
to the WHOLE 2-power tower as a single closed-form theorem, extending `card_witnessVal_zero_ge` at
the canonical even residue `j0 = 0`.

## What this is / is NOT (rules 3, 4, 6 + the ASYMPTOTIC-CLAIM GUARD)

* **A LOWER bound on the single-line root count `s*`, NOT a `delta*` / list claim.**  Exactly as
  `UncertaintyTwoPowerExtremal.SingleLineNotList` records, the single far line achieving `~n/2`
  agreement with ONE codeword does NOT lift to a large LIST; the prize `delta*` is the list radius,
  on which this witness contributes only `O(1)`.  So `s* >= 5n/8` is a super-Johnson floor on the
  WRONG object for the prize -- it is precisely the object the program already brackets away from
  CORE.  NO capacity / beyond-Johnson-`delta*` / sub-linear-`M` / closure claim is made; the
  cliff-at-`n/2` (which is the `delta*`/incidence object, not `s*`) is UNTOUCHED.

* **Thinness-essential (rule 3).**  The witness binomial `x^{n/2}+1` and the spike `x^{2^e} - c`
  both factor through 2-power-order elements; over a prime-order group Tao's principle forbids the
  construction.  A refutation of a would-be Johnson UPPER bound on `s*`, not a thinness-monotone
  CORE method.

* **EXTEND-proven (rule 4 / frontier-movement).**  Built directly on the in-tree
  `card_witnessVal_zero_ge`; the new content is the rate-`1/4` optimal-spike specialization, closed
  to `5n/8` for ALL `mu`, the general-`mu` form of the `n=8,16` `decide` facts.

All `sorry`-free; intended audit `[propext, Classical.choice, Quot.sound]`. Issues #407, #444.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.StructuredUncertainty

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- `2^{mu-1} + 2^{mu-3} = 5 * 2^{mu-3}` (a pure `Nat` identity for `mu >= 3`). -/
theorem half_add_quarter_spike_eq (μ : ℕ) (hμ : 3 ≤ μ) :
    2 ^ (μ - 1) + 2 ^ (μ - 3) = 5 * 2 ^ (μ - 3) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hμ
  -- mu = 3 + t, so mu-1 = t+2, mu-3 = t.
  have h1 : 3 + t - 1 = t + 2 := by omega
  have h3 : 3 + t - 3 = t := by omega
  rw [h1, h3, pow_add]
  ring

/-- `5 * 2^{mu-3} = 5 * 2^mu / 8` (so the floor IS `5n/8` with `n = 2^mu`), for `mu >= 3`. -/
theorem five_quarter_spike_eq_5n8 (μ : ℕ) (hμ : 3 ≤ μ) :
    5 * 2 ^ (μ - 3) = 5 * 2 ^ μ / 8 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hμ
  have h3 : 3 + t - 3 = t := by omega
  rw [h3]
  -- 2^{3+t} = 8 * 2^t, so 5 * 2^{3+t} / 8 = 5 * 2^t.
  have hpow : (2 : ℕ) ^ (3 + t) = 8 * 2 ^ t := by rw [pow_add]; norm_num
  rw [hpow]
  rw [show 5 * (8 * 2 ^ t) = (5 * 2 ^ t) * 8 from by ring]
  rw [Nat.mul_div_cancel _ (by norm_num : 0 < 8)]

/-- **The structured floor at rate `rho = 1/4` is `5n/8`, for ALL `mu >= 3`.**  Specializing
`card_witnessVal_zero_ge` at the optimal spike `e = mu-3` (the largest power of two `<= k-1` when
`k = n/4 = 2^{mu-2}`) and the canonical even residue `j0 = 0`, the witness
`(x^{n/2}+1)*(x^{2^{mu-3}} - 1)` vanishes on at least `5 * 2^{mu-3}` of the `n = 2^mu` roots:

> `s*(2^mu, 2^{mu-2}) >= 5 * 2^{mu-3} = n/2 + n/8 = 5n/8`.

The general-`mu` form of the `n = 8, 16` `decide` certificates in `FloorAsymptoticRadius`.  A
single-line LOWER bound (super-Johnson, since `sqrt(k n) = n/2 < 5n/8` at `rho = 1/4`); NOT the
list radius `delta*`. -/
theorem structuredFloor_rate_quarter_ge {μ : ℕ} (hμ : 3 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    5 * 2 ^ (μ - 3) ≤
      ((range (2 ^ μ)).filter (fun j => witnessVal μ (μ - 3) 0 ζ j = 0)).card := by
  have hbase :
      2 ^ (μ - 1) + 2 ^ (μ - 3) ≤
        ((range (2 ^ μ)).filter (fun j => witnessVal μ (μ - 3) 0 ζ j = 0)).card :=
    card_witnessVal_zero_ge (e := μ - 3) (j₀ := 0) (by omega) (by omega) (by simp)
      (by positivity) hζ
  rw [half_add_quarter_spike_eq μ hμ] at hbase
  exact hbase

/-- **`5n/8` closed form.**  Same floor, written explicitly as `5 * n / 8` with `n = 2^mu`. -/
theorem structuredFloor_rate_quarter_ge_5n8 {μ : ℕ} (hμ : 3 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    5 * 2 ^ μ / 8 ≤
      ((range (2 ^ μ)).filter (fun j => witnessVal μ (μ - 3) 0 ζ j = 0)).card := by
  rw [← five_quarter_spike_eq_5n8 μ hμ]
  exact structuredFloor_rate_quarter_ge hμ hζ

/-- **Super-Johnson, for ALL `mu >= 3`.**  At `rho = 1/4` the Johnson agreement is
`sqrt(k n) = sqrt((n/4) n) = n/2`; the structured floor `5n/8` strictly exceeds it.  Stated as the
clean `Nat` gap `n/2 < 5 * 2^{mu-3}` (`= 5n/8`), holding at every level of the 2-power tower (the
general-`mu` form of `FloorAsymptoticRadius.sstar_eq_5n8_beyond_johnson`, which is `decide`d only at
`n = 8, 16`). -/
theorem structuredFloor_rate_quarter_super_johnson {μ : ℕ} (hμ : 3 ≤ μ) :
    2 ^ μ / 2 < 5 * 2 ^ (μ - 3) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hμ
  have h3 : 3 + t - 3 = t := by omega
  rw [h3]
  have hpow : (2 : ℕ) ^ (3 + t) = 8 * 2 ^ t := by rw [pow_add]; norm_num
  have ht : 0 < (2 : ℕ) ^ t := by positivity
  rw [hpow]
  -- (8 * 2^t)/2 = 4 * 2^t < 5 * 2^t.
  rw [show 8 * 2 ^ t = (4 * 2 ^ t) * 2 from by ring, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  omega

end ProximityGap.StructuredUncertainty

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound`; no `sorryAx`). -/
#print axioms ProximityGap.StructuredUncertainty.half_add_quarter_spike_eq
#print axioms ProximityGap.StructuredUncertainty.five_quarter_spike_eq_5n8
#print axioms ProximityGap.StructuredUncertainty.structuredFloor_rate_quarter_ge
#print axioms ProximityGap.StructuredUncertainty.structuredFloor_rate_quarter_ge_5n8
#print axioms ProximityGap.StructuredUncertainty.structuredFloor_rate_quarter_super_johnson
