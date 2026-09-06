/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# C4 (Poisson ceiling) — the Bonferroni admissibility wall at prize scale (#407)

The in-tree **Poisson floor** (`PoissonCeilingFloor.lean`, axiom-clean) proves, for the
explicit evaluation code `evalCode g n d`,

  `epsMCA(evalCode g n d, δ) ≥ C(n, d+2)/(4 p)`   whenever `δ ≥ 1 − (d+2)/n`,

via a second-order Bonferroni inclusion–exclusion (`card_union_ge`).  Because a *large*
`epsMCA` makes a radius **bad**, this is structurally a **ceiling** (an UPPER bracket on
`δ*`, `poisson_mcaDeltaStar_le_floor_*`), NOT a floor on `δ*`.  Two further facts pin its
reach at the prize:

1. *(direction)* For a code of fixed degree `d`, the lemma speaks only at radii
   `δ ≥ 1 − (d+2)/n`; the tightest ceiling it yields for that code is
   `δ* ≤ 1 − (d+2)/n`.  For the prize code (`d = k−1`, `d+2 = k+1`) that is
   `1 − (k+1)/n = (1−ρ) − 1/n` — the **trivial capacity ceiling**, *above* the conjectured
   #407 ceiling `1 − ρ − H(ρ)/(β log n)`.  So C4 is *looser* than the ceiling already
   conjectured, and cannot move the lower bracket of `δ*` at all.

2. *(vacuity)* The Bonferroni step `card_union_ge` carries the hypothesis
   `hq : C(n, d+2) + 1 ≤ p` (the second-moment correction `C²·S` must not swamp the main
   term).  **This file proves that hypothesis is unsatisfiable at prize scale.**

The "promised polynomial, not exponential" Bonferroni bite point the lower-bound census
asked for is therefore *not polynomial*: at a constant rate the minimal-overdetermined-set
count `C(n, d+2)` is exponential in `n`, dwarfing any prize field `p = Θ(n·2^128)`.

Concretely, for the (slightly below-) rate-`1/2` prize code with `n = 2m`,
`d + 2 = m` (so `C(n, d+2) = centralBinom m`):

  `poisson_bonferroni_admissibility_fails` :
    `p * (2*m) < 4^m  →  ¬ (Nat.centralBinom m ... + 1 ≤ p)`

and the prize-field instantiation `prize_field_below_central_pow` shows
`p ≤ (2m)·2^128 < 4^m / (2m)` once `m` is past the explicit threshold
`(2m)² · 2^128 < 4^m`, i.e. C4 is vacuous for every prize field at large `n`.

No new mathematics is *claimed* on the lower-bound (floor) side — this is a precise,
machine-checked **method no-go** for the C4 route: it is a ceiling, and even as a ceiling
it is vacuous on the prize code.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall

open Nat

/-- **Exponential lower bound on the prize overdetermined-set count.**  For the rate-`≈1/2`
prize code with `n = 2m`, the minimal overdetermined `(d+2)`-set with `d+2 = m` has count
`C(2m, m) = centralBinom m ≥ 4^m / (2m)`, restated multiplicatively to avoid division:

  `4^m < 2m · centralBinom m`   (`4 ≤ m`),

so `2m · centralBinom m` is exponential while a prize field `p` is only `Θ(n·2^128)`. -/
theorem four_pow_lt_two_mul_centralBinom (m : ℕ) (hm : 4 ≤ m) :
    4 ^ m < 2 * m * Nat.centralBinom m := by
  have h := Nat.four_pow_lt_mul_centralBinom m hm
  calc 4 ^ m < m * Nat.centralBinom m := h
    _ ≤ 2 * m * Nat.centralBinom m := by
        refine Nat.mul_le_mul_right _ ?_
        omega

/-- The central count is exactly the count of the minimal overdetermined `(d+2)`-set with
`n = 2m`, `d + 2 = m` (so `C(n, d+2) = C(2m, m) = centralBinom m`). -/
theorem centralBinom_eq_choose_two_mul (m : ℕ) :
    Nat.centralBinom m = (2 * m).choose m :=
  Nat.centralBinom_eq_two_mul_choose m

/-- **The C4 Bonferroni admissibility wall (multiplicative form).**  For the prize code with
`n = 2m`, `d + 2 = m` (`4 ≤ m`), no field `p` with `p · (2m) < 4^m` can satisfy the
Bonferroni admissibility hypothesis `C(n, d+2) + 1 ≤ p` required by `card_union_ge`.

I.e. whenever the field is small enough that `p·n < 4^m` (which holds at every prize field,
see below), C4 is *vacuous*: its only hypothesis fails. -/
theorem poisson_bonferroni_admissibility_fails (m p : ℕ) (hm : 4 ≤ m)
    (hp : p * (2 * m) < 4 ^ m) :
    ¬ ((2 * m).choose m + 1 ≤ p) := by
  intro hadm
  -- From admissibility: p ≥ C(2m,m)+1 > C(2m,m) = centralBinom m.
  have hcb : (2 * m).choose m = Nat.centralBinom m := (centralBinom_eq_choose_two_mul m).symm
  have hple : Nat.centralBinom m + 1 ≤ p := by rw [hcb] at hadm; exact hadm
  -- Then p·(2m) ≥ (centralBinom m + 1)·(2m) ≥ centralBinom m·(2m) = 2m·centralBinom m > 4^m.
  have hexp := four_pow_lt_two_mul_centralBinom m hm
  have hchain : 2 * m * Nat.centralBinom m ≤ p * (2 * m) := by
    calc 2 * m * Nat.centralBinom m
        = Nat.centralBinom m * (2 * m) := by ring
      _ ≤ p * (2 * m) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Prize-field instantiation.**  Every prize field `p ≤ (2m)·2^128` is below the central
binomial wall once `(2m)² · 2^128 < 4^m` (an explicit large-`m` threshold).  Hence the C4
Bonferroni admissibility hypothesis fails for **every** prize field at large `n`. -/
theorem prize_field_below_central_pow (m p : ℕ) (hm : 4 ≤ m)
    (hpf : p ≤ (2 * m) * 2 ^ 128)
    (hthr : (2 * m) * (2 * m) * 2 ^ 128 < 4 ^ m) :
    ¬ ((2 * m).choose m + 1 ≤ p) := by
  refine poisson_bonferroni_admissibility_fails m p hm ?_
  calc p * (2 * m) ≤ ((2 * m) * 2 ^ 128) * (2 * m) := Nat.mul_le_mul_right _ hpf
    _ = (2 * m) * (2 * m) * 2 ^ 128 := by ring
    _ < 4 ^ m := hthr

/-- Polynomial-vs-exponential helper: `m² < 2^(2m−130)` for `m ≥ 132`, from the Mathlib
square-vs-two-power bound applied at the shifted argument `m − 66`. -/
theorem sq_lt_two_pow_shift (m : ℕ) (hm : 132 ≤ m) :
    m * m < 2 ^ (2 * m - 130) := by
  set j := m - 66 with hj
  have hjm : m = j + 66 := by omega
  have hkey : 2 * j ^ 2 + 1 ≤ 2 ^ (2 * j) := Nat.two_mul_sq_add_one_le_two_pow_two_mul j
  have hjsq : j ^ 2 < 2 ^ (2 * j) := by nlinarith [hkey]
  -- m ≤ 2j (since m = j+66 and j = m-66 ≥ 66), so m² ≤ 4 j².
  have hjge : 66 ≤ j := by omega
  have hmle : m ≤ 2 * j := by omega
  have hm4 : m * m ≤ 4 * (j ^ 2) := by nlinarith [hmle]
  have hstep : 4 * (j ^ 2) < 4 * 2 ^ (2 * j) := by gcongr
  calc m * m ≤ 4 * (j ^ 2) := hm4
    _ < 4 * 2 ^ (2 * j) := hstep
    _ = 2 ^ 2 * 2 ^ (2 * j) := by norm_num
    _ = 2 ^ (2 + 2 * j) := by rw [← pow_add]
    _ = 2 ^ (2 * m - 130) := by rw [show 2 + 2 * j = 2 * m - 130 from by omega]

/-- **The threshold is crossed for all `m ≥ 280`** (an explicit prize-scale point).  At
`n = 2m ≥ 560` the central binomial overruns any field of size `≤ n·2^128`:
`(2m)·(2m)·2^128 < 4^m`.  This pins the C4 "bite point" as *exponential*, not polynomial:
no polynomial field beats it. -/
theorem central_pow_threshold_holds (m : ℕ) (hm : 280 ≤ m) :
    (2 * m) * (2 * m) * 2 ^ 128 < 4 ^ m := by
  have hsq : m * m < 2 ^ (2 * m - 130) := sq_lt_two_pow_shift m (by omega)
  have h4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, Nat.mul_comm]
  -- (2m)(2m)2^128 = 4·m²·2^128 < 4·2^(2m-130)·2^128 = 2^(2m) = 4^m.
  calc (2 * m) * (2 * m) * 2 ^ 128
      = (m * m) * (4 * 2 ^ 128) := by ring
    _ < (2 ^ (2 * m - 130)) * (4 * 2 ^ 128) := by gcongr <;> norm_num
    _ = 2 ^ (2 * m - 130) * 2 ^ 130 := by norm_num
    _ = 2 ^ (2 * m - 130 + 130) := by rw [← pow_add]
    _ = 2 ^ (2 * m) := by rw [show 2 * m - 130 + 130 = 2 * m from by omega]
    _ = 4 ^ m := h4.symm

/-- **C4 vacuity at every prize field, packaged.**  For the rate-`≈1/2` prize code with
`n = 2m`, `m ≥ 280`, and any prize field `p ≤ n·2^128 = (2m)·2^128`, the Bonferroni
admissibility hypothesis of `card_union_ge` fails:

  `¬ (C(n, d+2) + 1 ≤ p)`   with `C(n, d+2) = C(2m, m)`.

Hence the C4 Poisson ceiling is *vacuous* on the prize code: its sole hypothesis is
unsatisfiable, so it yields no `δ*` bound at the prize.  (And even where it is admissible,
its ceiling `δ* ≤ 1−(d+2)/n` is the trivial capacity ceiling, above the conjectured #407
ceiling — see the module docstring.) -/
theorem poisson_C4_vacuous_at_prize (m p : ℕ) (hm : 280 ≤ m)
    (hpf : p ≤ (2 * m) * 2 ^ 128) :
    ¬ ((2 * m).choose m + 1 ≤ p) :=
  prize_field_below_central_pow m p (by omega) hpf (central_pow_threshold_holds m hm)

end ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall

open ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall in
#print axioms four_pow_lt_two_mul_centralBinom
open ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall in
#print axioms poisson_bonferroni_admissibility_fails
open ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall in
#print axioms prize_field_below_central_pow
open ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall in
#print axioms sq_lt_two_pow_shift
open ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall in
#print axioms central_pow_threshold_holds
open ArkLib.ProximityGap.Frontier.C4PoissonAdmissibilityWall in
#print axioms poisson_C4_vacuous_at_prize
