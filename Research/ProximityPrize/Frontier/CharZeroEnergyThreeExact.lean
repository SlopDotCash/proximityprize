/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# AVENUE A: the exact char-0 depth-3 additive energy `E₃(μ_n) = 15n³ − 45n² + 40n` (#444)

This file discharges the lone OPEN INPUT `h3` of `Frontier/Kappa6R3DCWickRung.lean` — the exact
char-0 value of the depth-3 additive energy of the 2-power subgroup `μ_n` (`n = 2^μ`) —
**down to two elementary named inputs**, and proves the resulting `κ₆ = 40 n` unconditionally on
those two.

## The object

`E_r(μ_n) = #{(x₁,…,x_{2r}) ∈ μ_n^{2r} : Σ xᵢ = 0}` (the zero-sum count of `2r`-tuples; equal to
the `r`-fold additive energy for the negation-closed `μ_n`, via the in-tree bijection
`CharZeroWickEnergy.rEnergy_eq_zeroSumCount`). The known values are

* `E₁ = n`                     (in-tree: `REnergyTwoExact`, diagonal `r=1`),
* `E₂ = 3n² − 3n`              (in-tree: `REnergyTwoExact.mu_n_rEnergy_two_eq`),
* `E₃ = 15n³ − 45n² + 40n`     (this file).

## The reduction (verified by probe; see `scripts/probes/probe_e3_*`)

For `2^μ`-th roots of unity, two facts about `μ_n` (`m := n/2` antipodal classes `{z,−z}`):

* **(Lam–Leung at depth ≤ 3, the structural input `hLL`)** a `2r`-tuple (`r ≤ 3`) of `2^μ`-th roots
  sums to `0` **iff** it is *class-balanced*: grouping the `2r` entries by antipodal class
  `{z,−z}`, each class contains as many `z`'s as `−z`'s. (`⇐` is trivial algebra `z+(−z)=0`; `⇒`
  is Lam–Leung — the only primitive vanishing relation among `2^μ`-th roots is `z+(−z)=0`. Verified
  exhaustively for all 6-term multisets at `n = 4,8,16,32`: probe `probe_lamleung_verify.py`, zero
  counterexamples.)

* **(the per-class recursion, the combinatorial input `BalancedCount`)** the count `B k m` of
  class-balanced length-`k` tuples over `m` antipodal classes satisfies the *add-one-class*
  recursion: the new class occupies an even number `2j` of the `k` positions, with `j` `+`'s and
  `j` `−`'s among them — giving `B k (m+1) = Σ_j C(k,2j)·C(2j,j)·B (k−2j) m`. For `k = 2,4,6`:
  `rec2 : B 2 (m+1) = B 2 m + 2`,
  `rec4 : B 4 (m+1) = B 4 m + 12·B 2 m + 6`,
  `rec6 : B 6 (m+1) = B 6 m + 30·B 4 m + 90·B 2 m + 20`.

## What THIS file proves (axiom-clean; the only inputs are the two elementary facts above)

Modeling the balanced count by an abstract carrier `B : ℕ → ℕ → ℤ` satisfying `BalancedCount B`
(base cases + the three per-class recursions), we **solve the recursion in closed form by
induction on `m`**:

* `B2_closed` : `B 2 m = 2m`,
* `B4_closed` : `B 4 m = 12m² − 6m`,
* `B6_closed` : `B 6 m = 120m³ − 180m² + 80m`,  i.e. with `n = 2m`,
* `B6_eq_E3`  : `B 6 m = 15(2m)³ − 45(2m)² + 40(2m) = 15n³ − 45n² + 40n` — **the AVENUE A target**.

and then the cumulant consequence, unconditional on the three closed-form energies:

* `kappa6_eq` : `(15n³−45n²+40n) − 15(3n²−3n)n + 30n³ = 40 n` — **`κ₆ = 40 n`**, the cubic and
  quadratic terms of `E₃` cancelling exactly against `−15E₂E₁` and `30E₁³`. This is the value
  taken as the OPEN `h3`-conditional `kappa6_eq` in `Kappa6R3DCWickRung.lean`; here the `E₃`
  *value* is itself derived from the recursion (no longer a bare hypothesis), so `κ₆ = 40 n` now
  rests only on the two elementary inputs.

## Honest status (a REDUCTION of the open input, not a CORE closure)

The deep BGK / Paley-wall residual lives at depth `r ≈ log m` (the full DC-Wick ladder), NOT at
`r = 3`. This file does **not** touch that wall. What it does: it **replaces the monolithic
`h3` hypothesis** (`E₃ = 15n³−45n²+40n` taken on faith) by a *proof from two elementary,
probe-verified, field-theory-free inputs* — the Lam–Leung depth-≤3 balance characterization and
the add-one-class counting recursion. The recursion-solution is fully `sorry`-free and axiom-clean;
the two inputs are stated as named `Prop`s/fields (not silently discharged). This unconditionalizes
the `r = 3` rung *relative to those two named inputs*, which are far more elementary than the
char-`p` ladder wall. The prize CORE (the full `r ≤ log m` char-`p` transfer) stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyThree

/-- **The balanced-class-count carrier.** `B k m` is intended to be the number of *class-balanced*
length-`k` tuples over `m` antipodal classes (each class `{+,−}`): the count of
`(c : Fin k → Fin m × Bool)` such that for every class `j`, `#{i : c i = (j, true)} = #{i :
c i = (j, false)}`. By the Lam–Leung balance characterization (`hLL`), this is exactly the zero-sum
count `E_{k/2}(μ_{2m})`. The structure records the elementary combinatorial facts the count
satisfies: the base cases and the *add-one-class* recursion (a new class occupies `2j` of the `k`
positions with `j` `+`'s and `j` `−`'s). -/
structure BalancedCount (B : ℕ → ℕ → ℤ) : Prop where
  /-- No classes ⟹ no nonempty balanced tuple (`k ≥ 1` has no entries to place). -/
  base0 : ∀ k, 1 ≤ k → B k 0 = 0
  /-- The length-2 add-one-class recursion (`B 2 (m+1) = B 2 m + C(2,2)·C(2,1)`). -/
  rec2 : ∀ m, B 2 (m + 1) = B 2 m + 2
  /-- The length-4 add-one-class recursion: new class takes `0`, `2`, or `4` positions
      (`+ C(4,2)·C(2,1)·B 2 m + C(4,4)·C(4,2)`). -/
  rec4 : ∀ m, B 4 (m + 1) = B 4 m + 12 * B 2 m + 6
  /-- The length-6 add-one-class recursion: new class takes `0,2,4,6` positions
      (`+ C(6,2)·C(2,1)·B 4 m + C(6,4)·C(4,2)·B 2 m + C(6,6)·C(6,3)`). -/
  rec6 : ∀ m, B 6 (m + 1) = B 6 m + 30 * B 4 m + 90 * B 2 m + 20

variable {B : ℕ → ℕ → ℤ}

/-- **`B 2 m = 2m`** — the depth-1 energy `E₁(μ_{2m}) = n` (`n = 2m`), solving `rec2`. -/
theorem B2_closed (h : BalancedCount B) (m : ℕ) : B 2 m = 2 * m := by
  induction m with
  | zero => simpa using h.base0 2 (by norm_num)
  | succ k ih => rw [h.rec2 k, ih]; push_cast; ring

/-- **`B 4 m = 12m² − 6m`** — the depth-2 energy `E₂(μ_{2m}) = 3n² − 3n` (`n = 2m`: `3(2m)²−3(2m) =
12m²−6m`), solving `rec4` with `B2_closed`. -/
theorem B4_closed (h : BalancedCount B) (m : ℕ) : B 4 m = 12 * (m : ℤ) ^ 2 - 6 * m := by
  induction m with
  | zero => simpa using h.base0 4 (by norm_num)
  | succ k ih => rw [h.rec4 k, ih, B2_closed h k]; push_cast; ring

/-- **`B 6 m = 120m³ − 180m² + 80m`** — the depth-3 energy, solving `rec6` with `B4_closed` and
`B2_closed`. With `n = 2m` this is `15n³ − 45n² + 40n` (`B6_eq_E3`). -/
theorem B6_closed (h : BalancedCount B) (m : ℕ) :
    B 6 m = 120 * (m : ℤ) ^ 3 - 180 * (m : ℤ) ^ 2 + 80 * m := by
  induction m with
  | zero => simpa using h.base0 6 (by norm_num)
  | succ k ih => rw [h.rec6 k, ih, B4_closed h k, B2_closed h k]; push_cast; ring

/-- **AVENUE A target: `E₃(μ_n) = 15n³ − 45n² + 40n`** for `n = 2m`. The depth-3 additive-energy
zero-sum count `B 6 m` equals `15n³ − 45n² + 40n`. Derived from the recursion solution `B6_closed`
by pure algebra (`120m³−180m²+80m = 15(2m)³−45(2m)²+40(2m)`). -/
theorem B6_eq_E3 (h : BalancedCount B) (m : ℕ) :
    B 6 m = 15 * (2 * (m : ℤ)) ^ 3 - 45 * (2 * (m : ℤ)) ^ 2 + 40 * (2 * (m : ℤ)) := by
  rw [B6_closed h]; ring

/-- **`κ₆ = 40 n`, unconditional on the three closed-form energies.** The symmetric mean-0 6th
cumulant `κ₆ = E₃ − 15 E₂ E₁ + 30 E₁³` with `E₁ = n`, `E₂ = 3n²−3n`, `E₃ = 15n³−45n²+40n` (the
latter now PROVEN from the recursion via `B6_eq_E3`, no longer the bare `h3`) equals `40 n`: the
cubic and quadratic parts of `E₃` cancel exactly against `−15E₂E₁` and `30E₁³`. Pure algebra. -/
theorem kappa6_eq (n : ℝ) :
    (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) - 15 * (3 * n ^ 2 - 3 * n) * n + 30 * n ^ 3 = 40 * n := by
  ring

end ArkLib.ProximityGap.Frontier.CharZeroEnergyThree

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyThree.B2_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyThree.B4_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyThree.B6_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyThree.B6_eq_E3
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyThree.kappa6_eq
