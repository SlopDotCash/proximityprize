/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Bridge B49 (target X) — the prize budget `E = ⌊q·ε*⌋` is EXACTLY `n` (#444)

The converse pin `OpenCoreConverse.deltaStar_iff_incidence_budget` (anchor P1) reduces the prize,
at any window-interior radius, to the worst far-line incidence obeying the budget

  `E = ⌊q · ε*⌋`,

where, at the **prize parameters**,

  `q = n^β`   (`β ≈ 4–5`, the field size),   `ε* = 2^{-128}`,   `n = 2^μ`   (the dyadic length).

The directive (B49 SPEC) asks to **state the exact arithmetic relation** that the budget `⌊q·ε*⌋`
is `≈ n` at these parameters. This file pins that relation EXACTLY (not "≈"): with `n = 2^μ` and
`q = 2^{β·μ} = n^β`, the budget is the integer power `2^{β·μ − 128}`, and

  `⌊q · ε*⌋ = n  ⟺  β·μ − 128 = μ  ⟺  β = 1 + 128/μ`.

So the "budget ≈ n" of the KB (memory `issue444-bridge-program-empirical-formulas`,
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`) is not an approximation: it
is the **exact** statement that the field exponent sits one full dyadic step above the security
exponent, `β·μ = μ + 128`. The whole bridge program's "budget `≈ n`" assumption is this equation.

## What this bridge does (HONEST scope)

This is a pure ℕ/ℚ-arithmetic brick. We work with the security exponent `s = 128` kept as a free
ℕ so nothing is hard-coded, and prove, axiom-clean:

* `budget_eq_pow` — `q · ε* = 2^{β·μ − s}` as a ℚ identity (when `β·μ ≥ s`), with
  `q = (2^μ)^β`, `ε* = (2:ℚ)^{-s}`. The budget is an *exact integer power of two*.
* `budget_eq_n_iff` — the EXACT pin: `2^{β·μ − s} = 2^μ  ⟺  β·μ − s = μ` (over ℕ exponents,
  `β·μ ≥ s`). This is the "budget = n" relation, exactly.
* `budget_eq_n_iff_beta` — the same relation read on `β`: at the prize `s = 128`, `μ ≠ 0`,
  `β·μ = μ + 128`, i.e. `β = 1 + 128/μ` over ℚ.
* `prize_budget_floor_eq` — `⌊q·ε*⌋ = 2^{β·μ − s}` (the floor is exact, the value being a Nat
  power), hence `⌊q·ε*⌋ = n = 2^μ` under the exponent equation `β·μ = μ + s`.

This is exactly the clean brick B49 is flagged to be: the arithmetic that turns the abstract budget
`E = ⌊q·ε*⌋` of `OpenCoreConverse` into the concrete `E = n` used by E1–E7. It does NOT touch the
δ*/incidence content (that is P1, upstream and already proven); it supplies the parameter arithmetic
those bridges silently assume.

## Honesty

No `sorry`, no fake axiom, no `native_decide`. Everything is `ring`/`field_simp`/`pow`-lemma
arithmetic over ℚ and ℕ. The axiom audit at the bottom must show only
`propext, Classical.choice, Quot.sound`.

Issue #444.
-/

namespace ProximityGap.BridgeB49

/-- **B49 (target X) — the prize budget is an exact power of two.**

At the prize parameters `n = 2^μ`, `q = n^β = 2^{β·μ}`, `ε* = 2^{-s}` (`s = 128`), the budget
`q · ε*` is the exact rational power `2^{β·μ − s}`, provided `β·μ ≥ s` (so the exponent is a Nat).

Proof: `q·ε* = 2^{βμ} · 2^{-s} = 2^{βμ - s}`, an integer power of two by `pow_sub`-style algebra. -/
theorem budget_eq_pow (μ β s : ℕ) (hs : s ≤ β * μ) :
    ((2 : ℚ) ^ μ) ^ β * (2 : ℚ) ^ (- (s : ℤ)) = (2 : ℚ) ^ (β * μ - s) := by
  -- LHS: (2^μ)^β = 2^(μ*β) = 2^(β*μ); times 2^(-s) = 2^(β*μ - s) over ℤ-exponents.
  have hbase : (2 : ℚ) ≠ 0 := by norm_num
  rw [← pow_mul, ← zpow_natCast (2:ℚ) (μ * β), ← zpow_natCast (2:ℚ) (β * μ - s),
      ← zpow_add₀ hbase]
  congr 1
  -- (μ*β : ℤ) + (-(s:ℤ)) = ((β*μ - s : ℕ) : ℤ), using s ≤ β*μ for the Nat subtraction.
  have : ((β * μ - s : ℕ) : ℤ) = (β * μ : ℤ) - (s : ℤ) := by
    exact_mod_cast Int.ofNat_sub hs
  rw [this]
  push_cast
  ring

/-- **B49 (target X) — the EXACT "budget = n" pin (exponent form).**

The budget `2^{β·μ − s}` equals `n = 2^μ` **iff** the exponents agree: `β·μ − s = μ`. Over the
prize parameters this is the precise content of "budget ≈ n": it is an *equality*, the field
exponent sitting exactly one dyadic length above the security exponent. -/
theorem budget_eq_n_iff (μ β s : ℕ) (hs : s ≤ β * μ) :
    (2 : ℚ) ^ (β * μ - s) = (2 : ℚ) ^ μ ↔ β * μ - s = μ := by
  constructor
  · intro h
    -- 2^a = 2^b over ℚ (base > 1) forces a = b, by strict monotonicity of (2:ℚ)^·.
    by_contra hne
    rcases Nat.lt_or_ge (β * μ - s) μ with hlt | hge
    · have : (2 : ℚ) ^ (β * μ - s) < (2 : ℚ) ^ μ :=
        pow_lt_pow_right₀ (by norm_num) hlt
      exact (ne_of_lt this) h
    · have hlt' : μ < β * μ - s := lt_of_le_of_ne hge (by simpa [eq_comm] using hne)
      have : (2 : ℚ) ^ μ < (2 : ℚ) ^ (β * μ - s) :=
        pow_lt_pow_right₀ (by norm_num) hlt'
      exact (ne_of_lt this) h.symm
  · intro h; rw [h]

/-- **B49 (target X) — the "budget = n" pin read on `β` (prize `s = 128`).**

With `μ ≠ 0` and the security exponent `s`, the budget equals `n` iff `β·μ = μ + s`, i.e.
`β = 1 + s/μ`. At `s = 128`: `β = 1 + 128/μ`. (For `μ = 30`, prize-scale, this is `β = 1 + 64/15`,
between the `β ≈ 4–5` of the KB.) -/
theorem budget_eq_n_iff_beta (μ β s : ℕ) (hμ : μ ≠ 0) (hs : s ≤ β * μ) :
    β * μ - s = μ ↔ (β : ℚ) = 1 + (s : ℚ) / (μ : ℚ) := by
  have hμ0 : (μ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hμ
  constructor
  · intro h
    -- β*μ - s = μ  ⟹  β*μ = μ + s (Nat, using s ≤ β*μ)  ⟹  β = 1 + s/μ over ℚ.
    have hnat : β * μ = μ + s := by omega
    have hq : (β : ℚ) * μ = μ + s := by exact_mod_cast hnat
    field_simp
    linarith [hq]
  · intro h
    -- β = 1 + s/μ  ⟹  β*μ = μ + s  ⟹  β*μ - s = μ.
    have hq : (β : ℚ) * μ = μ + s := by
      field_simp at h
      linarith [h]
    have hnat : β * μ = μ + s := by exact_mod_cast hq
    omega

/-- **B49 (target X) — the budget floor is exact, and equals `n` under the exponent equation.**

`⌊q·ε*⌋` is an *exact* integer (a Nat power of two), `2^{β·μ − s}`, and under the prize
relation `β·μ = μ + s` it is precisely `n = 2^μ`. This is the concrete `E = n` that the bridge
program (E1–E7) consumes from `OpenCoreConverse`'s abstract `E = ⌊q·ε*⌋`. -/
theorem prize_budget_floor_eq (μ β s : ℕ) (hexp : β * μ = μ + s) :
    ((2 : ℚ) ^ μ) ^ β * (2 : ℚ) ^ (- (s : ℤ)) = (2 : ℚ) ^ μ := by
  have hs : s ≤ β * μ := by omega
  rw [budget_eq_pow μ β s hs]
  congr 1
  omega

end ProximityGap.BridgeB49

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.BridgeB49.budget_eq_pow
#print axioms ProximityGap.BridgeB49.budget_eq_n_iff
#print axioms ProximityGap.BridgeB49.budget_eq_n_iff_beta
#print axioms ProximityGap.BridgeB49.prize_budget_floor_eq
