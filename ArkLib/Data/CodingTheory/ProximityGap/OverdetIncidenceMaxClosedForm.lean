/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Closed form for the over-determined far-line incidence MAX (#407, δ* decoupling)

This file records the **closed form** of the over-determined far-line incidence MAX for the
prize-regime thin 2-power subgroup `μ_n ⊊ F_q^×` (`n = 2^μ`), in the rate `k = 2`,
over-determined witness size `s = k + 2 = 4` (`s − k = 2`), and the structural inequality that
makes it matter for the δ* decoupling.

## Background (the δ* decoupling, char-0 / p-independent)

The far-line incidence `I(a,b; r = n−s)` counts the `γ` with `x^a + γ x^b` within distance `r`
of `RS[μ_n, k]`. For `s − k ≥ 2` (over-determined) it is **p-independent** (= its char-0 value,
proven via `disc(x^{2^μ} − 1) = ± n^n` a power of `2`), so the binding witness size
`s* = min { s : I(s) ≤ budget }` is computed in pure cyclotomic char-0 data and δ* decouples from
the open p-dependent BGK character-sum max. The single remaining char-0 open item is the
asymptotic `s*(n,k)` of the over-determined incidence threshold.

## This file's contribution: the MAX is an exact cubic, and it dominates budget

The empirical, exactly-reproduced (probe `probe_overdet_max_closedform.py`,
`probe_overdet_antipodal_only.py`, `probe_overdet_mechanism.py`; full-direction search and exact
integer cross-check) over-determined incidence MAX at `s = k + 2`, `k = 2`, is

> **`I_max(n) = n³/32 − n²/8 + 1`**,  written here with `n = 4·m` as **`2·m³ − 2·m² + 1`**,

attained at the **antipodal direction `(a,b) = (n/2, n/2 − 1)`**. Verified EXACTLY for
`n = 8, 12, 16, 20, 24, 28, 32, 36, 40` (`m = 2 … 10`), reproducing the campaign's published
sequence `9, 37, 97, 201, 361, 589, 897, 1297, 1801`. The mechanism: the bulk `2m³ − 2m²` are the
nonzero-`γ` proportional-reduction witnesses; the `+1` is exactly the trivial `γ = 0` witness (the
unique `γ` with an antipodal-closed witness set).

We formalize:
* `overdetIncidenceMax m := 2*m^3 - 2*m^2 + 1` — the closed form (`ℕ`, in terms of `m = n/4`);
* `overdetIncidenceMax_values` — it matches the published sequence on `m = 2 … 10` (`decide`);
* **`overdetIncidenceMax_gt_budget`** — `overdetIncidenceMax m > 4*m` for `m ≥ 2`, i.e. the
  over-determined incidence MAX **strictly exceeds the budget `n = 4·m`**. This is the quantitative
  form of "the binding `s*` is always over-determined", the inequality underpinning the δ*
  decoupling. (`budget ~ n`; here exactly `n = 4m` at `k = 2`.)

**Scope / honesty.** This is the EXACT closed form of the over-determined incidence MAX (an
empirical cyclotomic count, reproduced exactly at every probed `n`), and a fully-proved arithmetic
domination over budget. It is NOT a closure of CORE: it pins one ingredient (the over-det MAX curve)
that the open `s*(n,k)` asymptotic still needs (the MAX is at `s = k+2`; the budget-crossing `s*`
requires the full `s`-dependence). The closed form's *cyclotomic derivation* is not formalized here
(only its arithmetic and the domination); the value is established by exact computation.
-/

namespace ArkLib.ProximityGap.OverdetIncidence

/-- The over-determined far-line incidence MAX at rate `k = 2`, over-determined witness size
`s = k + 2 = 4`, for the thin 2-power subgroup `μ_n` with `n = 4·m`. Closed form
`2·m³ − 2·m² + 1` (equivalently `n³/32 − n²/8 + 1`), attained at the antipodal direction
`(n/2, n/2 − 1)`. -/
def overdetIncidenceMax (m : ℕ) : ℕ := 2 * m ^ 3 - 2 * m ^ 2 + 1

/-- The closed form reproduces the campaign's published over-determined incidence MAX sequence
`9, 37, 97, 201, 361, 589, 897, 1297, 1801` at `n = 8 … 40` (`m = 2 … 10`). Verified by exact
full-direction search + integer cross-check in the probes; here checked against the closed form. -/
theorem overdetIncidenceMax_values :
    overdetIncidenceMax 2 = 9 ∧ overdetIncidenceMax 3 = 37 ∧ overdetIncidenceMax 4 = 97 ∧
    overdetIncidenceMax 5 = 201 ∧ overdetIncidenceMax 6 = 361 ∧ overdetIncidenceMax 7 = 589 ∧
    overdetIncidenceMax 8 = 897 ∧ overdetIncidenceMax 9 = 1297 ∧ overdetIncidenceMax 10 = 1801 := by
  decide

/-- `2·m³ − 2·m² = 2·m²·(m − 1)`, the nonzero-`γ` bulk of the over-det incidence MAX (the `+1` is
the trivial `γ = 0` witness). A convenient factored identity over `ℕ` (no truncation: `m² ≥ m`
for the inner subtraction; `2m³ ≥ 2m²`). -/
theorem overdetIncidenceMax_bulk (m : ℕ) :
    2 * m ^ 3 - 2 * m ^ 2 = 2 * m ^ 2 * (m - 1) := by
  rcases m with _ | m
  · decide
  · -- with m = m'+1: both sides are 2*(m'+1)^2*m'; no ℕ-truncation in play.
    have hrhs : 2 * (m + 1) ^ 2 * (m + 1 - 1) = 2 * (m + 1) ^ 2 * m := by
      congr 1
    have hlhs : 2 * (m + 1) ^ 3 - 2 * (m + 1) ^ 2 = 2 * (m + 1) ^ 2 * m := by
      have hle : 2 * (m + 1) ^ 2 ≤ 2 * (m + 1) ^ 3 := by nlinarith [sq_nonneg (m + 1)]
      have hsum : 2 * (m + 1) ^ 2 * m + 2 * (m + 1) ^ 2 = 2 * (m + 1) ^ 3 := by ring
      omega
    rw [hrhs, hlhs]

/-- **The δ* decoupling inequality (quantitative).** For `m ≥ 2` (i.e. `n = 4m ≥ 8`, the regime
where over-determination `s − k ≥ 2` is nondegenerate), the over-determined incidence MAX
**strictly exceeds the budget** `n = 4·m`:

> `overdetIncidenceMax m > 4·m`.

Since the over-determined incidence MAX `≫ budget` at `s = k+2` for every `m ≥ 2`, the binding
witness size `s*` (the first `s` whose incidence drops to `≤ budget`) can never be the
over-determined boundary `s = k+2`; the incidence stays above budget there. This is the arithmetic
core of "the binding is always over-determined ⟹ δ* is p-independent" (decoupled from the
p-dependent BGK max), proven outright over `ℕ`. -/
theorem overdetIncidenceMax_gt_budget {m : ℕ} (hm : 2 ≤ m) :
    overdetIncidenceMax m > 4 * m := by
  unfold overdetIncidenceMax
  -- 2 m^3 - 2 m^2 + 1 > 4 m, for m ≥ 2. Since 2 m^3 ≥ 2 m^2 (m ≥ 1), the ℕ-subtraction is exact.
  have h2 : 2 * m ^ 2 ≤ 2 * m ^ 3 := by
    have : m ^ 2 ≤ m ^ 3 := by
      have : m ^ 2 * 1 ≤ m ^ 2 * m := by
        apply Nat.mul_le_mul_left
        omega
      simpa [pow_succ, pow_two, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using this
    omega
  -- It suffices to show 2 m^3 ≥ 2 m^2 + 4 m + 1 (so the lhs minus 2m^2 plus 1 > 4m).
  -- For m ≥ 2: 2 m^3 - 2 m^2 = 2 m^2 (m-1) ≥ 2·m^2·1 = 2 m^2 ≥ 8 m > 4 m (since m ≥ 2 ⟹ m^2 ≥ 2m).
  have hbulk : 2 * m ^ 2 * (m - 1) ≥ 4 * m := by
    have hm1 : 1 ≤ m - 1 := by omega
    have hsq : m * 2 ≤ m ^ 2 := by
      have : m * 2 ≤ m * m := by
        apply Nat.mul_le_mul_left; omega
      simpa [pow_two] using this
    calc 2 * m ^ 2 * (m - 1) ≥ 2 * m ^ 2 * 1 := by
              apply Nat.mul_le_mul_left; omega
      _ = 2 * m ^ 2 := by ring
      _ ≥ 2 * (m * 2) := by
              apply Nat.mul_le_mul_left; exact hsq
      _ = 4 * m := by ring
  have hbulk' : 2 * m ^ 3 - 2 * m ^ 2 ≥ 4 * m := by
    rw [overdetIncidenceMax_bulk]; exact hbulk
  omega

end ArkLib.ProximityGap.OverdetIncidence
