/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# A cubic proxy for the over-determined far-line incidence MAX (#407, δ* decoupling)

This file records an **empirically fitted cubic proxy** for the over-determined far-line
incidence MAX at rate `k = 2`, over-determined witness size `s = k + 2 = 4` (`s − k = 2`),
together with the purely arithmetic comparison of that proxy against the budget `4·m`.  Nothing
in this file defines or counts an actual incidence: no field, Reed–Solomon code, bad-scalar set or
cardinality appears in any declaration below.

## Background (the hoped-for δ* decoupling — conjectural, not proved here)

The far-line incidence `I(a,b; r = n−s)` counts the `γ ∈ F_q` with `x^a + γ x^b` within distance
`r` of `RS[μ_n, k]`.  The campaign conjectured that for `s − k ≥ 2` (over-determined) this count
is `p`-independent (equal to a characteristic-0 value), so that the binding witness size
`s* = min { s : I(s) ≤ budget }` would be computable from cyclotomic char-0 data and δ* would
decouple from the `p`-dependent BGK character-sum max.  **That `p`-independence is not proved,
and it is false without arithmetic hypotheses on `q`:**

* The heuristic "`disc(x^{2^μ} − 1) = ± n^n` is a power of `2`" only shows that the *domain
  roots* stay distinct mod every odd prime.  It does not exclude odd primes dividing the
  evaluation minors / resultants that decide whether a given `γ` is bad (the audit's PG-083 records
  a separate kernel-checked failure of a resultant premise), so it gives no good-prime transfer
  for the incidence count.
* An actual bad-scalar set is a subset of `F_q`, so the count is at most `q`.  For example
  `n = 32 = 4·8` in `F_97` (`97` prime and `32 ∣ 96`, so `μ_32 ⊊ F_97^×`; the element `28` has
  `28^32 = 1` and `28^16 = −1` mod `97`) has incidence `≤ 97`, while the proxy below gives
  `overdetIncidenceMax 8 = 897`.  So the proxy is not a field-independent count; at best it could
  be a large-characteristic value under a precise good-prime condition that is not yet stated.

Using the proxy to decouple δ* from `p` would therefore need (i) explicit arithmetic good-prime
hypotheses on `q` (relative to `n`, `k`, `s`) and (ii) a proof that, under them, the actual count
equals `overdetIncidenceMax`.  Neither is supplied here.

## This file's contribution: a cubic proxy and its arithmetic domination of budget

The campaign's probe scripts (`probe_overdet_max_closedform.py`,
`probe_overdet_antipodal_only.py`, `probe_overdet_mechanism.py`; not present in this tree — the
in-tree `scripts/probes/g322_*`, `g325_*`, `g326_*` only re-evaluate the polynomial) reported the
over-determined incidence MAX at `s = k + 2`, `k = 2`, at finitely many `(n, q)` cells as

> `I_max(n) = n³/32 − n²/8 + 1`,  written here with `n = 4·m` as `2·m³ − 2·m² + 1`,

attained at the antipodal direction `(a,b) = (n/2, n/2 − 1)`, for
`n = 8, 12, 16, 20, 24, 28, 32, 36, 40` (`m = 2 … 10`), i.e. the sequence
`9, 37, 97, 201, 361, 589, 897, 1297, 1801`.  These are finite probe observations in the fields
the probes used (any such cell needs `q > I_max(n)`, since a count of scalars is at most `q`), not
a theorem.  Note also that `n = 12, 20, 24, 28, 36, 40` are not powers of two, so these cells lie
outside the thin `2`-power subgroup family the discriminant heuristic was about.  The probes'
suggested mechanism (the bulk `2m³ − 2m²` from nonzero-`γ` proportional-reduction witnesses, the
`+1` from the trivial `γ = 0` witness) is likewise unformalized.

We formalize only arithmetic facts about the polynomial:
* `overdetIncidenceMax m := 2*m^3 - 2*m^2 + 1` — the cubic proxy (`ℕ`, in terms of `m = n/4`);
* `overdetIncidenceMax_values` — it evaluates to the reported sequence on `m = 2 … 10`
  (`decide`);
* `overdetIncidenceMax_bulk` — the factorisation `2m³ − 2m² = 2m²(m − 1)`;
* **`overdetIncidenceMax_gt_budget`** — `overdetIncidenceMax m > 4*m` for `m ≥ 2`.  Only if the
  actual over-determined incidence were shown to equal the proxy (under suitable good-prime
  hypotheses) would this say that the incidence exceeds the budget `n = 4·m` at `s = k + 2`.

**Scope / honesty.**  The proxy is a finite-probe / conjectural stand-in for the over-determined
incidence MAX, not its proved value, and it is provably not a field-independent count (the `F_97`
example above).  The theorems below are arithmetic facts about a polynomial; they do not establish
`p`-independence of δ*, the antipodal maximality, or any equality with an actual incidence count.
-/

namespace ArkLib.ProximityGap.OverdetIncidence

/-- **Cubic proxy** (not a proved count) for the over-determined far-line incidence MAX at rate
`k = 2`, over-determined witness size `s = k + 2 = 4`, with `n = 4·m`: the polynomial
`2·m³ − 2·m² + 1` (equivalently `n³/32 − n²/8 + 1`) fitted to finitely many probe cells.  It is
not a field-independent incidence count (an actual count is `≤ q`; e.g. `m = 8` gives `897 > 97`
for `μ_32 ⊊ F_97^×`), and no theorem here relates it to an actual bad-scalar set. -/
def overdetIncidenceMax (m : ℕ) : ℕ := 2 * m ^ 3 - 2 * m ^ 2 + 1

/-- The cubic proxy evaluates to the campaign's reported over-determined incidence MAX sequence
`9, 37, 97, 201, 361, 589, 897, 1297, 1801` at `n = 8 … 40` (`m = 2 … 10`).  This only evaluates
the polynomial; the reported values themselves are finite probe observations (in fields with
`q` larger than the value), not formalized counts. -/
theorem overdetIncidenceMax_values :
    overdetIncidenceMax 2 = 9 ∧ overdetIncidenceMax 3 = 37 ∧ overdetIncidenceMax 4 = 97 ∧
    overdetIncidenceMax 5 = 201 ∧ overdetIncidenceMax 6 = 361 ∧ overdetIncidenceMax 7 = 589 ∧
    overdetIncidenceMax 8 = 897 ∧ overdetIncidenceMax 9 = 1297 ∧ overdetIncidenceMax 10 = 1801 := by
  decide

/-- `2·m³ − 2·m² = 2·m²·(m − 1)`, the "bulk" term of the cubic proxy (the probes attribute it to
nonzero-`γ` witnesses and the `+1` to `γ = 0`; that attribution is not formalized).  A convenient
factored identity over `ℕ` (no truncation: `m² ≥ m` for the inner subtraction; `2m³ ≥ 2m²`). -/
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

/-- **Arithmetic domination of budget by the cubic proxy.** For `m ≥ 2` (i.e. `n = 4m ≥ 8`),
the polynomial proxy strictly exceeds `4·m`:

> `overdetIncidenceMax m > 4·m`.

This is a fact about the polynomial only.  It would imply that the actual over-determined
incidence exceeds the budget at `s = k + 2` only after a separate proof that the actual count
equals the proxy under explicit good-prime hypotheses on `q`; no such bridge exists, and the proxy
is not field-independent (see the module docstring).  In particular this theorem does not show
that δ* is `p`-independent or decoupled from the BGK max. -/
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
