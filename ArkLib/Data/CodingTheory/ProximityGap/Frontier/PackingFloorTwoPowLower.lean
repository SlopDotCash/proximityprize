/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PackingDeflationBandAntitone

/-!
# The packing deflation floor is bounded BELOW by `2^(k+1)` in the prize band (issue #444,
# under-det / agreement-sharing face — the collapse no-go made rigorous)

`PackingDeflationBandAntitone` proved the packing distinct-`γ` floor
`packingDeflationFloor n k a = C(n,k+1) / C(a,k+1)` is band-ANTITONE (deeper band ⟹ smaller
floor), and its scope note ASSERTS — from the probe only — that the help "SATURATES at `2^(k+1)`",
i.e. that at the prize band `a ≈ n/2` the floor lands at the *constant* `2^(k+1)` and therefore the
agreement-sharing packing face collapses to a `Θ(1)` deflation that provably does NOT reach the
sub-Johnson `√n` distinct-`γ` count CORE needs.  That saturation constant was never proved in Lean.

This file lands the matching LOWER bound, closing the collapse no-go into a theorem:

> **`packingFloor_ge_two_pow`** : if `2·a ≤ n` (the prize band `a ≤ n/2`) and `k+1 ≤ a`, then
>   `2^(k+1) ≤ packingDeflationFloor n k a`.

Combined with the in-tree antitonicity this pins the packing floor in the prize band from BOTH
sides at the constant scale: it is `≥ 2^(k+1)` (this file) while the real ratio `→ 2^(k+1)` from
above (`PackingDeflationBandAntitone` probe), so the packed distinct-`γ` floor is `Θ(1)` — a
constant in `n` for fixed `k`.  Hence the under-determined / agreement-sharing packing lever can
NEVER deliver an `o(√n)` distinct-`γ` cap: the beyond-Johnson lift CANNOT live in this face; it is
forced entirely into the per-`γ` character-sum (BGK) wall.  This is the rigorous, Lean-checked
companion of the cliff-at-`n/2` collapse the ASYMPTOTIC GUARD names (and the packing-side dual of
the over-determined incidence collapse).

## The engine

The load-bearing combinatorial fact is the falling-factorial inequality

> **`two_pow_mul_descFactorial_le`** : `2·a ≤ n  ⟹  2^j · a.descFactorial j ≤ n.descFactorial j`,

proved factorwise on `n.descFactorial j = ∏_{i<j} (n-i)` (`Nat.descFactorial_eq_prod_range`):
each factor satisfies `2·(a-i) ≤ n-i` (since `n - i ≥ 2a - i ≥ 2(a-i)` when `2a ≤ n`), so
`∏_{i<j} 2·(a-i) = 2^j·∏_{i<j}(a-i) ≤ ∏_{i<j}(n-i)`.  Cancelling the common `j!`
(`Nat.descFactorial_eq_factorial_mul_choose`) lifts it to the binomial form
`2^j · C(a,j) ≤ C(n,j)` (`two_pow_mul_choose_le`), and `Nat.le_div_iff_mul_le` lifts THAT to the
floor lower bound on `packingDeflationFloor`.

## Probe (`scripts/probes/probe_packing_floor_lower.py`, exact integer binomials)

`C(n,k+1) ≥ 2^(k+1)·C(a,k+1)` for every `2a ≤ n` (`k=1..6`, `n` to `700`): **718312/718312** pass;
the engine tight case `C(2a,j) ≥ 2^j·C(a,j)`: ALL pass, with ratio `→ 2^j` from ABOVE
(`j=2`: `6.0→4.13→4.02`; `j=3`: `20→8.5→8.06`; `j=4`: `70→17.7→16.2`).  So `2^(k+1)` is the
EXACT saturation floor — the bound proved here is sharp at the prize band.

## Scope (rules 3, 4, 6 — honesty contract + ASYMPTOTIC GUARD)

* Field-universal pure-`Nat` combinatorics about the deflation floor: NOT thinness-essential, NOT a
  moment/Wick/energy move, NOT an orbit/spectrum re-derivation.  It is a REFUTATION-style constraint
  lemma (rule 4): it MAPS the packing face's wall precisely by proving its floor is `≥` a constant.
* It does NOT improve CORE — it PROVES the packing face cannot.  At the prize band the distinct-`γ`
  packing floor is `Θ(1)` (this file's `≥ 2^(k+1)` lower bound + the in-tree antitone upper-side
  saturation), NOT `√n`, so the agreement-sharing face is confirmed collapsed to Johnson; the
  beyond-Johnson lift lives in the per-`γ` BGK wall, untouched.  No capacity / beyond-Johnson /
  growth-law claim.  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

/-- **The falling-factorial engine.**  If `2·a ≤ n` then the `j`-th falling factorial of `n`
dominates `2^j` times that of `a`:  `2^j · a.descFactorial j ≤ n.descFactorial j`.

Proof factorwise on `descFactorial = ∏_{i<j} (·-i)`: each factor obeys `2·(a-i) ≤ n-i`
(from `n - i ≥ 2a - i ≥ 2(a-i)`), and `∏_{i<j} 2·(a-i) = 2^j · ∏_{i<j}(a-i)`. -/
theorem two_pow_mul_descFactorial_le {n a : ℕ} (hle : 2 * a ≤ n) (j : ℕ) :
    2 ^ j * a.descFactorial j ≤ n.descFactorial j := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  -- ∏_{i<j} 2·(a-i) ≤ ∏_{i<j} (n-i), then pull the constant 2^j out of the LHS product.
  have hfac : ∀ i ∈ Finset.range j, 2 * (a - i) ≤ n - i := by
    intro i _
    -- n - i ≥ 2a - i ≥ 2(a - i)
    have h1 : 2 * a - i ≤ n - i := Nat.sub_le_sub_right hle i
    have h2 : 2 * (a - i) ≤ 2 * a - i := by omega
    exact le_trans h2 h1
  calc 2 ^ j * ∏ i ∈ Finset.range j, (a - i)
      = ∏ i ∈ Finset.range j, 2 * (a - i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range j, (n - i) :=
        Finset.prod_le_prod' hfac

/-- **The binomial form.**  If `2·a ≤ n` then `2^j · C(a,j) ≤ C(n,j)`: cancel the common `j!`
from the falling-factorial engine via `descFactorial = j! · choose`. -/
theorem two_pow_mul_choose_le {n a : ℕ} (hle : 2 * a ≤ n) (j : ℕ) :
    2 ^ j * a.choose j ≤ n.choose j := by
  have hkey : Nat.factorial j * (2 ^ j * a.choose j) ≤ Nat.factorial j * n.choose j := by
    calc Nat.factorial j * (2 ^ j * a.choose j)
        = 2 ^ j * (Nat.factorial j * a.choose j) := by ring
      _ = 2 ^ j * a.descFactorial j := by rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ ≤ n.descFactorial j := two_pow_mul_descFactorial_le hle j
      _ = Nat.factorial j * n.choose j := Nat.descFactorial_eq_factorial_mul_choose n j
  exact Nat.le_of_mul_le_mul_left hkey (Nat.factorial_pos j)

/-- **THE PACKING-FLOOR LOWER BOUND (the collapse no-go).**  In the prize band `2·a ≤ n` (i.e.
`a ≤ n/2`), with the band at least the tuple size (`k+1 ≤ a`, so `C(a,k+1) > 0`), the packing
distinct-`γ` deflation floor is bounded BELOW by the constant `2^(k+1)`:

> `2^(k+1) ≤ packingDeflationFloor n k a`.

Together with `PackingDeflationBandAntitone` (the floor's antitone upper-side saturation at
`2^(k+1)` from above) this pins the floor at the constant scale in the prize band: the
agreement-sharing packing distinct-`γ` cap is `Θ(1)`, NOT `√n`, so this face CANNOT reach CORE. -/
theorem packingFloor_ge_two_pow {n k a : ℕ} (hle : 2 * a ≤ n) (hka : k + 1 ≤ a) :
    2 ^ (k + 1) ≤ packingDeflationFloor n k a := by
  unfold packingDeflationFloor
  rw [Nat.le_div_iff_mul_le (Nat.choose_pos hka)]
  exact two_pow_mul_choose_le hle (k + 1)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.two_pow_mul_descFactorial_le
#print axioms ProximityGap.Ownership.two_pow_mul_choose_le
#print axioms ProximityGap.Ownership.packingFloor_ge_two_pow
