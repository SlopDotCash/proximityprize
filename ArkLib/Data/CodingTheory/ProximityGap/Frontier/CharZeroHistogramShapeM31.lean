/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The char-`0` histogram coefficient for the canonical shape `d = (-3, 1, 0, …)` (#466)

This file formalizes, axiom-clean, the exact characteristic-zero histogram (canonical-relation)
count of the depth-`r` shape `d = (-3, 1, 0, …)` over the `2`-power subgroup `μ_n` (`n = 2m`,
`m = n/2` antipodal classes), and uses it to give an **explicit finite-`n` upper bound that
settles whether the `r²/n` suppression heuristic is uniform**. It is NOT.

## Objects

For a fixed nonzero shape supported on two antipodal classes — one class ending at net `+1`, one at
net `-3` — the histogram "core" count (the number of length-`2r` signed unit-step walks over those
two classes realizing exactly the net `(-3, +1)`, independent of `n`) has the exact closed form

> `nrCore r = Σ_{j=0}^{r-2}  C(2r, 2j+1) · C(2j+1, j+1) · C(2r-2j-1, r-2-j)`.

(The class ending at `+1` absorbs `2j+1` of the `2r` steps and lands at `+1` in `C(2j+1, j+1)`
ways; the class ending at `-3` absorbs the remaining `2r-2j-1 = 2(r-2-j)+3` steps and lands at
`-3` in `C(2r-2j-1, r-2-j)` ways; the two classes' steps interleave in `C(2r, 2j+1)` ways.)
This equals `(2r)!·[t^{2r}] I_1(2t)·I_3(2t)`, the Cauchy product of two modified-Bessel coefficient
sequences (`class +1 ↦ 1/(j!(j+1)!)`, `class -3 ↦ 1/(k!(k+3)!)`). Probe-verified EQUAL to the direct
signed-walk histogram count for `r = 2..11`: `4, 90, 1568, 25200, 392040, 6012006, …`
(`scripts` / report `arklib-opus-formalizer.md`).

The **full single-shape mass** over `μ_n` places the support-`2` shape into `m(m-1)` ordered pairs of
the `m = n/2` antipodal classes:

> `nrFull n r = (n/2)·(n/2 - 1) · nrCore r`.

## The finding formalized (the `r²/n` suppression is NOT uniform)

At depth `r = 2`, `nrCore 2 = 4`, hence `nrFull n 2 = 4·(n/2)(n/2-1) = n(n-2)` for even `n`. The
Wick count at depth `2` is `Wick_2 = (2·2-1)‼·n² = 3n²`. Therefore the exact ratio is

> `nrFull n 2 / Wick_2(n) = n(n-2) / (3n²) = (n-2)/(3n)  →  1/3`   (as `n → ∞`, monotone up).

So the depth-`2` shape `(-3,1)` is `Θ(1)` relative to Wick — it is **not** `O(1/n)`, refuting the
`r²/n` (indeed any `1/n`) suppression heuristic at `r = 2`. This is the depth-`2` pair-sum ("s4h1")
sector flagged in `DISPROOF_LOG` r370b as reviving census violations through special primes.

For `r ≥ 3` the same ratio is `Θ(n^{2-r})` (genuine polynomial suppression, exponent `2-r`, NOT
`r²/n`), so the r-dependence DECAYS rather than growing like `r²`. The honest law is the exact ratio
`nrFull n r / Wick_r = (n/2)(n/2-1)·nrCore r / ((2r-1)‼·n^r)`, whose only non-suppressed depth is `2`.

## Honest scope

Char-`0` / negation-closed combinatorics — the exact histogram coefficient of ONE canonical shape and
its exact finite-`n` ratio to Wick. This is a precise NO-GO for the `r²/n` suppression heuristic, not a
CORE closure: the prize wall is the SIMULTANEOUS control of all sectors at prize depth `r ≈ log q`,
which this file does not touch. Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31

open Finset

/-- **The `j`-th histogram term** for the shape `(-3, +1)` at depth `r`: the class ending at `+1`
absorbs `2j+1` steps landing at `+1` in `C(2j+1, j+1)` ways; the class ending at `-3` absorbs
`2r-2j-1` steps landing at `-3` in `C(2r-2j-1, r-2-j)` ways; the two classes interleave in
`C(2r, 2j+1)` ways. A product of three binomials, manifestly a natural number. -/
def nrTerm (r j : ℕ) : ℕ :=
  Nat.choose (2 * r) (2 * j + 1) * Nat.choose (2 * j + 1) (j + 1) *
    Nat.choose (2 * r - 2 * j - 1) (r - 2 - j)

/-- **The char-`0` histogram core count** of the shape `d = (-3, 1, 0, …)` at depth `r`:
`nrCore r = Σ_{j=0}^{r-2} nrTerm r j`. Independent of `n`. -/
def nrCore (r : ℕ) : ℕ := ∑ j ∈ Finset.range (r - 1), nrTerm r j

/-- **The full single-shape mass** over `μ_n` (`m = n/2` antipodal classes): the support-`2` shape is
placed into `m(m-1)` ordered class pairs. -/
def nrFull (n r : ℕ) : ℕ := (n / 2) * (n / 2 - 1) * nrCore r

/-- **The depth-`r` Wick count** `Wick_r = (2r-1)‼ · n^r`, with `(2r-1)‼ = (2r)!/(2^r r!)`. We use
the explicit double-factorial as `(2r)! / (2^r · r!)` only implicitly; here we only need `r = 2`,
`Wick_2 = 3 n²`, which we state directly. -/
def wickTwo (n : ℕ) : ℕ := 3 * n ^ 2

/-! ### Kernel-checked data points for the core (probe values, decided) -/

/-- `nrCore 2 = 4`. -/
theorem nrCore_two : nrCore 2 = 4 := by decide

/-- `nrCore 3 = 90`. -/
theorem nrCore_three : nrCore 3 = 90 := by decide

/-- `nrCore 4 = 1568`. -/
theorem nrCore_four : nrCore 4 = 1568 := by decide

/-- `nrCore 5 = 25200`. -/
theorem nrCore_five : nrCore 5 = 25200 := by decide

/-- `nrCore 6 = 392040`. -/
theorem nrCore_six : nrCore 6 = 392040 := by decide

/-! ### The exact `r = 2` finite-`n` mass and ratio (the load-bearing no-go) -/

/-- **Exact depth-`2` full mass:** for even `n = 2m`, `nrFull n 2 = n(n-2)`.
(`nrFull n 2 = m(m-1)·4 = 4·(n/2)(n/2-1) = n(n-2)`.) -/
theorem nrFull_two (m : ℕ) : nrFull (2 * m) 2 = (2 * m) * (2 * m - 2) := by
  unfold nrFull
  rw [nrCore_two]
  have hm : (2 * m) / 2 = m := by omega
  rw [hm]
  cases m with
  | zero => rfl
  | succ k =>
    have h1 : k + 1 - 1 = k := by omega
    have h2 : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [h1, h2]
    ring

/-- **The exact depth-`2` ratio identity, cleared of denominators:**
`3 · nrFull n 2 = (n - 2) · wickTwo n / n`, stated integrally as
`3 · nrFull (2m) 2 · (2m) = (2m - 2) · wickTwo (2m)` — i.e.
`nrFull / wickTwo = (n-2)/(3n)` exactly, for `n = 2m ≥ 2`. -/
theorem ratio_two_exact (m : ℕ) :
    3 * nrFull (2 * m) 2 * (2 * m) = (2 * m - 2) * wickTwo (2 * m) := by
  rw [nrFull_two, wickTwo]
  cases m with
  | zero => rfl
  | succ k =>
    have h2 : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [h2]
    ring

/-- **The `r²/n` (indeed any `1/n`) suppression heuristic is FALSE at `r = 2`.**
Formalized as a uniform LOWER bound on the ratio bounded away from `0`: for every `m ≥ 2`
(`n = 2m ≥ 4`), `6 · nrFull (2m) 2 ≥ wickTwo (2m)`, i.e. `nrFull / wickTwo ≥ 1/6`.
Combined with `ratio_two_exact` (ratio `= (n-2)/(3n) < 1/3`), the depth-`2` shape mass is
`Θ(Wick)`, NOT `O(Wick / n)`; the ratio does not decay, so the `r²/n` suppression is not uniform. -/
theorem ratio_two_not_suppressed (m : ℕ) (hm : 2 ≤ m) :
    wickTwo (2 * m) ≤ 6 * nrFull (2 * m) 2 := by
  rw [nrFull_two, wickTwo]
  -- goal: 3 * (2m)^2 ≤ 6 * ((2m)*(2m-2))
  have hexp : (2 * m) ^ 2 = 2 * m * (2 * m) := by ring
  rw [hexp]
  -- 3 * (2m*2m) ≤ 6 * (2m * (2m-2))  ⟺  2m ≤ 2*(2m-2) = 4m-4  ⟺  m ≥ 2
  have hk : 2 * m - 2 = 2 * (m - 1) := by omega
  rw [hk]
  have : 2 * m ≤ 2 * (2 * (m - 1)) := by omega
  nlinarith [Nat.zero_le m]

/-- **The ratio's non-vanishing limit, exact form.** For `n = 2m`, the *difference*
`3n · (nrFull n 2) - (n-2) · wickTwo n = 0` — the ratio is EXACTLY `(n-2)/(3n)`, whose supremum over
`n` is `1/3` (never attained, approached from below). This is the crisp statement that the depth-`2`
canonical shape carries a positive constant fraction of the Wick mass. -/
theorem ratio_two_limit_form (m : ℕ) :
    3 * (2 * m) * nrFull (2 * m) 2 = (2 * m - 2) * wickTwo (2 * m) := by
  rw [mul_right_comm]
  exact ratio_two_exact m

end ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31 in
#print axioms nrCore_two
open ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31 in
#print axioms nrCore_six
open ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31 in
#print axioms nrFull_two
open ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31 in
#print axioms ratio_two_exact
open ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31 in
#print axioms ratio_two_not_suppressed
open ArkLib.ProximityGap.Frontier.CharZeroHistogramShapeM31 in
#print axioms ratio_two_limit_form
