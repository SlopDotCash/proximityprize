/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OffBGK_DegBadRGrowingSlack
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR5Bound

/-!
# LANE C (#444): the deep-rung degree certificate, extended to `r = 6, 7` (MEASURED + structural)

## Where this picks up

`_OffBGK_DegBadRGrowingSlack` settled the growing-slack sub-lead (A) at the PROVEN shallow rungs
(`g = n/4`):

| rung | `deg(#bad_r)` in `g` | `deg(O_r)` (orbit count) |
|---|---|---|
| `r = 3` | `3 = r`   | `2 = r-1` |
| `r = 4` | `4 = r`   | `3 = r-1` |
| `r = 5` | `4 = r-1` (the DROP) | `3 = r-2` |

(`#bad_5` drops one degree below `r` because the `r = 5` maximizer is the half-order `d = n/2`
resonance line `(x^{n/2+1}, x^{n-1})`, not the full-order order-2 line of `r = 3, 4`.)

LANE C asks: as `r` grows past `5`, does `deg(O_r)` stay `< r` (growing-slack persists) or does the
degree CATCH UP to `r` (slack saturates)?  We answer it with the residual-determinant ground-truth
kernel (`scripts/probes/genlaw/o191_plateau/fast_orbits_gen.c`, faithful BabyBear
`p = 2013265921`, `p² ≫ C(n, r+1)`, so the count is the char-0 structural value) extended to
`r = 6, 7` on the prize tower `n ∈ {16, 32, 64}`.

## The MEASURED data (exact-integer, kernel-faithful; probe `probe_laneC_deg_r6r7.py`)

Maximizing `2`-monomial line `(x^e, x^f)` and the deep-band count `#bad_r` (band `a = r+1`):

| `r` | `n = 16` (`g=4`) | `n = 32` (`g=8`) | `n = 64` (`g=16`) | maximizer family (`n ≥ 32`) |
|---|---|---|---|---|
| `6` | `113` (`d=8`)  | `5921` (`d=32`)  | `52353` (`d=64`)  | full-order `(n/2+1, n-6)` |
| `7` | `225` (`d=16`) | `16545` (`d=32`) | (`a=8`, kernel-heavy) | full-order `(n/2+2, n-1)` |

with the orbit-size factorization `#bad_r = 1 + d · full_orb` (the `+1` is the singleton `γ = 0`):

* `r = 6` dominant-family `full_orb (= O_6)`:  `g = 8 → 185`,  `g = 16 → 818`.
* `r = 7` dominant-family `full_orb (= O_7)`:  `g = 8 → 517`.

## The HONEST verdict (two-sided, the LANE C answer)

**THE MAXIMIZER FAMILY RE-SELECTS up the tower.**  At `n = 16` the `r = 6` worst line is the
half-order `d = 8` resonance (`#bad = 113`); at `n = 32, 64` the worst line FLIPS to a full-order
`d = n` line `(x^{n/2+1}, x^{n-6})`.  So the `g = 4` point belongs to a DIFFERENT resonance family
than `g = 8, 16` — there is **no single uniform polynomial** through the three max-over-lines
points (exactly the warning of `threadA_degree_verdict.py`: "the max RE-SELECTS the strong
resonance line at each `r`").  This is why `r = 6, 7` admit no clean closed form (unlike `r = 3, 4,
5`, whose maximizer family is stable across the measured tower).

**Within the asymptotically-dominant (full-order) family the degree stays `≪ r` — the slack
GROWS.**  The dominant-family orbit count `O_6` grows by `818/185 = 4.42 ≈ 2^{2.14}` per
`g`-doubling, i.e. `deg(O_6) ≈ 2–3` in `g`, far below `r = 6` (consistent with the proven pattern
`deg(O_3,O_4,O_5) = 2,3,3` CONTINUING to `deg(O_6) = 3`, NOT catching up to `r`).  Equivalently
`deg(#bad_6) = deg(O_6) + 1 ≈ 3–4 ≪ 6`.  The budget `K_r(g) = 2^r · C(2g, r)` is degree `r` in `g`,
so the slack `K / #bad` strictly GROWS:

* `r = 6`: `K(g=8)/#bad = 512512 / 5921 = 86.6×`  →  `K(g=16)/#bad = 57996288 / 52353 = 1108×`.

**LANE C answer (precise):** `deg(O_r) < r` CONTINUES to hold at `r = 6` (growing slack persists;
the degree does NOT catch up to `r`), BUT it is no longer a CLEAN integer-pinned closed form, because
the maximizer family is no longer stable on the measured tower — only `deg(O_r) ≤ r - 1` is
certified (two-point dominant-family slope `2^{2.14}` per doubling, well under `r = 6`), not an
exact polynomial like `r = 3, 4, 5`.

## What this file PROVES (axiom-clean, structural)

Per the `_OffBGK` caveat: even `deg(O_r) < r` for ALL `r` does NOT bound `m*` — that needs the
DEEP-rung `r ≈ log n` DIAGONAL, not a per-rung degree.  So this is a **per-rung degree certificate**,
NOT a `δ*`/`m*` pin.  The provable content is the GROWING-SLACK MECHANISM in clean `ℕ`-arithmetic:

> If the rung-`r` orbit count is bounded by a fixed polynomial of degree `< r` in `g`, then for
> every target ratio `T` there is a threshold `g₀` beyond which `K_r(g) ≥ T · (#orbit count)` — the
> budget-to-count slack is unbounded (grows without bound).

We package this against the explicit budget `K_r(g) = 2^r · C(2g, r)`, whose degree is exactly `r`
(`deepBandBudget_five` ties it to the in-tree `DeepBandR5.deepBandBudget5`), and the named
hypothesis `OrbitDegLeRSubOne` recording the measured dominant-family degree bound.

Character-sum-free, char-agnostic, `p`-independent.  Does **not** touch CORE
`M(μ_n) ≤ C·√(n·log(p/n))`.

Probe: `scripts/probes/probe_laneC_deg_r6r7.py` (re-derives the measured `r = 6, 7` counts, the
maximizer-family crossover, and the growing slack ratios over the kernel data; NEVER `n = q-1`).
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.LaneCDegR6R7

open ArkLib.ProximityGap
open ArkLib.ProximityGap.OffBGKDegBadR

/-! ## Part A — the budget `K_r(g) = 2^r · C(2g, r)` (the measured object)

The rung-`r` deep-band budget, identical to the in-tree `DeepBandR5.deepBandBudget5` at `r = 5`.
NOTE (honest): `K_r` is degree `r` in `g` but with a SMALL leading coefficient `4^r / r!` (since
`C(2g, r) ≈ (2g)^r / r!`).  The growing-slack mechanism therefore is NOT `g^r ≤ K_r` (false for
large `r`, `4^r/r! → 0`); it is the genuine `deg(K_r) = r` vs `deg(O_r) ≤ r-1` SEPARATION captured
abstractly in Part B, then instantiated with the measured `r = 6` data in Part C. -/

/-- The rung-`r` deep-band budget `K_r(g) = 2^r · C(2g, r)` (matches `deepBandBudget5` at `r = 5`). -/
def deepBandBudget (r g : ℕ) : ℕ := 2 ^ r * (2 * g).choose r

/-- Sanity: `deepBandBudget 5` is the in-tree `DeepBandR5.deepBandBudget5`. -/
theorem deepBandBudget_five (g : ℕ) : deepBandBudget 5 g = DeepBandR5.deepBandBudget5 g := rfl

/-! ## Part B — the GROWING-SLACK mechanism (abstract, fully proven)

The honest, character-free, `p`-independent statement of sub-lead (A) at any rung.  We model the
two measured quantities abstractly:

* `count g` — the rung-`r` orbit count `O_r(g)`, MEASURED to satisfy `count g ≤ c₁ · g^d` for a
  fixed `d < r` (a degree-`< r` polynomial bound; `d = r-1` is the certified dominant-family slope).
* `budget g` — the rung-`r` budget `K_r(g)`, satisfying `budget g ≥ c₂ · g^{d+1}` for some `c₂ > 0`
  (it is genuinely degree `r > d`, so degree `≥ d+1`).

Then the slack `budget / count` is UNBOUNDED: for every target `T`, eventually `budget ≥ T·count`.
This is the precise sense in which "`deg(count) < deg(budget)` ⟹ growing slack".  Pure `ℕ`. -/

/-- **(B.1) Growing slack from a degree gap.**  If `count g ≤ c₁ · g^d` and `budget g ≥ c₂ · g^(d+1)`
with `c₂ ≥ 1` and `c₁ ≥ 1`, then for every target multiplier `T`, there is a threshold `g₀` such
that for all `g ≥ g₀` the budget dominates `T` copies of the count:
`T · count g ≤ budget g`.

Witness `g₀ = T * c₁ + 1`: for `g ≥ g₀` we have `T · c₁ ≤ g - 1 < g`, so
`T · count g ≤ T · c₁ · g^d ≤ (g) · g^d = g^(d+1) ≤ c₂ · g^(d+1) ≤ budget g`. -/
theorem growing_slack_of_degree_gap
    (count budget : ℕ → ℕ) (c₁ c₂ d : ℕ)
    (hc₂ : 1 ≤ c₂)
    (hcount : ∀ g, count g ≤ c₁ * g ^ d)
    (hbudget : ∀ g, c₂ * g ^ (d + 1) ≤ budget g) :
    ∀ T : ℕ, ∃ g₀, ∀ g, g₀ ≤ g → T * count g ≤ budget g := by
  intro T
  refine ⟨T * c₁ + 1, fun g hg => ?_⟩
  -- T * count g ≤ T * c₁ * g^d ≤ g * g^d = g^(d+1) ≤ c₂ * g^(d+1) ≤ budget g
  have h1 : T * count g ≤ T * (c₁ * g ^ d) := Nat.mul_le_mul_left _ (hcount g)
  have h2 : T * (c₁ * g ^ d) = (T * c₁) * g ^ d := by ring
  have h3 : (T * c₁) * g ^ d ≤ g * g ^ d := Nat.mul_le_mul_right _ (by omega)
  have h4 : g * g ^ d = g ^ (d + 1) := by rw [pow_succ]; ring
  have h5 : g ^ (d + 1) ≤ c₂ * g ^ (d + 1) := Nat.le_mul_of_pos_left _ (by omega)
  calc T * count g ≤ (T * c₁) * g ^ d := by rw [← h2]; exact h1
    _ ≤ g * g ^ d := h3
    _ = g ^ (d + 1) := h4
    _ ≤ c₂ * g ^ (d + 1) := h5
    _ ≤ budget g := hbudget g

/-! ## Part C — the named measured hypotheses for `r = 6` and the instantiated slack

We record the MEASURED dominant-family degree bound for `r = 6` as a named `Prop` (the kernel data:
`O_6(g=8) = 185 ≤ g^3 = 512`, `O_6(g=16) = 818 ≤ g^3 = 4096`, consistent with `deg(O_6) = 3 =
r - 3 < r`), and instantiate `growing_slack_of_degree_gap` to get unbounded `r = 6` slack from it.

These are HYPOTHESES (the all-`g` degree bound is the open growth-law input, certified only at the
two measured points `g = 8, 16`); we name them precisely, exactly as `_OffBGK_DegBadRGrowingSlack`
names `OrbitDegreeBelowFold` for the all-`r` case. -/

/-- **(C) `OrbitDegLeRSubOne O r c d` — the named measured degree bound.**  The rung-`r` orbit count
`O` is bounded by `c · g^d` with `d < r`.  MEASURED at `r = 6` with `(c, d) = (1, 3)` at the two
dominant-family points `g = 8, 16` (`185 ≤ 8³`, `818 ≤ 16³`); the all-`g` form is the open growth
law.  When it holds with a budget of strictly larger degree, `growing_slack_of_degree_gap` gives the
unbounded slack. -/
def OrbitDegLeRSubOne (O : ℕ → ℕ) (r c d : ℕ) : Prop := d < r ∧ ∀ g, O g ≤ c * g ^ d

/-- **(C.1) The measured `r = 6` degree bound IMPLIES growing slack**, given a degree-`(d+1)` budget
lower bound.  This is the clean LANE C conclusion: a rung-`6` orbit count of degree `≤ d` (`d = 3`
measured), against a budget of degree `≥ d+1`, has unbounded budget-to-count slack — the
growing-slack signal persists at `r = 6`.  (Conditional on the named all-`g` bounds, exactly as the
shallow rungs reduce to `OrbitDegreeBelowFold`.) -/
theorem r6_growing_slack
    (O budget : ℕ → ℕ) (c c₂ d : ℕ)
    (hdeg : OrbitDegLeRSubOne O 6 c d)
    (hc₂ : 1 ≤ c₂)
    (hbudget : ∀ g, c₂ * g ^ (d + 1) ≤ budget g) :
    ∀ T : ℕ, ∃ g₀, ∀ g, g₀ ≤ g → T * O g ≤ budget g :=
  growing_slack_of_degree_gap O budget c c₂ d hc₂ hdeg.2 hbudget

/-- **(C.2) Non-vacuity: the measured `r = 6` dominant-family points satisfy `O_6(g) ≤ g^3`.**
The two kernel-measured dominant-family orbit counts (`g = 8 → 185`, `g = 16 → 818`) are each below
`g^3` (`512`, `4096`), witnessing that the named `OrbitDegLeRSubOne O₆ 6 1 3` predicate is
consistent (degree `3 < 6`) — the growing-slack horn is on the right (orbit) side at `r = 6`. -/
theorem r6_measured_points_below_cubic :
    (185 : ℕ) ≤ 8 ^ 3 ∧ (818 : ℕ) ≤ 16 ^ 3 := ⟨by decide, by decide⟩

/-- **(C.3) The measured `r = 6` slack ratios GROW** (the headline LANE C datum, as a `ℕ` fact).
`K_6(8) = 2^6·C(16,6) = 512512` against `#bad = 5921` (ratio `> 86`); `K_6(16) = 2^6·C(32,6) =
57996288` against `#bad = 52353` (ratio `> 1107`).  The slack multiplier strictly increases
`86 → 1107`, the degree-gap signature.  (`deepBandBudget 6 8 = 512512`, `deepBandBudget 6 16 =
57996288`.) -/
theorem r6_slack_grows :
    86 * 5921 ≤ deepBandBudget 6 8 ∧ 1107 * 52353 ≤ deepBandBudget 6 16 := by
  refine ⟨?_, ?_⟩ <;> · rw [deepBandBudget]; decide

end ArkLib.ProximityGap.LaneCDegR6R7

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.LaneCDegR6R7.deepBandBudget_five
#print axioms ArkLib.ProximityGap.LaneCDegR6R7.growing_slack_of_degree_gap
#print axioms ArkLib.ProximityGap.LaneCDegR6R7.r6_growing_slack
#print axioms ArkLib.ProximityGap.LaneCDegR6R7.r6_measured_points_below_cubic
#print axioms ArkLib.ProximityGap.LaneCDegR6R7.r6_slack_grows
