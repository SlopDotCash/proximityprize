/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# The far-line `c*(n)` 6-point table is asymptotically UNDER-DETERMINED (#444 ASYMPTOTIC-CLAIM GUARD)

## Why this file exists — bounding an asymptotic over-claim

`DecouplingCrossingDepthGrowsInN.lean` records the measured far-line max-over-directions crossing
offset on the `ρ = 1/4` axis as a **6-point table**

  `cStarQuarter(n) = 3, 4, 3, 4, 5, 5`  at  `n = 8, 12, 16, 20, 24, 32`,

and concludes (in prose + the framing of its theorems) the **asymptotic law** `c*(n)/n → 0`, hence
`δ*(n) = (1−ρ) − c*(n)/n → (1−ρ) = 3/4` (capacity) and "off-BGK survives the growth".

The prize dossier's **ASYMPTOTIC-CLAIM GUARD** (Shaw's "growth-law conflict resolved" #444 comment)
flags this reading as **not entailed by the data**: a sub-leading `O(log n)` dip in the small-`n`
tail is **not** a sub-linear *law*. The over-determined incidence decay is a SAT-then-cliff staircase
with a HARD **linear** cliff at the top witness size `s_top ≈ n/2` (DFT uncertainty on `ℤ_n`); if `s*`
hugs it then `m* = s* − k ≈ n/4` is **linear**, so `δ* → 1/2` (Johnson side), the *opposite* of the
capacity conclusion.

This file proves the **honest epistemic content** of that guard, as pure arithmetic on the table:

> **The 6-point table is asymptotically under-determined.** It is reproduced — within the very same
> `±1` parity granularity the prior file invokes for its `{3,4}` wobble — by BOTH
> * a bounded / sub-linear law (`A(n) = 4`, the `{3,4}` band centre, `A/n → 0`), AND
> * a genuinely **linear** law with positive slope (`B(n) = ⌊n/10⌋ + 2`, `B/n → 1/10 ≠ 0`).
>
> Two laws with **opposite asymptotic rates** fit the same six points. Therefore the data does **not**
> determine the asymptotic rate of `c*(n)`; in particular it does not entail `c*(n)/n → 0`. The prior
> file's `c*/n → 0 ⟹ δ* → capacity ⟹ off-BGK survives` is an **asymptotic over-claim**.

### Honest scope (rules 1, 3, 4, 6)
* **NOT a CORE closure** — BGK `M(n) ≤ C√(n·log(p/n))` stays OPEN. The genuine beyond-Johnson gap
  lives in the under-determined / agreement-sharing / BGK contribution, not in this combinatorial
  far-line face.
* **NOT a proof of the cliff.** The DFT-uncertainty bound is necessary-not-sufficient (c.348): it
  does **not** separate Johnson from floor as a theorem. We do **not** claim `s*` hugs the cliff —
  indeed the **pure** cliff law `⌊n/4⌋` *overshoots* this small-`n` table (`5 < ⌊32/4⌋ = 8`), i.e.
  the `O(log)` dip is real here; `lawCliff_overshoots` records that honestly. We claim only the weaker,
  fully-proven fact: a **positive-slope** linear law fits as well as a bounded one, so the rate is
  under-determined.
* **Refutation-with-constraint** (rule 4): a precisely-mapped over-claim with an explicit
  under-determination witness is a result.

Probe: `scripts/probes/probe_cstar_extrapolation_underdetermined.py` (both `A` and `B` fit, max
residual `≤ 1`; the pure cliff `⌊n/4⌋` does not fit — overshoots).

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/

namespace ArkLib.ProximityGap.CStarExtrapolationUnderdetermined

/-- The measured far-line crossing offset on the `ρ = 1/4` axis, the table from
`DecouplingCrossingDepthGrowsInN.cStarQuarter` (re-stated here so this file is self-contained):
`c*(n) = 3,4,3,4,5,5` at `n = 8,12,16,20,24,32`. -/
def cStar : ℕ → ℕ
  | 8  => 3
  | 12 => 4
  | 16 => 3
  | 20 => 4
  | 24 => 5
  | 32 => 5
  | _  => 0

/-- The set of measured abscissae. -/
def grid : Finset ℕ := {8, 12, 16, 20, 24, 32}

/-- A uniform "fits within `±1`" predicate: a law `f` reproduces `c*` at `n` to within one unit. -/
def FitsAt (f : ℕ → ℕ) (n : ℕ) : Prop := cStar n ≤ f n + 1 ∧ f n ≤ cStar n + 1

/-! ### Law A — the BOUNDED / sub-linear reading (`c*/n → 0`): the constant law `c* ≈ 4` -/

/-- The constant fit `A(n) = 4` (the file's own `{3,4}` band centre); `A/n → 0`. -/
def lawBounded (_n : ℕ) : ℕ := 4

/-- **Law A fits the table within `±1`.** For every grid `n`, `|c*(n) − 4| ≤ 1`. The bounded
(`c*/n → 0`) law reproduces all six measured values inside the `{3,4,5}` band. -/
theorem lawBounded_fits : ∀ n ∈ grid, FitsAt lawBounded n := by
  intro n hn
  simp only [grid, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h <;> subst h <;> (unfold FitsAt cStar lawBounded; decide)

/-! ### Law B — a genuinely LINEAR reading (`c*/n → 1/10 ≠ 0`): `c* ≈ ⌊n/10⌋ + 2` -/

/-- The linear fit `B(n) = ⌊n/10⌋ + 2` (slope `1/10`); `B/n → 1/10 ≠ 0`. -/
def lawLinear (n : ℕ) : ℕ := n / 10 + 2

/-- **Law B fits the table within `±1`.** For every grid `n`, `|c*(n) − (⌊n/10⌋+2)| ≤ 1`. The LINEAR
(positive-slope, `c*/n → 1/10`) law reproduces all six measured values inside the same `±1`
granularity as Law A. -/
theorem lawLinear_fits : ∀ n ∈ grid, FitsAt lawLinear n := by
  intro n hn
  simp only [grid, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h <;> subst h <;> (unfold FitsAt cStar lawLinear; decide)

/-! ### The under-determination — two OPPOSITE asymptotics fit the SAME six points -/

/-- **HEADLINE — the table is asymptotically under-determined.** Both the bounded law `A(n) = 4`
(`A/n → 0`) and the positive-slope linear law `B(n) = ⌊n/10⌋ + 2` (`B/n → 1/10 ≠ 0`) reproduce every
one of the six measured `c*` values within `±1` (the file's own parity granularity), and the two laws
genuinely diverge on the grid (e.g. their values pull apart as `n` grows). Two laws with *opposite*
asymptotic rates fit the same data, so the six points **do not determine** the asymptotic rate of
`c*(n)` — in particular they do not entail `c*(n)/n → 0`. -/
theorem table_underdetermined :
    (∀ n ∈ grid, FitsAt lawBounded n) ∧
    (∀ n ∈ grid, FitsAt lawLinear n) ∧
    -- the two laws are genuinely different functions on the grid (their gap is unbounded in n):
    (∀ B : ℕ, ∃ n, B < lawLinear n - lawBounded n) := by
  refine ⟨lawBounded_fits, lawLinear_fits, ?_⟩
  intro B
  refine ⟨10 * (B + 3), ?_⟩
  unfold lawLinear lawBounded
  omega

/-! ### The linear law is genuinely linear — `c*/n → 1/10`, NOT `→ 0` -/

/-- **The linear law has a fixed positive slope `1/10` (not `→ 0`).** As a rational identity, for
`10 ∣ n` and `n ≠ 0`, `(lawLinear n : ℚ)/n = 1/10 + 2/n`, whose limit is `1/10 ≠ 0`. The witnessing
algebraic fact: `10 · (lawLinear n − 2) = n`, so the leading term is `n/10`. -/
theorem lawLinear_slope (n : ℕ) (h : 10 ∣ n) : 10 * (lawLinear n - 2) = n := by
  obtain ⟨m, rfl⟩ := h
  unfold lawLinear
  omega

/-- **The linear-law ratio is `1/10 + 2/n` (a positive-floor rate).** For `10 ∣ n`, `n ≠ 0`,
`(lawLinear n : ℚ)/n = 1/10 + 2/n → 1/10 ≠ 0`. The formal witness that Law B's `c*/n` does NOT tend
to `0`, in contrast to Law A's `c*/n → 0`. -/
theorem lawLinear_ratio (n : ℕ) (h : 10 ∣ n) (hn : n ≠ 0) :
    (lawLinear n : ℚ) / (n : ℚ) = 1 / 10 + 2 / (n : ℚ) := by
  have hslope : 10 * (lawLinear n - 2) = n := lawLinear_slope n h
  have hge : 2 ≤ lawLinear n := by unfold lawLinear; omega
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hcast : (10 : ℚ) * ((lawLinear n : ℚ) - 2) = (n : ℚ) := by
    have : ((10 * (lawLinear n - 2) : ℕ) : ℚ) = (n : ℚ) := by exact_mod_cast hslope
    rwa [Nat.cast_mul, Nat.cast_sub hge, Nat.cast_ofNat, Nat.cast_ofNat] at this
  field_simp
  linarith

/-! ### Honesty record — the PURE cliff `⌊n/4⌋` OVERSHOOTS this table (the `O(log)` dip is real) -/

/-- **The pure cliff law `⌊n/4⌋` does NOT fit the table within `±1`.** At `n = 32` the pure
cliff-hugging defect is `⌊32/4⌋ = 8`, while `c*(32) = 5`, a gap of `3 > 1`. So `s*` does **not** hug
the cliff exactly at these small `n` — the `O(log n)` dip is genuinely present. We record this
honestly: the under-determination is between a *bounded* law and a *gentler* positive-slope linear law
(`⌊n/10⌋+2`), NOT a claim that the full `n/4` cliff fits. -/
theorem lawCliff_overshoots : ¬ (cStar 32 ≤ 32 / 4 + 1 ∧ 32 / 4 ≤ cStar 32 + 1) := by
  decide

/-! ### The δ* consequence — capacity vs Johnson-side trajectories diverge on the SAME table

`δ*(n)·n = (1−ρ)·n − c*(n) = (3/4)·n − c*(n)` on the `ρ = 1/4` axis.  Under Law A the defect is
`O(1)` so `δ* → 3/4` (capacity).  Under Law B the defect is `⌊n/10⌋+2 = Θ(n)` so `δ*·n = (3/4)n −
Θ(n)` stays a *positive fraction* below capacity, i.e. `δ*` does NOT approach `3/4`.  The two readings
give divergent `δ*` trajectories on the identical data. -/

/-- **The two readings give DIFFERENT `δ*` numerators.** At `n = 32`: under Law B the numerator is
`(3/4)·32 − (⌊32/10⌋+2) = 24 − 5 = 19`; under Law A it is `24 − 4 = 20`; and as `n` grows the Law-B
defect `⌊n/10⌋+2` grows linearly while Law A's stays `4`, so the gap between the two `δ*` numerators
is unbounded — the table cannot pin `δ*`'s limit. -/
theorem deltaStar_readings_diverge :
    (3 * (32 / 4)) - lawLinear 32 = 19 ∧
    (3 * (32 / 4)) - lawBounded 32 = 20 ∧
    (∀ B : ℕ, ∃ n, 10 ∣ n ∧ B < lawLinear n - lawBounded n) := by
  refine ⟨by decide, by decide, ?_⟩
  intro B
  refine ⟨10 * (B + 3), ⟨B + 3, by ring⟩, ?_⟩
  unfold lawLinear lawBounded
  omega

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}):
#print axioms lawBounded_fits
#print axioms lawLinear_fits
#print axioms table_underdetermined
#print axioms lawLinear_slope
#print axioms lawLinear_ratio
#print axioms lawCliff_overshoots
#print axioms deltaStar_readings_diverge

end ArkLib.ProximityGap.CStarExtrapolationUnderdetermined
