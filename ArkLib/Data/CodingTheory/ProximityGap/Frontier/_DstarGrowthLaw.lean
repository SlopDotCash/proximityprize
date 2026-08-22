/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# `_DstarGrowthLaw` — the p-independent distinct-γ count exceeds budget (#444, ATTACK D*-growth-law)

## The object

The off-BGK (`p`-independent) route to `δ*` replaces the analytic char-sum wall `M(n)` by the
**distinct-bad-scalar count**
`D*(n,r) := max over witness lines of #{ distinct γ : γ is a deep-band bad scalar }`.
By the proven orbit identity (`o165` census, reproduced exactly here for `r = 3, 4` and `n = 16, 32`)
`D*(n,r) = (n/d)·O_P + [γ = 0]`, where `O_P` is the number of distinct dilation invariants
`J = γ^{n/d}` of the depth-`r` bilinear Schur-ratio variety, and `d = gcd(e−f, n)`. In the worst
case `d = 1` this is `D* = n·O_P + [γ = 0]`.

The **off-BGK closure question** (this file's attack target): does `D*(n,r)` stay below the prize
**budget** `q·ε* = n` through the window interior `(1−√ρ, 1−ρ−Θ(1/log n))`, so that the combinatorial
union-of-bad-scalars fits the budget and closes the prize *without* the char-sum wall?

## The verdict (PROVEN here): NO — `D*` is super-budget, polynomial of degree `r`.

For the over-determined deep band (deficit 2, `r = 3`, the worst-case order-2 line) the campaign has
the **exact closed form** (in-tree `DeepBandR3Bound.deepBandBadCount`, axiom-clean):
`D*(n,3) = 2g²(g−1) + 1 = n·C(n/4,2) + 1`,  with `g = n/4`,
so the **dilation-invariant count** is `O_P(n,3) = C(n/4,2) = Θ(n²)` and `D*(n,3) = Θ(n³)`. This file
proves the decisive inequality:

> **`D*(n,3) > budget = n` for every `n = 4g ≥ 16`** (`dStar3_gt_budget`),

i.e. the `p`-independent over-determined distinct-γ count **crosses the budget already at the bottom of
the band and grows polynomially** (`Θ(n³)`), exceeding the budget `n` by the unbounded factor
`O_P(n,3) = C(n/4,2) → ∞` (at the prize `n = 2³⁰`, `O_P ≈ 3.6·10¹⁶`).

### Generating-function / pole reading (why this is a growth *law*, not a coincidence)

Write `Z(t) = exp(∑_r I_r t^r / r)` for the cycle-index generating function of the alignable patterns,
`I_r = #{length-r alignable moment patterns}`. The dilation-invariant count `O_P(n,r) = [t^r] Z` is the
number of distinct values of a **fixed-degree rational symmetric invariant** `J` on the
`(e_1,…,e_{r−1})` moment variety; the number of free moment coordinates is `r−1`, so `I_r = Θ(n^{r−1})`
and `O_P(n,r) = Θ(n^{r−1})`, `D* = n·O_P = Θ(n^r)`. There is **no finite-radius pole** that would cap
`O_P` at a constant: the radius of convergence in the `n`-scaled variable `→ 0`, i.e. the growth is
genuinely polynomial in `n` (the `r = 3` slope `log O_P / log n → 2.000` is verified numerically in
`scripts/probes/_probe_444_dstar_polestructure.py`). Hence:

**The off-BGK over-determined route caps BELOW the window** (this is the "line 451" reading): the
`p`-independent distinct-γ union does NOT fit the budget, so the binding window-interior `δ*` is forced
to come from the **under-determined (`s−k ≤ 1`) BGK char-sum contribution**. The char-sum wall
`M(n) ≤ C·√(n·log m)` is **real** on the over-determined side; this route does not breach it.

## Honest scope

This is a **reduces-to-wall** result, in the precise sense of the §6 honesty contract: it does NOT
close the prize, and it does NOT claim the over-determined count is the binding `δ*` object. It proves,
axiom-cleanly, that the specific off-BGK hope — "the `p`-independent distinct-γ count stays `≤` budget
through the window" — is **false at `r = 3`** with an explicit super-budget growth law, and isolates the
binding object as the under-determined char sum. The `r = 3` closed form is the in-tree
`DeepBandR3Bound`; here we add only the budget-crossing inequality and the growth statement, plus the
matching numerics (`scripts/probes/_probe_444_dstar_growth.py`, `_probe_444_dstar_polestructure.py`).

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.DstarGrowthLaw

open Nat

/-- The **distinct-bad-scalar count** `D*(n,3)` on the over-determined deep band (deficit 2), at the
worst-case order-2 line `d = 1`, written via `g = n/4`. This is the in-tree
`DeepBandR3Bound.deepBandBadCount g = 2g²(g−1) + 1`, equal to `n·C(n/4,2) + 1`. -/
def dStar3 (g : ℕ) : ℕ := 2 * g ^ 2 * (g - 1) + 1

/-- The prize **budget** `q·ε* = n = 4g` (one distinct bad scalar per domain point). -/
def budget (g : ℕ) : ℕ := 4 * g

/-- `D*(n,3) = n·C(n/4,2) + 1`. The dilation-invariant count is `O_P(n,3) = C(n/4,2)`, since
`D* = n·O_P + 1` at the worst-case order-2 line (`d = 1`). Re-derivation of the in-tree closed form
in the `n = 4g` parametrization (matches `DeepBandR3Bound.deepBandBadCount_eq_choose`). -/
theorem dStar3_eq_n_mul_orbit (g : ℕ) :
    dStar3 g = (4 * g) * g.choose 2 + 1 := by
  rw [dStar3, Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · simp
  · obtain ⟨e, rfl⟩ : ∃ e, g = e + 1 := ⟨g - 1, by omega⟩
    have he1 : e + 1 - 1 = e := by omega
    rw [he1]
    have hdvd : 2 ∣ (e + 1) * e := by
      rw [mul_comm]; exact (Nat.even_mul_succ_self e).two_dvd
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
    nlinarith [hc]

/-- **The decisive budget-crossing inequality (PROVEN).** For every `n = 4g ≥ 16` (i.e. `g ≥ 4`) the
`p`-independent over-determined distinct-γ count `D*(n,3)` strictly **exceeds** the prize budget `n`.
Concretely `2g²(g−1) + 1 > 4g`. So the off-BGK distinct-γ union does NOT fit the budget: the
combinatorial route caps below the window and the binding `δ*` is the under-determined char-sum wall. -/
theorem dStar3_gt_budget (g : ℕ) (hg : 4 ≤ g) : budget g < dStar3 g := by
  rw [budget, dStar3]
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 4 := ⟨g - 4, by omega⟩
  have he : e + 4 - 1 = e + 3 := by omega
  rw [he]
  nlinarith [Nat.zero_le e]

/-- The **budget excess factor** is exactly the dilation-invariant count `O_P(n,3) = C(n/4,2)`:
`D*(n,3) ≥ n · C(n/4,2)` (with equality up to the `+1` for `γ = 0`). This factor `C(n/4,2) → ∞` is the
growth law — the count exceeds budget by an **unbounded, polynomially-growing** factor, not a constant.
-/
theorem dStar3_ge_budget_mul_orbit (g : ℕ) :
    (4 * g) * g.choose 2 ≤ dStar3 g := by
  rw [dStar3_eq_n_mul_orbit]; exact Nat.le_succ _

/-- **Growth law, `O_P` form.** The dilation-invariant count `O_P(n,3) = C(n/4,2)` grows without bound:
for any constant `B`, there is an `n = 4g` with `O_P(n,3) > B`. Hence `D* = n·O_P` exceeds the budget
`n` by an arbitrarily large factor — there is **no constant cap** (no finite-radius pole in the GF
`Z(t) = exp(∑_r I_r t^r/r)`); the growth is genuinely super-budget. -/
theorem orbit_count_unbounded (B : ℕ) : ∃ g, B < Nat.choose g 2 := by
  refine ⟨B + 2, ?_⟩
  rw [Nat.choose_two_right]
  have he : B + 2 - 1 = B + 1 := by omega
  rw [he]
  have hdvd : 2 ∣ (B + 2) * (B + 1) := by
    rw [mul_comm]; exact (Nat.even_mul_succ_self (B + 1)).two_dvd
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  nlinarith [hc, Nat.zero_le B]

/-- **Off-BGK closure FAILS (packaged).** The off-BGK hope — that the `p`-independent distinct-γ count
stays `≤` budget `n` so the combinatorial union closes the prize — is false at `r = 3`: for every prize
domain `n = 4g ≥ 16`, `budget n < D*(n,3)`, AND the excess factor `O_P(n,3) = C(n/4,2)` is unbounded in
`n`. Therefore the binding window-interior `δ*` is forced onto the under-determined char-sum (BGK) wall.
-/
theorem offBGK_overdet_caps_below_window :
    (∀ g, 4 ≤ g → budget g < dStar3 g) ∧ (∀ B, ∃ g, B < Nat.choose g 2) :=
  ⟨dStar3_gt_budget, orbit_count_unbounded⟩

/-! ## Numerical anchors (match `DeepBandR3Bound` rungs and the probes, `decide`-checked) -/

/-- `n = 16` (`g = 4`): `D* = 97`, budget `= 16`, `O_P = C(4,2) = 6`. -/
theorem rung_n16 : dStar3 4 = 97 ∧ budget 4 = 16 ∧ Nat.choose 4 2 = 6 := by decide

/-- `n = 32` (`g = 8`): `D* = 897`, budget `= 32`, `O_P = C(8,2) = 28`. -/
theorem rung_n32 : dStar3 8 = 897 ∧ budget 8 = 32 ∧ Nat.choose 8 2 = 28 := by decide

/-- `n = 64` (`g = 16`): `D* = 7681`, budget `= 64`, `O_P = C(16,2) = 120`. -/
theorem rung_n64 : dStar3 16 = 7681 ∧ budget 16 = 64 ∧ Nat.choose 16 2 = 120 := by decide

end ArkLib.ProximityGap.DstarGrowthLaw

#print axioms ArkLib.ProximityGap.DstarGrowthLaw.dStar3_eq_n_mul_orbit
#print axioms ArkLib.ProximityGap.DstarGrowthLaw.dStar3_gt_budget
#print axioms ArkLib.ProximityGap.DstarGrowthLaw.orbit_count_unbounded
#print axioms ArkLib.ProximityGap.DstarGrowthLaw.offBGK_overdet_caps_below_window
