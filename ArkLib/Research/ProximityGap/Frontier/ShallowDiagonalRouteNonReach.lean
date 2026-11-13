/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaShallowTailUncond
import ArkLib.Data.CodingTheory.ProximityGap.MomentWickBridge

/-!
# The unconditional diagonal shallow-tail route has ZERO sub-`n` savings (#444)

`EtaShallowTailUncond.eta_pow_le_shallow_uncond` lands the **unconditional** per-order ceiling
`‖η_{b₀}‖^{2(r+1)} ≤ n^{2r}·(q − n)` for **every** order `r`, from the *thickness-blind* diagonal
additive-energy bound `E_r(G) ≤ |G|^{2r-1}` (no BGK, no Lam–Leung, no char-`p` energy transfer).
Its module doc asserts *qualitatively* that "as `r → ∞` it relaxes toward `M ≲ n`" and "the
unconditionally-reachable tail is `r = O(1)`" — but never lands the clean **global** boundary as a
theorem.

This file discharges that boundary. In the prize regime `n² < q − n` (i.e. `q > n² + n`, true for
`q = nᵝ`, `β ≥ 4`), the diagonal ceiling **strictly exceeds the trivial bound `M ≤ n` at every
finite order `r`**:

> **`shallow_pow_gt_card_pow`** — `n^{2(r+1)} < n^{2r}·(q − n)` (pure ℕ arithmetic).
> **`shallow_ceiling_gt_card`** (HEADLINE) — the diagonal-route norm ceiling
>   `R := (n^{2r}·(q − n))^{1/(2(r+1))}` satisfies `n < R` for **every** `r`.

So the unconditional diagonal route's best certificate over **all** `r` is the trivial `M ≤ n`
(`|μ_n|` itself): its infimum over `r` is exactly `n`, never beaten. The route has **zero**
`√`-cancellation; it falls short of the prize `M ≤ C√(n·log(q/n))` by the unbounded polynomial
factor `√(n / log(q/n))`. The cancellation the prize needs lives **entirely** in the gap between the
diagonal energy `E_r ≤ n^{2r-1}` and the BGK/Gaussian energy `E_r ≤ (2r-1)‼·nʳ` (the open char-`p`
energy transfer, `_AR_MomentOptimizedSupNorm` consumes the latter *conditionally*).

**Honesty / rule-3.** The diagonal energy bound `E_r ≤ n^{2r-1}` holds for **any** `G` (thickness-
blind), so this non-reach is an honest **negative boundary** of the route, NOT a thinness claim:
it neither proves nor disproves CORE. It precisely localises where the prize cannot come from.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.ShallowDiagonalRouteNonReach

/-- **The prize-regime gap, in ℕ.** Once `n² < q − n`, the diagonal ceiling's `2(r+1)`-th power
`n^{2r}·(q − n)` strictly exceeds the trivial bound's `2(r+1)`-th power `n^{2(r+1)}`, for **every**
order `r`. (Multiply `n² < q − n` by the positive `n^{2r}`; `n^{2r}·n² = n^{2(r+1)}`.) -/
theorem shallow_pow_gt_card_pow {n q : ℕ} (hn : 0 < n) (hreg : n ^ 2 < q - n) (r : ℕ) :
    n ^ (2 * (r + 1)) < n ^ (2 * r) * (q - n) := by
  have hpos : 0 < n ^ (2 * r) := pow_pos hn _
  have hstep : n ^ (2 * r) * n ^ 2 < n ^ (2 * r) * (q - n) :=
    Nat.mul_lt_mul_of_pos_left hreg hpos
  have hcollapse : n ^ (2 * r) * n ^ 2 = n ^ (2 * (r + 1)) := by
    rw [← pow_add]; ring_nf
  rwa [hcollapse] at hstep

/-- **The same gap, cast to ℝ** (the analytic ceiling lives in ℝ). -/
theorem shallow_pow_gt_card_pow_real {n q : ℕ} (hn : 0 < n) (hqn : n ≤ q)
    (hreg : n ^ 2 < q - n) (r : ℕ) :
    (n : ℝ) ^ (2 * (r + 1)) < (n : ℝ) ^ (2 * r) * ((q : ℝ) - (n : ℝ)) := by
  have hnat := shallow_pow_gt_card_pow hn hreg r
  have hcast : ((n ^ (2 * r) * (q - n) : ℕ) : ℝ)
      = (n : ℝ) ^ (2 * r) * ((q : ℝ) - (n : ℝ)) := by
    push_cast [Nat.cast_sub hqn]
    ring
  have h1 : ((n ^ (2 * (r + 1)) : ℕ) : ℝ) < ((n ^ (2 * r) * (q - n) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hcast] at h1
  simpa using h1

/-- **HEADLINE — the diagonal-route ceiling never beats the trivial bound `M ≤ n`.**
In the prize regime `n² < q − n`, the unconditional diagonal-route norm ceiling
`R := (n^{2r}·(q − n))^{1/(2(r+1))}` (the bound `EtaShallowTailUncond.eta_le_shallow_uncond_norm`
delivers, with `q = |F|`, `n = |G|`) satisfies `n < R` for **every** order `r`. Hence the best the
unconditional diagonal route certifies over all `r` is `M ≤ n = |μ_n|` (its infimum), never below —
**zero** sub-`n` savings, the full polynomial `√(n/log(q/n))` short of the prize. (Pure real-power
monotonicity on the ℝ gap; the analytic eta bound enters only to *name* `R` as the route's ceiling.)
-/
theorem shallow_ceiling_gt_card {n q : ℕ} (hn : 0 < n) (hqn : n ≤ q)
    (hreg : n ^ 2 < q - n) (r : ℕ) :
    (n : ℝ) < ((n : ℝ) ^ (2 * r) * ((q : ℝ) - (n : ℝ))) ^ ((2 * (r + 1) : ℕ)⁻¹ : ℝ) := by
  have hgap := shallow_pow_gt_card_pow_real hn hqn hreg r
  -- base of the rpow is `> n^{2(r+1)} ≥ 0`
  have hbasenn : (0 : ℝ) ≤ (n : ℝ) ^ (2 * r) * ((q : ℝ) - (n : ℝ)) :=
    le_of_lt (lt_of_le_of_lt (by positivity) hgap)
  set R : ℝ := ((n : ℝ) ^ (2 * r) * ((q : ℝ) - (n : ℝ))) ^ ((2 * (r + 1) : ℕ)⁻¹ : ℝ) with hR
  have hRnonneg : 0 ≤ R := by rw [hR]; exact Real.rpow_nonneg hbasenn _
  -- `R^{2(r+1)} = base` (mirror of EtaShallowTailUncond's root-extraction)
  have hRpow : R ^ (2 * (r + 1)) = (n : ℝ) ^ (2 * r) * ((q : ℝ) - (n : ℝ)) := by
    rw [hR]; exact Real.rpow_inv_natCast_pow hbasenn (by positivity)
  -- so `n^{2(r+1)} < R^{2(r+1)}`, and the strictly-monotone reverse gives `n < R`
  have hpow_lt : (n : ℝ) ^ (2 * (r + 1)) < R ^ (2 * (r + 1)) := by rw [hRpow]; exact hgap
  exact lt_of_pow_lt_pow_left₀ (2 * (r + 1)) hRnonneg hpow_lt

/-! ## Where the open BGK input first bites: the diagonal-vs-BGK energy crossover is at `r = 2`

The shallow route above uses the diagonal energy `E_r ≤ n^{2r-1}`; the BGK/Gaussian route
(`_AR_MomentOptimizedSupNorm`, which *does* reach the prize shape `√(2e·n·ln q)`) uses
`E_r ≤ (2r-1)‼·nʳ = doubleFactOdd r · nʳ`. The diagonal bound is strictly *weaker* (larger) than
the BGK bound exactly when `n^{2r-1} > doubleFactOdd r · nʳ`, i.e. `n^{r-1} > doubleFactOdd r`.

Probe (`probe_diag_bgk_crossover.py`, `n=2^2..2^30`): the crossover order is `r₀ = 2` for **every**
`n ≥ 4` — at `r = 1` the two bounds are *equal* (`n¹ = doubleFactOdd 1 · n¹ = n`), and at `r = 2`
the diagonal already strictly exceeds BGK (`n³ > 3n²` ⟺ `n > 3`). So there is **no** order `r ≥ 2`
at which the unconditional diagonal bound matches BGK: the open BGK input bites *immediately*, from
`r = 2` on. This pins precisely where the shallow route's deficiency (the headline `inf_r R = n`)
originates — there is no nontrivial unconditional rung where it could have helped. -/

open ArkLib.ProximityGap.MomentWickBridge in
/-- **At `r = 1`, the diagonal and BGK energy ceilings coincide.** `doubleFactOdd 1 · n¹ = n =
n^{2·1-1}`. (`E_1 ≤ n` either way — the Parseval rung, where the unconditional route loses nothing.) -/
theorem diag_eq_bgk_at_one (n : ℕ) :
    doubleFactOdd 1 * n ^ 1 = n ^ (2 * 1 - 1) := by
  simp [doubleFactOdd_one]

open ArkLib.ProximityGap.MomentWickBridge in
/-- **At `r = 2`, the diagonal ceiling STRICTLY exceeds the BGK ceiling, for every `n > 3`.**
`doubleFactOdd 2 · n² = 3n² < n³ = n^{2·2-1}` ⟺ `3 < n`. So already at the first non-Parseval rung
the unconditional diagonal bound is strictly looser than BGK — the open BGK input bites from `r = 2`. -/
theorem diag_gt_bgk_at_two {n : ℕ} (hn : 3 < n) :
    doubleFactOdd 2 * n ^ 2 < n ^ (2 * 2 - 1) := by
  have hdf : doubleFactOdd 2 = 3 := by decide
  rw [hdf]
  have h1 : n ^ (2 * 2 - 1) = n ^ 2 * n := by ring
  rw [h1]
  have hpos : 0 < n ^ 2 := pow_pos (by omega) 2
  calc 3 * n ^ 2 = n ^ 2 * 3 := by ring
    _ < n ^ 2 * n := Nat.mul_lt_mul_of_pos_left hn hpos

end ArkLib.ProximityGap.ShallowDiagonalRouteNonReach

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.ShallowDiagonalRouteNonReach.shallow_pow_gt_card_pow
#print axioms ArkLib.ProximityGap.ShallowDiagonalRouteNonReach.shallow_pow_gt_card_pow_real
#print axioms ArkLib.ProximityGap.ShallowDiagonalRouteNonReach.shallow_ceiling_gt_card
#print axioms ArkLib.ProximityGap.ShallowDiagonalRouteNonReach.diag_eq_bgk_at_one
#print axioms ArkLib.ProximityGap.ShallowDiagonalRouteNonReach.diag_gt_bgk_at_two
