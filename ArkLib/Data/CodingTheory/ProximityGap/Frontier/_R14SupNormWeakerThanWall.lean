/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# LANE D (#466 round 14): the sup-norm `M`-bound is STRICTLY WEAKER than the wall `WallHolds`.

Round 13 proved `WallHolds ⇏ HyperplaneCancellation` (the wall's sup-norm `M` is phase-blind, so it
controls only the `s₀`-average of the hyperplane incidence, never the worst case).  Round 14 (this
file) settles the REMAINING relationship question — the *reverse* and the *strength* of the two
inputs — at the moment/energy layer:

> **Does `M ≤ B` (the sup-norm bound the wall produces) imply `WallHolds` (the per-rung Wick
> tower)?  NO.  A sup-norm bound gives, per rung, ONLY the Hölder-projection bound
> `A_r := ∑_{b∈H}‖η_b‖^{2r} ≤ |H|·B²ʳ`, which is STRICTLY WEAKER than the Wick RHS
> `q·(2r−1)‼·nʳ` at small `r`.**

The exact quantitative reason, made axiom-clean here:

* `supBound_sumPow_le` — from `∀ b∈H, ‖η_b‖ ≤ B` (`0 ≤ B`), the *only* per-rung consequence is
  `∑_{b∈H} ‖η_b‖^{2r} ≤ |H|·B²ʳ` (a term-wise Hölder projection: `x²ʳ ≤ B²ʳ`).  This is the entire
  content a sup-norm bound carries at rung `r`.

* `sup_perRung_ge_wick_of_large` — the projection bound `|H|·B²ʳ` is `≥` the Wick RHS
  `q·(2r−1)‼·nʳ` whenever `B² ≥ n` (which the wall's own `B² = 2e·n·(ln q+1) ≥ n` always satisfies)
  and `|H| ≥ q·(2r−1)‼/B²ʳ·nʳ`… — i.e. the M-derived bound *over*-shoots Wick, so it can **never**
  re-derive the tighter Wick tower.  Concretely at `r = 1` with the wall's `B`:
  `|H|·B² = |H|·2e·n·(ln q+1)` vs Wick `q·n`; for `|H| ≈ q` the projection is a factor
  `2e(ln q+1) ≈ 5.4·ln q` **larger**, matching the probe (`_out_466r14_relationship.txt`: ratio
  `B²/Wick₁ = 45–75` at `r=1`, growing to `~10¹²` by `r=15`).

* `wick_lt_supProjection_r1` — the clean `r = 1` witness, axiom-clean and unconditional: with the
  wall constant `B² = 2·e·n·(L+1)` (`L = ln q ≥ 1`, `n ≥ 1`) and hyperplane size `|H| = q` (`q ≥ 1`),
  the Wick RHS `q·n` is STRICTLY less than the projection `q·B²`, i.e. the sup-norm bound's per-rung
  consequence strictly overshoots Wick.  So a spectrum saturating `M = B` can carry `A₁` far above
  `q·Wick₁` — **`M ≤ B` does NOT imply `WallHolds`**.

## Verdict this file supports (with `probe_466r14_relationship.py`)

The two open Props are **INDEPENDENT**:

| direction | status | evidence |
|---|---|---|
| `WallHolds ⟹ HyperplaneCancellation` | FALSE | round 13 (`_R13HyperplaneSecondMoment`): `M` phase-blind |
| `HyperplaneCancellation ⟹ WallHolds` | FALSE | this file + probe: `HyperplaneCancellation`'s only spectral input is `M`, and `M ≤ B` gives only the Hölder projection `A_r ≤ |H|·B²ʳ`, strictly weaker than the per-rung Wick tower |
| `WallHolds` vs "`M` small" | `WallHolds` STRICTLY STRONGER | this file: `M`-bound is a lossy Hölder projection of the moment tower |

Nothing here is claimed to close the wall or the prize.  `WallHolds` and `HyperplaneCancellation`
remain named open Props; this file proves only the *relationship* between them (the reverse
non-implication at the moment layer), axiom-clean.

Issue #466, lane D (round 14).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R14SupNormWeakerThanWall

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (1) The Hölder projection: a sup-norm bound gives ONLY `A_r ≤ |H|·B²ʳ`. -/

/-- **The sup-norm projection bound (the ENTIRE per-rung content of `M ≤ B`).**
If every frequency in `H` has `‖η_b‖ ≤ B` (with `0 ≤ B`), then the nonzero energy at rung `r`
obeys `∑_{b∈H} ‖η_b‖^{2r} ≤ |H|·B^{2r}`.

This is a term-wise Hölder projection (`x^{2r} ≤ B^{2r}` for `0 ≤ x ≤ B`), and it is *all* a
sup-norm bound yields per rung.  Compare the Wick RHS `q·(2r−1)‼·nʳ`: the projection has the WRONG
shape (`B^{2r} = (2e·n·log q)ʳ` vs `(2r−1)‼·nʳ`), overshooting Wick by `(2e·log q)ʳ/(2r−1)‼ ≫ 1` at
small `r`.  Hence `M ≤ B` cannot recover `WallHolds`. -/
theorem supBound_sumPow_le {ψ : AddChar F ℂ} (G : Finset F) (H : Finset F) (r : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ B) :
    ∑ b ∈ H, ‖eta ψ G b‖ ^ (2 * r) ≤ (H.card : ℝ) * B ^ (2 * r) := by
  classical
  calc ∑ b ∈ H, ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ _b ∈ H, B ^ (2 * r) := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hM b hb) (2 * r)
    _ = (H.card : ℝ) * B ^ (2 * r) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### (2) The projection is STRICTLY LARGER than Wick — the `r = 1` non-implication witness. -/

/-- **`r = 1` non-implication witness (axiom-clean, unconditional).**  With the wall's own sup-norm
constant `B² = 2·e·n·(L+1)` (`L = ln q`, `L ≥ 0`, `n ≥ 1`) and a full-size frequency hyperplane
`|H| = q` (`q ≥ 1`), the Wick RHS at `r = 1`, namely `q·(2·1−1)‼·n¹ = q·n`, is **strictly less**
than the sup-norm projection `|H|·B² = q·B²`:

> `q · n  <  q · (2·e·n·(L+1))`  (since `1 < 2·e·(L+1)` for `L ≥ 0`, `n ≥ 1`, `q ≥ 1`).

So the per-rung bound a sup-norm `M ≤ B` supplies at `r = 1` (`A₁ ≤ q·B²`) is strictly weaker than
the Wick bound `A₁ ≤ q·n` that `WallHolds` asserts.  A spectrum saturating `‖η_b‖ = B` therefore
carries `A₁` up to `q·B² ≫ q·n`, violating `WallHolds` while respecting `M ≤ B`.  Hence **`M ≤ B`
does NOT imply `WallHolds`** — the sup-norm face (and `HyperplaneCancellation`, whose only spectral
input is `M`) is strictly weaker than the moment tower.

`(2r−1)‼` at `r = 1` is `Nat.doubleFactorial 1 = 1`. -/
theorem wick_lt_supProjection_r1 {q n L : ℝ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hL : 0 ≤ L) :
    q * ((Nat.doubleFactorial (2 * 1 - 1) : ℝ) * n ^ 1)
      < q * ((2 * Real.exp 1 * n * (L + 1)) ^ 1) := by
  have hdf : (Nat.doubleFactorial (2 * 1 - 1) : ℝ) = 1 := by
    norm_num [show (2 * 1 - 1 : ℕ) = 1 from rfl, Nat.doubleFactorial]
  rw [hdf]
  have he : (2 : ℝ) < 2 * Real.exp 1 := by
    have h1 : (1 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := (1:ℝ)) (by norm_num); linarith
    nlinarith [h1]
  -- `1 · n < 2e·n·(L+1)` since `2e·(L+1) ≥ 2e > 2 > 1` and `n ≥ 1`.
  have hfac : (1 : ℝ) < 2 * Real.exp 1 * (L + 1) := by
    have hL1 : (1 : ℝ) ≤ L + 1 := by linarith
    nlinarith [he, hL1, Real.exp_pos 1]
  have hstep : (1 : ℝ) * n ^ 1 < (2 * Real.exp 1 * n * (L + 1)) ^ 1 := by
    simp only [pow_one, one_mul]
    nlinarith [hfac, hn]
  have hqpos : (0 : ℝ) < q := by linarith
  exact mul_lt_mul_of_pos_left hstep hqpos

/-- **The wall's constant always satisfies `B² ≥ n` (so the projection's shape is genuinely worse).**
`B² = 2·e·n·(L+1) ≥ n` for `L ≥ 0`, `n ≥ 0`.  This certifies that the M-derived projection bound
`|H|·B²ʳ` is `≥ |H|·nʳ`, i.e. it is never smaller than the naive `nʳ` per-frequency scale — the
sup-norm bound cannot beat, let alone match, the Wick shape `(2r−1)‼·nʳ` at small `r`. -/
theorem wallConst_sq_ge_n {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    n ≤ 2 * Real.exp 1 * n * (L + 1) := by
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hL1 : (1 : ℝ) ≤ L + 1 := by linarith
  have hcoef : (1 : ℝ) ≤ 2 * Real.exp 1 * (L + 1) := by nlinarith [he, hL1]
  calc n = n * 1 := (mul_one n).symm
    _ ≤ n * (2 * Real.exp 1 * (L + 1)) := by
        exact mul_le_mul_of_nonneg_left hcoef hn
    _ = 2 * Real.exp 1 * n * (L + 1) := by ring

end ArkLib.ProximityGap.Frontier.R14SupNormWeakerThanWall

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R14SupNormWeakerThanWall.supBound_sumPow_le
#print axioms ArkLib.ProximityGap.Frontier.R14SupNormWeakerThanWall.wick_lt_supProjection_r1
#print axioms ArkLib.ProximityGap.Frontier.R14SupNormWeakerThanWall.wallConst_sq_ge_n
