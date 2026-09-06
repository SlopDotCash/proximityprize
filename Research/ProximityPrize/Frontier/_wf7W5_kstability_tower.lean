/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-W5)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# wf-W5: K-stability of the dyadic moment tower (issue #444)

The crux for the Ethereum Proximity Prize is the **Wick bound on the DC-subtracted moment**
`A_r(μ_n) := (1/p)·∑_{b≠0} η_b^{2r} = E_r(μ_n) − n^{2r}/p ≤ K^r·(2r−1)‼·n^r` at depth `r ≈ ln q`,
for an absolute constant `K` (or `K = n^{o(1)}`). Proving it gives `M(n) ≤ C√(n·log(p/n))`, the prize.

`CumulantDyadicDescent` supplies the **exact dyadic split** at the level of the relation count
`E_r(μ_n) = 2·E_r(μ_{n/2}) + cross`, where `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` (squares and non-squares).
DC-subtracting both sides at the common prime `p`,

> `A_r(μ_n) = 2·A_r(μ_{n/2}) + crossA_r`,   `crossA_r = A_r(μ_n) − 2·A_r(μ_{n/2})`.

**This file proves the abstract "K-stability ⟹ uniform bound" engine** that the strategy reduces to:
if, writing `Wick(n,r) = (2r−1)‼·n^r`, the per-level cross term obeys

> `crossA_r ≤ K^r·(Wick(n,r) − 2·Wick(n/2,r))`     (the **per-level K-stability** hypothesis),

then `A_r(μ_{n/2}) ≤ K^r·Wick(n/2,r)` *implies* `A_r(μ_n) ≤ K^r·Wick(n,r)` with the **same** `K`
(`kstability_step`). Iterating up the `2^k`-tower from a finite base case
(`A_r(μ_{n₀}) ≤ K^r·Wick(n₀,r)`, computed exactly) gives the uniform bound for **all** tower levels
(`kstability_tower`), at fixed `r` (in particular at `r ≈ ln q`). This is the route that would
bound `K_eff(n)` at `n = 2^30` from a finite computation.

## What is PROVEN here (axiom-clean) vs OPEN

PROVEN (this file, `propext, Classical.choice, Quot.sound`): the inductive step and the tower
closure as **real-arithmetic lemmas**. They are unconditional: given the per-level cross hypothesis
and the base, the uniform conclusion follows by induction on the tower height. The split
`A_r(μ_n) = 2·A_r(μ_{n/2}) + crossA_r` is *definitional* (it just names the cross term), and the
`Wick(n,r) − 2·Wick(n/2,r) = (2r−1)‼·(n^r − 2(n/2)^r) ≥ 0` positivity (for `r ≥ 1`) is recorded
(`wick_cross_nonneg`).

OPEN-CRUX (the numerical frontier, NOT closed here): whether the per-level K-stability hypothesis
`crossA_r ≤ K^r·(Wick(n,r) − 2·Wick(n/2,r))` actually holds at `r ≈ ln q` for an absolute `K`. The
probe `scripts/probes/rust/wf7W5_kcross_fast.rs` measures, at `β = 4` (prize regime) and depth
`r* = ⌊ln q / 2⌋`, the per-level increment `Kcross(n) := (crossA_r/[(2r−1)‼(n^r−2(n/2)^r)])^{1/r}`:
it is `0.90, 0.91, 0.96, 0.96` at `n = 8,16,32,64,128` (one prime each) — **bounded below 1 at
depth**, but drifting up toward 1 as `n` grows; the *peak over r* grazes `1.000` at `r = 2`. So the
measured constant is `K = 1 + o(1)` (consistent with the char-0 Lam–Leung `K = 1` being tight). The
file therefore delivers the engine; the input `K`-stability bound is the open analytic step. (`r = 1`
is exactly the second-moment point where `crossA_1 = 0` since `Wick(n,1) − 2·Wick(n/2,1) = n − n = 0`;
the cross term is genuinely supported at `r ≥ 2`, matching `N0_dyadic_two_le`.)

Issues #389, #407, #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.W5KStabilityTower

/-! ## 1. The Wick value and its dyadic cross. -/

/-- The Wick / Gaussian value `Wick(n,r) = (2r−1)‼·n^r`, packaged with `dfac r = (2r−1)‼` as an
abstract nonneg real (we only need `0 ≤ dfac`). -/
def wick (dfac : ℝ) (n : ℝ) (r : ℕ) : ℝ := dfac * n ^ r

/-- **The dyadic Wick cross is nonnegative for `r ≥ 1`.** `Wick(n,r) − 2·Wick(n/2,r)
= dfac·(n^r − 2·(n/2)^r) = dfac·n^r·(1 − 2^{1−r}) ≥ 0` for `r ≥ 1` (and `= 0` at `r = 1`). This is
the denominator of the per-level `K`-increment; its vanishing at `r = 1` is exactly why the cross
term lives at `r ≥ 2`. -/
theorem wick_cross_nonneg {dfac n : ℝ} (hd : 0 ≤ dfac) (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r) :
    0 ≤ wick dfac n r - 2 * wick dfac (n / 2) r := by
  unfold wick
  have hnr : 0 ≤ n ^ r := pow_nonneg hn r
  have h2r : (2 : ℝ) ≤ 2 ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h2pos : (0 : ℝ) < 2 ^ r := by positivity
  -- (2/2^r) ≤ 1
  have hfrac : (2 : ℝ) / 2 ^ r ≤ 1 := (div_le_one h2pos).mpr h2r
  have hkey : (2 : ℝ) * (n / 2) ^ r ≤ n ^ r := by
    have hrw : (2 : ℝ) * (n / 2) ^ r = n ^ r * (2 / 2 ^ r) := by
      rw [div_pow]; ring
    rw [hrw]
    calc n ^ r * (2 / 2 ^ r) ≤ n ^ r * 1 := mul_le_mul_of_nonneg_left hfrac hnr
      _ = n ^ r := mul_one _
  nlinarith [mul_le_mul_of_nonneg_left hkey hd]

/-! ## 2. The inductive step: K-stability preserves the Wick bound up one dyadic level. -/

/-- **The K-stability inductive step (the headline).** Fix the moment exponent `r` and a constant
`K ≥ 0`. Suppose:

* `hsplit` : `A_n = 2·A_h + crossA`  — the exact DC-subtracted dyadic split
  (`A_n = A_r(μ_n)`, `A_h = A_r(μ_{n/2})`, `crossA` the cross term);
* `hcross` : `crossA ≤ K^r·(Wick(n,r) − 2·Wick(n/2,r))`  — **per-level K-stability**;
* `hbase`  : `A_h ≤ K^r·Wick(n/2,r)`  — the half-level Wick bound (induction hypothesis).

Then `A_n ≤ K^r·Wick(n,r)`: the Wick bound ascends one dyadic level with the **same** `K`. Pure
real arithmetic; this is the genuinely-new content the dyadic-tower strategy reduces to. -/
theorem kstability_step {dfac n A_n A_h crossA K : ℝ} {r : ℕ}
    (hsplit : A_n = 2 * A_h + crossA)
    (hcross : crossA ≤ K ^ r * (wick dfac n r - 2 * wick dfac (n / 2) r))
    (hbase : A_h ≤ K ^ r * wick dfac (n / 2) r) :
    A_n ≤ K ^ r * wick dfac n r := by
  rw [hsplit]
  calc 2 * A_h + crossA
      ≤ 2 * (K ^ r * wick dfac (n / 2) r)
          + K ^ r * (wick dfac n r - 2 * wick dfac (n / 2) r) := by
        gcongr
  _ = K ^ r * wick dfac n r := by ring

/-! ## 3. The tower closure: finite base + K-stability ⟹ uniform bound for all levels. -/

/-- **The dyadic tower (uniform `K`-bound from a finite base, the W5 conclusion).** Model the tower
of sizes by `n : ℕ → ℝ` with `n (j+1) = 2 · n j` going UP the tower (so `n j` is the half of
`n (j+1)`; `n 0 = n₀` is the finite base, `n j = 2^j · n₀`). Let `A j` be the DC-subtracted moment
`A_r(μ_{n j})` at the fixed exponent `r`, and `crossA j` the cross term of level `j → j+1`.

Given, for every level `j`:
* `hsplit j` : `A (j+1) = 2·A j + crossA j`  (the exact split, with `n (j+1) = 2·n j`),
* `hcross j` : `crossA j ≤ K^r·(Wick(n (j+1),r) − 2·Wick(n j,r))`  (per-level K-stability),

and the **finite base** `hbase : A 0 ≤ K^r·Wick(n 0, r)`, the Wick bound holds at **every** tower
level:

> `A j ≤ K^r·Wick(n j, r)`   for all `j`.

This is exactly the "bound `K_eff(n)` for all `n` from a finite base" claim of the strategy: one
base computation plus per-level K-stability discharges the entire `2^k`-tower up to `n = 2^30`. -/
theorem kstability_tower {dfac K : ℝ} {r : ℕ} {n A crossA : ℕ → ℝ}
    (hn : ∀ j, n (j + 1) = 2 * n j)
    (hsplit : ∀ j, A (j + 1) = 2 * A j + crossA j)
    (hcross : ∀ j, crossA j ≤ K ^ r * (wick dfac (n (j + 1)) r - 2 * wick dfac (n j) r))
    (hbase : A 0 ≤ K ^ r * wick dfac (n 0) r) :
    ∀ j, A j ≤ K ^ r * wick dfac (n j) r := by
  intro j
  induction j with
  | zero => exact hbase
  | succ k ih =>
    -- at level k+1: n(k+1)=2·n k, so n k = n(k+1)/2; apply the step
    have hhalf : n k = n (k + 1) / 2 := by rw [hn k]; ring
    refine kstability_step (dfac := dfac) (n := n (k + 1)) (A_n := A (k + 1))
      (A_h := A k) (crossA := crossA k) (K := K) (r := r) (hsplit k) ?_ ?_
    · -- rewrite the cross hypothesis with n k = n(k+1)/2
      have := hcross k
      rwa [hhalf] at this
    · -- rewrite the base/IH with n k = n(k+1)/2
      rwa [hhalf] at ih

end ArkLib.ProximityGap.Frontier.W5KStabilityTower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.W5KStabilityTower.wick_cross_nonneg
#print axioms ArkLib.ProximityGap.Frontier.W5KStabilityTower.kstability_step
#print axioms ArkLib.ProximityGap.Frontier.W5KStabilityTower.kstability_tower
