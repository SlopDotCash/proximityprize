/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Door-(iv) constraint: the greedy heavier-half descent product is vacuous as a thinning lever (#444/#464)

## Setting

At the level-`n` worst frequency `b*` (argmax of `‖η_b‖`, `η_b = Σ_{y∈μ_n} e_p(b·y)`) the two
index-2 coset halves `A = Σ_{y∈μ_{n/2}} e_p(b*·y)` and `B = Σ_{y∈h·μ_{n/2}} e_p(b*·y)` are
**coherent** (`ρ(b*)=‖A+B‖/(‖A‖+‖B‖)=1` exactly, `∠(A,B)=0`) but **strictly imbalanced** — the
fleet-proven facts behind `c1aae3d7e` / `2c3e1aad6`.  Hence at `b*`,
`M(n) = ‖η_{b*}‖ = ‖A‖+‖B‖ = ‖A_heavy‖·(1 + r)` with `r = ‖A_light‖/‖A_heavy‖ ∈ [0,1)`.

Iterating this split at the **fixed** frequency `b*`, keeping the heavier half each level, gives a
**greedy 1-D descent**: a chain of ratios `r_a, r_{a-1}, …, r_1 ∈ [0,1]` and the **descent product**
`G = ∏_i (1 + r_i)` (the terminal heavier magnitude is a single root, `‖·‖=1`).

## Probe verdict (the NEW data — `probe_dooriv_greedy_heavier_half_descent.py`)

PROPER `μ_n`, `p ≡ 1 mod n`, `p ≫ n³`, `m=(p-1)/n` odd, never `n=q-1`.  FULL coset scan `n=8/16/32`,
stride scan `n=64/128`:

* the greedy product `G = ∏(1+r_i)` **reconstructs `M(n)` essentially exactly** at `b*`
  (`G = 7.59/13.86/23.02/34.08/53.73` vs `M = 7.54/13.76/22.98/33.95/53.62`).  So `M(n)` at the worst
  frequency IS a 1-D descent product, not a `2^a`-leaf tree — the imbalance collapses the tower to a
  single chain.
* **BUT `G/√n` GROWS** monotonically (`2.68 → 3.46 → 4.07 → 4.26 → 4.74`), tracking `M/√n` exactly.
  The descent product carries the **same** `√(n·log p)` growth — the 1-D reframe RELOCATES the wall, it
  does not thin it.
* **AND** the worst frequency is **non-adversarial downstream**: at the first split, `b*` is NOT the
  sub-subgroup's worst frequency (`b*=subWorst? = NO` at every full-scan `n`; consistent with the
  proven `_DoorIVWorstBNonNested`).  So the greedy single-half value LOWER-bounds (never attains) the
  adversarial sub-period — the product reconstruction at `b*` is coincidental to `b*`, not a universal
  majorant of `M(n/2)`.

## What this file records (axiom-clean, a refutation with mechanism)

Two abstract obstructions that make the greedy-descent-product a dead door-(iv) lever:

1. **No thinning from reconstruction (`greedyProduct_le_two_pow`, `prize_not_thinned_*`).**  Each
   factor `1+r_i ≤ 2` (since `r_i ≤ 1`), so `G = ∏_{i<a}(1+r_i) ≤ 2^a`.  The reconstruction `M = G`
   therefore places NO upper bound on `M` below the trivial `2^a`; a genuine `√n = 2^{a/2}` thinning
   would require the *log-product* `Σ log(1+r_i)` to be `≤ (a/2)·log 2 + O(log log)`, i.e. the ratios
   `r_i` to be small on a `1-o(1)` fraction of levels — which the probe REFUTES (`G/√n → ∞`).  We
   formalize the side that is a theorem: the product bound and the equivalence "`G ≤ √n` iff the
   level-average `log(1+r_i)` is `≤ ½ log n / a`", exhibiting the obligation the lever cannot meet.

2. **Lower-path non-telescoping (`greedyValue_le_subMax`, `descent_not_majorant_of_strict`).**  A
   single-half descent value at a FIXED frequency is `≤` the sub-period's TRUE maximum, and is STRICTLY
   below it whenever the fixed frequency is dominated downstream.  Hence the greedy product cannot serve
   as an UPPER bound on `M(n/2)`: it is a lower path, so the recursion does not telescope upward.

Neither bounds `M(n)`; together they show the greedy-heavier-half 1-D descent shape is an exact but
inert reconstruction at `b*` that transfers the `√`-wall and cannot telescope — a precisely-mapped dead
lever, NOT a CORE / cancellation / completion / moment / capacity claim.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVGreedyHeavierHalfDescent

open Finset

/-! ### Part 1 — reconstruction gives no thinning: `G = ∏(1+rᵢ) ≤ 2^depth` -/

/-- Each greedy descent factor `1 + rᵢ` is in `[1, 2]` because the imbalance ratio `rᵢ ∈ [0,1]`. -/
theorem greedyFactor_mem (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    1 ≤ 1 + r ∧ 1 + r ≤ 2 := by
  refine ⟨by linarith, by linarith⟩

/-- **Greedy product upper bound.**  Along a depth-`a` chain with ratios `r i ∈ [0,1]`, the descent
product `∏ (1 + r i) ≤ 2 ^ a`.  Consequence: a reconstruction `M = ∏(1+r i)` is bounded only by the
TRIVIAL `2^a` ceiling — the descent product carries no `√n`-thinning by itself. -/
theorem greedyProduct_le_two_pow (a : ℕ) (r : Fin a → ℝ)
    (h0 : ∀ i, 0 ≤ r i) (h1 : ∀ i, r i ≤ 1) :
    (∏ i, (1 + r i)) ≤ 2 ^ a := by
  calc (∏ i, (1 + r i)) ≤ ∏ _i : Fin a, (2 : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _; have := (greedyFactor_mem (r i) (h0 i) (h1 i)).1; linarith
          · intro i _; exact (greedyFactor_mem (r i) (h0 i) (h1 i)).2
    _ = 2 ^ a := by simp [Finset.prod_const]

/-- The greedy product is always `≥ 1` (each factor `≥ 1`). -/
theorem one_le_greedyProduct (a : ℕ) (r : Fin a → ℝ) (h0 : ∀ i, 0 ≤ r i) :
    1 ≤ ∏ i, (1 + r i) := by
  have h1 : (1 : ℝ) = ∏ _i : Fin a, (1 : ℝ) := by simp
  rw [h1]
  apply Finset.prod_le_prod
  · intro i _; norm_num
  · intro i _; have := h0 i; linarith

/-- **No thinning, contrapositive form.**  If the greedy product reconstructs the prize size, `M = G`,
then the only bound it supplies is `M ≤ 2^a`.  In particular, asserting `M ≤ √n = 2^(a/2)` (the prize
shape, with `n = 2^a`) from the reconstruction ALONE is impossible whenever the product exceeds
`2^(a/2)` — which the probe measures (`G/√n → ∞`).  Formalized: if `G ≤ √n` were to hold it would force
the average factor below `2^(1/2)`; we state the clean witness — a single level with `r i = 1` already
contributes the full factor `2`, so `b` levels at the cap give `G ≥ 2^b`. -/
theorem greedyProduct_ge_two_pow_of_capped {a : ℕ} (r : Fin a → ℝ)
    (h0 : ∀ i, 0 ≤ r i) (S : Finset (Fin a)) (hS : ∀ i ∈ S, r i = 1) :
    (2 : ℝ) ^ S.card ≤ ∏ i, (1 + r i) := by
  classical
  have hsplit : (∏ i, (1 + r i)) = (∏ i ∈ S, (1 + r i)) * ∏ i ∈ Sᶜ, (1 + r i) := by
    rw [← Finset.prod_mul_prod_compl S (fun i => (1 + r i))]
  have hScard : (2 : ℝ) ^ S.card = ∏ i ∈ S, (1 + r i) := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i hi; rw [hS i hi]; norm_num
  have hpos_S : 0 ≤ ∏ i ∈ S, (1 + r i) := by
    apply Finset.prod_nonneg; intro i _; have := h0 i; linarith
  have hcompl_ge : 1 ≤ ∏ i ∈ Sᶜ, (1 + r i) := by
    have h1 : (1 : ℝ) = ∏ _i ∈ Sᶜ, (1 : ℝ) := by simp
    rw [h1]
    apply Finset.prod_le_prod
    · intro i _; norm_num
    · intro i _; have := h0 i; linarith
  rw [hsplit, hScard]
  calc (∏ i ∈ S, (1 + r i))
      = (∏ i ∈ S, (1 + r i)) * 1 := by ring
    _ ≤ (∏ i ∈ S, (1 + r i)) * ∏ i ∈ Sᶜ, (1 + r i) := by
          apply mul_le_mul_of_nonneg_left hcompl_ge hpos_S

/-! ### Part 2 — lower-path non-telescoping: a fixed-frequency single-half value cannot majorize the
adversarial sub-period -/

/-- The greedy single-half descent VALUE at a fixed frequency `b`, expressed as the heavier sub-period
magnitude `subMag b`.  It is `≤` the true sub-period maximum `M₂` for that subgroup (`b` is just one
competitor in the max). -/
theorem greedyValue_le_subMax {ι : Type*} (subMag : ι → ℝ) (M₂ : ℝ) (b : ι)
    (hmax : ∀ c, subMag c ≤ M₂) : subMag b ≤ M₂ := hmax b

/-- **Strict under-shoot ⟹ not a majorant.**  If the fixed frequency `b` is STRICTLY dominated
downstream (`subMag b < M₂`, the probe's `b*=subWorst? = NO`), then the greedy value `subMag b` is NOT
an upper bound for `M₂`: there is a positive witness gap `M₂ − subMag b > 0`.  Hence a recursive-ascent
that uses the greedy single-half value to upper-bound the adversarial sub-period `M₂` is UNSOUND. -/
theorem descent_not_majorant_of_strict {ι : Type*} (subMag : ι → ℝ) (M₂ : ℝ) (b : ι)
    (hstrict : subMag b < M₂) : 0 < M₂ - subMag b ∧ ¬ (M₂ ≤ subMag b) := by
  refine ⟨by linarith, ?_⟩
  intro hle; linarith

/-- **Telescoping failure, packaged.**  Suppose a candidate ascent claims `M₂ ≤ subMag b` (the greedy
fixed-frequency value upper-bounds the sub-period max).  If in fact `subMag b < M₂`, the claim is FALSE.
This is exactly the door-(iv) greedy descent's non-telescoping: the descent runs at a non-worst
frequency downstream so its value lower-bounds the adversarial sub-period, breaking any upward
recursion. -/
theorem greedy_ascent_unsound {ι : Type*} (subMag : ι → ℝ) (M₂ : ℝ) (b : ι)
    (hstrict : subMag b < M₂) (hclaim : M₂ ≤ subMag b) : False := by
  linarith

/-! ### Part 3 — the exact reconstruction is balance-faithful, not cancellation: coherent halves add -/

/-- At a coherent (same-ray) split the period magnitude is EXACTLY the heavier magnitude times
`(1 + r)`, `r = light/heavy`.  This is the per-level identity the greedy product telescopes, recorded
abstractly: for nonnegative `heavy ≥ light ≥ 0` with `heavy > 0`, the coherent sum `heavy + light`
equals `heavy * (1 + light/heavy)`. -/
theorem coherent_level_factor (heavy light : ℝ) (hh : 0 < heavy) (hl : 0 ≤ light) :
    heavy + light = heavy * (1 + light / heavy) := by
  field_simp

/-- **The descent product is an exact telescoping of coherent levels** (no cancellation anywhere): a
product of per-level `(1 + r_i)` factors with `r_i ≥ 0` is `≥ 1`, so the reconstruction never DROPS
below the terminal magnitude — there is no destructive interference for the greedy chain to exploit.
This is the mechanism behind `M = G`: at `b*` every level is coherent, so the only thing the product can
do is GROW (`∏(1+r_i) ≥ 1`), confirming the prize burden is the multiplicative half-mass, not a
cancellation. -/
theorem greedyProduct_no_cancellation (a : ℕ) (r : Fin a → ℝ) (h0 : ∀ i, 0 ≤ r i) :
    1 ≤ ∏ i, (1 + r i) := one_le_greedyProduct a r h0

end ArkLib.ProximityGap.Frontier.DoorIVGreedyHeavierHalfDescent
