/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The alignment-cocycle large-deviation gate (#407)

## Why this file exists

The proximity-prize floor needs a worst-case sup-norm bound on the dyadic
Gaussian-period envelope `M i = max_{b ≠ 0} |S_b(μ_{2^i})|`.  The single-level
`√2`-descent input `LocalAlignedChildSubmaximality` (an upper bound `M (i+1)^2 ≤
2 · M i ^2` at *every* level) is **refuted** worst-case
(`_DyadicPhaseChainingSubmaxRefuted.lean`): the realized per-level ratio
`r i = M (i+1) / M i` can reach almost `2` (the trivial child bound), measured at
`1.99` across all probed primes and `n ≤ 4096`
(`scripts/probes/probe_cocycle_worst_path.py`).

This file records the *correct* re-localization: the floor does **not** need a
uniform per-step bound; it needs a control on the **alignment cocycle**
`∏_j r j` along the whole tower — a worst-case-PATH (Lyapunov / large-deviation)
statement.  Empirically (same probe) the per-step ratios reach `2` but the
**geometric mean** of the realized cocycle is `≈ 1.50–1.54` — strictly below `2`,
slightly above `√2`, with the small excess over `√2` accounting *exactly* for the
`√(log(q/n))` polylog factor in the floor envelope
`M(2^K) ≍ √(2^K · log(q / 2^K))` (probe: `M / √(n log(q/n)) ∈ [1.34, 1.45]`).

So the genuine open input is a **geometric-mean bound on the cocycle**, NOT a
uniform-step bound.  This file:

* defines the cocycle and its geometric-mean budget over a tower window;
* proves the deterministic chaining lemma "geometric-mean budget ⟹ top-level
  bound" (it tolerates individual steps up to `2`, unlike the refuted uniform
  form — that is the whole point);
* names the prize-level large-deviation hypothesis `CocycleGeometricMeanLaw`
  and proves the conditional chain to the floor;
* records the refutation hook (a measured top level above the budget refutes the
  law) — so a future probe finding a sustained near-`2` path would fire here.

It contains no list-decoding vocabulary, no Johnson reduction, and no `sorry` /
`axiom`.  The single open input is `CocycleGeometricMeanLaw` (= the BGK/MRSS
incomplete-character-sum sup-norm bound, a recognized 25-year-open problem); this
file is the *closed deterministic consumer* for it.

## Relation to `_DyadicPhaseChaining.lean`

That file telescopes a *per-step* multiplicative recursion `Q (i+1) ≤ step i · Q i`.
The refutation shows no `step i ≤ 2` (equivalently `r i ≤ √2`) holds at every
level.  The present file telescopes a *product* (geometric-mean) hypothesis, which
is strictly weaker per-level and is the form consistent with the probe data.
The two are the multiplicative telescope viewed step-wise vs. path-wise.
-/

namespace ProximityGap.Frontier.DyadicCocycle

open Finset

/-- The alignment cocycle ratio at level `i`: `M (i+1) / M i`. -/
noncomputable def cocycle (M : ℕ → ℝ) (i : ℕ) : ℝ := M (i + 1) / M i

/--
The realized top level is the start level times the product of the cocycle ratios
over the window — the exact telescoping identity, valid whenever no intermediate
level vanishes.
-/
theorem level_eq_start_mul_cocycle_prod {M : ℕ → ℝ} {N0 : ℕ} (L : ℕ)
    (hpos : ∀ j, N0 ≤ j → j < N0 + L → M j ≠ 0) :
    M (N0 + L) = M N0 * ∏ j ∈ range L, cocycle M (N0 + j) := by
  induction L with
  | zero => simp
  | succ L ih =>
      have hposL : ∀ j, N0 ≤ j → j < N0 + L → M j ≠ 0 := by
        intro j hj hjlt
        exact hpos j hj (Nat.lt_trans hjlt (by omega))
      have hMNL : M (N0 + L) ≠ 0 := hpos (N0 + L) (by omega) (by omega)
      rw [prod_range_succ, ← mul_assoc, ← ih hposL]
      unfold cocycle
      rw [mul_div_assoc']
      have : M (N0 + L) * M (N0 + L + 1) / M (N0 + L) = M (N0 + L + 1) := by
        field_simp
      rw [show N0 + (L + 1) = N0 + L + 1 from by ring, this]

/--
**Geometric-mean (large-deviation) budget.**

`CocycleProductBudget M N0 L P` says the product of the cocycle ratios over the
length-`L` window starting at `N0` is at most `P`.  Equivalently the *geometric
mean* is at most `P^{1/L}`.  This is the worst-case-PATH object: it constrains the
whole path, not any single step, and so survives the per-step refutation.

In the intended prize instantiation `M i = max_{b≠0}|S_b(μ_{2^i})|`,
`P = (√2)^L · polylog(q/2^{N0+L})`, i.e. geometric mean `√2 · (polylog)^{1/L}`.
-/
def CocycleProductBudget (M : ℕ → ℝ) (N0 L : ℕ) (P : ℝ) : Prop :=
  ∏ j ∈ range L, cocycle M (N0 + j) ≤ P

/--
**Deterministic path chaining.**  A product (geometric-mean) budget on the
cocycle bounds the top level by `M N0 · P`, *with no per-step hypothesis*.

This is the key separation from the refuted uniform form: individual ratios
`cocycle M (N0+j)` may be as large as `2`; only their product is constrained.
Requires non-vanishing intermediate levels and a nonnegative start (the envelope
`M i = sup-norm ≥ 0`).
-/
theorem level_le_of_cocycleProductBudget {M : ℕ → ℝ} {N0 L : ℕ} {P : ℝ}
    (hstart : 0 ≤ M N0)
    (hpos : ∀ j, N0 ≤ j → j < N0 + L → M j ≠ 0)
    (hbudget : CocycleProductBudget M N0 L P) :
    M (N0 + L) ≤ M N0 * P := by
  have heq := level_eq_start_mul_cocycle_prod (M := M) (N0 := N0) L hpos
  rw [heq]
  exact mul_le_mul_of_nonneg_left hbudget hstart

/--
**Refutation hook.**  A measured top level above `M N0 · P` refutes the product
budget.  If a probe ever exhibits a frequency whose path sustains ratio near `2`
(so the product exceeds the `√2`-geometric-mean budget), this fires and the
candidate large-deviation law is falsified into `DISPROOF_LOG.md`.
-/
theorem not_cocycleProductBudget_of_level_gt {M : ℕ → ℝ} {N0 L : ℕ} {P : ℝ}
    (hstart : 0 ≤ M N0)
    (hpos : ∀ j, N0 ≤ j → j < N0 + L → M j ≠ 0)
    (hbad : M N0 * P < M (N0 + L)) :
    ¬ CocycleProductBudget M N0 L P := by
  intro hbudget
  exact not_lt_of_ge (level_le_of_cocycleProductBudget hstart hpos hbudget) hbad

/--
The geometric-mean phrasing of the budget: `(∏ r_j)^{1/L} ≤ G` (equivalently the
product is at most `G^L`).  Stated multiplicatively to avoid roots, with `G ≥ 0`.
-/
def CocycleGeometricMeanLaw (M : ℕ → ℝ) (N0 L : ℕ) (G : ℝ) : Prop :=
  0 ≤ G ∧ ∏ j ∈ range L, cocycle M (N0 + j) ≤ G ^ L

/--
The geometric-mean law is a product budget with `P = G^L`.
-/
theorem cocycleProductBudget_of_geometricMeanLaw {M : ℕ → ℝ} {N0 L : ℕ} {G : ℝ}
    (hlaw : CocycleGeometricMeanLaw M N0 L G) :
    CocycleProductBudget M N0 L (G ^ L) :=
  hlaw.2

/--
**Conditional chain to the floor envelope.**

If the cocycle geometric mean over the window is at most `G`, then the top level
is at most `M N0 · G^L`.  In the prize instantiation `N0 = 2`, `L = μ − 2`,
`2^{N0+L} = n`, and the floor `M(n) ≍ √(n log(q/n))` is recovered by taking
`G = √2 · (1 + Θ(1/μ))`: then `G^L = (√2)^L · (1+Θ(1/μ))^L → √(n/4) · polylog`,
matching the probe's `M / √(n log(q/n)) ∈ [1.34, 1.45]` and measured geometric
mean `≈ 1.50` (`= √2 · 1.06`, the `1.06^L` supplying the polylog).
-/
theorem floor_of_cocycleGeometricMeanLaw {M : ℕ → ℝ} {N0 L : ℕ} {G : ℝ}
    (hstart : 0 ≤ M N0)
    (hpos : ∀ j, N0 ≤ j → j < N0 + L → M j ≠ 0)
    (hlaw : CocycleGeometricMeanLaw M N0 L G) :
    M (N0 + L) ≤ M N0 * G ^ L :=
  level_le_of_cocycleProductBudget hstart hpos
    (cocycleProductBudget_of_geometricMeanLaw hlaw)

/--
**The uniform-step form is the special case `r_j ≤ G` at every level.**  This
records *why* the refuted input is strictly stronger than what the floor needs:
a per-step bound `cocycle M (N0+j) ≤ G` (with the ratios nonneg) implies the
geometric-mean law, but not conversely.  The probe shows the per-step bound fails
(`max step ≈ 1.99 > √2`) while the geometric-mean law plausibly holds
(`GM ≈ 1.50`).
-/
theorem cocycleGeometricMeanLaw_of_uniform_step {M : ℕ → ℝ} {N0 L : ℕ} {G : ℝ}
    (hG : 0 ≤ G)
    (hnonneg : ∀ j, j < L → 0 ≤ cocycle M (N0 + j))
    (hstep : ∀ j, j < L → cocycle M (N0 + j) ≤ G) :
    CocycleGeometricMeanLaw M N0 L G := by
  refine ⟨hG, ?_⟩
  calc ∏ j ∈ range L, cocycle M (N0 + j)
      ≤ ∏ _j ∈ range L, G := by
        apply prod_le_prod
        · intro j hj; exact hnonneg j (mem_range.mp hj)
        · intro j hj; exact hstep j (mem_range.mp hj)
    _ = G ^ L := by rw [prod_const, card_range]

/--
**Drift decomposition of the geometric mean.**  Writing `G = √2 · (1 + drift)`,
the top-level bound becomes `M N0 · (√2)^L · (1 + drift)^L`.  The `(√2)^L` factor
is the random-scale `√n` term; the entire excess over the floor is `(1+drift)^L`,
which must be `polylog(q/n)`.  This isolates the analytic content (`drift =
Θ(1/μ)` ⟺ `(1+drift)^L = polylog`) as the single open quantity.
-/
theorem floor_drift_form {M : ℕ → ℝ} {N0 L : ℕ} {drift : ℝ}
    (hstart : 0 ≤ M N0)
    (hpos : ∀ j, N0 ≤ j → j < N0 + L → M j ≠ 0)
    (hlaw : CocycleGeometricMeanLaw M N0 L (Real.sqrt 2 * (1 + drift))) :
    M (N0 + L) ≤ M N0 * (Real.sqrt 2 ^ L * (1 + drift) ^ L) := by
  have h := floor_of_cocycleGeometricMeanLaw hstart hpos hlaw
  rwa [mul_pow] at h

end ProximityGap.Frontier.DyadicCocycle

#print axioms ProximityGap.Frontier.DyadicCocycle.level_eq_start_mul_cocycle_prod
#print axioms ProximityGap.Frontier.DyadicCocycle.level_le_of_cocycleProductBudget
#print axioms ProximityGap.Frontier.DyadicCocycle.not_cocycleProductBudget_of_level_gt
#print axioms ProximityGap.Frontier.DyadicCocycle.cocycleProductBudget_of_geometricMeanLaw
#print axioms ProximityGap.Frontier.DyadicCocycle.floor_of_cocycleGeometricMeanLaw
#print axioms ProximityGap.Frontier.DyadicCocycle.cocycleGeometricMeanLaw_of_uniform_step
#print axioms ProximityGap.Frontier.DyadicCocycle.floor_drift_form
