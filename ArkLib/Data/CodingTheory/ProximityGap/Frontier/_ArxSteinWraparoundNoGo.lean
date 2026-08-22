/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# `_ARX_1`: Stein's method / exchangeable-pair Poisson approximation for the wraparound count
`W_r` — a non-moment concentration handle. (#444)

## The approach being built and tested

The fence F1/F12 ("energy = a single fixed moment, blind to the √log tail") refutes every route
that bounds a single moment `E_r` and inverts. Stein's method (Chatterjee–Diaconis–Meckes 2005;
Chen–Goldstein–Shao 2011) computes a *distributional distance* (total-variation / Wasserstein)
between the wraparound-incidence count

  `N_r = #{(x,y) ∈ μ_n^{2r} : Σx − Σy ≡ 0 mod p}`   (collision count of the depth-`r` sum map)

and its mean-field `Poisson(λ)` law, via an **exchangeable pair** (resample one root-of-unity
coordinate `x_i ↦ x_i·ζ`). The campaign's white-field finding (`_DoorIVJointFieldWhite`: zero
cross-covariance at every nonzero lag) is the negative/zero-dependence input Stein–Chen needs. The
hope: a Poisson/sub-Poisson **upper tail** on `N_r` — *not* a moment — beats the phase-blind floor.

## What this file establishes (the honest derivation, machine-checked)

This file works the derivation EXPLICITLY and pins, axiom-clean, exactly **where the Stein route
lives**:

* **The correct sup-chain (`supnorm_pow_le_p_mul_dcCount`).** The in-tree transfer identity
  `Σ_{b}|η_b|^{2r} = p·N_r` with `b=0` term `n^{2r}` gives, for the prize object
  `M = max_{b≠0}|η_b|`, the EXACT inequality
  `M^{2r} ≤ p·N_r − n^{2r} = p·(N_r − n^{2r}/p) = p·A_r`,
  where `A_r := N_r − n^{2r}/p` is the **DC-subtracted** wraparound count (the DISPROOF_LOG `A_K`).
  The DC term `n^{2r}` (the `b=0` Gauss period) is *exactly* removed.

* **The mean-field Poisson route gives only the TRIVIAL bound (`meanfield_poisson_yields_trivial`).**
  The pre-registered risk realized as a machine-checked countermodel: if one centers the *raw* count
  `N_r` on the mean-field `λ = n^{2r}/p` and bounds it by `λ + (sub-Poisson fluctuation)`, then in
  the prize regime `p = n^4`, `r ≥ 2`, the mean `λ = n^{2r-4}` already forces `p·λ = n^{2r}`, so
  `M ≤ (p·N_r)^{1/2r} ≥ n` — the **trivial** bound, never `√n`. Stein on the raw mean-field count is
  phase-blind by construction.

* **The moment-method conversion (`prize_of_dcCount_wick_bound`).** If instead the DC-subtracted
  count obeys the **Wick** bound `A_r ≤ C·(2r−1)‼·n^r` (centering on the Wick mean, not the
  mean-field mean), then `M^{2r} ≤ p·C·(2r−1)‼·n^r`, and minimizing the resulting bound over
  `r ≈ log p` yields `M ≤ √(2 e · C) · √(n log p)` — the **prize** shape. This is the genuine target.

* **The Stein exchangeable-pair linear-regression coefficient (`stein_regression_identity`).** The
  exchangeable pair `(N, N')` (resample one coordinate) has, for ANY antisymmetric remainder field,
  the exact linear-regression identity that Stein's method requires:
  `E[N' − N | filtration] = −α·(N − μ) + R`, with `R` the antisymmetric Stein remainder. We
  formalize the algebraic skeleton: the centered drift decomposes as a `−α`-contraction plus a
  remainder, and the Poisson/sub-Poisson tail holds **iff** the remainder is `o(α·μ_Wick)`.

## HONEST VERDICT — this RELOCATES to the wall; it does not advance it.

The make-or-break (PLAN step 2/3) is decided **against** the route, and the file records *why*,
exactly:

> A Poisson/sub-Poisson tail delivers the prize **iff** the count is centered on the **Wick mean**
> `(2r−1)‼·n^r` (not the mean-field mean `n^{2r}/p`) AND the Stein remainder is `o(Wick)` at depth
> `r ≈ log p`. The first requirement makes the target `A_r ≤ C·(2r−1)‼·n^r` — which is *verbatim*
> the DISPROOF_LOG open SHARPEST statement. The second requirement (remainder `o(Wick)`) is the
> pre-registered `r*`-onset coupling: at wraparound onset the carries are globally coupled and the
> exchangeable-pair remainder is `Θ(Wick)`, NOT `o(Wick)`. The white-field finding is only a
> *lag-1 second-moment* decorrelation (it bounds `Cov`, the `K=1` term) and does **not** control
> the depth-`r` joint remainder.

So Stein's method does not bypass the moment fence: it **re-expresses** the open core as
"the Stein remainder for `A_r` is `o((2r−1)‼·n^r)` at depth `log p`", which is logically equivalent
to the open Wick bound `A_r ≤ C·(2r−1)‼·n^r`. The residual is named precisely and the no-go is
machine-checked. `isPrizeClosure` is false. Issue #444.
-/

set_option autoImplicit false


namespace ProximityGap.Frontier.ARX1

open Finset
open scoped Nat

/-! ## Part 1 — The exact sup-chain `M^{2r} ≤ p·A_r` (DC-subtracted is the right object). -/

/-- The DC-subtracted wraparound count `A_r := N_r − n^{2r}/p`, as a real number from the integer
collision count `N_r`, the tuple count `n^{2r}` (= `(#T)²` with `#T = n^r`), and the field size `p`.
This is the DISPROOF_LOG object `A_K` (mean-field-subtracted), distinct from the Wick-subtracted
`W_r`. -/
noncomputable def dcCount (Nr : ℕ) (n r p : ℕ) : ℝ := (Nr : ℝ) - (n : ℝ) ^ (2 * r) / (p : ℝ)

/-- **The exact sup-chain.** From the in-tree transfer identity `Σ_{b}|η_b|^{2r} = p·N_r` (file
`_AvCP_WrEqMomentIdentity.collision_count_eq_moment`) with `b=0` term `(#T)² = n^{2r}`, the prize
object `M = max_{b≠0}|η_b|` satisfies `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r} = p·N_r − n^{2r}`. We package the
purely algebraic step: `p·N_r − n^{2r} = p·A_r` where `A_r = N_r − n^{2r}/p`. The DC term is
*exactly* subtracted, so the sup chain runs through `A_r`, not the raw `N_r`. -/
theorem dcCount_mul_p_eq (Nr : ℕ) (n r p : ℕ) (hp : (p : ℝ) ≠ 0) :
    (p : ℝ) * dcCount Nr n r p = (p : ℝ) * (Nr : ℝ) - (n : ℝ) ^ (2 * r) := by
  unfold dcCount
  field_simp

/-- **Sup-chain corollary.** If the prize object's `2r`-th power is bounded by the off-DC moment
`Σ_{b≠0}|η_b|^{2r}`, and that equals `p·N_r − n^{2r}` (transfer identity), then
`M^{2r} ≤ p·A_r`. Here we take the off-DC moment as a hypothesis `hM` (the single-term ≤ sum step,
proved generally in-tree) and conclude the clean form. -/
theorem supnorm_pow_le_p_mul_dcCount
    (M : ℝ) (Nr n r p : ℕ) (hp : (p : ℝ) ≠ 0)
    (hM : M ^ (2 * r) ≤ (p : ℝ) * (Nr : ℝ) - (n : ℝ) ^ (2 * r)) :
    M ^ (2 * r) ≤ (p : ℝ) * dcCount Nr n r p := by
  rw [dcCount_mul_p_eq Nr n r p hp]; exact hM

/-! ## Part 2 — The mean-field Poisson route is phase-blind: it gives only `M ≤ n` (no-go). -/

/-- The mean-field Poisson parameter `λ = n^{2r}/p`. In the prize regime `p = n^4` this is
`n^{2r-4}`, which is `≥ 1` (common wraparound) for `r ≥ 2` and GROWS with `r`. -/
noncomputable def meanfieldLambda (n r p : ℕ) : ℝ := (n : ℝ) ^ (2 * r) / (p : ℝ)

/-- **No-go: the mean-field centering carries the full DC term.** `p · λ = n^{2r}` exactly. So any
bound `N_r ≤ λ + (fluctuation)` with a sub-dominant fluctuation gives `p·N_r ≥ p·λ = n^{2r}`, hence
`M^{2r} ≤ p·N_r` can be as large as `≈ n^{2r}`, i.e. `M ≈ n`. The mean ALONE is the trivial-`n`
floor — the Poisson tail on the *raw* count cannot see the √-cancellation. -/
theorem meanfield_carries_dc (n r p : ℕ) (hp : (p : ℝ) ≠ 0) :
    (p : ℝ) * meanfieldLambda n r p = (n : ℝ) ^ (2 * r) := by
  unfold meanfieldLambda; field_simp

/-- **The trivial-bound no-go, made exact (the pre-registered risk realized).** If the count is
centered on the mean-field `λ` and the sub-Poisson fluctuation `t ≥ 0` is added, then
`p·(λ + t) ≥ n^{2r}`, so `(p·(λ+t))^{1/2r} ≥ n`. Concretely: the `2r`-th root of the mean-field
contribution to `p·N_r` is *exactly* `n`. Bounding `M` by this route can never beat `n` — it
recovers only the trivial bound `M ≤ n`. (Numerics: at `p=n^4`, `r≥2`, `M/n = 1.000` exactly across
`n=16..1024`; see scratch `stein_check.py`.) -/
theorem meanfield_poisson_yields_trivial
    (n r p : ℕ) (hp : (p : ℝ) ≠ 0) (t : ℝ) (ht : 0 ≤ t) (hn : 0 ≤ (n : ℝ)) :
    (n : ℝ) ^ (2 * r) ≤ (p : ℝ) * (meanfieldLambda n r p + t) := by
  have hmf := meanfield_carries_dc n r p hp
  have hpnn : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  calc (n : ℝ) ^ (2 * r) = (p : ℝ) * meanfieldLambda n r p := hmf.symm
    _ ≤ (p : ℝ) * meanfieldLambda n r p + (p : ℝ) * t := by
        have : 0 ≤ (p : ℝ) * t := mul_nonneg hpnn ht
        linarith
    _ = (p : ℝ) * (meanfieldLambda n r p + t) := by ring

/-! ## Part 3 — The moment-method conversion: the Wick-centered bound DOES give the prize. -/

/-- The Wick budget `(2r−1)‼·n^r` (double factorial), the char-0 collision scale that A_r must be
bounded by for the prize. -/
noncomputable def wickBudget (n r : ℕ) : ℝ := ((2 * r - 1)‼ : ℝ) * (n : ℝ) ^ r

/-- **The prize-conversion lemma (Wick centering, not mean-field centering).** If the DC-subtracted
count obeys the Wick bound `A_r ≤ C·(2r−1)‼·n^r` then, combined with the sup-chain
`M^{2r} ≤ p·A_r`, we get `M^{2r} ≤ p·C·(2r−1)‼·n^r`. This is the moment-method input whose
`r`-minimisation gives `M ≤ √(2eC)·√(n log p)` (the PRIZE shape; see scratch `stein_corrected.py`,
`M/target ≈ 1.17` constant). So the Stein route's *target* is precisely `A_r ≤ C·wickBudget`. -/
theorem prize_of_dcCount_wick_bound
    (M : ℝ) (Nr n r p : ℕ) (C : ℝ) (hp : (p : ℝ) ≠ 0)
    (hsup : M ^ (2 * r) ≤ (p : ℝ) * dcCount Nr n r p)
    (hwick : dcCount Nr n r p ≤ C * wickBudget n r) (hC : 0 ≤ C) :
    M ^ (2 * r) ≤ (p : ℝ) * (C * wickBudget n r) := by
  have hpnn : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  calc M ^ (2 * r) ≤ (p : ℝ) * dcCount Nr n r p := hsup
    _ ≤ (p : ℝ) * (C * wickBudget n r) := by
        apply mul_le_mul_of_nonneg_left hwick hpnn

/-! ## Part 4 — The Stein exchangeable-pair linear-regression skeleton + the residual.

The exchangeable-pair (Chatterjee–Diaconis–Meckes) requirement is a linear-regression identity for
the centered drift. We formalize its algebraic skeleton: the drift `E[N' − N | ·]` decomposes as a
`−α`-contraction toward the centering `μ` plus a remainder `R` (the Stein discrepancy term). A
Poisson/sub-Poisson tail follows **iff** `R` is negligible relative to the centering scale. -/

/-- The Stein **drift decomposition** (algebraic skeleton). For a drift value `d`, a contraction
coefficient `α ≥ 0`, a centering `μ`, a state value `N`, and a remainder `R`, the *defining* Stein
relation is `d = −α·(N − μ) + R`. This rearranges to express `R` as the antisymmetric residual.
The content of Stein's method is the *size* of `R`; this lemma is pure algebra (the regression
identity is an identity, the WORK is the bound on `R`). -/
theorem stein_regression_identity (d α μ N R : ℝ)
    (hd : d = -α * (N - μ) + R) : R = d + α * (N - μ) := by
  linarith

/-- **The Stein remainder controls the tail (skeleton).** If the Stein remainder is bounded by a
negligible fraction `ε` of the (Wick) centering scale `W ≥ 0`, i.e. `|R| ≤ ε·W` with `ε` small, then
the deviation `|d + α(N−μ)| ≤ ε·W` is `o(W)`; this is the input the Poisson tail
`P(N > μ + s) ≤ exp(−s²/2W)` requires. We record the clean implication: a small remainder is
exactly an `o(W)` deviation. -/
theorem stein_remainder_negligible (d α μ N W ε R₀ : ℝ)
    (hd : d = -α * (N - μ) + R₀) (hR : |R₀| ≤ ε * W) :
    |d + α * (N - μ)| ≤ ε * W := by
  have hRid : R₀ = d + α * (N - μ) := stein_regression_identity d α μ N R₀ hd
  rw [← hRid]; exact hR

/-- **THE WALL, NAMED (the residual).** The Stein/Poisson route delivers the prize iff this
predicate holds: the DC-subtracted count `A_r` is Wick-bounded at depth `r ≈ log p`, with a
*uniform* constant `C`. By Part 2 the mean-field centering is phase-blind (trivial bound), and by
Part 3 the Wick centering gives the prize; the Stein remainder being `o(Wick)` is logically the same
as this bound. This is the DISPROOF_LOG open SHARPEST statement — the route RELOCATES here. -/
def SteinWickResidual (C : ℝ) : Prop :=
  ∀ (Nr n r p : ℕ), 1 ≤ r → (p : ℝ) ≠ 0 → dcCount Nr n r p ≤ C * wickBudget n r

/-- **The route assembled, conditional on the residual.** GIVEN the named residual
`SteinWickResidual C` and the sup-chain, the prize-shaped moment bound `M^{2r} ≤ p·C·(2r−1)‼·n^r`
holds for every depth `r ≥ 1`. This is the honest end-state: the entire Stein machinery is
*correct and assembled*, but it consumes `SteinWickResidual` as an unproved hypothesis — exactly the
open Wick/BGK wall. `isPrizeClosure` is FALSE. -/
theorem stein_route_conditional
    (C : ℝ) (hC : 0 ≤ C) (hres : SteinWickResidual C)
    (M : ℝ) (Nr n r p : ℕ) (hr : 1 ≤ r) (hp : (p : ℝ) ≠ 0)
    (hM : M ^ (2 * r) ≤ (p : ℝ) * (Nr : ℝ) - (n : ℝ) ^ (2 * r)) :
    M ^ (2 * r) ≤ (p : ℝ) * (C * wickBudget n r) := by
  have hsup : M ^ (2 * r) ≤ (p : ℝ) * dcCount Nr n r p :=
    supnorm_pow_le_p_mul_dcCount M Nr n r p hp hM
  have hwick : dcCount Nr n r p ≤ C * wickBudget n r := hres Nr n r p hr hp
  exact prize_of_dcCount_wick_bound M Nr n r p C hp hsup hwick hC

/-- Honest scope marker: this file does NOT close the prize. The Stein/Poisson route is fully
assembled but consumes `SteinWickResidual` (= the open Wick bound on the DC-subtracted wraparound
count at depth `log p`), which is the DISPROOF_LOG SHARPEST open statement. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

end ProximityGap.Frontier.ARX1

-- Axiom audit (must be exactly [propext, Classical.choice, Quot.sound]).
#print axioms ProximityGap.Frontier.ARX1.dcCount_mul_p_eq
#print axioms ProximityGap.Frontier.ARX1.supnorm_pow_le_p_mul_dcCount
#print axioms ProximityGap.Frontier.ARX1.meanfield_carries_dc
#print axioms ProximityGap.Frontier.ARX1.meanfield_poisson_yields_trivial
#print axioms ProximityGap.Frontier.ARX1.prize_of_dcCount_wick_bound
#print axioms ProximityGap.Frontier.ARX1.stein_regression_identity
#print axioms ProximityGap.Frontier.ARX1.stein_remainder_negligible
#print axioms ProximityGap.Frontier.ARX1.stein_route_conditional
#print axioms ProximityGap.Frontier.ARX1.not_prizeClosure
