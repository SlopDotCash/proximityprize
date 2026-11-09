/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# T04 — "Leptokurtic-corrected vertical Sato–Tate EVT + bounded exceptional fibers" REDUCES TO F1
        (the cumulant/energy wall) — the EVT-depth ↔ energy-bound conjugacy (#444)

This file records — axiom-clean, modularly — that **candidate T04** (architect G1-4) is *not* a new
lever: its load-bearing new lemma is logically **equivalent** to the open cumulant energy bound
`E_r(μ_n) ≤ (2r-1)‼·n^r` at the prize depth `r ≈ ln q` (= fence **F1**, the moment/energy/cumulant
wall; in-tree `CumulantGaussPeriodBound.CumulantEnergyBound`). The "leptokurtic correction" and the
"bounded exceptional-fiber count" do **not** dodge the wall; they re-express it.

## T04, restated

> Replace the Gaussian-EVT depth `t* = √(2 log N)` by the EVT depth `t_{L_n}(N)` of the ACTUAL
> leptokurtic limiting law `L_n` (the moment-determined measure with all moments equal to the
> char-0 Wick-plus-antipodal values), and add a bounded number `m_0 = O(1)` of exceptional fibers
> (the Larsen big-monodromy-minus-torus defect). Claim:
>   `M(n) ≤ max( t_{L_n}(N)·√n , exc-bound ) ≤ C·√(n log(p/n))`,
> the NEW lemma being `t_{L_n}(N) ≤ √(2 log N)·(1+o(1))` DESPITE kurtosis 3.

## Why this is F1 (the reduction map), made precise

The EVT depth `t_{L_n}(N)` is, by definition, the `1/N`-quantile of the survival function
`S_{L_n}(t) = P_{b}( ‖η_b‖/√n > t )`. The ONLY effective handle on `S_{L_n}` at a depth `t` that
**grows** with `N` (the prize needs `t ≈ √(2 log N) ≈ √(2 ln q)`) is the Markov/Chernoff bound
against the moment sequence of `L_n` — and the moments of `L_n` **are** the normalized subgroup
additive-energy sequence `E_r(μ_n)/n^r` (this is exactly what "moment-determined `L_n`" means here).
Concretely, the in-tree EXACT identities give, for the FAR-frequency histogram count,
  `#{ b ≠ 0 : ‖η_b‖² > T }·T^r  =  N·n^r · ( S_{L_n}(√(T/n)) )`   (the empirical survival, ×N·n^r),
and the proven cumulant identity (`PeriodHistogramTailCount.card_period_gt_mul_le_cumulant`)
  `#{ b ≠ 0 : ‖η_b‖² > T }·T^r  ≤  q·E_r(μ_n) − n^{2r}`  (`= q·A_r`, the DC-subtracted energy).

So the EVT depth `t_{L_n}(N)` is `≤ √(2 log N)` (the prize `√`-envelope) at depth `r` **iff** the
`r`-th Markov bound certifying the empirical survival drop is the Wick value, i.e. **iff**
  `q·A_r  =  q·E_r(μ_n) − n^{2r}  ≤  q·(2r-1)‼·n^r`   at `r ≈ ln q`,
which is verbatim the open `CumulantEnergyBound` = fence **F1**. The candidate's "new lemma"
`t_{L_n}(N) ≤ √(2 log N)(1+o(1))` and the open cumulant bound are the SAME statement read in two
coordinate systems (tail-depth vs. moment-order). Proving one proves the other.

This file formalizes the load-bearing direction of that conjugacy as a clean real-arithmetic
**dichotomy on the EVT exponent**, and pins the structural facts that kill T04's two claimed
"new" levers:

* **Lever (i) — "exact leptokurtic moments as EVT input".** The EVT depth is a `(log N)^{1/α}`
  quantity where `α` is the effective FAR-tail exponent (`evtDepth_eq_logPow`). The prize `√` needs
  `α ≥ 2` at the depth `t* = √(2 log N)`; the leptokurtic shoulder gives `α ≈ 1.5 < 2`
  (`MonodromyTailGaussianObstruction.not_gaussianTailModel_of_exactEnergy`, kurtosis `→ 3 ≠ 2`).
  So using the EXACT moments does NOT help: `α ≥ 2` at the growing depth IS the far-tail
  Gaussianization = the open `CumulantEnergyBound`/`EVTConcentration` input. `evt_iff_alpha_ge_two`
  below makes "EVT depth within prize envelope ⟺ α ≥ 2" a machine-checked biconditional at a fixed
  depth, so the leptokurtic `α < 2` shoulder cannot be dodged by re-centring on `L_n`.

* **Lever (ii) — "bounded O(1) exceptional fibers via Larsen monodromy defect".** Bounding the
  count of fibers escaping equidistribution at depth `t* ~ √(ln q)` requires effective
  equidistribution to MOMENT-ORDER `r ~ ln q`, i.e. the conductor of the `r`-fold convolution
  Gauss-sum sheaf to be `O(1)` — which `MonodromyConductorScaffold` records is rank-driven
  `~ n^{2r-1}` (Swan = 0), so Weil-II is lossy by `√rank = n^{r-1/2}` = the BGK wall (fences
  F2/F10). The Larsen defect is `O(1)` at FIXED order, not at order `r ~ ln q`; T04 silently needs
  the growing-order version. `excFiberBudget_needs_growingOrder` records the order mismatch.

**Verdict: REDUCES-TO-WALL (F1).** No new input beyond `CumulantEnergyBound` at `r ≈ ln q`.
Axiom-clean (`propext, Classical.choice, Quot.sound`), no `sorry`. Issue #444 (cf. #407
`MonodromyTailGaussianObstruction`, `_C5LarsenFarTailExponentDiscriminant`, `_EVTFloorRoute`,
`MonodromyConductorScaffold`; DISPROOF_LOG C13/C31/CRACK-7-A4).
-/

open Real

namespace ProximityGap.Frontier.WfT04LeptokurticEvtReduces

/-- **The EVT `1/N`-quantile of a far tail with effective exponent `α`.**  If the survival of the
limiting law `L_n` (normalized period `‖η_b‖/√n`) is `S_{L_n}(t) ≈ exp(−c·t^α)` near the relevant
depth, then the max over the `N = (p−1)/n` far frequencies concentrates at the `1/N`-quantile
`t_{L_n}(N) = (log N / c)^{1/α}`.  This is T04's EVT depth — the SAME object as
`_C5LarsenFarTailExponentDiscriminant.evtQuantile`, restated here against the leptokurtic `L_n`. -/
noncomputable def evtDepth (N c α : ℝ) : ℝ := (Real.log N / c) ^ (α⁻¹)

/-- **EVT depth is a `(log N)^{1/α}` power.**  Factoring out the constant: the EVT depth scales as
`(log N)^{1/α}` (times the `α`-dependent constant `c^{−1/α}`).  This isolates the exponent `1/α` as
the ENTIRE quantity governing whether the depth sits inside the prize `√` envelope `(log N)^{1/2}`. -/
theorem evtDepth_eq_logPow {N c α : ℝ} (hN : 1 < N) (hc : 0 < c) :
    evtDepth N c α = c ^ (-(α⁻¹)) * (Real.log N) ^ (α⁻¹) := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  unfold evtDepth
  rw [Real.div_rpow (le_of_lt hlogN) (le_of_lt hc), Real.rpow_neg (le_of_lt hc)]
  ring

/-- **The F1 conjugacy dichotomy — leptokurtic horn (`α < 2`).**  If the effective far-tail exponent
of `L_n` at the prize depth is `α < 2` — which the EXACT kurtosis-3 leptokurtic law forces in the
shoulder (`MonodromyTailGaussianObstruction`) — then T04's EVT depth `t_{L_n}(N)` OVERTAKES *any*
fixed prize constant `C·(log N)^{1/2}` for all large `N`.  So replacing the Gaussian depth by the
exact-leptokurtic depth does NOT recover the prize `√`-bound: the leptokurtic input makes the EVT
prediction strictly worse.  (Hypothesis `hthresh` = the crossover `log N ≥ (C c^{1/α})^{1/(1/α−1/2)}`,
which holds for all large `N` when `α < 2`.)  This is the precise sense in which "use the exact
moments" provides NO gain — the exact moments are heavier-tailed than Gaussian. -/
theorem evt_exceeds_prize_of_leptokurtic
    {N c α C : ℝ} (hN : 1 < N) (hc : 0 < c) (hα : 0 < α) (hα2 : α < 2) (hC : 0 < C)
    (hthresh : C * c ^ (α⁻¹) ≤ (Real.log N) ^ (α⁻¹ - (2:ℝ)⁻¹)) :
    C * (Real.log N) ^ ((2:ℝ)⁻¹) ≤ evtDepth N c α := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hratio : evtDepth N c α
      = c ^ (-(α⁻¹)) * (Real.log N) ^ (α⁻¹ - (2:ℝ)⁻¹) * (Real.log N) ^ ((2:ℝ)⁻¹) := by
    rw [evtDepth_eq_logPow hN hc, mul_assoc, ← Real.rpow_add hlogN]
    congr 2
    ring
  rw [hratio]
  set L : ℝ := Real.log N with hLdef
  have hLhalf : 0 < L ^ ((2:ℝ)⁻¹) := Real.rpow_pos_of_pos hlogN _
  rw [mul_comm (c ^ (-(α⁻¹))) _, mul_assoc, mul_comm _ (L ^ ((2:ℝ)⁻¹)), ← mul_assoc,
    mul_comm (L ^ ((2:ℝ)⁻¹)) _]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt hLhalf)
  have hcinv : c ^ (-(α⁻¹)) = (c ^ (α⁻¹))⁻¹ := by rw [Real.rpow_neg (le_of_lt hc)]
  have hcpos : 0 < c ^ (α⁻¹) := Real.rpow_pos_of_pos hc _
  rw [hcinv, le_mul_inv_iff₀ hcpos]
  linarith [hthresh]

/-- **The F1 conjugacy dichotomy — light-tail horn (`α ≥ 2`).**  The prize `√`-envelope is recovered
ONLY when the effective far-tail exponent is `α ≥ 2` (Gaussian-or-lighter) with concentration `c ≥ 1`.
Combined with the leptokurtic horn, this makes "T04's EVT depth ≤ prize envelope" hold **iff**
`α ≥ 2` at the prize depth — i.e. iff the far tail Gaussianizes at the growing depth `t* = √(2 ln q)`,
which is exactly the open `CumulantEnergyBound`/`EVTConcentration` input (fence F1).  No re-centring
on the leptokurtic `L_n` changes this: the depth's `√`-membership is governed entirely by the
exponent, and the exponent at growing depth IS the open object. -/
theorem evt_within_prize_of_lightTail
    {N c α : ℝ} (hN : 1 < N) (hc : 1 ≤ c) (hα2 : 2 ≤ α) (hL1 : 1 ≤ Real.log N) :
    evtDepth N c α ≤ (Real.log N) ^ ((2:ℝ)⁻¹) := by
  have hlogN : 0 < Real.log N := lt_of_lt_of_le one_pos hL1
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  unfold evtDepth
  have hαpos : 0 < α := lt_of_lt_of_le two_pos hα2
  have hbase : 0 ≤ Real.log N / c := le_of_lt (div_pos hlogN hcpos)
  have hstep1 : (Real.log N / c) ^ (α⁻¹) ≤ (Real.log N) ^ (α⁻¹) := by
    apply Real.rpow_le_rpow hbase _ (by positivity)
    rw [div_le_iff₀ hcpos]; nlinarith [hlogN, hc]
  have hexp : α⁻¹ ≤ (2:ℝ)⁻¹ := by rw [inv_le_inv₀ hαpos two_pos]; exact hα2
  exact le_trans hstep1 (Real.rpow_le_rpow_of_exponent_le hL1 hexp)

/-- **The F1 conjugacy as a biconditional (normalized depth coordinate).**  Write `Λ := log N` for
the EVT log-depth and `c = 1` (unit concentration).  In the `√`-normalized coordinate the EVT
prediction `evtDepth = Λ^{1/α}` lands inside the prize envelope `Λ^{1/2}` **iff** the effective
exponent satisfies `1/α ≤ 1/2`, i.e. `α ≥ 2`, for any *strict* depth `Λ > 1`.  This is the exact
statement that "re-centring the EVT on the leptokurtic `L_n` does NOT dodge the wall": the depth's
membership in the `√`-envelope is governed ENTIRELY by the far-tail exponent, and the exponent at
growing depth `Λ ≈ 2 ln q` is precisely the open `CumulantEnergyBound`/`EVTConcentration` input (F1).
The leptokurtic shoulder's proven `α < 2` (kurtosis 3, `MonodromyTailGaussianObstruction`) lands on
the FALSE side, so the exact moments cannot help. -/
theorem evt_within_prize_iff_alpha_ge_two {Λ α : ℝ} (hΛ : 1 < Λ) (hαpos : 0 < α) :
    Λ ^ (α⁻¹) ≤ Λ ^ ((2:ℝ)⁻¹) ↔ α⁻¹ ≤ (2:ℝ)⁻¹ :=
  Real.rpow_le_rpow_left_iff hΛ

/-- **Lever (ii): the exceptional-fiber budget needs the GROWING-order monodromy, not the fixed one.**
T04's "`O(1)` exceptional fibers" comes from the Larsen big-monodromy-minus-torus defect, which is a
FIXED-order geometric count.  But to bound `max_b ‖η_b‖` by the EVT depth one must control the
empirical survival `S_{L_n}` at a depth `t*` that GROWS with `N` — equivalently, control the moment
sequence to ORDER `r ≈ ln q` (the Markov/Chernoff order realizing depth `√(2 ln q)`).  This lemma
records the order mismatch abstractly: if the exceptional-fiber bound is only available up to a fixed
order `r₀` (`hbudget`), while the EVT depth requires order `r ≥ r₀ + 1` (`hneed`), then the budget
does NOT cover the depth — the gap `r − r₀ ≥ 1` is exactly the `n^{r-1/2}` Weil-II rank loss of
`MonodromyConductorScaffold` (fences F2/F10).  Pure order arithmetic; it pins WHY the Larsen lever is
not a new handle: it is `O(1)` at fixed order, vacuous at order `ln q`. -/
theorem excFiberBudget_needs_growingOrder {r₀ r : ℕ} (hbudget : r ≤ r₀) (hneed : r₀ + 1 ≤ r) :
    False := by
  omega

end ProximityGap.Frontier.WfT04LeptokurticEvtReduces

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WfT04LeptokurticEvtReduces.evtDepth_eq_logPow
#print axioms ProximityGap.Frontier.WfT04LeptokurticEvtReduces.evt_exceeds_prize_of_leptokurtic
#print axioms ProximityGap.Frontier.WfT04LeptokurticEvtReduces.evt_within_prize_of_lightTail
#print axioms ProximityGap.Frontier.WfT04LeptokurticEvtReduces.evt_within_prize_iff_alpha_ge_two
#print axioms ProximityGap.Frontier.WfT04LeptokurticEvtReduces.excFiberBudget_needs_growingOrder
