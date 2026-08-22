/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.LiuZhouSplitRecursion
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The log-ratio tower has BOUNDED increments, the Azuma/Freedman prerequisite (#444)

The proven geometric-mean recasting (`DyadicGeomeanPrizeVsSqrtN`) writes the prize quantity as a
telescoped product over the 2-power tower:
`M(μ_{2^a}) = M(μ_1) · ∏_{i<a} ρ_i`, with `ρ_i = M(μ_{2^{i+1}}) / M(μ_{2^i})`.
Taking logs, `log M(μ_{2^a}) − log M(μ_1) = Σ_{i<a} log ρ_i =: S_a` is a TELESCOPED SUM, and the
prize `M(μ_{2^a}) ≤ C·√(2^a · log(p/2^a))` is equivalent (§1.2 "Martingale / Azuma–Freedman" lever)
to a bound on this sum: `S_a ≤ ½·a·log 2 + ½·log(log(p/2^a)) + log C`.

A Freedman/Azuma martingale concentration bound on `S_a` REQUIRES bounded increments: each
`Δ_i := log ρ_i` must lie in a fixed interval. The DIRECT η-tower (the partial sums
`η^{(2^k)}_b` of the Gauss period itself) FAMOUSLY FAILS this, `probe_407_cumulant_martingale_deep`
mapped that obstruction: the per-level η-increment `η^{(2^{k})}_{ζ b}` is a full order-`2^{k}`
period, its own magnitude `~√(2^k log m)`, i.e. **as big as the whole partial sum**, an
UNBOUNDED-increment walk, so Azuma gives nothing.

**This file establishes the contrasting positive fact: the LOG-RATIO tower IS bounded-increment.**
The Liu–Zhou dyadic doubling `M(μ_{2^{i+1}}) ≤ 2·M(μ_{2^i})` (landed: `LiuZhouSplitRecursion.
M_union_le_two_mul`) gives, after taking logs of positive terms, `Δ_i = log ρ_i ≤ log 2`. Combined
with the trivial monotonicity `M(μ_{2^{i+1}}) ≥ M(μ_{2^i})` (the subgroup grows), `ρ_i ≥ 1` so
`Δ_i ≥ 0`. So `Δ_i ∈ [0, log 2]`: the log-ratio increments are bounded, exactly the Freedman
prerequisite. The probe (`scripts/probes/probe_rho_increment_bounded.py`,
`probe_rho_excess_growth.py`) confirms `ρ_i ∈ [√2, 2]` (so `Δ_i ∈ [½log 2, log 2]`) on PROPER thin
subgroups `p ≫ n³`, never `n=q−1`.

## What is landed (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)
Abstract over a tower `Mtow : ℕ → ℝ` with `Mtow 0 > 0`, the doubling `Mtow (i+1) ≤ 2·Mtow i`, and
monotonicity `Mtow i ≤ Mtow (i+1)` (both DISCHARGED for the real prize tower from the landed
Liu–Zhou recursion + subgroup monotonicity, see `logRatio_le_log2_of_M` consuming
`M_union_le_two_mul`):
* `logRatio_le_log2` : `Δ_i = log(Mtow (i+1)) − log(Mtow i) ≤ log 2` (the BOUNDED-INCREMENT
  property).
* `logRatio_nonneg` : `0 ≤ Δ_i` (from monotonicity), so `Δ_i ∈ [0, log 2]`.
* `logTower_telescope` : `log(Mtow a) − log(Mtow 0) = Σ_{i<a} Δ_i` (the telescope, exact).
* `logTower_le_card_mul_log2` (the bounded-increment SUM): `log(Mtow a) − log(Mtow 0) ≤ a·log 2`,
  i.e. `Mtow a ≤ 2^a · Mtow 0`, the TRIVIAL bound recovered as a bounded-increment martingale-sum.
* `logRatio_le_log2_of_M` : the concrete discharge, for the real `M`-tower (`Mtow i = M(μ_{2^i})`),
  the doubling hypothesis is exactly `LiuZhouSplitRecursion.M_union_le_two_mul` (the `M(μ_{2^{i+1}})
  ≤ 2·M(μ_{2^i})` step), so `Δ_i ≤ log 2` holds for the actual prize tower (given positivity).

## HONEST SCOPE (rules 1, 3, 4, 6 + the asymptotic guard). This is a WALL-MAP, not a closure.
The bounded-increment property is REAL and is the genuine Freedman prerequisite, but it is NOT
thinness-essential: the doubling `M(μ_{2^{i+1}}) ≤ 2·M(μ_{2^i})` is the thickness-BLIND Liu–Zhou
triangle inequality (it holds verbatim in the thick `β≈2.3` window where the prize is FALSE). By
rule 3, no bound derivable from `Δ_i ≤ log 2` ALONE can prove the prize. Concretely (the rule-4
constraint, `logTower_excess_lower` below): the prize needs the EXCESS
`Σ_{i<a} (Δ_i − ½log 2) ≤ ½·log(log(p/2^a)) + log C = O(log log m) = O(log a)`, i.e. the increments
must AVERAGE down to `½log 2 + o(1)`. The probe shows the opposite: `ρ_i ∈ [√2, 2]` with `ρ_i > √2`
strictly at every measured level, so `Δ_i − ½log 2 > 0` and the excess grows `~Θ(a)` (LINEAR), not
`O(log a)`. Bounded increments give only `S_a ≤ a·log 2` (the trivial `M ≤ 2^a = n`, `√n` short).
A martingale concentration bound on `S_a` controls the FLUCTUATION (`~√a`) around the MEAN, but the
prize is a statement about the MEAN of `Δ_i` (it must be `≤ ½log 2 + o(1)`), which bounded-increment
concentration cannot supply. So the Azuma/Freedman lever is MAPPED: the prerequisite holds (this
file), but the open object is the per-level MEAN drift `E[Δ_i] − ½log 2` (the binding-frequency
phase law `θ_b`, the N13 transfer operator), which this magnitude-only recursion cannot reach. This
is the same wall as the Liu-Zhou magnitude recursion, viewed on the log-tower. CORE `M(μ_n) ≤
C·√(n·log(p/n))` stays OPEN; logged to `DISPROOF_LOG.md` [LRTBI].

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.LogRatioTowerBoundedIncrement

/-! ## Abstract bounded-increment log-ratio tower

We abstract the real prize tower `Mtow i = M(μ_{2^i})` as a positive sequence with the two proven
structural inputs: the Liu–Zhou doubling and subgroup monotonicity. The headline facts are stated
abstractly here and discharged for the concrete `M` below. -/

variable {Mtow : ℕ → ℝ}

/-- **The bounded-increment property (headline).** If the tower doubles at most each step
(`Mtow (i+1) ≤ 2·Mtow i`, the Liu–Zhou recursion) and is positive, then the log-ratio increment is
bounded by `log 2`:
`log(Mtow (i+1)) − log(Mtow i) ≤ log 2`.

This is the Freedman/Azuma prerequisite the direct η-tower lacks (η-increments are unbounded). -/
theorem logRatio_le_log2 (i : ℕ) (hpos : 0 < Mtow i)
    (hpos1 : 0 < Mtow (i + 1))
    (hdouble : Mtow (i + 1) ≤ 2 * Mtow i) :
    Real.log (Mtow (i + 1)) - Real.log (Mtow i) ≤ Real.log 2 := by
  -- log is monotone: log (Mtow (i+1)) ≤ log (2 * Mtow i) = log 2 + log (Mtow i)
  have hmono : Real.log (Mtow (i + 1)) ≤ Real.log (2 * Mtow i) :=
    Real.log_le_log hpos1 hdouble
  rw [Real.log_mul (by norm_num) (ne_of_gt hpos)] at hmono
  linarith

/-- **Non-negativity of the increment.** If the tower is monotone non-decreasing
(`Mtow i ≤ Mtow (i+1)`, the subgroup `μ_{2^i} ⊆ μ_{2^{i+1}}` grows) and positive, then
`0 ≤ log(Mtow (i+1)) − log(Mtow i)`. So the increment lies in `[0, log 2]`. -/
theorem logRatio_nonneg (i : ℕ) (hpos : 0 < Mtow i)
    (hmono : Mtow i ≤ Mtow (i + 1)) :
    0 ≤ Real.log (Mtow (i + 1)) - Real.log (Mtow i) := by
  have : Real.log (Mtow i) ≤ Real.log (Mtow (i + 1)) := Real.log_le_log hpos hmono
  linarith

/-- **The telescope (exact).** The log-tower is the telescoped sum of its log-ratio increments:
`log(Mtow a) − log(Mtow 0) = Σ_{i<a} (log(Mtow (i+1)) − log(Mtow i))`.
This is the recasting `log M(μ_{2^a}) − log M(μ_1) = Σ_{i<a} log ρ_i` the martingale lever uses. -/
theorem logTower_telescope (a : ℕ) :
    Real.log (Mtow a) - Real.log (Mtow 0) =
      ∑ i ∈ Finset.range a, (Real.log (Mtow (i + 1)) - Real.log (Mtow i)) := by
  rw [Finset.sum_range_sub (fun i => Real.log (Mtow i)) a]

/-- **The bounded-increment SUM (the trivial bound, as a martingale-sum).** Summing the bounded
increment `Δ_i ≤ log 2` over the telescope gives `log(Mtow a) − log(Mtow 0) ≤ a·log 2`, i.e.
`Mtow a ≤ 2^a · Mtow 0`. This is the TRIVIAL bound (`M(μ_{2^a}) ≤ 2^a = n`), recovered here as a
**bounded-increment martingale-sum**, the form a Freedman/Azuma concentration step would consume.
It is `√n` short of the prize: the prize needs the AVERAGE increment `≤ ½log 2`, not `≤ log 2`. -/
theorem logTower_le_card_mul_log2 (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ a * Real.log 2 := by
  rw [logTower_telescope a]
  calc ∑ i ∈ Finset.range a, (Real.log (Mtow (i + 1)) - Real.log (Mtow i))
      ≤ ∑ _i ∈ Finset.range a, Real.log 2 :=
        Finset.sum_le_sum (fun i _ => logRatio_le_log2 i (hpos i) (hpos (i + 1)) (hdouble i))
    _ = a * Real.log 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Rule-4 constraint lemma (the wall, mean-drift form).** Define the EXCESS increment
`e_i := Δ_i − ½log 2`. The prize floor `log(Mtow a) − log(Mtow 0) ≤ ½·a·log 2 + R` (with
`R = ½·log(log(p/2^a)) + log C = O(log a)` the prize slack) is EQUIVALENT to the excess-sum bound
`Σ_{i<a} e_i ≤ R`. So the prize requires the excess sum to be `O(log a)` (sub-linear).
The bounded-increment property gives only `e_i ≤ ½log 2` (each), hence `Σ e_i ≤ ½·a·log 2` -
LINEAR, useless. The probe shows `e_i > 0` strictly at every level (`ρ_i > √2`), so `Σ e_i ~ Θ(a)`
LINEAR, NOT the required `O(log a)`. This pins the wall: bounded increments (this file) do not
control the MEAN drift `e_i`; the open object is the binding-frequency phase law that would force
`e_i → 0` (the N13 transfer operator). -/
theorem logTower_excess_eq (a : ℕ) (R : ℝ) :
    (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * (Real.log 2 / 2) + R) ↔
      (∑ i ∈ Finset.range a,
        ((Real.log (Mtow (i + 1)) - Real.log (Mtow i)) - Real.log 2 / 2) ≤ R) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← logTower_telescope a]
  constructor <;> intro h <;> linarith

/-- **Bounded increments give only a linear excess ceiling.** From `Δ_i ≤ log 2`, each centered
increment `Δ_i − ½log 2` is at most `½log 2`; summing gives
`Σ_{i<a}(Δ_i − ½log 2) ≤ (a/2) log 2`. This formalizes the wall stated in the file header: the
bounded-increment theorem by itself supplies a LINEAR excess allowance, while the prize needs the
excess to be sublinear (`O(log log(p/2^a))`). No mean-drift control is obtained here. -/
theorem logTower_excess_le_half_card_mul_log2 (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    (∑ i ∈ Finset.range a,
        ((Real.log (Mtow (i + 1)) - Real.log (Mtow i)) - Real.log 2 / 2))
      ≤ (a : ℝ) * (Real.log 2 / 2) := by
  calc
    (∑ i ∈ Finset.range a,
        ((Real.log (Mtow (i + 1)) - Real.log (Mtow i)) - Real.log 2 / 2))
        ≤ ∑ _i ∈ Finset.range a, Real.log 2 / 2 :=
          Finset.sum_le_sum (fun i _ => by
            have hΔ := logRatio_le_log2 i (hpos i) (hpos (i + 1)) (hdouble i)
            linarith)
    _ = (a : ℝ) * (Real.log 2 / 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The predictable quadratic-variation bound (Freedman prerequisite).** Freedman's martingale
concentration inequality — the sharper sibling of Azuma the file header invokes — consumes not just
bounded increments but the PREDICTABLE QUADRATIC VARIATION `⟨S⟩_a = ∑_{i<a} Δ_i²`. Since each
`Δ_i ∈ [0, log 2]` (`logRatio_nonneg` + `logRatio_le_log2`), the per-step square is dominated by the
step itself scaled by the increment bound: `Δ_i² ≤ (log 2)·Δ_i`. Summing over the telescope gives the
quadratic variation in terms of the telescoped drift:
`∑_{i<a} Δ_i² ≤ (log 2)·(log(Mtow a) − log(Mtow 0))`.
This is the genuine Freedman QV prerequisite (distinct from the bounded-increment SUM): it ties the
quadratic variation to the same telescoped drift `S_a = log(Mtow a) − log(Mtow 0)` whose MEAN is the
open object.

NOTE: this is a DEDUCTIVE consequence of the already-landed envelope `Δ_i ∈ [0, log 2]`
(`logRatio_nonneg` + `logRatio_le_log2`), not a new empirical fact — `Δ_i² ≤ (log 2)·Δ_i` holds for
any `Δ_i` in that interval. The companion `probe_logtower_qv.py` is a SYNTHETIC algebraic sanity
check (it samples `Δ_i` directly inside the envelope and confirms the bound is consequence-true);
the envelope itself is the prize-regime-validated input (`rho_i ∈ [√2, 2]` on PROPER thin subgroups,
per the file header probes), not re-derived here. -/
theorem logTower_sq_le_log2_mul (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    (∑ i ∈ Finset.range a, (Real.log (Mtow (i + 1)) - Real.log (Mtow i)) ^ 2)
      ≤ Real.log 2 * (Real.log (Mtow a) - Real.log (Mtow 0)) := by
  rw [logTower_telescope a, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  set Δ := Real.log (Mtow (i + 1)) - Real.log (Mtow i) with hΔ
  have hlo : 0 ≤ Δ := logRatio_nonneg i (hpos i) (hmono i)
  have hhi : Δ ≤ Real.log 2 := logRatio_le_log2 i (hpos i) (hpos (i + 1)) (hdouble i)
  -- Δ² = Δ·Δ ≤ (log 2)·Δ since 0 ≤ Δ ≤ log 2
  have : Δ ^ 2 = Δ * Δ := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hhi hlo

/-! ## Concrete discharge for the real `M`-tower

The abstract doubling hypothesis `Mtow (i+1) ≤ 2·Mtow i` is EXACTLY the landed Liu–Zhou recursion
`LiuZhouSplitRecursion.M_union_le_two_mul` applied to the split `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ·μ_{2^i}`
(both halves `≤ M(μ_{2^i})`). So the bounded-increment property holds for the actual prize tower. -/

open ProximityGap.Frontier.PaleyCayleyEigenvalue
open ProximityGap.Frontier.LiuZhouSplitRecursion

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Concrete bounded-increment for the real `M`-tower.** Let `prev = M(μ_{2^i})` and
`M(A ∪ B) = M(μ_{2^{i+1}})` be one tower step of a disjoint split
`μ_{2^{i+1}} = μ_{2^i} ⊍ ζ·μ_{2^i}` whose halves are both `≤ prev`. Then the log-ratio increment is
`≤ log 2`. The doubling hypothesis is
discharged from `M_union_le_two_mul` (the landed Liu–Zhou recursion); the positivity
`0 < M(A ∪ B)` is supplied by the subgroup-monotone input `prev ≤ M(A ∪ B)` (`μ_{2^i} ⊆ μ_{2^{i+1}}`
makes the sup-norm non-decreasing), which is always true for the prize tower.

This shows the bounded-increment property of the previous section is NOT vacuous: it holds for the
genuine prize quantity `M`, via the landed Liu–Zhou recursion. -/
theorem logRatio_le_log2_of_M (ψ : AddChar F ℂ) {A B : Finset F}
    (hAB : Disjoint A B)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty)
    {prev : ℝ} (hprevpos : 0 < prev)
    (hmono : prev ≤ M ψ (A ∪ B) hb)
    (hMA : M ψ A hb ≤ prev) (hMB : M ψ B hb ≤ prev) :
    Real.log (M ψ (A ∪ B) hb) - Real.log prev ≤ Real.log 2 := by
  -- the Liu–Zhou doubling: M(A ∪ B) ≤ 2 * prev
  have hdouble : M ψ (A ∪ B) hb ≤ 2 * prev := M_union_le_two_mul ψ hAB hb hMA hMB
  -- positivity of M(A ∪ B) from prev ≤ M(A ∪ B) and 0 < prev (monotone tower)
  have hupos : (0 : ℝ) < M ψ (A ∪ B) hb := lt_of_lt_of_le hprevpos hmono
  -- log monotone: log (M(A∪B)) ≤ log (2 * prev) = log 2 + log prev
  have hlog : Real.log (M ψ (A ∪ B) hb) ≤ Real.log (2 * prev) :=
    Real.log_le_log hupos hdouble
  rw [Real.log_mul (by norm_num) (ne_of_gt hprevpos)] at hlog
  linarith

end ProximityGap.Frontier.LogRatioTowerBoundedIncrement

#print axioms ProximityGap.Frontier.LogRatioTowerBoundedIncrement.logTower_excess_le_half_card_mul_log2
#print axioms ProximityGap.Frontier.LogRatioTowerBoundedIncrement.logTower_sq_le_log2_mul
