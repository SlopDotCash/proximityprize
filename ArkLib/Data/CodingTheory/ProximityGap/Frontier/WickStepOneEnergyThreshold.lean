/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WickMonotonicityReduction

/-!
# The first Wick monotonicity step is an exact additive-energy threshold (#444, #407)

The reduction in `_WickMonotonicityReduction.lean` reframes the #407 prize floor as
`f 1 ≤ 1` **and** the single-step antitone law `WickMonotonicity : ∀ r ≥ 1, f (r+1) ≤ f r`,
with `f r = A_r / Wick_r`, `A_r = (1/q)·∑_{b≠0}‖η_b‖^{2r}`, `Wick_r = (2r−1)‼·|G|^r`.

This file isolates the **`r = 1` step** of that ladder and proves, axiom-clean, the EXACT
algebraic reformulation

> `WickStepCross`-at-1  ⟺  `A_2 ≤ 3·|G|·A_1`

(`wickStepCross_one_iff`). The constant `3·|G| = Wick_2 / Wick_1` is forced: `Wick_1 = |G|`,
`Wick_2 = 3·|G|²` (`Wick_two`). This is the *first* and structurally *simplest* instance of the
open `WickMonotonicity` core.

## Why this is a frontier brick, not a point-confirm (probe-grounded NOTE)

The natural hope is that the *base* step `A_2 ≤ 3·|G|·A_1` might be **unconditional** (it would extend
the proven base `f 1 ≤ 1` to `f 2 ≤ f 1` with no BGK input). The probes
`scripts/probes/probe_wickstep_one_energy_threshold_{1..6}*.py` (proper 2-power subgroups `μ_n ⊊ F_p^*`, `p ∈ {193,…,786433}`,
`n = 2^a`, prize regime `β = log_n p ∈ [2.5, 6.5]`) **REFUTE** that hope and pin the obstruction
*exactly*:

* Writing `A_1 = E_1 − |G|²/q` and `A_2 = E_2 − |G|⁴/q` with `E_r := rEnergy(μ_n) r` (`E_1 = n`),
  the step `A_2 ≤ 3·|G|·A_1` is, by pure algebra, **equivalent** to the additive-energy threshold
  `E_2(μ_n) ≤ 3n² + n³(n−3)/q`.  This `iff` was verified cell-by-cell (`…_5_iff.py`): the step holds
  exactly when `E_2` is under threshold and fails exactly when over.
* The threshold is **violated** at concrete prize-regime cells: `(p,n)=(40961,64)` has
  `E_2 = 13632 > 12678 = 3n² + n³(n−3)/q`, so the step **FAILS** (`A_2/A_1 = 206.9 > 192 = 3n`);
  likewise `(40961,512)`. Neighbours `n=32,128,256,1024` satisfy it. The violation is
  **generator-independent** (the order-`n` subgroup is unique) and **non-monotone in β**.
* Mechanism (`…_6_wrapdecomp.py`): the in-tree char-0 closed form `rEnergy(μ_n) 2 = 3n² − 3n` carries the
  hypothesis `2^n < p` (`DefectOnsetEnergySandwich.energy_eq`), which is **incompatible with the
  prize regime** `q ≈ n^β ≪ 2^n` for `n ≥ 64`.  In the prize regime `E_2(μ_n)` acquires excess
  additive energy from (a) wraparound quadruples `a+b ≥ p` and (b) genuine extra additive
  coincidences of the *multiplicative* set `μ_n` — both are `0` for `n ≤ 32` and turn on at
  `n ≥ 64`.  This excess is *exactly* the BGK additive-energy content, and it is what breaks the
  first Wick step.

**Consequence (honest, no overclaim).** Even the *base* `r = 1` Wick step is **not** an
unconditional / soft / β-monotone inequality: it is equivalent to an additive-energy threshold on
`E_2(μ_n)` that prize-regime subgroups genuinely cross. Hence the only route through this lane is
the sup-norm-conditional one (`WickMonoDCSupNormPresupposition.wickMono_step_of_dc_supNorm`), whose
sup-norm hypothesis is *genuinely load-bearing*: dropping it makes the statement **false**. This
localizes the open core's first obstruction to the wraparound/multiplicative additive-energy excess
`E_2(μ_n) − (3n²−3n)` — a concrete object, not the full deep-`r` tower. No CORE closure; no
char-p transfer; no capacity / beyond-Johnson / growth-law claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #444, #407.
-/

set_option autoImplicit false

open Finset

namespace ProximityGap.Frontier.WickMonotonicityReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `Wick_2 = 3·|G|²`: the second Wick value, with `(2·2−1)‼ = 3!! = 3`. -/
theorem Wick_two (G : Finset F) : Wick G 2 = 3 * (G.card : ℝ) ^ 2 := by
  unfold Wick
  have : (WickMomentCapability.oddWickCoeff 2 : ℝ) = 3 := by
    simp [WickMomentCapability.oddWickCoeff, Finset.prod_range_succ]
  rw [this]

/-- **The exact `r = 1` Wick cross-step, in clean form.** The cross-multiplied step
`A_2 · Wick_1 ≤ A_1 · Wick_2` is *equivalent* to `A_2 ≤ 3·|G|·A_1`. The constant `3·|G|` is
`Wick_2/Wick_1` and is forced; this is the first instance of the open `WickMonotonicity` core.
(Pure algebra: substitute `Wick_1 = |G|`, `Wick_2 = 3|G|²`, cancel one factor of `|G| > 0`.) -/
theorem wickStepCross_one_iff {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty) :
    (Ar ψ G 2 * Wick G 1 ≤ Ar ψ G 1 * Wick G 2) ↔
      (Ar ψ G 2 ≤ 3 * (G.card : ℝ) * Ar ψ G 1) := by
  have hcard : (0 : ℝ) < (G.card : ℝ) := by
    have : 0 < G.card := Finset.card_pos.mpr hG
    exact_mod_cast this
  rw [Wick_one, Wick_two]
  constructor
  · intro h
    -- A_2 · |G| ≤ A_1 · (3|G|²) = (3|G|·A_1)·|G|; cancel |G| > 0.
    have h' : Ar ψ G 2 * (G.card : ℝ) ≤ (3 * (G.card : ℝ) * Ar ψ G 1) * (G.card : ℝ) := by
      nlinarith [h]
    exact le_of_mul_le_mul_right h' hcard
  · intro h
    -- multiply both sides by |G| > 0
    have h' : Ar ψ G 2 * (G.card : ℝ) ≤ (3 * (G.card : ℝ) * Ar ψ G 1) * (G.card : ℝ) :=
      mul_le_mul_of_nonneg_right h (le_of_lt hcard)
    nlinarith [h']

/-- **The `r = 1` step is exactly `WickStepCross` evaluated at `1`.** Unfolding `WickStepCross`
at `r = 1` (legal since `1 ≤ 1`) gives precisely the clean form `A_2 ≤ 3·|G|·A_1`. So proving the
single inequality `A_2 ≤ 3·|G|·A_1` is *necessary* for `WickStepCross ψ G` (the open core), and the
probe-refuted unconditionality (see file NOTE) shows this necessary condition is already
non-trivial. -/
theorem wickStepCross_imp_step_one {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty)
    (hWSC : WickStepCross ψ G) :
    Ar ψ G 2 ≤ 3 * (G.card : ℝ) * Ar ψ G 1 :=
  (wickStepCross_one_iff hG).mp (hWSC 1 (le_refl 1))

/-- **Contrapositive witness (downstream-usable).** If the first concrete step `A_2 ≤ 3·|G|·A_1`
*fails* (as the probes exhibit at `(p,n)=(40961,64)`), then the open core `WickStepCross ψ G` is
false — hence no soft / unconditional discharge of `WickMonotonicity` can exist for that cell. This
is the honest constraint lemma: the open core is *genuinely* open even at `r = 1`. -/
theorem not_wickStepCross_of_step_one_fails {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty)
    (hfail : ¬ (Ar ψ G 2 ≤ 3 * (G.card : ℝ) * Ar ψ G 1)) :
    ¬ WickStepCross ψ G := by
  intro hWSC
  exact hfail (wickStepCross_imp_step_one hG hWSC)

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.Wick_two
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.wickStepCross_one_iff
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.wickStepCross_imp_step_one
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.not_wickStepCross_of_step_one_fails

end ProximityGap.Frontier.WickMonotonicityReduction
