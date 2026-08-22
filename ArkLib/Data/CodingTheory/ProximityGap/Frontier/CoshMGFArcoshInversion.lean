/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFIdentity
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The explicit root-free CORE sup-norm bound: `‖η_{b₀}‖ ≤ arcosh(MGF(y))/y` (#444 §6.2, §5.0)

## What this file does (frontier-movement: it *extends a proven theorem*)

`CoshMGFIdentity.lean` proves the assembled MGF comparison

> `cosh_period_le_evenMoment_tsum` : `cosh(‖η_{b₀}‖·y) ≤ ∑_r (q·E_r(G)/(2r)!)·y^{2r}` (all `y`),

and its docstring states, but **does not formalize**, the inversion
"`for y > 0 this bounds ‖η_{b₀}‖ by arcosh(RHS(y))/y`".  That inverted, *explicit* sup-norm form
is the object the whole §5.0 / §6.2 funnel keeps referencing ("the root-free `CORE` upper-bound
mechanism", `min_y arcosh(p·I₀(2y)^{n/2})/y`).  This file supplies the missing inversion brick,
purely from the in-tree theorem + Mathlib's `arcosh` API.  No new analytic-NT input enters: this is
the unconditional, field-general bridge from the proven cosh-MGF bound to the explicit
`‖η‖ ≤ arcosh(MGF)/y` statement that an eventual Wick/saddle estimate plugs into.

## The mechanism (elementary, unconditional)

For `y > 0` and `t := ‖η_{b₀}‖·y ≥ 0`:
`cosh t ≤ S` with `t ≥ 0` gives `t = arcosh(cosh t) ≤ arcosh S` (apply `arcosh`, monotone
on `(0,∞)`; `cosh t ≥ 1` so both arguments are `≥ 1 > 0`), hence `‖η_{b₀}‖ = t / y ≤ arcosh S / y`.

The only subtlety is junk-value safety of `arcosh`: we use `arcosh_le_arcosh`
(valid on `0 < x, y`) together with `1 ≤ cosh t ≤ S` (so `0 < cosh t` and `0 < S`), and
`arcosh_cosh` (valid for the nonneg argument `t`).

## What is and is NOT proved here

- **PROVED:** `period_le_arcosh_of_cosh_le`, the abstract inversion: `0 < y`, `0 ≤ a`,
  `cosh (a*y) ≤ S` ⟹ `a ≤ arcosh S / y`.  (Pure real analysis; `a` and `S` arbitrary.)
- **PROVED:** `core_supNorm_le_arcosh_mgf`, the assembled explicit CORE bound: for `y > 0`,
  `‖η_{b₀}‖ ≤ arcosh (MGF y) / y`, where `MGF y = ∑_r (q·E_r/(2r)!)·y^{2r}` is the even-moment MGF
  (the RHS of `cosh_period_le_evenMoment_tsum`).  This is the explicit, root-free, `max`-free upper
  bound on a single Gauss period, optimisable in `y`.
- **NOT proved (honest, this is the open prize, §6.2):** any *bound on the MGF itself* at the
  saddle `y* = √(2 log q / n)`.  That is the char-`p` Wick inequality `A_r ≤ (2r−1)‼·n^r` at depth
  `r ≈ ln q`, the single open inequality.  This file does NOT touch it; it only makes the consumer
  explicit, so a future Wick bound yields the prize `M(n) ≤ C√(n log(p/n))` by substitution + the
  saddle choice.

All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

namespace ProximityGap.Frontier.CoshMGFArcoshInversion

open scoped Real
open ProximityGap.Frontier.CoshMGFIdentity
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-- **The arcosh inversion brick (abstract).**  If `y > 0`, `a ≥ 0`, and `cosh (a·y) ≤ S`, then
`a ≤ arcosh S / y`.  Proof: `a·y = arcosh (cosh (a·y)) ≤ arcosh S` by monotonicity of `arcosh`
on the positives (both `cosh(a·y) ≥ 1` and `S ≥ cosh(a·y) ≥ 1` lie in the strictly-monotone range),
then divide by `y > 0`.  Unconditional, field-free, no special-function machinery beyond Mathlib's
`arcosh` API. -/
theorem period_le_arcosh_of_cosh_le {a y S : ℝ} (hy : 0 < y) (ha : 0 ≤ a)
    (hle : Real.cosh (a * y) ≤ S) : a ≤ Real.arcosh S / y := by
  have hay : (0 : ℝ) ≤ a * y := mul_nonneg ha hy.le
  -- `cosh (a*y) ≥ 1` and hence `0 < cosh (a*y)` and `0 < S`
  have hcosh_one : (1 : ℝ) ≤ Real.cosh (a * y) := Real.one_le_cosh _
  have hcosh_pos : (0 : ℝ) < Real.cosh (a * y) := lt_of_lt_of_le one_pos hcosh_one
  have hS_pos : (0 : ℝ) < S := lt_of_lt_of_le hcosh_pos hle
  -- apply `arcosh` (monotone on `Ioi 0`) to `cosh (a*y) ≤ S`
  have harc : Real.arcosh (Real.cosh (a * y)) ≤ Real.arcosh S :=
    (Real.arcosh_le_arcosh hcosh_pos hS_pos).mpr hle
  -- `arcosh (cosh (a*y)) = a*y` since `a*y ≥ 0`
  rw [Real.arcosh_cosh hay] at harc
  -- `a*y ≤ arcosh S` ⟹ `a ≤ arcosh S / y`
  rwa [le_div_iff₀ hy]

/-- **The explicit root-free CORE sup-norm bound (assembled, #444 §6.2 / §5.0).**  For every
primitive additive character `ψ`, every subset `G`, every `b₀`, and every `y > 0`,
the single Gauss period satisfies
`‖η_{b₀}‖ ≤ arcosh (∑_r (q·E_r(G)/(2r)!)·y^{2r}) / y`.
This is the inverted, `max`-free, root-free upper bound on `CORE` that the campaign's `arcosh`
mechanism keeps referencing: optimising `y` (the open `§5.0` saddle step) over a Wick bound on the
MGF would yield the prize constant.  Proof: combine the in-tree MGF comparison
`cosh_period_le_evenMoment_tsum` with the inversion `period_le_arcosh_of_cosh_le`
(`‖η_{b₀}‖ ≥ 0`). -/
theorem core_supNorm_le_arcosh_mgf {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) (hy : 0 < y) (b₀ : F) :
    ‖eta ψ G b₀‖
      ≤ Real.arcosh
          (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ)) / y :=
  period_le_arcosh_of_cosh_le hy (norm_nonneg _)
    (cosh_period_le_evenMoment_tsum hψ G y b₀)

/-- **arcosh-to-log upper bridge.**  For `x ≥ 1`, `arcosh x ≤ log (2*x)`.  Since
`arcosh x = log (x + √(x²−1))` and `√(x²−1) ≤ √(x²) = x` (as `x ≥ 0`), the argument is `≤ 2x`,
and `log` is monotone on the positives.  This converts the `arcosh`-form CORE bound into the
**log-MGF / cumulant** form the §6.2 saddle `y* = √(2 log q / n)` actually consumes. -/
theorem arcosh_le_log_two_mul {x : ℝ} (hx : 1 ≤ x) : Real.arcosh x ≤ Real.log (2 * x) := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  -- √(x²−1) ≤ √(x²) = x
  have hsqrt : Real.sqrt (x ^ 2 - 1) ≤ x := by
    calc Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt (x ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
      _ = x := by rw [Real.sqrt_sq hx0]
  have harg : x + Real.sqrt (x ^ 2 - 1) ≤ 2 * x := by linarith
  have hpos : (0 : ℝ) < x + Real.sqrt (x ^ 2 - 1) := by positivity
  rw [Real.arcosh]
  exact (Real.log_le_log_iff hpos (by positivity)).mpr harg

/-- **log-to-arcosh lower bridge.**  For `x ≥ 1`, `log x ≤ arcosh x`.  Immediate from
`arcosh x = log (x + √(x²−1))` and `√(x²−1) ≥ 0`.  Pins the cumulant form as a faithful
(constant-factor-tight) surrogate: `log x ≤ arcosh x ≤ log (2x)`. -/
theorem log_le_arcosh {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.arcosh x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.arcosh]
  exact (Real.log_le_log_iff hx0 (by positivity)).mpr
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- **The explicit log-MGF (cumulant) CORE sup-norm bound (the §6.2 saddle form).**  For `y > 0`
and any subset `G` whose even-moment MGF `S(y) := ∑_r (q·E_r/(2r)!)·y^{2r}` is `≥ 1` (always true:
the `r=0` term is `q·E_0/0! = q ≥ 1` for nonempty `F`, but we keep `1 ≤ S` as an explicit hypothesis
to stay unconditional), the single Gauss period satisfies
`‖η_{b₀}‖ ≤ log (2 · S(y)) / y`.
This is the cumulant-generating-function form the saddle `y* = √(2 log q / n)` plugs into directly
(a Wick bound `S(y) ≤ exp(n·y²/2)` then gives `‖η‖ ≤ (log 2 + n·y²/2)/y`, minimised at the saddle).
Proof: chain `core_supNorm_le_arcosh_mgf` with `arcosh_le_log_two_mul`, divide by `y > 0`. -/
theorem core_supNorm_le_log_mgf {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) (hy : 0 < y) (b₀ : F)
    (hS : (1 : ℝ) ≤ ∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ)) :
    ‖eta ψ G b₀‖
      ≤ Real.log
          (2 * ∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ)) / y := by
  refine (core_supNorm_le_arcosh_mgf hψ G y hy b₀).trans ?_
  -- divide both sides of `arcosh S ≤ log (2S)` by `y > 0`
  gcongr
  exact arcosh_le_log_two_mul hS

end ProximityGap.Frontier.CoshMGFArcoshInversion

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, NO sorryAx)
open ProximityGap.Frontier.CoshMGFArcoshInversion in
#print axioms period_le_arcosh_of_cosh_le
open ProximityGap.Frontier.CoshMGFArcoshInversion in
#print axioms core_supNorm_le_arcosh_mgf
open ProximityGap.Frontier.CoshMGFArcoshInversion in
#print axioms arcosh_le_log_two_mul
open ProximityGap.Frontier.CoshMGFArcoshInversion in
#print axioms log_le_arcosh
open ProximityGap.Frontier.CoshMGFArcoshInversion in
#print axioms core_supNorm_le_log_mgf
