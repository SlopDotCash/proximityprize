/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCSubtractedCoshMGF
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.NearRamanujanFromSaddle

/-!
# The **DC-subtracted** saddle weld: the *satisfiable* hypothesis discharges `NearRamanujanSqrtLog`

`Frontier/NearRamanujanFromSaddle.lean` welds the **raw** even-moment MGF inequality
`∑_r (q·E_r·y^{2r}/(2r)!) ≤ q·exp(n·y²/2)` (at the saddle) to the universal spectral predicate
`NearRamanujanSqrtLog`.  But `Frontier/DCSubtractedCoshMGF.lean` documents — and the numeric probe
`scripts/probes/probe_dc_vs_raw_mgf_saddle.py` **confirms with mechanism** — that the *raw* MGF
object is the **wrong** one: the `b = 0` term contributes `cosh(|G|·y)` (period `= |G|` at `b = 0`),
which at the saddle `y*² = 2 log q / n` grows like `exp(√(2·|G|·log q))` and **single-handedly
exceeds `q²`** from `n = 32` onward in the prize regime (β ≈ 4).  So the raw hypothesis `hMGF` of
`nearRamanujan_of_saddle` is **unsatisfiable** in the prize regime — that weld, while axiom-clean, can
never be discharged.

The **DC-subtracted** MGF `∑_r ((q·E_r − n^{2r})·y^{2r}/(2r)!)` drops the `b = 0` term and stays
`≈ 10×` below `q²` at every probed `n` (the satisfiable object, mandated by §407 / the live #444
reduction).  `Frontier/DCSubtractedCoshMGF.lean` proved the per-`b₀` consumer
`period_le_of_dcGaussianMGFBound` but **never** lifted it to the *universal* predicate.

This file builds that universal weld:

* **`nearRamanujan_of_dcSaddle`** — at the saddle, the **DC-subtracted** Gaussian MGF inequality
  (the *satisfiable* object) discharges the universally-quantified `NearRamanujanSqrtLog ψ G C₀`
  with the **same** explicit constant `C₀ = saddleConst F G y*` as the raw weld (because at the
  saddle `q·exp(n y*²/2) = q²`, so the per-frequency closed form `log(2q²)/y*` is identical).
* **`prizeFloor_of_dcSaddle`** — composing with the convergence hub, the DC-subtracted MGF
  inequality discharges `PrizeFloor ψ G C₀`.

**Value (frontier-movement, honesty rules 1/3/6):** this re-grounds the entire prize-floor reduction
on a hypothesis that is at least *consistent* in the prize regime.  Mechanism: the per-`b₀` DC
consumer's bound is `b₀`-independent, so the same closed form bounds *every* nonzero frequency.

**Still NOT a CORE closure.**  The DC-subtracted MGF inequality itself remains the open prize (the
char-`p` Wick bound at depth `r ≈ log q`).  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.NearRamanujanFromDCSaddle

open Finset AddChar
open ProximityGap.Frontier.DCSubtractedCoshMGF
open ProximityGap.Frontier.CoshMGFSaddle
open ProximityGap.Frontier.NearRamanujanFromSaddle
open ProximityGap.Frontier.ConvergenceHub
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC-subtracted saddle floor (single frequency, closed form).**  At the saddle `y*`
(`y*² = 2 log q / n`, `y* > 0`, `n = |G| > 0`), if the **DC-subtracted** even-moment MGF obeys the
*satisfiable* Gaussian inequality `DC-MGF(y*) ≤ q·exp(n·y*²/2)`, then **every** nonzero Gauss period
satisfies the same `b₀`-independent closed form `‖η_b‖ ≤ log(2·q²)/y*`.  Mechanism: feed the DC
consumer `period_le_of_dcGaussianMGFBound` and collapse `q·exp(n y*²/2) = q·q = q²` via
`exp_saddle_eq_card`. -/
theorem period_le_dcSaddle_closedForm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (b₀ : F) (hb₀ : b₀ ≠ 0) (hn : 0 < (G.card : ℝ))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hDCMGF : (∑' r : ℕ,
        (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
          * y ^ (2 * r) / ((2 * r).factorial : ℝ)))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    ‖eta ψ G b₀‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y := by
  -- the DC consumer (satisfiable shape)
  have hcons :
      ‖eta ψ G b₀‖
        ≤ Real.log (2 * ((Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2))) / y :=
    period_le_of_dcGaussianMGFBound (F := F) hψ G hy hb₀ hDCMGF
  -- collapse `exp(n y²/2) = q` at the saddle, so the inner factor is `q·q = q²`
  have hexp : Real.exp ((G.card : ℝ) * y ^ 2 / 2) = (Fintype.card F : ℝ) :=
    exp_saddle_eq_card (F := F) hn hsaddle
  rw [hexp] at hcons
  -- `q * q = q²`
  have hsq : (Fintype.card F : ℝ) * (Fintype.card F : ℝ) = (Fintype.card F : ℝ) ^ 2 := by ring
  rwa [hsq] at hcons

/-- **The DC-subtracted bridge.**  At the saddle `y*` (`y*² = 2 log q / n`, `y* > 0`, `n = |G| > 0`),
given the **satisfiable** DC-subtracted Gaussian MGF inequality, the **universally-quantified**
spectral predicate `NearRamanujanSqrtLog ψ G C₀` holds with the *same* explicit constant
`C₀ = saddleConst F G y*` as the raw weld `nearRamanujan_of_saddle`.

Mechanism: `period_le_dcSaddle_closedForm` bounds *every* frequency by the `b₀`-independent closed
form `log(2q²)/y*`; dividing by the positive length scale `√(n·log(q/n)) > 0` rewrites that into the
spectral normalization, exactly as in the raw bridge. -/
theorem nearRamanujan_of_dcSaddle {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hDCMGF : (∑' r : ℕ,
        (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
          * y ^ (2 * r) / ((2 * r).factorial : ℝ)))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    NearRamanujanSqrtLog ψ G (saddleConst F G y) := by
  intro b hb
  -- the `b₀`-independent DC saddle closed form, applied at this frequency `b`
  have hclosed : ‖eta ψ G b‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y :=
    period_le_dcSaddle_closedForm (F := F) hψ G hy b hb hn hsaddle hDCMGF
  -- write the target length scale and show it is positive
  set s : ℝ := Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) with hs
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hL
  have hyne : y ≠ 0 := ne_of_gt hy
  have hsne : s ≠ 0 := ne_of_gt hspos
  -- `saddleConst F G y * s = log(2q²)/y`  (the tautological rewrite, shared with the raw weld)
  have hkey : saddleConst F G y * s = Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y := by
    rw [saddleConst, ← hs]
    field_simp
  calc ‖eta ψ G b‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y := hclosed
    _ = saddleConst F G y * s := hkey.symm

/-- **End-to-end (DC-subtracted): the *satisfiable* MGF inequality ⟹ the δ*-pinning hub.**
Composing `nearRamanujan_of_dcSaddle` with the in-tree convergence-hub face
`prizeFloor_of_nearRamanujan`, the **DC-subtracted** Gaussian MGF inequality at the saddle discharges
`PrizeFloor ψ G C₀` through the same explicit constant `C₀ = saddleConst F G y*`.

This is the satisfiable-hypothesis twin of `prizeFloor_of_saddle`: the raw weld's hypothesis is
unsatisfiable in the prize regime (probe `probe_dc_vs_raw_mgf_saddle.py`: raw MGF `>` `q²` from
`n = 32`), whereas this one consumes the DC-subtracted object that stays below `q²` at every probed
`n`.  Still NOT a CORE closure — the DC-subtracted MGF inequality itself is the open prize. -/
theorem prizeFloor_of_dcSaddle {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ)) (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hq : (G.card : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hDCMGF : (∑' r : ℕ,
        (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
          * y ^ (2 * r) / ((2 * r).factorial : ℝ)))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    PrizeFloor ψ G (saddleConst F G y) :=
  prizeFloor_of_nearRamanujan hq (saddleConst_nonneg G hy hq1 hL)
    (nearRamanujan_of_dcSaddle hψ G hy hn hL hsaddle hDCMGF)

end ProximityGap.Frontier.NearRamanujanFromDCSaddle

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.NearRamanujanFromDCSaddle.period_le_dcSaddle_closedForm
#print axioms ProximityGap.Frontier.NearRamanujanFromDCSaddle.nearRamanujan_of_dcSaddle
#print axioms ProximityGap.Frontier.NearRamanujanFromDCSaddle.prizeFloor_of_dcSaddle
