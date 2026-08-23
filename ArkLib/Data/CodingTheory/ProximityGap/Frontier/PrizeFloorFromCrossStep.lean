/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf5M3_crossstep_ceiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickMGFFromTermwise

/-!
# `M3CrossStepBound` ⟹ `PrizeFloor` through the **satisfiable** DC-saddle route (axiom-clean reduction)

The campaign converged (lalalune's "4 independent reductions" note) onto the single open object
**`M3CrossStepBound`** — the sharp per-step slack `cross_r ≤ 2r·(2r−1)‼·n^{r+1}` of the proven
additive-depth recursion `E_{r+1} = n·E_r + cross_r`.  `_wf5M3_crossstep_ceiling.lean` proved the
closure `lamLeung_ceiling_of_crossStep : M3CrossStepBound G ⟹ ∀ r, E_r ≤ (2r−1)‼·n^r`
(`LamLeungCeiling`), and noted the prize follows "via the raw `q·E_r` moment identity."

But the **raw** moment route is exactly the one shown UNSATISFIABLE at the prize
(`WickMGFFromTermwise.mgf_unsat_of_dc_gt`: the `b=0` DC term blows the raw saddle hypothesis past
`q²` from `n ≥ 2^6`).  So routing M3 through the raw `hMGF` lands on a dead hypothesis.

This file routes `M3CrossStepBound` to the prize floor through the **satisfiable** DC-saddle chain
(`DCWickMGFFromTermwise.prizeFloor_of_dcWick`) instead:

> `M3CrossStepBound`  ⟹  `∀ r, LamLeungCeiling`  (proven, `lamLeung_ceiling_of_crossStep`)
> ⟹ `∀ r, GaussianEnergyBound`  (ℕ→ℝ cast)  ⟹ `∀ r, DCWickBound`  (DC is weaker)
> ⟹ DC-subtracted MGF inequality  ⟹ `NearRamanujanSqrtLog`  ⟹ `PrizeFloor`.

**Value (frontier-movement):** this is a SECOND axiom-clean Lean reduction of the prize floor from
`M3CrossStepBound`, independent of M1's count route, and crucially routed through the *satisfiable*
MGF object rather than the raw one (which provably fails at the prize).  The open input is now
exactly the single named char-`p` crux `M3CrossStepBound` — nothing else.

**NOT a CORE closure.**  `M3CrossStepBound` itself (the char-`p` per-step cross bound at depth
`r ≈ log q`) is the open prize.  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.
-/

namespace ProximityGap.Frontier.PrizeFloorFromCrossStep

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.CrossStepCeiling
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.ConvergenceHub
open ProximityGap.Frontier.NearRamanujanFromSaddle
open ProximityGap.Frontier.DCWickMGFFromTermwise

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`LamLeungCeiling ⟹ GaussianEnergyBound`** (ℕ-ceiling to its ℝ-cast form).  `LamLeungCeiling`
states `E_r ≤ (2r−1)‼·n^r` in `ℕ`; `GaussianEnergyBound` is the same inequality cast to `ℝ`. -/
theorem gaussianEnergyBound_of_lamLeungCeiling {G : Finset F} {r : ℕ}
    (h : LamLeungCeiling G r) : GaussianEnergyBound G r := by
  unfold LamLeungCeiling at h
  unfold GaussianEnergyBound
  have hcast : ((rEnergy G r : ℕ) : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) * G.card ^ r : ℕ) : ℝ) := by exact_mod_cast h
  simpa using hcast

/-- **`M3CrossStepBound ⟹ ∀ r, DCWickBound`** — the per-step cross bound discharges the termwise
DC-Wick ceiling at every depth.  Chains `lamLeung_ceiling_of_crossStep` (M3 closure) →
`gaussianEnergyBound_of_lamLeungCeiling` (cast) → `dcWick_of_gaussianEnergyBound` (DC is weaker). -/
theorem dcWick_of_crossStep (G : Finset F) (hstep : M3CrossStepBound G) :
    ∀ r, DCWickBound G r := by
  intro r
  exact dcWick_of_gaussianEnergyBound
    (gaussianEnergyBound_of_lamLeungCeiling (lamLeung_ceiling_of_crossStep G hstep r))

/-- **The satisfiable M3 → spectral bridge.**  At the saddle `y*` (`y*² = 2 log q / n`, `y* > 0`,
`n = |G| > 0`), the per-step cross bound `M3CrossStepBound` discharges the universal spectral
predicate `NearRamanujanSqrtLog ψ G C₀` with `C₀ = saddleConst F G y*`, routed through the
**satisfiable** DC-subtracted MGF inequality (NOT the unsatisfiable raw one). -/
theorem nearRamanujan_of_crossStep {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hstep : M3CrossStepBound G) :
    NearRamanujanSqrtLog ψ G (saddleConst F G y) :=
  nearRamanujan_of_dcWick hψ G hy hn hL hsaddle (dcWick_of_crossStep G hstep)

/-- **THE REDUCTION (axiom-clean): `M3CrossStepBound` ⟹ `PrizeFloor` via the satisfiable DC-saddle
chain.**  At the saddle, the single open char-`p` per-step cross bound `M3CrossStepBound` discharges
the δ*-pinning prize floor `PrizeFloor ψ G C₀` (`C₀ = saddleConst F G y*`) — a SECOND axiom-clean
reduction of the prize floor from `M3CrossStepBound`, independent of M1's count route, and routed
through the **satisfiable** MGF object (the raw `q·E_r` saddle hypothesis the M3 docstring suggested
is unsatisfiable at the prize — `WickMGFFromTermwise.mgf_unsat_of_dc_gt`).

Still NOT a CORE closure — `M3CrossStepBound` (char-`p`, depth `r ≈ log q`) is the open prize. -/
theorem prizeFloor_of_crossStep {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ)) (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hq : (G.card : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hstep : M3CrossStepBound G) :
    PrizeFloor ψ G (saddleConst F G y) :=
  prizeFloor_of_dcWick hψ G hy hn hq1 hq hL hsaddle (dcWick_of_crossStep G hstep)

end ProximityGap.Frontier.PrizeFloorFromCrossStep

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.PrizeFloorFromCrossStep.gaussianEnergyBound_of_lamLeungCeiling
#print axioms ProximityGap.Frontier.PrizeFloorFromCrossStep.dcWick_of_crossStep
#print axioms ProximityGap.Frontier.PrizeFloorFromCrossStep.nearRamanujan_of_crossStep
#print axioms ProximityGap.Frontier.PrizeFloorFromCrossStep.prizeFloor_of_crossStep
