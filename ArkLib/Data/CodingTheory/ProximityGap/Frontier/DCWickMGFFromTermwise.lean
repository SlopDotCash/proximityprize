/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.WickMGFFromTermwise
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCSubtractedCoshMGF
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.NearRamanujanFromDCSaddle

/-!
# The termwise **DC-Wick** bound ⟹ the **DC-subtracted** MGF inequality (the producer of the *satisfiable* `hDCMGF`)

`Frontier/WickMGFFromTermwise.lean` (0xSolace) produced the **raw** MGF inequality `hMGF` from the
termwise raw-Wick bound `E_r ≤ (2r−1)‼·n^r`, then proved that bound is **unsatisfiable** at the prize
(the `b = 0` DC term `cosh(n y)` forces `RawMGF ≥ cosh(n y) > q·exp(n y²/2)` from `n ≥ 2^6`).  So the
raw producer feeds a dead hypothesis.

`Frontier/DCSubtractedCoshMGF.lean` (the satisfiable side) and
`Frontier/NearRamanujanFromDCSaddle.lean` (the universal weld) consume the **DC-subtracted** MGF
inequality

> `hDCMGF : ∑' r, ((q·E_r − n^{2r})·y^{2r}/(2r)!) ≤ q·exp(n·y²/2)`

but NO in-tree file produced *that* from a termwise input.  This file supplies the missing producer,
mirroring 0xSolace's raw producer but on the satisfiable object.

The natural termwise carrier is the **DC-Wick bound**

> `DCWickBound G r : (q·E_r(G) − n^{2r}) ≤ q·(2r−1)‼·n^r`   (`n = |G|`, `q = |F|`)

which is **strictly weaker** than the raw `GaussianEnergyBound` (it subtracts the nonnegative DC mass
`n^{2r}` from the LHS), so it can hold exactly where the raw bound fails — the satisfiable object
mandated by §8 / `DCEnergyEssential` (`A_r = E_r − n^{2r}/q ≤ Wick`).  Probe
`scripts/probes/probe_dc_vs_raw_mgf_saddle.py`: the DC-subtracted MGF stays `~10×` below `q²` at the
saddle for every probed `n` (incl. `n = 32` where the raw object exceeds `q²`).

## What is and is NOT proved
- **PROVED (`dcMGF_le_of_termwise_dcWick`):** `(∀ r, DCWickBound G r) ⟹ hDCMGF` for every real `y`.
  Mechanism: termwise, `(q·E_r − n^{2r})·y^{2r}/(2r)! ≤ q·(2r−1)‼·n^r·y^{2r}/(2r)! = q·n^r·y^{2r}/(2^r r!)`
  (the exp-series term, via 0xSolace's coefficient identity `(2r−1)‼/(2r)! = 1/(2^r r!)`); summing
  (`tsum_le_tsum`, both summable) gives `q·exp(n y²/2)`.  The DC LHS terms may be negative — fine.
- **PROVED end-to-end:** `nearRamanujan_of_dcWick`, `prizeFloor_of_dcWick` — termwise DC-Wick (∀r) at
  the saddle ⟹ `NearRamanujanSqrtLog` / `PrizeFloor` with `C₀ = saddleConst F G y*`.
- **NOT proved (honest, the open prize):** the termwise `∀ r, DCWickBound G r` ITSELF in char `p` at
  the prize regime — the char-`p` DC-subtracted Wick bound `A_r ≤ Wick` at depth `r ≈ log q`.  This is
  the open core of #444.  This file is the deductive producer, NOT a closure.

All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).  CORE stays **OPEN**.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DCWickMGFFromTermwise

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.WickMGFFromTermwise
open ProximityGap.Frontier.DCSubtractedCoshMGF
open ProximityGap.Frontier.ConvergenceHub
open ProximityGap.Frontier.NearRamanujanFromDCSaddle
open ProximityGap.Frontier.NearRamanujanFromSaddle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Summability of the DC-subtracted moment series.**  The term function
`r ↦ (q·E_r − n^{2r})·y^{2r}/(2r)!` is summable because, by the in-tree identity proof, it is the
`b`-sum (over the FINITE set `b ≠ 0`) of the cosh power series `(‖η_b‖·y)^{2r}/(2r)!`, each of which
is summable (`Real.hasSum_cosh`); a finite sum of summable functions is summable. -/
theorem summable_dcMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) :
    Summable (fun r : ℕ =>
      (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
        * y ^ (2 * r) / ((2 * r).factorial : ℝ))) := by
  classical
  -- the finite-`b` HasSum from the identity proof
  have hb : ∀ b : F,
      HasSum (fun r : ℕ => (‖eta ψ G b‖ * y) ^ (2 * r) / ((2 * r).factorial : ℝ))
        (Real.cosh (‖eta ψ G b‖ * y)) := fun b => Real.hasSum_cosh _
  have hsum := hasSum_sum (fun b (_ : b ∈ (univ.erase (0 : F))) => hb b)
  -- rewrite the `b`-summed term into the DC moment term (the per-`r` identity from the in-tree proof)
  have hterm_eq : ∀ r : ℕ,
      (∑ b ∈ (univ.erase (0 : F)), (‖eta ψ G b‖ * y) ^ (2 * r) / ((2 * r).factorial : ℝ))
        = ((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
            * y ^ (2 * r) / ((2 * r).factorial : ℝ) := by
    intro r
    rw [← sum_nonzero_moment hψ G r]
    rw [show ((∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ))
          = ∑ b ∈ univ.erase (0 : F),
              (‖eta ψ G b‖ ^ (2 * r) * y ^ (2 * r) / ((2 * r).factorial : ℝ)) by
        rw [Finset.sum_mul, Finset.sum_div]]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [mul_pow]
  exact (hsum.summable).congr (fun r => hterm_eq r)

/-- **The termwise DC-Wick bound** at order `r`: the DC-subtracted even moment
`q·E_r − n^{2r}` is at most the raw Wick ceiling `q·(2r−1)‼·n^r` (`n = |G|`, `q = |F|`).
Strictly weaker than `GaussianEnergyBound G r` (LHS reduced by the DC mass `n^{2r} ≥ 0`), so it is
the *satisfiable* object: it holds wherever the raw bound holds, and can hold where the raw fails. -/
def DCWickBound (G : Finset F) (r : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)

set_option linter.unusedSectionVars false in
/-- **`GaussianEnergyBound ⟹ DCWickBound`** (the satisfiable object is weaker).  Subtracting the
nonnegative DC mass `n^{2r}` from the LHS only loosens the inequality. -/
theorem dcWick_of_gaussianEnergyBound {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) : DCWickBound G r := by
  have hEr : (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := h
  have hqpos : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hdc : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  have hmul : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left hEr hqpos
  unfold DCWickBound
  linarith

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **The termwise comparison (DC version).**  Under `DCWickBound G r`, the `r`-th DC-subtracted MGF
term is `≤` the `r`-th Gaussian (exp-series) term:
`(q·E_r − n^{2r})·y^{2r}/(2r)! ≤ q·n^r·y^{2r}/(2^r r!)`.
Uses `y^{2r} ≥ 0` and the coefficient identity `(2r−1)‼/(2r)! = 1/(2^r r!)`. -/
theorem dcTerm_le_gaussianTerm {G : Finset F} {r : ℕ} (y : ℝ) (h : DCWickBound G r) :
    ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
        * y ^ (2 * r) / ((2 * r).factorial : ℝ)
      ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  have hy2 : (0 : ℝ) ≤ y ^ (2 * r) := by rw [pow_mul]; positivity
  have hfacpos : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast (2 * r).factorial_pos
  have hcoeff := doubleFactorial_div_factorial_eq r
  -- LHS ≤ q·(2r-1)‼·n^r · y^{2r}/(2r)!  (DC-Wick, times nonneg y^{2r}/(2r)!)
  have hstep1 :
      (q * (rEnergy G r : ℝ) - n ^ (2 * r)) * y ^ (2 * r) / ((2 * r).factorial : ℝ)
        ≤ (q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r)) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ) := by
    have hDC : q * (rEnergy G r : ℝ) - n ^ (2 * r)
        ≤ q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) := h
    have hfront : (0 : ℝ) ≤ y ^ (2 * r) / ((2 * r).factorial : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_right hDC hfront
    -- a * (y^{2r}/(2r)!) = a * y^{2r} / (2r)!
    calc (q * (rEnergy G r : ℝ) - n ^ (2 * r)) * y ^ (2 * r) / ((2 * r).factorial : ℝ)
        = (q * (rEnergy G r : ℝ) - n ^ (2 * r)) * (y ^ (2 * r) / ((2 * r).factorial : ℝ)) := by
          ring
      _ ≤ (q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r))
            * (y ^ (2 * r) / ((2 * r).factorial : ℝ)) := this
      _ = (q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r)) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ) := by ring
  -- RHS rewrite: q·(2r-1)‼·n^r·y^{2r}/(2r)! = q·n^r·y^{2r}/(2^r r!)  via the coefficient identity
  have hstep2 :
      (q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r)) * y ^ (2 * r)
          / ((2 * r).factorial : ℝ)
        = q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
    have hcoeff' : (Nat.doubleFactorial (2 * r - 1) : ℝ) / ((2 * r).factorial : ℝ)
        = 1 / ((2 : ℝ) ^ r * r.factorial) := hcoeff
    calc (q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r)) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ)
        = (q * n ^ r * y ^ (2 * r))
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) / ((2 * r).factorial : ℝ)) := by ring
      _ = (q * n ^ r * y ^ (2 * r)) * (1 / ((2 : ℝ) ^ r * r.factorial)) := by rw [hcoeff']
      _ = q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by ring
  exact hstep1.trans_eq hstep2

/-- **THE DC PRODUCER — the producer of the *satisfiable* `hDCMGF`.**  If the termwise DC-Wick bound
`DCWickBound G r` holds for *every* `r`, then the **DC-subtracted** MGF inequality consumed by
`DCSubtractedCoshMGF.period_le_of_dcGaussianMGFBound` / `NearRamanujanFromDCSaddle.*` holds:
`∑' r, ((q·E_r − n^{2r})·y^{2r}/(2r)!) ≤ q·exp(n·y²/2)`.  No positivity on `y` needed (the DC terms
may be negative). -/
theorem dcMGF_le_of_termwise_dcWick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ)
    (h : ∀ r, DCWickBound G r) :
    (∑' r : ℕ,
        (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
          * y ^ (2 * r) / ((2 * r).factorial : ℝ)))
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  -- RHS as a tsum of the Gaussian (exp-series) terms
  have hRHS : q * Real.exp (n * y ^ 2 / 2)
      = ∑' r : ℕ, q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := q_exp_eq_tsum q n y
  have hsumR : Summable (fun r : ℕ => q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial)) :=
    summable_gaussianTerms q n y
  -- termwise: DC term ≤ Gaussian term
  have hterm : ∀ r : ℕ,
      ((q * (rEnergy G r : ℝ) - n ^ (2 * r)) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
        ≤ q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
    intro r
    have := dcTerm_le_gaussianTerm (G := G) (r := r) y (h r)
    simpa [hq, hn] using this
  -- LHS summable (finite cosh sum identity)
  have hsumL : Summable (fun r : ℕ =>
      ((q * (rEnergy G r : ℝ) - n ^ (2 * r)) * y ^ (2 * r) / ((2 * r).factorial : ℝ))) := by
    have := summable_dcMoment hψ G y
    simpa [hq, hn] using this
  rw [hRHS]
  have hLHSeq :
      (∑' r : ℕ, (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
          * y ^ (2 * r) / ((2 * r).factorial : ℝ)))
        = ∑' r : ℕ, ((q * (rEnergy G r : ℝ) - n ^ (2 * r)) * y ^ (2 * r)
            / ((2 * r).factorial : ℝ)) := by
    rw [hq, hn]
  rw [hLHSeq]
  exact Summable.tsum_le_tsum hterm hsumL hsumR

/-- **End-to-end (DC): termwise DC-Wick (∀r) at the saddle ⟹ `NearRamanujanSqrtLog`.**  Composes the
DC producer `dcMGF_le_of_termwise_dcWick` with the universal DC weld
`NearRamanujanFromDCSaddle.nearRamanujan_of_dcSaddle`. -/
theorem nearRamanujan_of_dcWick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (h : ∀ r, DCWickBound G r) :
    NearRamanujanSqrtLog ψ G (saddleConst F G y) :=
  nearRamanujan_of_dcSaddle hψ G hy hn hL hsaddle (dcMGF_le_of_termwise_dcWick hψ G y h)

/-- **End-to-end (DC): termwise DC-Wick (∀r) at the saddle ⟹ `PrizeFloor`.**  The full satisfiable
spine: termwise DC-Wick bound ⟹ DC-subtracted MGF inequality ⟹ universal spectral predicate ⟹ the
δ*-pinning prize floor, all through `C₀ = saddleConst F G y*`.  Still NOT a CORE closure — the termwise
DC-Wick bound itself (char-`p` `A_r ≤ Wick` at depth `r ≈ log q`) is the open prize. -/
theorem prizeFloor_of_dcWick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ)) (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hq : (G.card : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (h : ∀ r, DCWickBound G r) :
    PrizeFloor ψ G (saddleConst F G y) :=
  prizeFloor_of_dcSaddle hψ G hy hn hq1 hq hL hsaddle (dcMGF_le_of_termwise_dcWick hψ G y h)

end ProximityGap.Frontier.DCWickMGFFromTermwise

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.DCWickMGFFromTermwise.dcWick_of_gaussianEnergyBound
#print axioms ProximityGap.Frontier.DCWickMGFFromTermwise.dcMGF_le_of_termwise_dcWick
#print axioms ProximityGap.Frontier.DCWickMGFFromTermwise.nearRamanujan_of_dcWick
#print axioms ProximityGap.Frontier.DCWickMGFFromTermwise.prizeFloor_of_dcWick
