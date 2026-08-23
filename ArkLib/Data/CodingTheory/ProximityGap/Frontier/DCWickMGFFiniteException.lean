/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickMGFFromTermwise
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.NearRamanujanFromDCSaddle

/-!
# The **finite-exception** (slack-tolerant) DC-Wick MGF producer

`Frontier/DCWickMGFFromTermwise.lean` (`dcMGF_le_of_termwise_dcWick`) produces the satisfiable
DC-subtracted MGF inequality `hDCMGF` from the **`∀ r`** termwise bound `∀ r, DCWickBound G r`.
That `∀ r` hypothesis is stronger than the MGF actually needs.

lalalune's #444 (2026-06-15 21:06) "prove the wall directly" analysis observed that the
prize-equivalent MGF is a **Poisson(log q)-weighted average** of the per-`r` ratios `A_r/Wick_r`, a
single scalar that **tolerates per-`r` violations** of `A_r ≤ Wick_r`: only a small share of the MGF
mass sits at any one depth, and the char-`0` carrier closes with `≈√q` of slack. Concretely, the
producer need not assume `DCWickBound G r` at **every** `r`: it can absorb a **finite** set of
exceptional depths whose aggregate excess over the Gaussian (exp-series) envelope is carried
explicitly into the bound.

This file lands exactly that **strictly weaker** producer. It is **NOT** a closure: the open prize
core (char-`p` `DCWickBound` at depth `r ≈ log q`) is untouched; this only relaxes the *deductive
interface* from `∀ r` to `cofinite + an explicit exceptional-excess remainder`.

## Probe / scope note (honesty rules 1, 3, 6 + asymptotic guard)
- `scripts/probes/probe_dcmgf_perr_violation_hunt.py`: across `n ∈ {8, 16}` thin prize primes
  (incl. the maximally-structured Fermat `p = 65537`, `v₂ = 16`), the per-`r` ratio `E_r/Wick_r ≤ 1`
  is monotone-decreasing, so **no** `DCWickBound` violation occurs in the brute-forceable thin band.
  So in the **thin** regime the `∀ r` producer is already non-vacuous; the finite-exception producer
  is the deductively-weaker generalization (it degenerates to the `∀ r` producer when the
  exceptional set is empty), absorbing sparse violations should they appear deeper / at larger `n`.
  It is the honest Lean form of "the MGF tolerates per-`r` violations", and **provably contains**
  the old producer as the `s = ∅` special case (`dcMGF_le_of_termwise_dcWick_via_finite`).
- A negation-agnostic, char-agnostic re-summation; **NOT** thinness-essential; does **NOT** close
  CORE.  `CORE M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.

All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DCWickMGFFiniteException

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ProximityGap.Frontier.WickMGFFromTermwise
open ProximityGap.Frontier.DCWickMGFFromTermwise
open ProximityGap.Frontier.ConvergenceHub
open ProximityGap.Frontier.NearRamanujanFromSaddle
open ProximityGap.Frontier.NearRamanujanFromDCSaddle
open ArkLib.ProximityGap.GaussPeriodSpectralFrame

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `r`-th DC-subtracted MGF term `(q·E_r − n^{2r})·y^{2r}/(2r)!`. -/
noncomputable def dcTerm (G : Finset F) (y : ℝ) (r : ℕ) : ℝ :=
  ((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
    * y ^ (2 * r) / ((2 * r).factorial : ℝ)

/-- The `r`-th Gaussian (exp-series) term `q·n^r·y^{2r}/(2^r r!)`. -/
noncomputable def gaussTerm (G : Finset F) (y : ℝ) (r : ℕ) : ℝ :=
  (Fintype.card F : ℝ) * (G.card : ℝ) ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial)

theorem summable_dcTerm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) :
    Summable (dcTerm G y) := by
  simpa [dcTerm] using summable_dcMoment hψ G y

set_option linter.unusedSectionVars false in
theorem summable_gaussTerm (G : Finset F) (y : ℝ) : Summable (gaussTerm G y) := by
  simpa [gaussTerm] using
    summable_gaussianTerms (Fintype.card F : ℝ) (G.card : ℝ) y

set_option linter.unusedSectionVars false in
/-- `∑' gaussTerm = q·exp(n y²/2)`. -/
theorem tsum_gaussTerm (G : Finset F) (y : ℝ) :
    ∑' r : ℕ, gaussTerm G y r
      = (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) := by
  simpa [gaussTerm] using (q_exp_eq_tsum (Fintype.card F : ℝ) (G.card : ℝ) y).symm

/-- Termwise: `DCWickBound G r ⟹ dcTerm ≤ gaussTerm` (the per-`r` comparison of the existing
producer, repackaged on the named `dcTerm`/`gaussTerm`). -/
theorem dcTerm_le_gaussTerm {G : Finset F} {r : ℕ} (y : ℝ) (h : DCWickBound G r) :
    dcTerm G y r ≤ gaussTerm G y r := by
  simpa [dcTerm, gaussTerm] using dcTerm_le_gaussianTerm (G := G) (r := r) y h

/-- **THE FINITE-EXCEPTION DC PRODUCER (strictly weaker than `∀ r`).**  Let `s : Finset ℕ` be a
finite set of *exceptional* depths.  If `DCWickBound G r` holds for **every `r ∉ s`**, then the
DC-subtracted MGF is bounded by the Gaussian envelope **plus the explicit exceptional remainder**

> `∑' r, dcTerm ≤ q·exp(n y²/2) + ∑_{r∈s} (dcTerm r − gaussTerm r)`.

The exceptional remainder is a **finite** sum (over `s`) of the per-`r` excesses; on the
non-exceptional cofinite part the termwise comparison applies.  When `s = ∅` (no exceptions) this
recovers the `∀ r` producer exactly (the remainder is `0`).  No positivity on `y`. -/
theorem dcMGF_le_of_dcWick_except_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (y : ℝ) (s : Finset ℕ) (h : ∀ r ∉ s, DCWickBound G r) :
    (∑' r : ℕ, dcTerm G y r)
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)
          + ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) := by
  classical
  have hsumDc : Summable (dcTerm G y) := summable_dcTerm hψ G y
  have hsumG : Summable (gaussTerm G y) := summable_gaussTerm G y
  -- The "capped" comparison function: on `s` it is `dcTerm` (the exceptional depths, carried
  -- exactly), off `s` it is `gaussTerm` (the Gaussian envelope). Then `dcTerm ≤ cap` TERMWISE.
  set cap : ℕ → ℝ := fun r => if r ∈ s then dcTerm G y r else gaussTerm G y r with hcap
  have hsumCap : Summable cap := by
    -- `cap` differs from `gaussTerm` only on the finite set `s`, hence summable.
    have : cap = fun r => gaussTerm G y r
        + (if r ∈ s then dcTerm G y r - gaussTerm G y r else 0) := by
      funext r; by_cases hr : r ∈ s <;> simp [hcap, hr]
    rw [this]
    refine hsumG.add (summable_of_finite_support ?_)
    apply Set.Finite.subset s.finite_toSet
    intro r hr
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hr
    exact Finset.mem_coe.mpr hr.1
  -- termwise `dcTerm ≤ cap`
  have hterm : ∀ r, dcTerm G y r ≤ cap r := by
    intro r
    by_cases hr : r ∈ s
    · simp only [hcap, hr, if_true, le_refl]
    · have hcmp := dcTerm_le_gaussTerm (G := G) (r := r) y (h r hr)
      simp only [hcap, hr, if_false]
      exact hcmp
  -- `∑' dcTerm ≤ ∑' cap`
  have hle : ∑' r : ℕ, dcTerm G y r ≤ ∑' r : ℕ, cap r :=
    Summable.tsum_le_tsum hterm hsumDc hsumCap
  -- `∑' cap = ∑' gaussTerm + ∑_{r∈s}(dcTerm − gaussTerm)`
  have hcapsum : ∑' r : ℕ, cap r
      = (∑' r : ℕ, gaussTerm G y r) + ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) := by
    have hrw : cap = fun r => gaussTerm G y r
        + (if r ∈ s then dcTerm G y r - gaussTerm G y r else 0) := by
      funext r; by_cases hr : r ∈ s <;> simp [hcap, hr]
    rw [hrw]
    have hsumCorr : Summable
        (fun r : ℕ => if r ∈ s then dcTerm G y r - gaussTerm G y r else 0) := by
      refine summable_of_finite_support ?_
      apply Set.Finite.subset s.finite_toSet
      intro r hr
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hr
      exact Finset.mem_coe.mpr hr.1
    rw [Summable.tsum_add hsumG hsumCorr]
    congr 1
    -- the correction tsum collapses to the finite sum over `s`
    rw [tsum_eq_sum (s := s)]
    · exact Finset.sum_congr rfl (fun r hr => by simp [hr])
    · intro r hr; simp [hr]
  rw [hcapsum, tsum_gaussTerm G y] at hle
  exact hle

/-- **Specialization: `s = ∅` recovers the `∀ r` producer** (the finite-exception producer
*contains* `dcMGF_le_of_termwise_dcWick`).  With no exceptions the remainder is `0`, so the bound is
exactly the Gaussian envelope `q·exp(n y²/2)`. -/
theorem dcMGF_le_of_termwise_dcWick_via_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (y : ℝ) (h : ∀ r, DCWickBound G r) :
    (∑' r : ℕ, dcTerm G y r)
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) := by
  have := dcMGF_le_of_dcWick_except_finite hψ G y (∅ : Finset ℕ) (by intro r _; exact h r)
  simpa using this

/-- **The MGF consumer plugs in directly.**  If `DCWickBound G r` holds off a finite set `s` whose
exceptional excess is **non-positive** (`∑_{r∈s}(dcTerm − gaussTerm) ≤ 0`, i.e. the aggregate of the
sparse violations is dominated by the finitely-many sub-Wick surpluses in `s`), then the clean
Gaussian-form DC-MGF bound `∑' dcTerm ≤ q·exp(n y²/2)` holds, exactly the hypothesis the saddle
consumer `DCSubtractedCoshMGF.period_le_of_dcGaussianMGFBound` takes.  This is the
deductively-weakest clean interface: it does not need `DCWickBound` at the violating depths, only
that their *aggregate* excess is absorbed within `s`. -/
theorem dcMGF_le_of_dcWick_except_finite_aggNonpos {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (y : ℝ) (s : Finset ℕ) (h : ∀ r ∉ s, DCWickBound G r)
    (hagg : ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) ≤ 0) :
    (∑' r : ℕ, dcTerm G y r)
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) := by
  have := dcMGF_le_of_dcWick_except_finite hψ G y s h
  linarith

/-- **End-to-end (finite-exception): `DCWickBound` off a finite `s` with non-positive aggregate
excess at the saddle implies `NearRamanujanSqrtLog`.**  Composes the finite-exception producer
`dcMGF_le_of_dcWick_except_finite_aggNonpos` (delivering the clean `hDCMGF`) with the universal DC
saddle weld `nearRamanujan_of_dcSaddle`.  The deductively-weaker twin of
`DCWickMGFFromTermwise.nearRamanujan_of_dcWick`: it does **not** need `DCWickBound` at the violating
depths, only that their aggregate excess is absorbed within the finite `s`. -/
theorem nearRamanujan_of_dcWick_except_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (s : Finset ℕ) (h : ∀ r ∉ s, DCWickBound G r)
    (hagg : ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) ≤ 0) :
    NearRamanujanSqrtLog ψ G (saddleConst F G y) := by
  refine nearRamanujan_of_dcSaddle hψ G hy hn hL hsaddle ?_
  have := dcMGF_le_of_dcWick_except_finite_aggNonpos hψ G y s h hagg
  simpa [dcTerm] using this

/-- **End-to-end (finite-exception): the δ*-pinning prize floor.**  The full satisfiable spine on
the finite-exception hypothesis: `DCWickBound` off a finite `s` with non-positive aggregate excess
at the saddle implies `PrizeFloor`, through `C₀ = saddleConst F G y*`.  Deductively-weaker twin of
`DCWickMGFFromTermwise.prizeFloor_of_dcWick`.  Still NOT a CORE closure: the open prize is whether a
thin `μ_n` realizes such a finite-exception `DCWickBound` configuration at depth `r ≈ log q`. -/
theorem prizeFloor_of_dcWick_except_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ)) (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hq : (G.card : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (s : Finset ℕ) (h : ∀ r ∉ s, DCWickBound G r)
    (hagg : ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) ≤ 0) :
    PrizeFloor ψ G (saddleConst F G y) := by
  refine prizeFloor_of_dcSaddle hψ G hy hn hq1 hq hL hsaddle ?_
  have := dcMGF_le_of_dcWick_except_finite_aggNonpos hψ G y s h hagg
  simpa [dcTerm] using this

end ProximityGap.Frontier.DCWickMGFFiniteException

/-! ## Axiom audit -/
#print axioms
  ProximityGap.Frontier.DCWickMGFFiniteException.dcMGF_le_of_dcWick_except_finite
#print axioms
  ProximityGap.Frontier.DCWickMGFFiniteException.dcMGF_le_of_termwise_dcWick_via_finite
#print axioms
  ProximityGap.Frontier.DCWickMGFFiniteException.dcMGF_le_of_dcWick_except_finite_aggNonpos
#print axioms
  ProximityGap.Frontier.DCWickMGFFiniteException.nearRamanujan_of_dcWick_except_finite
#print axioms
  ProximityGap.Frontier.DCWickMGFFiniteException.prizeFloor_of_dcWick_except_finite
