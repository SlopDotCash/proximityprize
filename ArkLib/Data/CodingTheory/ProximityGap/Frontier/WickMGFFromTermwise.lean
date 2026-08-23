/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoshMGFSaddle
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFSaddleAssembled
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.RawMGFSaddleVacuity
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The termwise Wick bound ⟹ the single open MGF inequality (#444 §6.2 — the producer of `hMGF`)

Every cosh-MGF saddle consumer in tree (`_CoshMGFSaddle.period_le_of_mgfBound`,
`CoshMGFSaddleAssembled.period_le_saddle_closedForm`, and through it
`NearRamanujanFromSaddle.nearRamanujan_of_saddle`) takes the **single open inequality**

> `MGF(y) := ∑' r, (q · E_r(G)) · y^{2r} / (2r)!  ≤  q · exp(n · y² / 2)`   (`hMGF`)

as an *unproven hypothesis*.  NO in-tree file produces it.  This file produces it from the
**termwise** real-Gaussian energy bound — the in-tree carrier of the prize's open core,

> `GaussianEnergyBound G r := E_r(G) ≤ (2r−1)‼ · n^r`   (for every `r`)

— which is **PROVEN unconditionally in characteristic 0** for `μ_{2^k}`
(`_CharZeroWickEnergy.gaussianEnergyBound_dyadic`), but char-0 fields are infinite so that bound
does NOT apply to this finite-field (`[Fintype F]`, char `p`) saddle setting.  Over `F_q` the
termwise hypothesis is exactly the open char-`p` core.

**The honest verdict (refutation-with-mechanism).**  Composing the producer with the just-landed
`RawMGFSaddleVacuity.rawMGF_ge_dc` (`RawMGF(y) ≥ cosh(n·y)`, the `b=0` DC term, since `‖η_0‖ = n`)
proves the **termwise raw-`E_r` Wick bound is UNSATISFIABLE wherever the DC term dominates the
saddle RHS** (`q·exp(n y²/2) < cosh(n y)`): `mgf_unsat_of_dc_gt`.  In the prize regime `q = n^β`
this strict gap holds at the saddle for every `n ≥ 2^6` (probe-verified there), so the raw Wick
bound (the whole basis of the raw saddle route) cannot hold at the prize.  This SHARPENS the vacuity
localization from "the raw saddle hypothesis is vacuous" to "the termwise raw Wick bound itself is
unsatisfiable at the prize," forcing the move to the **DC-subtracted** `A_r` form (#444 §8 /
`DCEnergyEssential`).  CORE stays OPEN.

## The mechanism (exact, real-analysis)

The exponential series gives `exp(n y²/2) = ∑' r, (n y²/2)^r / r! = ∑' r, n^r y^{2r} / (2^r r!)`.
The **odd double-factorial coefficient identity** (Mathlib `factorial_eq_mul_doubleFactorial` +
`doubleFactorial_two_mul`) is

> `(2r)! = 2^r · r! · (2r−1)‼`            (`factorial_two_mul_eq`)

so `(2r−1)‼ / (2r)! = 1 / (2^r r!)`, and the termwise bound `E_r ≤ (2r−1)‼ n^r` lifts to

> `q · E_r · y^{2r} / (2r)!  ≤  q · (2r−1)‼ n^r · y^{2r}/(2r)!  =  q · n^r y^{2r} / (2^r r!)`,

a term of the exp series.  Summing (`tsum_le_tsum`, both summable — the dominating series is the
exp series, the dominated one then summable by comparison) yields exactly the open `hMGF`.

## What is and is NOT proved

- **PROVED (`mgf_le_of_termwise_gaussianEnergyBound`):** `(∀ r, GaussianEnergyBound G r) ⟹ hMGF`
  for every real `y` (no positivity needed), RHS `q · exp(n y²/2)` — the exact `hMGF`.
- **NOT proved (honest, the open prize):** the termwise hypothesis `∀ r, GaussianEnergyBound G r`
  ITSELF in char `p` at the prize regime.  It is PROVEN in char 0 for `μ_{2^k}`
  (`gaussianEnergyBound_dyadic`); in char `p` it fails for `r ≳ log q` (spurious mod-`p`
  vanishing), which is the open core of #444.  This file is the deductive WELD, not a closure.

All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

set_option autoImplicit false

namespace ProximityGap.Frontier.WickMGFFromTermwise

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The coefficient identity** `(2r)! = 2^r · r! · (2r−1)‼` (as naturals).
For `r ≥ 1`, write `2r = (2r−1)+1`, so `(2r)! = (2r)‼ · (2r−1)‼ = (2^r · r!) · (2r−1)‼`
(`factorial_eq_mul_doubleFactorial` + `doubleFactorial_two_mul`).  The `r = 0` case is `1 = 1`. -/
theorem factorial_two_mul_eq (r : ℕ) :
    (2 * r).factorial = 2 ^ r * r.factorial * Nat.doubleFactorial (2 * r - 1) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · -- 2r = (2r-1)+1, so (2r)! = ((2r-1)+1)‼ * (2r-1)‼ = (2r)‼ * (2r-1)‼ = (2^r r!) * (2r-1)‼
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e2, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
      Nat.factorial_eq_mul_doubleFactorial (2 * m + 1),
      show (2 * m + 1 + 1) = 2 * (m + 1) by ring, Nat.doubleFactorial_two_mul]

/-- **The coefficient identity over `ℝ`**, in the divided form actually consumed:
`(2r−1)‼ / (2r)! = 1 / (2^r · r!)`, equivalently `(2r−1)‼ * (2^r * r!) = (2r)!`. -/
theorem doubleFactorial_div_factorial_eq (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) / ((2 * r).factorial : ℝ)
      = 1 / ((2 : ℝ) ^ r * r.factorial) := by
  have hfac : ((2 * r).factorial : ℝ)
      = (2 : ℝ) ^ r * r.factorial * (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
    have := factorial_two_mul_eq r
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at hcast
    linarith [hcast]
  have hpos2 : ((2 : ℝ) ^ r * r.factorial) ≠ 0 := by positivity
  have hdfne : (Nat.doubleFactorial (2 * r - 1) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
      exact_mod_cast (2 * r - 1).doubleFactorial_pos
    exact ne_of_gt this
  rw [hfac]
  field_simp

/-- **The Gaussian / exp-series term identity.** The `r`-th term of `q · exp(n y²/2)` is
`q · n^r · y^{2r} / (2^r · r!)`.  (Pure rewriting of `(n y²/2)^r / r!`.) -/
theorem exp_term_eq (q n y : ℝ) (r : ℕ) :
    q * ((n * y ^ 2 / 2) ^ r / r.factorial)
      = q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
  have hkey : (n * y ^ 2 / 2) ^ r = n ^ r * y ^ (2 * r) / (2 : ℝ) ^ r := by
    rw [div_pow, mul_pow, pow_mul]
  rw [hkey]
  ring

/-- **`q · exp(n y²/2)` as a tsum of the Gaussian terms.**  Via `Real.exp_eq_exp_ℝ` +
`NormedSpace.exp_eq_tsum_div` (`exp x = ∑' k, x^k / k!`) and `exp_term_eq`. -/
theorem q_exp_eq_tsum (q n y : ℝ) :
    q * Real.exp (n * y ^ 2 / 2)
      = ∑' r : ℕ, q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
  have hexp : Real.exp (n * y ^ 2 / 2)
      = ∑' r : ℕ, (n * y ^ 2 / 2) ^ r / r.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, ← tsum_mul_left]
  exact tsum_congr (fun r => exp_term_eq q n y r)

/-- Summability of the Gaussian (exp) series of terms `q · n^r y^{2r} / (2^r r!)`.
Pulled back from summability of the `exp` power series `∑ x^r/r!`. -/
theorem summable_gaussianTerms (q n y : ℝ) :
    Summable (fun r : ℕ => q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial)) := by
  have hbase : Summable (fun r : ℕ => (n * y ^ 2 / 2) ^ r / r.factorial) := by
    simpa using (Real.summable_pow_div_factorial (n * y ^ 2 / 2))
  have heq : (fun r : ℕ => q * ((n * y ^ 2 / 2) ^ r / r.factorial))
      = (fun r : ℕ => q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial)) :=
    funext (fun r => exp_term_eq q n y r)
  have := (hbase.mul_left q)
  rwa [heq] at this

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **The termwise comparison.** For `y` real, `0 ≤ q`, and the termwise Wick bound
`E_r ≤ (2r−1)‼ n^r`, the `r`-th MGF term is `≤` the `r`-th Gaussian term:
`q · E_r · y^{2r} / (2r)! ≤ q · n^r y^{2r} / (2^r r!)`.
(`Fintype F` is unused — a pure real-analysis fact about `rEnergy`/`G.card`.) -/
theorem mgfTerm_le_gaussianTerm {G : Finset F} {r : ℕ} (q : ℝ) (hq : 0 ≤ q) (y : ℝ)
    (h : GaussianEnergyBound G r) :
    (q * (rEnergy G r : ℝ)) * y ^ (2 * r) / ((2 * r).factorial : ℝ)
      ≤ q * (G.card : ℝ) ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
  have hEr : (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := h
  have hfacpos : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast (2 * r).factorial_pos
  have hy2 : (0 : ℝ) ≤ y ^ (2 * r) := by
    rw [pow_mul]; positivity
  -- Coefficient: (2r-1)‼ / (2r)! = 1 / (2^r r!).
  have hcoeff := doubleFactorial_div_factorial_eq r
  -- Rewrite both sides into the common factor `q · y^{2r}` times a scalar, then compare scalars.
  have hsplitL :
      (q * (rEnergy G r : ℝ)) * y ^ (2 * r) / ((2 * r).factorial : ℝ)
        = (q * y ^ (2 * r)) * ((rEnergy G r : ℝ) / ((2 * r).factorial : ℝ)) := by ring
  have hsplitR :
      q * (G.card : ℝ) ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial)
        = (q * y ^ (2 * r)) * ((G.card : ℝ) ^ r / ((2 : ℝ) ^ r * r.factorial)) := by ring
  rw [hsplitL, hsplitR]
  have hfront : (0 : ℝ) ≤ q * y ^ (2 * r) := by
    have : (0 : ℝ) ≤ q := hq
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hfront
  -- E_r/(2r)! ≤ (2r-1)‼ n^r /(2r)! = n^r/(2^r r!)
  have h1 : (rEnergy G r : ℝ) / ((2 * r).factorial : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) / ((2 * r).factorial : ℝ) := by
    gcongr
  have h2 : ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) / ((2 * r).factorial : ℝ)
      = (G.card : ℝ) ^ r / ((2 : ℝ) ^ r * r.factorial) := by
    rw [mul_comm (Nat.doubleFactorial (2 * r - 1) : ℝ) ((G.card : ℝ) ^ r), mul_div_assoc, hcoeff]
    ring
  rw [h2] at h1
  exact h1

/-- **THE BRIDGE — the producer of `hMGF`.**  If the termwise real-Gaussian energy bound
`GaussianEnergyBound G r` holds for *every* `r` (PROVEN char-0 for `μ_{2^k}`,
`gaussianEnergyBound_dyadic`; the open prize in char `p`), then the **single open MGF inequality**
the cosh-MGF saddle consumers take as hypothesis holds:
`∑' r, (q · E_r) · y^{2r} / (2r)! ≤ q · exp(n · y²/2)`.  No positivity on `y` needed. -/
theorem mgf_le_of_termwise_gaussianEnergyBound (G : Finset F) (y : ℝ)
    (h : ∀ r, GaussianEnergyBound G r) :
    (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  have hqpos : (0 : ℝ) < q := by
    rw [hq]; exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) ≤ q := hqpos.le
  -- RHS as a tsum of Gaussian terms
  have hRHS : q * Real.exp (n * y ^ 2 / 2)
      = ∑' r : ℕ, q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := q_exp_eq_tsum q n y
  -- both series summable
  have hsumR : Summable (fun r : ℕ => q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial)) :=
    summable_gaussianTerms q n y
  have hterm : ∀ r : ℕ,
      (q * (rEnergy G r : ℝ)) * y ^ (2 * r) / ((2 * r).factorial : ℝ)
        ≤ q * n ^ r * y ^ (2 * r) / ((2 : ℝ) ^ r * r.factorial) := by
    intro r
    have := mgfTerm_le_gaussianTerm (G := G) (r := r) q hq0 y (h r)
    -- the RHS of `mgfTerm_le_gaussianTerm` is `q * n^r * y^{2r} / (2^r r!)` modulo `n = G.card`
    simpa [hn, mul_assoc] using this
  have hsumL : Summable (fun r : ℕ =>
      (q * (rEnergy G r : ℝ)) * y ^ (2 * r) / ((2 * r).factorial : ℝ)) := by
    apply Summable.of_nonneg_of_le ?_ hterm hsumR
    intro r
    have hyr : (0 : ℝ) ≤ y ^ (2 * r) := by rw [pow_mul]; positivity
    have hq0' : (0 : ℝ) ≤ q := hq0
    have hfacpos : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast (2 * r).factorial_pos
    positivity
  -- compare the two tsums
  rw [hRHS]
  have hLHSeq :
      (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
        = ∑' r : ℕ, (q * (rEnergy G r : ℝ)) * y ^ (2 * r) / ((2 * r).factorial : ℝ) := by
    rw [hq]
  rw [hLHSeq]
  exact Summable.tsum_le_tsum hterm hsumL hsumR

/-- **End-to-end: termwise Wick (∀r) at the saddle ⇒ the closed-form saddle floor.**  Composing the
bridge with the in-tree saddle consumer `CoshMGFSaddleAssembled.period_le_saddle_closedForm`: at the
saddle `y*` (`y*² = 2 log q / n`, `y* > 0`, `n = |G| > 0`), if the **termwise** real-Gaussian energy
bound `GaussianEnergyBound G r` holds for *every* `r`, then every Gauss period obeys the closed-form
prize floor `‖η_{b₀}‖ ≤ log(2q²)/y*`.

This is the deductive payload of the raw saddle route: the saddle floor's hypothesis `hMGF` is
discharged from the **termwise** raw-`E_r` Wick bound.  Over `F_q` (char `p`) the termwise hyp
`∀ r, GaussianEnergyBound G r` is the open prize core; `mgf_unsat_of_dc_gt` below shows it is
DC-unsatisfiable at the prize, so this conditional is true on a premise that fails there. -/
theorem period_le_saddle_of_termwise_gaussianEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {y : ℝ} (hy : 0 < y) (b₀ : F) (hn : 0 < (G.card : ℝ))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (h : ∀ r, GaussianEnergyBound G r) :
    ‖eta ψ G b₀‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y :=
  ProximityGap.Frontier.CoshMGFSaddleAssembled.period_le_saddle_closedForm
    hψ G hy b₀ hn hsaddle (mgf_le_of_termwise_gaussianEnergyBound G y h)

/-- **The DC-forced unsatisfiability of the termwise raw-`E_r` Wick bound (the honest verdict).**
Composing the producer `mgf_le_of_termwise_gaussianEnergyBound` (termwise Wick gives
`RawMGF(y) ≤ q exp(n y²/2)`) with the DC lower bound `RawMGFSaddleVacuity.rawMGF_ge_dc`
(`cosh(n y) ≤ RawMGF(y)`): if the saddle RHS is below the DC term (`q exp(n y²/2) < cosh(n y)`), the
termwise raw-`E_r` Wick bound `∀ r, GaussianEnergyBound G r` is **impossible**.  In the prize regime
`q = n^β` the strict gap holds at the saddle for every `n ≥ 2^6` (probe-verified in
`RawMGFSaddleVacuity`), so the termwise raw Wick bound — the basis of the raw saddle route — cannot
hold at the prize, mandating the DC-subtracted `A_r` form (#444 §8).  A constraint lemma, not a CORE
closure: it localizes the open target, CORE stays OPEN. -/
theorem mgf_unsat_of_dc_gt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ)
    (hgt : (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)
              < Real.cosh ((G.card : ℝ) * y))
    (h : ∀ r, GaussianEnergyBound G r) : False :=
  ProximityGap.Frontier.RawMGFSaddleVacuity.raw_saddle_hyp_false_of_dc_gt hψ G y hgt
    (mgf_le_of_termwise_gaussianEnergyBound G y h)

end ProximityGap.Frontier.WickMGFFromTermwise

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only, NO `sorryAx`). -/
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms factorial_two_mul_eq
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms doubleFactorial_div_factorial_eq
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms q_exp_eq_tsum
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms mgfTerm_le_gaussianTerm
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms mgf_le_of_termwise_gaussianEnergyBound
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms period_le_saddle_of_termwise_gaussianEnergyBound
open ProximityGap.Frontier.WickMGFFromTermwise in
#print axioms mgf_unsat_of_dc_gt
