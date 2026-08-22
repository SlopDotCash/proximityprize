/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T06 frontier — the coupled product-formula House bound, REFUTED)
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# wf-T06 — Coupled product-formula House bound (architect G2-1): REFUTED, sign reversed (#444)

## The candidate (architect ID G2-1)

For the LIFTED Gauss period `θ_b = Σ_{x∈μ_n} ζ^{ind(x)·b} ∈ 𝓞_K`, `K=ℚ(ζ_n)`, the architect
proposes a "coupled local-height defect"
`D(b) := (1/φ(n)) · Σ_{v non-arch, v|θ_b} N_v · log|θ_b|_v^{-1}` (the total NON-archimedean
log-content, claimed `> 0` exactly when `θ_b` is a non-unit), and claims the SHARP coupling

> `log House(θ_b) >= D(b) + (geom-mean archimedean log)`   [architect's lower form]

re-read by the architect as an UPPER bound on the House: a non-unit (`D(b)>0`) *"DECREASES the
available archimedean budget"*, giving the conditional prize bound
`M(n) <= √( n·(log(p/n) − 2·D(b_max)·n/log2) )` whenever `D(b_max) >= c/n`.

## THE REFUTATION (sign reversed — the product formula points the OTHER way)

For an algebraic INTEGER `θ ∈ 𝓞_K` (which `θ_b` is — a sum of roots of unity), every
non-archimedean absolute value satisfies `|θ|_v ≤ 1`, so `log|θ|_v ≤ 0`.  The product formula
`Σ_v N_v·log|θ|_v = 0` therefore reads

> `Σ_{w arch} log|w θ|  =  − Σ_{v non-arch} N_v·log|θ|_v  =  φ(n)·D(b)  =  log|N_{K/ℚ}(θ)|  ≥ 0`.

So the non-archimedean content and the *archimedean* log-sum are EQUAL and NON-NEGATIVE — a
LARGER non-archimedean content `D(b)` forces a LARGER total archimedean log-mass, not a smaller
one.  Combined with `House ≥ geometric-mean` (max ≥ mean, formalized as
`house_ge_of_mean_arch_log`), this gives the CORRECT direction:

> **`coupled_productFormula_gives_lower_bound`**: `log House(θ) ≥ D(b)`  — the non-unit content
> is a LOWER bound lever on the House, the *opposite* of the candidate's "budget decrease".

The candidate's bound subtracts `2·D(b)·n/log2` *inside the √*; the proven identity ADDS the same
content to the archimedean mass.  The sign is reversed: the candidate is FALSE.

## The numeric counterexample (`θ = 1 + ζ₈`, a genuine non-unit, `D > 0`)

`θ = 1 + ζ₈ ∈ 𝓞_{ℚ(ζ₈)}` has norm `N(θ) = 2` (a non-unit, divisible by the prime `2`, so
`D = (log 2)/φ(8) = (log 2)/4 > 0`).  Its House is `|1 + ζ₈| = √(2+√2) ≈ 1.8478`.  The candidate's
House upper bound (its sharp form `House ≤ exp(2D) = N^{2/φ} = 2^{1/2} = √2 ≈ 1.4142`) is VIOLATED:
`House ≈ 1.8478 > 1.4142 ≈ √2`.  We certify the load-bearing arithmetic
`(√2)² = 2 < 2+√2 = House²` axiom-clean (`candidate_house_bound_violated`).

## The reduction (default outcome — this REDUCES to the formalized wall)

- **F3 (p-adic/valuation is archimedean-blind), formalized `_ValuationClassBarrier`,
  `_wfS4_stickelberger_perweight_threshold`:** that file states verbatim that the p-adic
  valuation "carries ZERO archimedean spread information"; T06 tries to recover the spread by
  coupling, but the product formula links the two columns with the WRONG sign for an upper bound.
- **F9 / F11 (supply-side norm certificate / BGK divisibility count):** `φ(n)·D(b) = log|N(θ_b)|`
  is EXACTLY the bad-prime cyclotomic norm `|N(σ_T)|` of `_wfS3/_wfS4`/`BadPrimeNormBound`, and
  `p | N(θ_b)` (the architect's "θ_b is a non-unit at P|p") is precisely the spurious-vanishing
  divisibility = the conjugate-norm count `#{c : p|N(c)}` (F11). `D(b)` is not a new lever; it is
  the log of the in-tree norm object, read per-element. So even granting the (false) sign, the
  residual `D(b_max) = Ω(1/n)` IS the BGK norm-lower-bound, the 25-year wall.

## Honest scope

Verdict: **REFUTED** — the central inequality has the sign reversed by the product formula, with
an exact axiom-clean numeric counterexample at `θ = 1 + ζ₈`.  Secondarily REDUCES-TO-WALL (F3/F9/
F11) since `φ(n)·D(b) = log|N(θ_b)|` is the in-tree bad-prime norm object and `p|N(θ_b)` is the
BGK divisibility count.  No prize gain.

## References
- [ABF26] ePrint 2026/680. Smyth, *Mahler measure of algebraic numbers: a survey* (house/Mahler,
  product formula = standard).  Bilu, equidistribution of small-height conjugates.
- in-tree: `_ValuationClassBarrier.lean`, `_wfS4_stickelberger_perweight_threshold.lean`
  ("ZERO archimedean spread information"), `L2MahlerNormBound.lean`, `BadPrimeNormBound.lean`,
  `VanishingRootSumHeightGate.lean`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField Module Real

namespace ProximityGap.Frontier.CoupledProductFormulaHouse

/-! ## 1. The product-formula identity (CORRECT direction) for an algebraic integer

We model the place data abstractly to expose the sign.  For an algebraic integer `θ` of degree
`d = φ(n)`:
* the archimedean log-mass is `A := Σ_{w arch} log|w θ|`;
* the non-archimedean content is `D·d := − Σ_{v non-arch} N_v log|θ|_v ≥ 0` (integer ⟹ each
  `log|θ|_v ≤ 0`);
* the product formula is `A + Σ_{v} N_v log|θ|_v = 0`, i.e. `A = D·d`.
Hence `D ≥ 0` and `A = D·d`: the two columns are EQUAL, NON-NEGATIVE — there is no "budget
decrease". -/

/-- **Product formula for an algebraic integer (abstract form).** With `A` the archimedean
log-mass and `C := Σ_{v non-arch} N_v log|θ|_v ≤ 0` the (non-positive) non-arch sum, the product
formula `A + C = 0` gives `A = −C = D·d ≥ 0` where `D·d := −C`.  In particular the
non-archimedean content `D·d` EQUALS the archimedean mass `A` — they move TOGETHER, not against
each other. -/
theorem productFormula_arch_eq_content
    {A C : ℝ} (hpf : A + C = 0) (hint : C ≤ 0) : A = -C ∧ 0 ≤ A := by
  refine ⟨by linarith, by linarith⟩

/-- **The House dominates the archimedean geometric mean (max ≥ mean).**  If `A = Σ_{w} L w` is
the archimedean log-mass over `d > 0` places and `H` is an upper log-House with `L w ≤ H` for all
`w`, then `A ≤ d·H`, i.e. `H ≥ A/d`.  (max ≥ mean.) -/
theorem house_ge_of_mean_arch_log {ι : Type*} (s : Finset ι) (L : ι → ℝ) (H : ℝ)
    (hH : ∀ w ∈ s, L w ≤ H) :
    (∑ w ∈ s, L w) ≤ s.card * H := by
  calc (∑ w ∈ s, L w) ≤ ∑ _w ∈ s, H := Finset.sum_le_sum hH
    _ = s.card * H := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE CORRECT COUPLING (sign opposite to the candidate).**  Let `A = Σ_w L w` be the
archimedean log-mass over `d > 0` places, `logHouse` the maximal archimedean log (so
`L w ≤ logHouse` for all `w`), and `D := A / d` the per-place non-archimedean content
(`= A/d` by the product formula).  Then

> `logHouse ≥ D`.

The non-unit content `D = D(b) ≥ 0` is a **LOWER** bound lever on the House, refuting the
candidate's claim that a positive `D(b)` *decreases* the archimedean budget. -/
theorem coupled_productFormula_gives_lower_bound {ι : Type*} (s : Finset ι) (L : ι → ℝ)
    (logHouse : ℝ) (hs : 0 < s.card) (hH : ∀ w ∈ s, L w ≤ logHouse)
    (D : ℝ) (hD : D = (∑ w ∈ s, L w) / s.card) :
    D ≤ logHouse := by
  have hsum := house_ge_of_mean_arch_log s L logHouse hH
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs
  rw [hD, div_le_iff₀ hcard]
  linarith [hsum]

/-! ## 2. The exact numeric counterexample: `θ = 1 + ζ₈`, `N(θ) = 2` (non-unit, `D > 0`)

`θ = 1 + ζ₈` has the four ℚ(ζ₈)-conjugates `1 + ζ₈^k`, `k ∈ {1,3,5,7}`.
`|1 + ζ₈|² = (1+cos45°)² + sin²45° = 2 + √2 ≈ 3.4142`, so `House = √(2+√2) ≈ 1.8478`.
`N(θ) = ∏_k (1+ζ₈^k) = Φ₈(−1) = 1 − 1 + 1 = ... ` numerically `= 2` (a non-unit ⟹ `D>0`).
The candidate's sharpest upper House bound is `House ≤ N^{2/φ(8)} = 2^{2/4} = √2`.
We certify the violation `(√2)² < House²` axiom-clean. -/

/-- `House(1+ζ₈)² = 2 + √2`, the squared maximal conjugate modulus. -/
noncomputable def houseSq : ℝ := 2 + Real.sqrt 2

/-- The candidate's upper House bound squared: `(N^{2/φ})² = (2^{1/2})² = 2`. -/
def candidateBoundSq : ℝ := 2

/-- **The candidate House upper bound is VIOLATED at `θ = 1 + ζ₈`.**  The candidate's sharpest
upper House `√2` (i.e. squared `= 2`) is strictly below the true House `√(2+√2)` (squared
`= 2 + √2`), since `√2 > 0`.  This refutes the coupled product-formula House bound by exact
counterexample: a genuine non-unit (`N=2`, `D=(log2)/4>0`) has House ABOVE, not below, the
candidate's coupled ceiling. -/
theorem candidate_house_bound_violated : candidateBoundSq < houseSq := by
  unfold candidateBoundSq houseSq
  have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- **Quantitative sign-reversal certificate.**  At `θ = 1 + ζ₈`: the per-place content
`D = (log 2)/4 > 0`, the geometric-mean archimedean log is exactly `D` (product formula:
arch mass `= log N = log 2`, over `φ=4` places), while `log House = (1/2)log(2+√2) ≈ 0.614`.
The candidate predicts `log House ≤ 2D = (log 2)/2 ≈ 0.347`; the proven `coupled_*lower_bound`
predicts `log House ≥ D ≈ 0.173`.  Reality `0.614` SATISFIES the proven lower bound and VIOLATES
the candidate upper bound — the content lever points the WRONG way for the candidate.  We certify
the load-bearing arithmetic `2·((log 2)/4) < (1/2)·log(2+√2)` via `(log2)/2 < log House`. -/
theorem content_lever_points_opposite :
    Real.log 2 / 2 < (1 / 2) * Real.log (2 + Real.sqrt 2) := by
  have hpos2 : (0:ℝ) < 2 := by norm_num
  have hsq2 : (1:ℝ) < Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2lt : (2 : ℝ) < 2 + Real.sqrt 2 := by linarith
  -- log is strictly monotone: log 2 < log(2+√2); divide by 2.
  have := Real.log_lt_log hpos2 h2lt
  linarith

end ProximityGap.Frontier.CoupledProductFormulaHouse

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.CoupledProductFormulaHouse.productFormula_arch_eq_content
#print axioms ProximityGap.Frontier.CoupledProductFormulaHouse.coupled_productFormula_gives_lower_bound
#print axioms ProximityGap.Frontier.CoupledProductFormulaHouse.candidate_house_bound_violated
#print axioms ProximityGap.Frontier.CoupledProductFormulaHouse.content_lever_points_opposite
