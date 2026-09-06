/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Algebra.Field.GeomSum

/-!
# AVENUE Z — the v₂-ultrametric depth-circulant identity `Tr(D²)` and `λ_max` (#444, R1_v2dirac_circulant)

This file lands the **2-adic dyadic depth-circulant** skeleton certificate as a clean, axiom-clean
rational-arithmetic brick. It is a **p-INDEPENDENT, M-ABSENT, prize-INERT** object by construction:
it contains no field `F_p`, no character sum, and no quantity that bounds the prize constant
`M(μ_n) = max_{b≠0} |Σ_{y∈μ_n} e_p(b y)|`. It cannot — and does not claim to — bound `M`.

## The object

On the cyclic group `Z/n` with `n = 2^μ`, consider the **circulant operator** `D` whose symbol is the
inverse dyadic weight `c(d) = 2^{-v₂(d)}` (`v₂ = 2-adic valuation), with the diagonal weight set to
`c(0) = 0`. For a real-symmetric circulant the two spectral invariants of interest are

* the **Hilbert–Schmidt norm** `Tr(D²) = n · Σ_{d=1}^{n-1} c(d)² = n · Σ_{d=1}^{n-1} 4^{-v₂(d)}`, and
* the **top eigenvalue** at the trivial character `λ_max = Σ_{d=0}^{n-1} c(d) = Σ_{d=1}^{n-1} 2^{-v₂(d)}`.

Stratifying `{1,…,n-1}` by the value of `v₂(d)` (`#{d : v₂(d)=j} = n/2^{j+1}` for `j = 0,…,μ-1`),
both sums collapse to **geometric series**:

* `Tr(D²) = Σ_{j=0}^{μ-1} (n/2^{j+1}) · 4^{-j} · n = (n²/2) · Σ_{j<μ} (1/8)^j`,
* `λ_max  = Σ_{j=0}^{μ-1} (n/2^{j+1}) · 2^{-j}     = (n/2)  · Σ_{j<μ} (1/4)^j`.

This file proves, **by pure telescoping of the geometric sum (axiom-clean, all `μ`):**

* `traceSqStratum μ = (4 n² / 7) · (1 - n⁻³)`   (`traceSq_closedForm`),
* `lambdaMaxStratum μ = 2 (n² - 1) / (3 n)`      (`lambdaMax_closedForm`),

where `n = 2^μ` and the `…Stratum` functions are the geometric (already-stratified) sums above —
the genuine pure-telescoping content. The stratification step (a `v₂`-counting identity) is the
combinatorial preprocessing; the rational closed forms below are the load-bearing arithmetic.

## Honesty

* **p-independent.** No `F_p`, no prime, no character appears.
* **M-absent / prize-INERT.** Nothing here is, or bounds, `M`. This is a self-contained spectral
  identity for a fixed dyadic operator; it is a *skeleton certificate*, not a step toward closure.
* `#444` is a recognized OPEN problem; this brick does not close it. `closesOpenCore = false`.

## Numerical anchors (exact, see `traceSq_small` / `lambdaMax_small`)

`μ`:        1     2     3       4        5
`Tr(D²)`:   2     9     73/2    585/4    4681/8
`λ_max`:    1     5/2   21/4    85/8     341/16
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.AvZ

open Finset

/-- The (already `v₂`-stratified) Hilbert–Schmidt invariant
`Tr(D²) = n · Σ_{j<μ} (n/2^{j+1}) · 4^{-j}`, written as `(n²/2) · Σ_{j<μ} (1/8)^j` over `ℚ`,
with `n = 2^μ`. -/
noncomputable def traceSqStratum (μ : ℕ) : ℚ :=
  (((2 : ℚ) ^ μ) ^ 2 / 2) * ∑ j ∈ Finset.range μ, (1 / 8 : ℚ) ^ j

/-- The (already `v₂`-stratified) top-eigenvalue invariant
`λ_max = Σ_{j<μ} (n/2^{j+1}) · 2^{-j} = (n/2) · Σ_{j<μ} (1/4)^j` over `ℚ`, with `n = 2^μ`. -/
noncomputable def lambdaMaxStratum (μ : ℕ) : ℚ :=
  (((2 : ℚ) ^ μ) / 2) * ∑ j ∈ Finset.range μ, (1 / 4 : ℚ) ^ j

/-- Geometric closed form `Σ_{j<μ} (1/8)^j = (8/7)·(1 - (1/8)^μ)`. -/
theorem geom_eighth (μ : ℕ) :
    ∑ j ∈ Finset.range μ, (1 / 8 : ℚ) ^ j = (8 / 7) * (1 - (1 / 8 : ℚ) ^ μ) := by
  have h : (1 / 8 : ℚ) ≠ 1 := by norm_num
  rw [geom_sum_eq h]
  field_simp
  ring

/-- Geometric closed form `Σ_{j<μ} (1/4)^j = (4/3)·(1 - (1/4)^μ)`. -/
theorem geom_quarter (μ : ℕ) :
    ∑ j ∈ Finset.range μ, (1 / 4 : ℚ) ^ j = (4 / 3) * (1 - (1 / 4 : ℚ) ^ μ) := by
  have h : (1 / 4 : ℚ) ≠ 1 := by norm_num
  rw [geom_sum_eq h]
  field_simp
  ring

/-- `(1/8)^μ = 1 / (2^μ)^3` over `ℚ`. -/
theorem inv_eighth_pow (μ : ℕ) : (1 / 8 : ℚ) ^ μ = 1 / ((2 : ℚ) ^ μ) ^ 3 := by
  rw [div_pow, one_pow, ← pow_mul, mul_comm μ 3, pow_mul]
  norm_num

/-- `(1/4)^μ = 1 / (2^μ)^2` over `ℚ`. -/
theorem inv_quarter_pow (μ : ℕ) : (1 / 4 : ℚ) ^ μ = 1 / ((2 : ℚ) ^ μ) ^ 2 := by
  rw [div_pow, one_pow, ← pow_mul, mul_comm μ 2, pow_mul]
  norm_num

/-- **Closed form for the Hilbert–Schmidt invariant.**
`Tr(D²) = (4 n² / 7) · (1 - n⁻³)` with `n = 2^μ`, by pure telescoping. Axiom-clean, all `μ`. -/
theorem traceSq_closedForm (μ : ℕ) :
    traceSqStratum μ
      = (4 * ((2 : ℚ) ^ μ) ^ 2 / 7) * (1 - 1 / ((2 : ℚ) ^ μ) ^ 3) := by
  have hn : ((2 : ℚ) ^ μ) ≠ 0 := by positivity
  unfold traceSqStratum
  rw [geom_eighth, inv_eighth_pow]
  field_simp
  ring

/-- **Closed form for the top eigenvalue.**
`λ_max = 2 (n² - 1) / (3 n)` with `n = 2^μ`, by pure telescoping. Axiom-clean, all `μ`. -/
theorem lambdaMax_closedForm (μ : ℕ) :
    lambdaMaxStratum μ
      = 2 * (((2 : ℚ) ^ μ) ^ 2 - 1) / (3 * (2 : ℚ) ^ μ) := by
  have hn : ((2 : ℚ) ^ μ) ≠ 0 := by positivity
  unfold lambdaMaxStratum
  rw [geom_quarter, inv_quarter_pow]
  field_simp
  ring

/-- Concrete exact checks of `Tr(D²)` for `μ = 1,…,5` (non-vacuous numeric anchors). -/
theorem traceSq_small :
    traceSqStratum 1 = 2 ∧ traceSqStratum 2 = 9 ∧ traceSqStratum 3 = 73 / 2 ∧
      traceSqStratum 4 = 585 / 4 ∧ traceSqStratum 5 = 4681 / 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold traceSqStratum; norm_num [Finset.sum_range_succ]

/-- Concrete exact checks of `λ_max` for `μ = 1,…,5` (non-vacuous numeric anchors). -/
theorem lambdaMax_small :
    lambdaMaxStratum 1 = 1 ∧ lambdaMaxStratum 2 = 5 / 2 ∧ lambdaMaxStratum 3 = 21 / 4 ∧
      lambdaMaxStratum 4 = 85 / 8 ∧ lambdaMaxStratum 5 = 341 / 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold lambdaMaxStratum; norm_num [Finset.sum_range_succ]

/-- Consistency cross-check of the two closed forms against their definitions at `μ = 6`. -/
theorem closedForm_check_six :
    traceSqStratum 6 = (4 * ((2 : ℚ) ^ 6) ^ 2 / 7) * (1 - 1 / ((2 : ℚ) ^ 6) ^ 3) ∧
      lambdaMaxStratum 6 = 2 * (((2 : ℚ) ^ 6) ^ 2 - 1) / (3 * (2 : ℚ) ^ 6) :=
  ⟨traceSq_closedForm 6, lambdaMax_closedForm 6⟩

end ProximityGap.Frontier.AvZ

#print axioms ProximityGap.Frontier.AvZ.traceSq_closedForm
#print axioms ProximityGap.Frontier.AvZ.lambdaMax_closedForm
#print axioms ProximityGap.Frontier.AvZ.traceSq_small
#print axioms ProximityGap.Frontier.AvZ.lambdaMax_small
