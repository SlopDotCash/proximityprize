/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RandomLinearCodeEquidistribution

/-!
# GLMRSW22 first moment: expected count of nonzero random-linear codewords in a set

Building on the per-message uniform marginal `vecMul_uniform_mem_prob`
(`Pr[m ᵥ* G ∈ S] = |S| / qⁿ` for a fixed nonzero message `m`, proved in
`RandomLinearCodeEquidistribution.lean`), this file discharges the **linearity-of-expectation**
step its docstring describes but leaves open: summing that per-message probability over the
`qᵏ − 1` nonzero messages gives the first moment

`E[#{ m ≠ 0 : m ᵥ* G ∈ S }] = (qᵏ − 1) · |S| / qⁿ`.

This is the first-moment count feeding the GLMRSW22 / ABF26 T3.11 random-linear-code list-size
estimate (issue #79). It does **not** close the list-size *lower* bound itself, which additionally
needs the second-moment / variance combinatorics — that remains the deep residual.

## Main results

* `sum_vecMul_mem_prob_nonzero` — the first-moment sum equals
  `(#nonzero messages) • (|S| / qⁿ)`.
* `card_filter_ne_zero` — `#{ m : Fin k → F // m ≠ 0 } = qᵏ − 1` as a `Finset` count.
* `firstMoment_expected_count` — the closed form `(qᵏ − 1) • (|S| / qⁿ)`.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix ENNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **First-moment sum.** Summing the per-message hit probability over the nonzero messages:
`∑_{m ≠ 0} Pr[m ᵥ* G ∈ S] = (#nonzero messages) • (|S| / qⁿ)`. Each summand is the constant
`|S| / qⁿ` from `vecMul_uniform_mem_prob`. -/
theorem sum_vecMul_mem_prob_nonzero (S : Set (ι → F)) [Fintype S] :
    (∑ m ∈ Finset.univ.filter (fun m : Fin k → F => m ≠ 0),
        ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => m ᵥ* G)).toOuterMeasure S)
      = (Finset.univ.filter (fun m : Fin k → F => m ≠ 0)).card
          • (Fintype.card S / Fintype.card (ι → F) : ℝ≥0∞) := by
  have hconst : ∀ m ∈ Finset.univ.filter (fun m : Fin k → F => m ≠ 0),
      ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => m ᵥ* G)).toOuterMeasure S
        = (Fintype.card S / Fintype.card (ι → F) : ℝ≥0∞) :=
    fun m hm => vecMul_uniform_mem_prob (Finset.mem_filter.1 hm).2 S
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]

/-- The number of nonzero messages is `qᵏ − 1`. -/
theorem card_filter_ne_zero :
    (Finset.univ.filter (fun m : Fin k → F => m ≠ 0)).card
      = Fintype.card (Fin k → F) - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- **First moment, closed form.** The expected number of nonzero messages whose random-linear
codeword lands in `S` is `(qᵏ − 1) · |S| / qⁿ`. -/
theorem firstMoment_expected_count (S : Set (ι → F)) [Fintype S] :
    (∑ m ∈ Finset.univ.filter (fun m : Fin k → F => m ≠ 0),
        ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => m ᵥ* G)).toOuterMeasure S)
      = (Fintype.card (Fin k → F) - 1)
          • (Fintype.card S / Fintype.card (ι → F) : ℝ≥0∞) := by
  rw [sum_vecMul_mem_prob_nonzero, card_filter_ne_zero]

end ArkLib.RandomLinearCode

-- Axiom audit: every public result must reduce to the standard kernel axioms only.
#print axioms ArkLib.RandomLinearCode.sum_vecMul_mem_prob_nonzero
#print axioms ArkLib.RandomLinearCode.card_filter_ne_zero
#print axioms ArkLib.RandomLinearCode.firstMoment_expected_count
