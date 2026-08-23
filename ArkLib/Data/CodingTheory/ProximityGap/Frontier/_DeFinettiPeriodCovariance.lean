/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodFirstMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodRealValued

/-!
# The exact pairwise covariance of the Gauss-period family: `Cov = −Var/(m−1)` (#407)

The crack-audit's top closure re-attack (CRACK 7 / comment c.314-N4) is to prove the BGK floor
`max_{b≠0}‖η_b‖ ≤ √(2n·log(p/n))` as an **extreme-value theorem** for the *exchangeable de-Finetti*
period family `{η_b}` over the nonzero frequencies. Three pieces of the de-Finetti substrate are
already landed and axiom-clean on main:

* first moment   `Σ_{b≠0} η_b = −|G|`               (`subgroup_gaussSum_firstMoment`),
* second moment  `Σ_{b≠0} ‖η_b‖² = q·|G| − |G|²`     (`sum_sq_erase_zero`),
* real-valuedness `conj(η_b) = η_b` when `−1 ∈ G`     (`eta_conj_eq_of_neg_closed`).

This file lands the **fourth** piece — the *exact* pairwise (de-Finetti / exchangeable) covariance
structure forced by a **fixed sum**. The genuinely-clean, fully-provable mathematical content is a
**general fact about any family with a fixed sum** (nothing period-specific):

> **Centered off-diagonal = minus diagonal.** For any `x : ι → R` over a finite index set `S`,
> with mean `x̄ = (Σ x)/|S|`,
> `Σ_{i∈S} Σ_{j∈S, j≠i} (x_i − x̄)(x_j − x̄) = − Σ_{i∈S} (x_i − x̄)²`.

Equivalently the **off-diagonal of the products** is `(Σx)² − Σx²` (Newton's identity), and centering
makes the *total* sum vanish so the off-diagonal is exactly minus the diagonal. The de-Finetti
`Cov = −Var/(m−1)` consequence is then arithmetic: averaging the LHS over the `M(M−1)` ordered
off-diagonal pairs and the RHS diagonal over the `M` indices (`M = |S|`),

> `(avg pairwise covariance) = − (variance) / (M − 1)`.

This is the **EXACT negative correlation** that a fixed sum imposes on an exchangeable family — the
substrate the EVT/Gumbel max consumes. We then **specialize** to the period family by plugging in the
two landed moments: over the `M = q − 1` nonzero frequencies the mean is `μ̄ = −|G|/(q−1)` and the
variance `Var = (q|G|−|G|²)/(q−1) − μ̄²`, so the average pairwise covariance of the (real, when
`−1∈G`) periods is exactly `−Var/(q−2)`.

**Honesty note.** The centered-family identity and the `Cov = −Var/(M−1)` relation are GENERAL
(true for any fixed-sum family); the *exchangeability* (that the periods are identically distributed
across cosets) is the structural de-Finetti input and is not itself a theorem here. What is proven is
the algebraic covariance identity and its period specialization wired to the two landed moments.
Axiom-clean. Issue #407.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodParsevalFloor
open ProximityGap.Frontier.GaussPeriodFirstMoment

namespace ProximityGap.Frontier.DeFinettiPeriodCovariance

/-! ## Part 1 — the general fixed-sum / centered-family covariance identity

These are pure algebra over a commutative ring (for the off-diagonal Newton form) or a field (for the
centered/mean form). They are completely independent of the Gauss periods; we specialize in Part 2. -/

section General

variable {ι : Type*} [DecidableEq ι]

/-- **Newton off-diagonal identity.** Over any commutative ring, the sum of the *ordered* off-diagonal
products of a family equals the square of the sum minus the sum of squares:
`Σ_{i∈S} Σ_{j∈S, j≠i} x_i x_j = (Σ x)² − Σ x²`. (The `i = j` diagonal contributes exactly `Σ x²`.) -/
theorem sum_offDiag_mul {R : Type*} [CommRing R] (S : Finset ι) (x : ι → R) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, x i * x j = (∑ i ∈ S, x i) ^ 2 - ∑ i ∈ S, x i ^ 2 := by
  have key : (∑ i ∈ S, x i) ^ 2 = (∑ i ∈ S, x i ^ 2) + ∑ i ∈ S, ∑ j ∈ S.erase i, x i * x j := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    -- split the inner `∑_{j∈S} x i * x j` at the diagonal `j = i`
    rw [← Finset.add_sum_erase S (fun j => x i * x j) hi, ← sq]
  rw [key]; ring

/-- **Centered total sum vanishes.** For a family over a finite set `S` of size `M` with mean
`x̄ = (Σ x)/M`, the centered family `x_i − x̄` sums to zero: `Σ_{i∈S} (x_i − x̄) = 0`. (Requires a
field so the mean exists; `M ≠ 0` so `M·x̄ = Σ x`.) -/
theorem sum_centered_eq_zero {K : Type*} [Field K] [CharZero K] (S : Finset ι) (x : ι → K)
    (hS : S.Nonempty) :
    ∑ i ∈ S, (x i - (∑ k ∈ S, x k) / (S.card : K)) = 0 := by
  have hMne : (S.card : K) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := K)).mpr (Finset.card_ne_zero_of_mem hS.choose_spec)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hMne]
  ring

/-- **Centered off-diagonal = minus the diagonal (the de-Finetti covariance identity).** For any
family over a finite set `S` with mean `x̄`, the sum of the ordered off-diagonal *centered* products
equals minus the sum of centered squares:
`Σ_{i∈S} Σ_{j∈S, j≠i} (x_i − x̄)(x_j − x̄) = − Σ_{i∈S} (x_i − x̄)²`.
This is the exact negative correlation a fixed sum forces: the centered family has total sum `0`
(`sum_centered_eq_zero`), so by Newton (`sum_offDiag_mul`) its off-diagonal is `0² − Σ(x−x̄)²`. -/
theorem sum_offDiag_centered_eq_neg_diag {K : Type*} [Field K] [CharZero K] (S : Finset ι)
    (x : ι → K) (hS : S.Nonempty) :
    (∑ i ∈ S, ∑ j ∈ S.erase i,
        (x i - (∑ k ∈ S, x k) / (S.card : K)) * (x j - (∑ k ∈ S, x k) / (S.card : K)))
      = - ∑ i ∈ S, (x i - (∑ k ∈ S, x k) / (S.card : K)) ^ 2 := by
  -- abbreviate the centered family `c i := x i − x̄`
  set c : ι → K := fun i => x i - (∑ k ∈ S, x k) / (S.card : K) with hc
  have hzero : ∑ i ∈ S, c i = 0 := sum_centered_eq_zero S x hS
  have hNewton : ∑ i ∈ S, ∑ j ∈ S.erase i, c i * c j
      = (∑ i ∈ S, c i) ^ 2 - ∑ i ∈ S, c i ^ 2 := sum_offDiag_mul S c
  rw [hNewton, hzero]; ring

/-- **The de-Finetti `Cov = −Var/(M−1)` form.** With `M = |S| ≥ 2`, mean `x̄ = (Σx)/M`,
variance `Var = (Σ(x−x̄)²)/M`, and average pairwise covariance
`Cov = (Σ_{i≠j}(x_i−x̄)(x_j−x̄))/(M(M−1))`, the exact identity holds:

> `Cov = − Var / (M − 1)`.

This is the clean general consequence of `sum_offDiag_centered_eq_neg_diag` after dividing the
off-diagonal by its `M(M−1)` ordered pairs and the diagonal by `M`. Pure arithmetic; no analysis. -/
theorem avg_offDiag_centered_eq_neg_var_div {K : Type*} [Field K] [CharZero K] (S : Finset ι)
    (hcard : 2 ≤ S.card)
    (x' : ι → K) :
    (∑ i ∈ S, ∑ j ∈ S.erase i,
        (x' i - (∑ k ∈ S, x' k) / (S.card : K)) * (x' j - (∑ k ∈ S, x' k) / (S.card : K)))
        / ((S.card : K) * ((S.card : K) - 1))
      = - ((∑ i ∈ S, (x' i - (∑ k ∈ S, x' k) / (S.card : K)) ^ 2) / (S.card : K))
          / ((S.card : K) - 1) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  -- in a char-0 field, `M ≠ 0` and `M − 1 ≠ 0` (M ≥ 2) without any order structure (works for ℂ).
  have hMne : (S.card : K) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := K)).mpr (Finset.card_ne_zero_of_mem hS.choose_spec)
  have hM1ne : (S.card : K) - 1 ≠ 0 := by
    have : ((S.card - 1 : ℕ) : K) ≠ 0 := (Nat.cast_ne_zero (R := K)).mpr (by omega)
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
  -- collapse the off-diagonal to the (opaque) diagonal `D`, then it is pure field arithmetic.
  rw [sum_offDiag_centered_eq_neg_diag S x' hS]
  set D : K := ∑ i ∈ S, (x' i - (∑ k ∈ S, x' k) / (S.card : K)) ^ 2 with hD
  field_simp [hMne, hM1ne]

end General

/-! ## Part 2 — specialization to the Gauss-period family

We instantiate the general fixed-sum identity at the period family `{η_b}_{b≠0}` over the index set
`S = univ.erase 0`, pulling in the two landed moments. Two routes:

* **Off-diagonal raw products** (`eta_offDiag_eq`): purely the Newton form using BOTH landed moments,
  `Σ_{b≠b'} η_b η_{b'} = (−|G|)² − (sum of η_b²)`. Over ℂ the second moment we landed is for `‖η_b‖²`,
  which equals `η_b²` only when the periods are real (`−1 ∈ G`). So we give the clean statement under
  the real-valuedness hypothesis where `Σ η_b² = Σ ‖η_b‖²`.
* **Centered de-Finetti covariance** (`eta_avg_offDiag_centered_eq_neg_var`): the `Cov = −Var/(M−1)`
  form specialized to the periods over the `M = q − 1` nonzero frequencies (real case). -/

section Periods

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Raw off-diagonal product sum of the periods, via Newton + the first moment.** For ANY family the
Newton identity gives `Σ_{b≠b'} η_b η_{b'} = (Σ η_b)² − Σ η_b²`; substituting the landed first moment
`Σ_{b≠0} η_b = −|G|` turns the leading term into `|G|²`:

> `Σ_{b≠0} Σ_{b'≠0, b'≠b} η_b η_{b'} = |G|² − Σ_{b≠0} η_b²`.

The remaining `Σ η_b²` is the *un-conjugated* square sum; it equals the landed Parseval `q|G|−|G|²`
only in the real case (`eta_offDiag_real`), so here we keep it symbolic — this is the honest purely-
algebraic content true over ℂ with no reality assumption. -/
theorem eta_offDiag_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : (0 : F) ∉ G) :
    ∑ b ∈ Finset.univ.erase (0 : F), ∑ b' ∈ (Finset.univ.erase (0 : F)).erase b,
        eta ψ G b * eta ψ G b'
      = (G.card : ℂ) ^ 2 - ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ 2 := by
  rw [sum_offDiag_mul (Finset.univ.erase (0 : F)) (eta ψ G),
    subgroup_gaussSum_firstMoment hψ hG]
  ring

/-- **Real-case off-diagonal product sum, both moments substituted.** When `−1 ∈ G` (so the periods
are real, `eta_conj_eq_of_neg_closed`) the un-conjugated square equals the Parseval `‖η_b‖²`, so
`Σ_{b≠0} η_b² = Σ_{b≠0} ‖η_b‖² = q|G|−|G|²` and the off-diagonal collapses to a closed form in `q, |G|`:

> `Σ_{b≠0} Σ_{b'≠0, b'≠b} η_b η_{b'} = |G|² − (q|G| − |G|²) = 2|G|² − q|G|`.

This is the exact pairwise-product sum of the (real) period family, using BOTH landed moments. -/
theorem eta_offDiag_real {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : (0 : F) ∉ G) (hneg : ∀ y ∈ G, -y ∈ G) :
    ∑ b ∈ Finset.univ.erase (0 : F), ∑ b' ∈ (Finset.univ.erase (0 : F)).erase b,
        eta ψ G b * eta ψ G b'
      = 2 * (G.card : ℂ) ^ 2 - (Fintype.card F : ℂ) * (G.card : ℂ) := by
  -- each `η_b² = ‖η_b‖²` (real value), via `η_b · conj η_b = ‖η_b‖²` and `conj η_b = η_b`.
  have hsq : ∀ b : F, eta ψ G b ^ 2 = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    have hc := ProximityGap.Frontier.GaussPeriodRealValued.eta_conj_eq_of_neg_closed hψ hneg b
    have : eta ψ G b * (starRingEnd ℂ) (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [hc] at this; rw [← this]; ring
  have hsumsq : ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ 2
      = ((((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 : ℝ)) : ℂ) := by
    rw [Finset.sum_congr rfl (fun b _ => hsq b), ← Complex.ofReal_sum, sum_sq_erase_zero hψ G]
  rw [eta_offDiag_eq hψ hG, hsumsq]
  push_cast
  ring

/-- **The de-Finetti `Cov = −Var/(M−1)` covariance of the period family (real case).** Specializing
the general `avg_offDiag_centered_eq_neg_var_div` to `{η_b}` over the `M = q − 1` nonzero frequencies:
with mean `μ̄ = (Σ_{b≠0} η_b)/(q−1) = −|G|/(q−1)` (`subgroup_gaussSum_firstMoment`) the average
pairwise covariance equals `−Var/(q−2)`, the exact negative correlation a fixed sum forces on the
exchangeable family. Stated symbolically in the centered periods (the moment values are pinned by the
two landed theorems). Requires `q ≥ 3` (so `M = q − 1 ≥ 2`). -/
theorem eta_avg_offDiag_centered_eq_neg_var {ψ : AddChar F ℂ} (G : Finset F)
    (hq : 3 ≤ Fintype.card F) :
    let S := Finset.univ.erase (0 : F)
    let μ := (∑ k ∈ S, eta ψ G k) / (S.card : ℂ)
    (∑ b ∈ S, ∑ b' ∈ S.erase b, (eta ψ G b - μ) * (eta ψ G b' - μ))
        / ((S.card : ℂ) * ((S.card : ℂ) - 1))
      = - ((∑ b ∈ S, (eta ψ G b - μ) ^ 2) / (S.card : ℂ)) / ((S.card : ℂ) - 1) := by
  intro S μ
  have hScard : S.card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hcard2 : 2 ≤ S.card := by rw [hScard]; omega
  exact avg_offDiag_centered_eq_neg_var_div (K := ℂ) S hcard2 (eta ψ G)

end Periods

end ProximityGap.Frontier.DeFinettiPeriodCovariance

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.sum_offDiag_mul
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.sum_centered_eq_zero
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.sum_offDiag_centered_eq_neg_diag
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.avg_offDiag_centered_eq_neg_var_div
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.eta_offDiag_eq
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.eta_offDiag_real
#print axioms ProximityGap.Frontier.DeFinettiPeriodCovariance.eta_avg_offDiag_centered_eq_neg_var
