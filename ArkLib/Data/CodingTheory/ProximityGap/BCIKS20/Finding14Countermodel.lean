/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Field.ZMod
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StructuredWeightInduction

/-!
# Finding 14 countermodel: the in-tree (A.1) cell coefficient is NOT the paper's cleared B

[BCIKS20] Appendix A.4 (lines 4060–4210) runs the `(A.1)` recursion with the W-TWISTED
cell coefficients `B_{i1,λ} = W^{d−δ−Σλ}·A_{i1,λ}`, where `A` evaluates the iterated Hasse
coefficient at `α₀ = T/W` — per monomial `c_b·W^{d−δ−Σλ−b}·T^b` (the in-tree analogue is
`hasseCoeffRepr𝒪_cleared`). The in-tree `B_coeff` instead `mk`s the UN-cleared `Y ↦ T`
lift `Σ_b c_b·T^b`, while `βHensel_succ` copies the paper's engine exponents verbatim.

This file gives the **machine-checked separation** (DISPROOF_LOG O156): a concrete
instance — `F = ZMod 5`, `H = Z·Y + 1` (non-monic, `W = Z`), `R = Z·Y² + Y + X`,
`x₀ = 0`, satisfying `ClaimA2.Hypotheses` — in which the in-tree order-1 numerator
`β₁ = −B_coeff(1,∅)` (the proven `βHensel_one`) differs from the paper's cleared value
`−⟦cleared at k = d_R − δ − Σλ = 2⟧` as elements of `𝒪 H`:

`βHensel 1 = −1 ≠ −Z² = −(paper's β₁)`.

Hence the in-tree recursion and the paper's `(A.1)` produce DIFFERENT sequences from
order 1 on (for non-monic `H`), confirming finding 14's normalization divergence at the
level of the recursion's values. (Which of the two satisfies the genuine Hensel lift
identity is settled by the paper's derivation: the cleared one.)
-/

namespace BCIKS20.HenselNumerator.Finding14

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The base field of the countermodel. -/
abbrev F5 := ZMod 5

/-- `H = Z·Y + 1`: degree 1 in `Y`, NON-monic (`W = Z`, `deg W = 1`) — the divergence
needs a non-unit leading coefficient. -/
noncomputable def Hcm : F5[X][Y] :=
  Polynomial.C Polynomial.X * Polynomial.X + Polynomial.C 1

theorem Hcm_natDegree : Hcm.natDegree = 1 := by
  rw [Hcm]
  exact Polynomial.natDegree_linear Polynomial.X_ne_zero

theorem Hcm_natDegree_pos : 0 < Hcm.natDegree := by
  rw [Hcm_natDegree]
  norm_num

theorem Hcm_coeff_zero : Hcm.coeff 0 = 1 := by
  rw [Hcm]
  simp

theorem Hcm_ne_zero : Hcm ≠ 0 := by
  intro h
  have := Hcm_coeff_zero
  rw [h] at this
  simp at this

/-- `H` is irreducible: degree 1 in `Y` with unit content (the constant coefficient
is `1`). -/
theorem Hcm_irreducible : Irreducible Hcm := by
  constructor
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Hcm_natDegree] at h0
    exact one_ne_zero h0
  · intro a b hab
    have ha0 : a ≠ 0 := by
      intro h
      exact Hcm_ne_zero (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := by
      intro h
      exact Hcm_ne_zero (by rw [hab, h, mul_zero])
    have hsum : a.natDegree + b.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, Hcm_natDegree]
    -- the constant coefficients multiply to 1, so the degree-0 factor is a unit
    have hc0 : a.coeff 0 * b.coeff 0 = 1 := by
      have := Hcm_coeff_zero
      rw [hab, Polynomial.mul_coeff_zero] at this
      exact this
    rcases Nat.eq_zero_or_pos a.natDegree with hA | hA
    · left
      obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hA
      refine Polynomial.isUnit_C.mpr ?_
      rw [Polynomial.coeff_C_zero] at hc0
      exact IsUnit.of_mul_eq_one _ hc0
    · right
      have hB : b.natDegree = 0 := by omega
      obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hB
      refine Polynomial.isUnit_C.mpr ?_
      rw [Polynomial.coeff_C_zero] at hc0
      exact IsUnit.of_mul_eq_one _ (by rw [mul_comm] at hc0; exact hc0)

instance moduleInstance_Finding14Countermodel_1 : Fact (Irreducible Hcm) := ⟨Hcm_irreducible⟩
instance moduleInstance_Finding14Countermodel_2 : Fact (0 < Hcm.natDegree) := ⟨Hcm_natDegree_pos⟩

/-- `R = Z·Y² + Y + X` (outer `Y`, middle `X` the lift variable, inner `Z`):
`R(0, Y, Z) = Z·Y² + Y = H·Y` (divisible by `H`, separable), and `Δ_X R = 1` supplies a
nonzero order-1 cell. -/
noncomputable def Rcm : F5[X][X][Y] :=
  Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X ^ 2 + Polynomial.X
    + Polynomial.C Polynomial.X

/-- The specialization at `x₀ = 0`: `R(0,Y,Z) = Z·Y² + Y`. -/
theorem evalX_Rcm : Polynomial.Bivariate.evalX (Polynomial.C (0 : F5)) Rcm
    = Polynomial.C Polynomial.X * Polynomial.X ^ 2 + Polynomial.X := by
  rw [Rcm, Polynomial.Bivariate.evalX_eq_map]
  simp

/-- The Claim A.2 hypotheses hold: `H ∣ R(0,·,·)` (witness `Y`) and `R(0,·,·) = Z·Y²+Y`
is separable (explicit Bézout: `(−4Z)·P + P'·P' = 1` over any commutative ring). -/
theorem hyp_cm : ClaimA2.Hypotheses (0 : F5) Rcm Hcm := by
  constructor
  · rw [evalX_Rcm]
    exact ⟨Polynomial.X, by rw [Hcm, map_one]; ring⟩
  · rw [evalX_Rcm]
    have hder : Polynomial.derivative
        (Polynomial.C Polynomial.X * Polynomial.X ^ 2 + Polynomial.X
          : F5[X][Y])
        = Polynomial.C Polynomial.X * (2 * Polynomial.X) + 1 := by
      simp [Polynomial.derivative_X_pow]
      ring
    rw [Polynomial.separable_def, hder]
    refine ⟨-(4 * Polynomial.C (Polynomial.X : F5[X])),
      Polynomial.C Polynomial.X * (2 * Polynomial.X) + 1, ?_⟩
    ring

/-- The order-1 specialized Hasse payload is the constant `1`:
`evalX(0)(Δ_X¹ Δ_Y⁰ R) = 1`. -/
theorem p1_eq_one : Polynomial.Bivariate.evalX (Polynomial.C (0 : F5))
    (hasseDerivX 1 (hasseDerivY 0 Rcm)) = 1 := by
  have hY0 : hasseDerivY 0 Rcm = Rcm := by
    rw [hasseDerivY, Polynomial.hasseDeriv_zero, LinearMap.id_apply]
  rw [hY0]
  refine Polynomial.ext fun n => ?_
  have hcomm : (Polynomial.Bivariate.evalX (Polynomial.C (0 : F5))
      (hasseDerivX 1 Rcm)).coeff n
      = Polynomial.eval (Polynomial.C 0) ((hasseDerivX 1 Rcm).coeff n) := by
    rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rfl
  rw [hcomm, hasseDerivX_coeff, Polynomial.hasseDeriv_one']
  -- the Y-coefficients of `R`: `coeff 0 = X`, `coeff 1 = 1`, `coeff 2 = C Z`, else `0`
  match n with
  | 0 =>
      have hc : Rcm.coeff 0 = Polynomial.X := by
        rw [Rcm]
        simp [Polynomial.coeff_X_zero]
      rw [hc]
      simp
  | 1 =>
      have hc : Rcm.coeff 1 = 1 := by
        rw [Rcm]
        simp [Polynomial.coeff_X_one]
      rw [hc]
      simp [Polynomial.coeff_one]
  | 2 =>
      have hc : Rcm.coeff 2 = Polynomial.C Polynomial.X := by
        rw [Rcm]
        simp [Polynomial.coeff_X]
      rw [hc]
      simp [Polynomial.coeff_one]
  | (m + 3) =>
      have hc : Rcm.coeff (m + 3) = 0 := by
        rw [Rcm]
        simp [Polynomial.coeff_X]
      rw [hc]
      simp [Polynomial.coeff_one]

/-- **The in-tree cell value:** `B_coeff(1, ∅) = 1` in `𝒪 H` (the un-cleared `Y ↦ T`
lift of the constant payload, with trivial multinomial prefactor). -/
theorem B_coeff_value : B_coeff Hcm 0 Rcm 1 (default : Nat.Partition 0)
    = (1 : 𝒪 Hcm) := by
  rw [B_coeff, hasseCoeffRepr𝒪]
  have hσ : sigmaLambda (default : Nat.Partition 0) = 0 := by
    rw [sigmaLambda, Nat.Partition.partition_zero_parts]
    rfl
  rw [hσ, p1_eq_one]
  have hpre : prefactor Rcm.natDegree 1 (default : Nat.Partition 0) = 1 := by
    rw [prefactor, Nat.Partition.partition_zero_parts]
    rfl
  rw [hpre, map_one, one_smul]

/-- **The paper's cleared cell value:** `⟦cleared at k = 2⟧ = Z²` in `𝒪 H` — the
W-twisted `B_{1,∅} = W^{d_R−0−0}·A_{1,∅} = Z²·1`. -/
theorem cleared_B_value :
    (Ideal.Quotient.mk (Ideal.span {H_tilde' Hcm})
        (hasseCoeffRepr𝒪_cleared Hcm 0 Rcm 1 0 2) : 𝒪 Hcm)
      = Ideal.Quotient.mk (Ideal.span {H_tilde' Hcm})
          (Polynomial.C (Polynomial.X ^ 2)) := by
  congr 1
  refine Polynomial.ext fun b => ?_
  rw [hasseCoeffRepr𝒪_cleared_coeff]
  have hlc : Hcm.leadingCoeff = Polynomial.X := by
    rw [Hcm]
    exact Polynomial.leadingCoeff_linear Polynomial.X_ne_zero
  rw [p1_eq_one, hlc]
  match b with
  | 0 =>
      rw [show ((Polynomial.C (Polynomial.X ^ 2) : F5[X][Y])).coeff 0
          = Polynomial.X ^ 2 from Polynomial.coeff_C_zero.trans rfl]
      simp [Polynomial.coeff_one]
  | 1 =>
      rw [show ((Polynomial.C (Polynomial.X ^ 2) : F5[X][Y])).coeff 1 = 0 by
        rw [Polynomial.coeff_C]; simp]
      simp [Polynomial.coeff_one]
  | 2 =>
      rw [show ((Polynomial.C (Polynomial.X ^ 2) : F5[X][Y])).coeff 2 = 0 by
        rw [Polynomial.coeff_C]; simp]
      simp [Polynomial.coeff_one]
  | (m + 3) =>
      rw [if_neg (by omega),
        show ((Polynomial.C (Polynomial.X ^ 2) : F5[X][Y])).coeff (m + 3) = 0 by
          rw [Polynomial.coeff_C]; simp]

/-- **THE SEPARATION (finding 14, machine-checked):** the in-tree cell coefficient and
the paper's cleared cell coefficient are DIFFERENT elements of `𝒪 H`: `1 ≠ Z²`
(their difference is a nonzero `Y`-constant, which the monic degree-1 `H̃'` cannot
divide). -/
theorem inTree_B_ne_paper_B :
    B_coeff Hcm 0 Rcm 1 (default : Nat.Partition 0)
      ≠ (Ideal.Quotient.mk (Ideal.span {H_tilde' Hcm})
          (hasseCoeffRepr𝒪_cleared Hcm 0 Rcm 1 0 2) : 𝒪 Hcm) := by
  rw [B_coeff_value, cleared_B_value]
  intro heq
  -- `mk 1 = mk (C Z²)` would force `H̃' ∣ (C Z² − 1)`, impossible by degree
  have hdvd : H_tilde' Hcm ∣ (Polynomial.C (Polynomial.X ^ 2) - 1 : F5[X][Y]) := by
    have h2 : (Ideal.Quotient.mk (Ideal.span {H_tilde' Hcm})
        (Polynomial.C (Polynomial.X ^ 2) - 1 : F5[X][Y]) : 𝒪 Hcm) = 0 := by
      rw [map_sub, map_one, ← heq]
      exact sub_self _
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
  have hne : (Polynomial.C (Polynomial.X ^ 2) - 1 : F5[X][Y]) ≠ 0 := by
    rw [show (1 : F5[X][Y]) = Polynomial.C 1 from (Polynomial.C_1).symm, ← map_sub]
    rw [ne_eq, Polynomial.C_eq_zero]
    intro h
    have h2 := congrArg (fun q => Polynomial.coeff q 2) h
    simp [Polynomial.coeff_one] at h2
  have hdeglt : (Polynomial.C (Polynomial.X ^ 2) - 1 : F5[X][Y]).degree
      < (H_tilde' Hcm).degree := by
    have h1 : (H_tilde' Hcm).degree = 1 := by
      have hmon := H_tilde'_monic Hcm Hcm_natDegree_pos
      have hnd := natDegree_H_tilde' (H := Hcm) Hcm_natDegree_pos
      rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hnd, Hcm_natDegree]
      rfl
    have h0 : (Polynomial.C (Polynomial.X ^ 2) - 1 : F5[X][Y]).degree ≤ 0 := by
      have : (Polynomial.C (Polynomial.X ^ 2) - 1 : F5[X][Y])
          = Polynomial.C (Polynomial.X ^ 2 - 1) := by
        rw [map_sub, map_one]
      rw [this]
      exact Polynomial.degree_C_le
    rw [h1]
    exact lt_of_le_of_lt h0 (by norm_num)
  have := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeglt
  exact hne this

/-- **The recursions diverge at order 1:** the in-tree `βHensel 1` is NOT the paper's
order-1 numerator `−⟦cleared B⟧` — via the proven exact value `β₁ = −B_{1,∅}`. -/
theorem βHensel_one_ne_paper :
    βHensel Hcm 0 Rcm hyp_cm 1
      ≠ -(Ideal.Quotient.mk (Ideal.span {H_tilde' Hcm})
          (hasseCoeffRepr𝒪_cleared Hcm 0 Rcm 1 0 2) : 𝒪 Hcm) := by
  rw [βHensel_one]
  intro h
  exact inTree_B_ne_paper_B (neg_injective h)

/-! ## Source audit -/

#print axioms Hcm_irreducible
#print axioms hyp_cm
#print axioms p1_eq_one
#print axioms B_coeff_value
#print axioms cleared_B_value
#print axioms inTree_B_ne_paper_B
#print axioms βHensel_one_ne_paper

end BCIKS20.HenselNumerator.Finding14
