/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore

/-!
# BCIKS20 App-A.2 — the `Λ`-weight of a `{1, Y}`-element (issue #232)

The `𝒪`-side computational companion to `FunctionFieldZLinear` (`{1,T}` independence in `𝕃 H`).
For the BCIKS20 Appendix-A.4 weight-1 invariant (#138), once Claim 5.9 supplies the `Z`-linear
(`{1, T}`) shape of a Hensel-root coefficient and the GS degree budget bounds its `X`-degrees, the
weight bound `Λ_𝒪 ≤ 1` is a pure `weight_Λ` computation on the degree-`≤ 1`-in-`Y` element
`C c₀ + X · C c₁`.  This file mechanizes that computation, generalizing the by-hand single-instance
calculation of `P1MonicWeightHolds.weight_holds` (`H = Y²−2 / ZMod 3`) to **arbitrary** monic `H`.

`weight_Λ f H D = sup_{j ∈ supp f} [ j·(D+1−natDegreeY H) + (f.coeff j).natDegree ]`.  For
`f = C c₀ + X·C c₁` the only `Y`-powers are `0` (coeff `c₀`) and `1` (coeff `c₁`), so the weight is
bounded by `max(deg_X c₀, (D+1−natDegreeY H) + deg_X c₁)`.

* `weight_Λ_zLinear_le` — the bivariate bound `Λ(C c₀ + X·C c₁) ≤ max(deg_X c₀, M + deg_X c₁)`,
  `M = D+1−natDegreeY H`.
* `weight_Λ_over_𝒪_zLinear_le` — the `𝒪`-side bound (for `natDegreeY H ≥ 2` the element is already
  reduced mod `H̃'`, so the `𝒪`-weight equals the polynomial weight).
* `weight_Λ_over_𝒪_zLinear_le_one` — the weight-`≤ 1` criterion: `deg_X c₀ ≤ 1` and
  `M + deg_X c₁ ≤ 1` (e.g. `D = natDegreeY H` so `M = 1`, plus `deg_X c₁ = 0`) ⟹ `Λ_𝒪 ≤ 1`.
  This is exactly the shape `P1MonicWeightHolds.weight_holds` exhibited, now general.

These are unconditional `weight_Λ` facts; they isolate the genuinely-open part of the weight-1
invariant to the `X`-degree bounds on the `{1,T}` coefficients (the GS `deg_{Y,Z}` budget input),
the computation itself being done here.  Axiom-clean.
-/

open Polynomial Polynomial.Bivariate

namespace BCIKS20AppendixA

variable {F : Type} [Field F]

/-- **The `Λ`-weight of a `{1, Y}`-element is bounded by its coefficient `X`-degrees.**
`Λ(C c₀ + X·C c₁) ≤ max(deg_X c₀, (D+1−natDegreeY H) + deg_X c₁)`. The support of `C c₀ + X·C c₁`
is `⊆ {0, 1}`, with coefficients `c₀` (at `Y^0`) and `c₁` (at `Y^1`). -/
theorem weight_Λ_zLinear_le (c₀ c₁ : F[X]) (H : F[X][Y]) (D : ℕ) :
    weight_Λ (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁) H D
      ≤ max (WithBot.some c₀.natDegree)
          (WithBot.some ((D + 1 - Bivariate.natDegreeY H) + c₁.natDegree)) := by
  classical
  set f : F[X][Y] := Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁ with hf
  have hc0 : f.coeff 0 = c₀ := by
    rw [hf, Polynomial.coeff_add, Polynomial.coeff_C, if_pos rfl,
      Polynomial.coeff_X_mul_zero, add_zero]
  have hc1 : f.coeff 1 = c₁ := by
    have hX : ((Polynomial.X : F[X][Y]) * Polynomial.C c₁).coeff 1 = c₁ := by
      simp
    rw [hf, Polynomial.coeff_add, Polynomial.coeff_C, if_neg one_ne_zero, zero_add, hX]
  rw [weight_Λ]
  apply Finset.sup_le
  intro j hj
  rw [Polynomial.mem_support_iff] at hj
  -- A nonzero coefficient forces `j ≤ 1` (higher `Y`-powers vanish).
  have hj01 : j ≤ 1 := by
    by_contra hjgt
    rw [not_le] at hjgt
    apply hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [hf, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.succ_ne_zero n), zero_add,
      Polynomial.coeff_X_mul, Polynomial.coeff_C, if_neg (by omega : n ≠ 0)]
  interval_cases j
  · rw [hc0]
    simp only [Nat.zero_mul, Nat.zero_add]
    exact le_max_left _ _
  · rw [hc1]
    simp only [Nat.one_mul]
    exact le_max_right _ _

/-- **The `𝒪`-side `{1, Y}`-weight bound.** For `natDegreeY H ≥ 2`, the element `C c₀ + X·C c₁` has
`Y`-degree `≤ 1 < natDegreeY (H̃' H)`, so it is its own canonical representative and the `𝒪`-weight
equals the polynomial weight; hence the same bound holds in `𝒪 H`. -/
theorem weight_Λ_over_𝒪_zLinear_le {H : F[X][Y]} (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree)
    (c₀ c₁ : F[X]) (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)) D
      ≤ max (WithBot.some c₀.natDegree)
          (WithBot.some ((D + 1 - Bivariate.natDegreeY H) + c₁.natDegree)) := by
  have hdeg : (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁).degree < (H_tilde' H).degree := by
    have hlhs : (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁).degree ≤ (1 : WithBot ℕ) := by
      refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.degree_C_le).trans (by decide)
      · refine (Polynomial.degree_mul_le _ _).trans ?_
        calc (Polynomial.X : F[X][Y]).degree + (Polynomial.C c₁).degree
            ≤ (1 : WithBot ℕ) + 0 := add_le_add Polynomial.degree_X_le Polynomial.degree_C_le
          _ = 1 := by simp
    have hrhs : (1 : WithBot ℕ) < (H_tilde' H).degree := by
      rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero, natDegree_H_tilde' hH]
      exact_mod_cast hd
    exact lt_of_le_of_lt hlhs hrhs
  rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdeg]
  exact weight_Λ_zLinear_le c₀ c₁ H D

/-- **Weight-`≤ 1` criterion for a `{1, Y}`-element in `𝒪 H`.** If the constant coefficient has
`X`-degree `≤ 1` and the `Y`-coefficient term contributes `≤ 1` (e.g. `D = natDegreeY H`, so the
per-`Y`-power weight `M = 1`, and `deg_X c₁ = 0`), then `Λ_𝒪 (C c₀ + X·C c₁) ≤ 1`.  This is exactly
the shape `P1MonicWeightHolds.weight_holds` exhibited on `H = Y²−2 / ZMod 3`, now for arbitrary
monic `H`. -/
theorem weight_Λ_over_𝒪_zLinear_le_one {H : F[X][Y]} (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree)
    (c₀ c₁ : F[X]) (D : ℕ)
    (hc0 : c₀.natDegree ≤ 1)
    (hc1 : (D + 1 - Bivariate.natDegreeY H) + c₁.natDegree ≤ 1) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)) D
      ≤ WithBot.some 1 := by
  refine (weight_Λ_over_𝒪_zLinear_le hH hd c₀ c₁ D).trans ?_
  rw [max_le_iff]
  exact ⟨WithBot.coe_le_coe.mpr hc0, WithBot.coe_le_coe.mpr hc1⟩

end BCIKS20AppendixA

section AxiomAudit
#print axioms BCIKS20AppendixA.weight_Λ_zLinear_le
#print axioms BCIKS20AppendixA.weight_Λ_over_𝒪_zLinear_le
#print axioms BCIKS20AppendixA.weight_Λ_over_𝒪_zLinear_le_one
end AxiomAudit
