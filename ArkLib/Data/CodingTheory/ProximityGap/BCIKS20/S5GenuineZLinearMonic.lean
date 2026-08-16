/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightDivisibility

/-!
# BCIKS20 §5.2.7 — Claim 5.9 (Z-linearity): the order-0 face dissolves for monic `H` (issue #232)

Claim 5.9 says the genuine Hensel root `γ = gammaGenuine` is **linear in `Z`**:
`γ = v₀(X) + Z·v₁(X)`. `S5Genuine.lean` reduces it (axiom-clean, `gammaGenuine_Z_linear_target` +
`gammaGenuine_Z_linear_of_coeffs_Z_linear`) to the **per-coefficient** `Z`-degree-`≤ 1` fact:
for every `t`, `αGenuine t = liftToFunctionField c₀ + functionFieldT · liftToFunctionField c₁` for
some `c₀, c₁ : F[X]` (the `Z ↦ T` linear shape).

This file discharges the **order-`0` face** of that fact for monic `H`. By
`AlphaWeight.αGenuine_zero_eq_functionFieldT_of_monic`, the monic order-0 root is literally
`αGenuine 0 = functionFieldT = T`, which is already in the `Z`-degree-`1` shape with `c₀ = 0`,
`c₁ = 1` (since `liftToFunctionField` is a ring hom: `lift 0 = 0`, `lift 1 = 1`, and `T·1 = T`).
This parallels `AlphaWeightDivisibility`'s dissolution of the order-0 face of the (P1) weight
invariant: the single `W`-division that obstructs the general case is vacuous when `W = 1`.

Consequently the **entire** Claim 5.9 target reduces, for monic `H`, to just the **successor**
per-coefficient residual (`t ≥ 1`) — `gammaGenuine_Z_linear_target_of_succ_of_monic`.

## Honest scope

The successor case (`t ≥ 1`) is **not** discharged here and is **not** dischargeable from the
recursion alone: `R(X, Y, Z)` carries `Z`-degree `deg_Z R` (which exceeds `1` in general), and the
`(A.1)` recursion mixes these degrees — only the Guruswami–Sudan interpolant's `deg_{Y,Z}` budget
forces `Z`-degree `1`. That is exactly the paper's separate geometric §5.2.7 interpolation argument
(fulltext 1719–1740), an external degree input, not reducible to the lift identity. So the genuine
remaining content of Claim 5.9 is precisely this successor residual; the order-0 face is gone. This
is Johnson-regime known math, not the genuinely-open capacity prize.

## Main results (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `claim59_zLinear_zero_of_monic` — the order-0 per-coefficient `Z`-degree-`1` fact for monic `H`.
* `gammaGenuine_Z_linear_target_of_succ_of_monic` — Claim 5.9 reduced to the successor residual
  (the order-0 base case discharged) for monic `H`.
-/

set_option linter.style.longLine false


noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.S5Genuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Claim 5.9 order-0 face, for monic `H` (axiom-clean).**
The order-0 coefficient of the genuine Hensel root is in the `Z`-degree-`≤ 1` shape: with `c₀ = 0`,
`c₁ = 1`, `αGenuine 0 = 0 + functionFieldT · 1 = functionFieldT = T`
(via `αGenuine_zero_eq_functionFieldT_of_monic` and `liftToFunctionField` being a ring hom). -/
theorem claim59_zLinear_zero_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic) :
    ∃ c₀ c₁ : F[X], αGenuine H x₀ R hHyp 0
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  refine ⟨0, 1, ?_⟩
  rw [AlphaWeight.αGenuine_zero_eq_functionFieldT_of_monic H x₀ R hHyp hmonic]
  simp only [map_zero, map_one, mul_one, zero_add]

/-- **Claim 5.9 reduced to the successor residual, for monic `H` (axiom-clean).**
The full `Z`-linearity target `gammaGenuine_Z_linear_target` follows from the per-coefficient
`Z`-degree-`1` fact at the **successor** indices alone (`t ≥ 1`): the order-0 face is supplied by
`claim59_zLinear_zero_of_monic`. So for monic `H`, the entire remaining content of Claim 5.9 is the
successor residual — the geometric §5.2.7 `Z`-degree input. -/
theorem gammaGenuine_Z_linear_target_of_succ_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic)
    (hsucc : ∀ t : ℕ, ∃ c₀ c₁ : F[X], αGenuine H x₀ R hHyp (t + 1)
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁) :
    gammaGenuine_Z_linear_target H x₀ R hHyp := by
  refine gammaGenuine_Z_linear_of_coeffs_Z_linear H hHyp ?_
  intro t
  cases t with
  | zero => exact claim59_zLinear_zero_of_monic H hHyp hmonic
  | succ n => exact hsucc n

end BCIKS20.HenselNumerator.S5Genuine

section AxiomAudit
#print axioms BCIKS20.HenselNumerator.S5Genuine.claim59_zLinear_zero_of_monic
#print axioms BCIKS20.HenselNumerator.S5Genuine.gammaGenuine_Z_linear_target_of_succ_of_monic
end AxiomAudit
