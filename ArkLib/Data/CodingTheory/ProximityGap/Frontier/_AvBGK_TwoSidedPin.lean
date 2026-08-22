/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant
import ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum

/-!
# Both unconditional bounds on the BGK character sum, proven (#444/#334)

The BGK object is the worst-case Gauss period `M(n) = max_{b≠0}‖η_b‖`, equivalently
`Λ² = prizeRadiusSq ψ G = max_{b≠0}‖η_b‖²`. This file proves **both** unconditional bounds on it,
axiom-clean and with no citation:

* **Upper bound** `Λ² ≤ |G|²`, i.e. `M ≤ |G| = n` (`prizeRadiusSq_le_card_sq`). Triangle inequality:
  `‖η_b‖ = ‖∑_{y∈G} ψ(by)‖ ≤ ∑_{y∈G}‖ψ(by)‖ = |G|`, since each character value has norm `1`.
* **Lower bound** `Λ² ≥ (q·n − n²)/(q−1)`, i.e. `M ≥ √(≈ n)` (the Alon–Boppana / Parseval floor,
  in-tree `prizeRadiusSq_parseval_floor`): the max is at least the average, and the average squared
  period is `(qn−n²)/(q−1) ≈ n`.

Combined (`prizeRadiusSq_two_sided`): **`(q·n − n²)/(q−1) ≤ Λ² ≤ n²`**, i.e. the worst-case period is
pinned unconditionally between `√n` and `n`:
  `√((qn−n²)/(q−1)) ≤ M(n) ≤ n`     (`worstCasePeriod_two_sided`).

This is the *complete* unconditional two-sided pin on the BGK object, both directions proven here.
The refinements of the **upper** bound are the harder theorems: BGK (Bourgain–Glibichuk–Konyagin)
sharpens `n → n^{1-δ}` via the sum-product theorem, and the open Paley/prize conjecture would sharpen
it to `√(n log q)` (the lower bound shows that target is within a `√log q` factor of optimal — the
prize bound is essentially the truth). Those refinements are NOT in this file; the elementary
two-sided pin is.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AvBGKPin

open ArkLib.ProximityGap.PrizeStructuralConstant
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.IncidenceDeviationCharSum (norm_addChar_apply)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The trivial period bound:** each Gauss period has norm at most `|G|`, by the triangle
inequality and `‖ψ(t)‖ = 1`. -/
theorem norm_eta_le_card (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) := by
  unfold eta
  calc ‖∑ y ∈ G, ψ (b * y)‖
      ≤ ∑ y ∈ G, ‖ψ (b * y)‖ := norm_sum_le _ _
    _ = ∑ _y ∈ G, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        exact norm_addChar_apply ψ (b * y)
    _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Upper bound (proven):** the worst-case squared period satisfies `Λ² ≤ |G|²`, i.e. `M ≤ n`. -/
theorem prizeRadiusSq_le_card_sq (ψ : AddChar F ℂ) (G : Finset F) :
    prizeRadiusSq ψ G ≤ (G.card : ℝ) ^ 2 := by
  unfold prizeRadiusSq
  refine Finset.sup'_le _ _ (fun b _ => ?_)
  have h := norm_eta_le_card ψ G b
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  calc ‖eta ψ G b‖ ^ 2 ≤ (G.card : ℝ) ^ 2 := by
        apply pow_le_pow_left₀ hnn h
  -- (pow_le_pow_left₀ closes it)

/-- **Both bounds, together (proven).** The worst-case squared Gauss period `Λ² = prizeRadiusSq`
is pinned unconditionally between its Parseval floor `(q·n − n²)/(q−1) ≈ n` and the trivial ceiling
`n²`:
  `(q·n − n²)/(q−1) ≤ Λ² ≤ n²`. -/
theorem prizeRadiusSq_two_sided {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
        ≤ prizeRadiusSq ψ G
      ∧ prizeRadiusSq ψ G ≤ (G.card : ℝ) ^ 2 :=
  ⟨prizeRadiusSq_parseval_floor hψ G, prizeRadiusSq_le_card_sq ψ G⟩

/-- **The two-sided pin on `M(n)` itself** (taking square roots). The worst-case Gauss period
`M = √Λ²` satisfies
  `√((q·n − n²)/(q−1)) ≤ M ≤ n`. -/
theorem worstCasePeriod_two_sided {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    Real.sqrt (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1))
        ≤ Real.sqrt (prizeRadiusSq ψ G)
      ∧ Real.sqrt (prizeRadiusSq ψ G) ≤ (G.card : ℝ) := by
  refine ⟨Real.sqrt_le_sqrt (prizeRadiusSq_parseval_floor hψ G), ?_⟩
  rw [show (G.card : ℝ) = Real.sqrt ((G.card : ℝ) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt (prizeRadiusSq_le_card_sq ψ G)

end ArkLib.ProximityGap.Frontier.AvBGKPin

#print axioms ArkLib.ProximityGap.Frontier.AvBGKPin.prizeRadiusSq_le_card_sq
#print axioms ArkLib.ProximityGap.Frontier.AvBGKPin.prizeRadiusSq_two_sided
#print axioms ArkLib.ProximityGap.Frontier.AvBGKPin.worstCasePeriod_two_sided
