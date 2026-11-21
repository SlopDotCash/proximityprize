/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.OrdinaryPolarCappedGcd

/-! # The ordinary-polar gcd bound on genuine selected cubic sections -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeOrdinaryPolarBudget

open Polynomial Finset OrdinaryPolarGcdBudget
open scoped Polynomial

variable {K : Type} [Field K]

/-- The large-population gcd bound needs only coordinate degree ceilings. It also applies when the second
polynomial vanishes identically. -/
theorem degree_ceiling_budget (A B : K[X][X]) (hA : A ≠ 0) (W : ℕ)
    (hw : 201326589 ≤ W) (hw' : W ≤ 290805098)
    (hAD : A.natDegree ≤ 6 * W - 9 * 67108863 - 3)
    (hBD : B.natDegree ≤ 6 * W - 9 * 67108863 - 3)
    (hAH : Bivariate.degreeX A ≤ 195) (hBH : Bivariate.degreeX B ≤ 195)
    (S : Finset K) (hS : 1342177085 ≤ S.card) (q : K → K[X])
    (hq : ∀ z ∈ S, q z ≠ 0 ∧ (q z).natDegree = W - 67108863 ∧
      q z ^ 2 ∣ A.map (evalRingHom z) ∧ q z ^ 2 ∣ B.map (evalRingHom z)) :
    2 * (W - 67108863) ≤ genericDegree A B + 201 := by
  classical
  by_cases hB : B = 0
  · subst B
    have hh := OrdinaryPolarCappedGcd.production_gcd_lower A A hA hA W hw hw' hAD hAD
      hAH hAH S hS q (fun z hz => by
        obtain ⟨hne, hd, hAz, _⟩ := hq z hz
        exact ⟨hne, hd, hAz, hAz⟩)
    simpa [genericDegree] using hh
  · exact OrdinaryPolarCappedGcd.production_gcd_lower A B hA hB W hw hw' hAD hBD hAH hBH
      S hS q hq

#print axioms degree_ceiling_budget

end ArkLib.ProximityGap.Frontier.SecondPrimeOrdinaryPolarBudget
