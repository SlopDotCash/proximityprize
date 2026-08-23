/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CodeJohnsonRadius

/-!
# The explicit √-form Johnson radius (#82)

The recognizable textbook form of the Johnson radius.  `code_johnson_radius` takes the algebraic
condition `A² > T·B`; here it is re-expressed in the explicit square-root form

  `√(T·B) < A`,  i.e.  `e < n − n/q − √(T·B)`,

with `A = (n−e) − n/q`, `B = (n−d) − n/q`, `T = n(1−1/q)`.  Any code with minimum distance `≥ d` is
list-decodable at every radius below this explicit Johnson radius.  The bridge is `Real.sqrt_lt'`
(`√y < x ↔ y < x²` for `0 < x`).  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Explicit √-form Johnson radius (#82).** If `e` lies below the explicit Johnson radius
`A > √(T·B)` (equivalently `e < n − n/q − √(T·B)`, with `A=(n−e)−n/q`, `B=(n−d)−n/q`, `T=n(1−1/q)`),
then any code with minimum distance `≥ d` is list-decodable at radius `e`. -/
theorem code_johnson_radius_sqrt (𝒞 : Finset (ι → F)) (e d : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hApos : 0 < ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
    (hradius :
      Real.sqrt
          (((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
            * (((Fintype.card ι - d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
        < ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) :
    ∃ ℓ : ℕ, ∀ w : ι → F, closeCount 𝒞 e w ≤ ℓ := by
  have hAB :
      (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) :=
    (Real.sqrt_lt' hApos).mp hradius
  exact code_johnson_radius 𝒞 e d hq1 hn hmin hP hAB

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.code_johnson_radius_sqrt
