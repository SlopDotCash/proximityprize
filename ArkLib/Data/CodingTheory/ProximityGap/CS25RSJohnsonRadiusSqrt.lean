/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CodeJohnsonRadiusSqrt
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance

/-!
# Explicit √-form Johnson radius for Reed–Solomon (#82)

The concrete, recognizable Reed–Solomon list-decoding radius: specialising `code_johnson_radius_sqrt`
to the RS minimum distance `n−(k−1)` (`rsCodeFinset_hammingDist_ge`), Reed–Solomon codes are
list-decodable below the explicit Johnson radius

  `√(T·B) < A`,  `A = (n−e) − n/q`,  `B = (n − (n−(k−1))) − n/q`,  `T = n(1−1/q)`.

`sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Explicit √-form Johnson radius for Reed–Solomon (#82).** Reed–Solomon codes are list-decodable
below the explicit Johnson radius `√(T·B) < A` (`A=(n−e)−n/q`, `B=(n−(n−(k−1)))−n/q`, `T=n(1−1/q)`),
specialising `code_johnson_radius_sqrt` to the RS minimum distance `n−(k−1)`. -/
theorem rs_johnson_radius_sqrt (domain : ι ↪ F) (k : ℕ) [NeZero k] (e : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hApos : 0 < ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
    (hradius :
      Real.sqrt
          (((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
            * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
                - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
        < ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) :
    ∃ ℓ : ℕ, ∀ w : ι → F, closeCount (rsCodeFinset domain k) e w ≤ ℓ :=
  code_johnson_radius_sqrt (rsCodeFinset domain k) e (Fintype.card ι - (k - 1)) hq1 hn
    (fun c hc c' hc' hne => rsCodeFinset_hammingDist_ge domain k c c' hc hc' hne) hP hApos hradius

-- Axiom audit.
#print axioms ArkLib.CS25.rs_johnson_radius_sqrt
