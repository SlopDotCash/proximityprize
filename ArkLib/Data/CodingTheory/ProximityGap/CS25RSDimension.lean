/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSEncodingInjective

/-!
# Reed–Solomon dimension `|RS| = qᵏ` (#82)

The Reed–Solomon code `rsCodeFinset domain k` (with `k ≤ n`) has exactly `qᵏ` codewords: it is the
injective image (`evalOnPoints_injOn_degreeLT`) of the degree-`<k` polynomials, of which there are
`Fintype.card (degreeLT F k) = qᵏ` (via `Polynomial.degreeLTEquiv : degreeLT F k ≃ₗ (Fin k → F)`).
With `rsCodeFinset_hammingDist_ge` (minimum distance `n−k+1`) this records the full
`[n, k, n−k+1]` MDS parameters of Reed–Solomon codes.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon dimension.**  For `1 ≤ k ≤ n`, the RS code has exactly `qᵏ` codewords. -/
theorem rsCodeFinset_card (domain : ι ↪ F) (k : ℕ) [NeZero k] (hnk : k ≤ Fintype.card ι)
    [Fintype (Polynomial.degreeLT F k)] :
    (rsCodeFinset domain k).card = Fintype.card F ^ k := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hnd : ∀ p : Polynomial.degreeLT F k, (p : Polynomial F).natDegree < k := by
    intro p
    by_cases hp0 : (p : Polynomial F) = 0
    · rw [hp0, Polynomial.natDegree_zero]; exact hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr (Polynomial.mem_degreeLT.mp p.2)
  rw [rsCodeFinset_eq_image, Finset.card_image_of_injOn]
  · rw [Finset.card_univ, Fintype.card_congr (Polynomial.degreeLTEquiv F k).toEquiv,
        Fintype.card_fun, Fintype.card_fin]
  · intro p _ p' _ h
    apply Subtype.ext
    exact evalOnPoints_injOn_degreeLT domain k hnk (p : Polynomial F) (p' : Polynomial F)
      (hnd p) (hnd p') h

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rsCodeFinset_card
