/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding

/-!
# Reed–Solomon list-decodability up to the Johnson radius (#82)

The qualitative Johnson-radius theorem for Reed–Solomon, eliminating the explicit list-size hypothesis
from `rs_list_size_le`.  If the **Johnson radius condition** holds —

  `A² > T·B`,  with  `A = (n−e) − n/q`,  `B = (n−d) − n/q`,  `T = n(1−1/q)`,  `d = n−(k−1)` —

then a finite list-size bound exists: some `ℓ` bounds the number of RS codewords within distance `e`
of *every* word.  The witness `ℓ` is produced by the Archimedean property (any `ℓ` past
`(T²−A²)/(A²−T·B)` discharges the Johnson quadratic), then fed through `rs_list_size_le`.  This is the
RS list-decoding radius; beyond it (`A² ≤ T·B`) the list size is unbounded — the open content of #141.
`sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon list-decodability up to the Johnson radius.** If the Johnson radius condition holds
(`A² > T·B` with `A = (n−e) − n/q`, `B = (n−d) − n/q`, `T = n(1−1/q)`, `d = n−(k−1)`), then there is a
finite list-size bound: some `ℓ` bounds the number of RS codewords within distance `e` of every word. -/
theorem rs_johnson_radius (domain : ι ↪ F) (k : ℕ) [NeZero k] (e : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
            - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))) :
    ∃ ℓ : ℕ, ∀ w : ι → F, closeCount (rsCodeFinset domain k) e w ≤ ℓ := by
  set A := ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) with hA
  set B := ((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
    - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) with hB
  set T := (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) with hT
  have hden : 0 < A ^ 2 - T * B := by linarith [hradius]
  obtain ⟨ℓ, hℓ⟩ := exists_nat_gt ((T ^ 2 - A ^ 2) / (A ^ 2 - T * B))
  rw [div_lt_iff₀ hden] at hℓ
  refine ⟨ℓ, fun w => ?_⟩
  have hsq : ((ℓ : ℝ) + 1) * A ^ 2 > T * (T + (ℓ : ℝ) * B) := by nlinarith [hℓ]
  have hlist := rs_list_size_le domain k hq1 hn w e ℓ hP hsq
  rw [closeCount]
  have hfe : (rsCodeFinset domain k).filter (fun c => hammingDist w c ≤ e)
      = (rsCodeFinset domain k).filter (fun c => hammingDist c w ≤ e) := by
    apply Finset.filter_congr; intro c _; rw [hammingDist_comm]
  rw [hfe]; exact hlist

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_johnson_radius
