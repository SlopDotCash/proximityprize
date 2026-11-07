/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding

/-!
# Reed–Solomon list-decodability up to the Johnson radius (#82)

The qualitative Johnson-radius theorem for Reed–Solomon, eliminating the explicit list-size hypothesis
from `rs_list_size_le`.  If the **Johnson radius condition** holds —

  `A² > T·B`,  with  `A = (n−e) − n/q`,  `B = (n−d) − n/q`,  `T = n(1−1/q)`,  `d = n−(k−1)` —

then every RS list at radius `e` has size at most `⌊(T²−A²)/(A²−T·B)⌋₊ + 1`
(`rs_johnson_radius_explicit`): this `ℓ` is past `(T²−A²)/(A²−T·B)`, so it discharges the Johnson
quadratic, and is then fed through `rs_list_size_le`. The bound depends only on `n`, `q`, `k`, `e`
and blows up as the Johnson margin `A² − T·B` tends to `0`.

`rs_johnson_radius` keeps only the existential `∃ ℓ, ∀ w, closeCount … ≤ ℓ`, which on its own is
uninformative: every finite code satisfies it at every radius with `ℓ = |RS|` (at radius `n` the
list is all of RS). Outside the Johnson condition (`A² ≤ T·B`) this sufficient bound is merely
unavailable; that is **not** a proof that lists are large there. The open content of #141 is a
*uniform* (field-size-independent, polynomial in `n`) list-size bound up to capacity — see
`UniformPolyListSizeConjecture` in `RSListDecodingCapacityGap.lean`.
`sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Quantitative Reed–Solomon Johnson list-size bound.** If the Johnson radius condition holds
(`A² > T·B` with `A = (n−e) − n/q`, `B = (n−d) − n/q`, `T = n(1−1/q)`, `d = n−(k−1)`), then every
Hamming ball of radius `e` contains at most `⌊(T² − A²)/(A² − T·B)⌋₊ + 1` RS codewords. -/
theorem rs_johnson_radius_explicit (domain : ι ↪ F) (k : ℕ) [NeZero k] (e : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
            - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
    (w : ι → F) :
    closeCount (rsCodeFinset domain k) e w ≤
      ⌊(((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) ^ 2
          - (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        / ((((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
          - ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
            * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))⌋₊
        + 1 := by
  set A := ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) with hA
  set B := ((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
    - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) with hB
  set T := (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) with hT
  have hden : 0 < A ^ 2 - T * B := by linarith [hradius]
  set ℓ : ℕ := ⌊(T ^ 2 - A ^ 2) / (A ^ 2 - T * B)⌋₊ + 1 with hℓdef
  have hℓ : (T ^ 2 - A ^ 2) / (A ^ 2 - T * B) < (ℓ : ℝ) := by
    rw [hℓdef]; push_cast; exact Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hden] at hℓ
  have hsq : ((ℓ : ℝ) + 1) * A ^ 2 > T * (T + (ℓ : ℝ) * B) := by nlinarith [hℓ]
  have hlist := rs_list_size_le domain k hq1 hn w e ℓ hP hsq
  rw [closeCount]
  have hfe : (rsCodeFinset domain k).filter (fun c => hammingDist w c ≤ e)
      = (rsCodeFinset domain k).filter (fun c => hammingDist c w ≤ e) := by
    apply Finset.filter_congr; intro c _; rw [hammingDist_comm]
  rw [hfe]; exact hlist

/-- **Reed–Solomon list-decodability up to the Johnson radius.** If the Johnson radius condition holds
(`A² > T·B` with `A = (n−e) − n/q`, `B = (n−d) − n/q`, `T = n(1−1/q)`, `d = n−(k−1)`), then there is a
finite list-size bound: some `ℓ` bounds the number of RS codewords within distance `e` of every word.

The existential alone is weak (it holds at every radius with `ℓ = |RS|`); the Johnson content is the
explicit bound in `rs_johnson_radius_explicit`. -/
theorem rs_johnson_radius (domain : ι ↪ F) (k : ℕ) [NeZero k] (e : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
            - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))) :
    ∃ ℓ : ℕ, ∀ w : ι → F, closeCount (rsCodeFinset domain k) e w ≤ ℓ :=
  ⟨_, fun w => rs_johnson_radius_explicit domain k e hq1 hn hP hradius w⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_johnson_radius_explicit
#print axioms ArkLib.CS25.rs_johnson_radius
