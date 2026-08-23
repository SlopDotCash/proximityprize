/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.JohnsonBound.CodeListSize
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Reed–Solomon list-size at the Johnson radius

Specialising the `Code.minDist` list-decoding ball-size bound
(`ArkLib.JohnsonBound.card_ball_le_minDist`) to a Reed–Solomon code, whose minimum distance is
`n_ι − k + 1` (`ReedSolomon.minDist_eq'`), gives the RS list-size at the Johnson radius — the input
the correlated-agreement / proximity development consumes.

* `rs_card_ball_le` — for a finite set `C` enumerating the Reed–Solomon code `code α k`, the number
  of codewords within Hamming distance `e` of a word `w` is, in the Johnson regime, at most
  `n_ι · (n_ι − k + 1) / ((n_ι − e)² − n_ι · (n_ι − (n_ι − k + 1)))`.

This is a *foundational* rung: the remaining step to the actual `ε_mca` Johnson-range bound
(BCHKS25 T4.12 multiplicity-coded interpolation) is genuinely open mathematics and is **not**
discharged here.
-/

open scoped BigOperators

namespace ArkLib.JohnsonBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- **Reed–Solomon list-size at the Johnson radius.** If a finite set `C` enumerates the
Reed–Solomon code `ReedSolomon.code α k` (degree-`< k` evaluations), then in the Johnson regime the
number of RS codewords within Hamming distance `e` of any word `w` is bounded by the Johnson
list-size with the RS minimum distance `Fintype.card ι − k + 1`. -/
theorem rs_card_ball_le {k : ℕ} [NeZero k] {α : ι ↪ F}
    (C : Finset (ι → F)) (hC : (↑C : Set (ι → F)) = (ReedSolomon.code α k : Set (ι → F)))
    (w : ι → F) (e : ℕ) (hk : k ≤ Fintype.card ι)
    (hen : e ≤ Fintype.card ι)
    (hJ : 0 < johnsonDenom (Fintype.card ι) (Fintype.card ι - k + 1) e) :
    ((C.filter (fun c => hammingDist c w ≤ e)).card : ℚ)
      ≤ (Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
          / johnsonDenom (Fintype.card ι) (Fintype.card ι - k + 1) e := by
  have hk1 : 0 < k := NeZero.pos k
  have hmd : Code.minDist (↑C : Set (ι → F)) = Fintype.card ι - k + 1 := by
    rw [hC]; exact ReedSolomon.minDist_eq' hk
  have hdn : Code.minDist (↑C : Set (ι → F)) ≤ Fintype.card ι := by
    rw [hmd]; omega
  have hJ' : 0 < johnsonDenom (Fintype.card ι) (Code.minDist (↑C : Set (ι → F))) e := by
    rw [hmd]; exact hJ
  have hbound := card_ball_le_minDist C w e hen hdn hJ'
  rwa [hmd] at hbound

end ArkLib.JohnsonBound
