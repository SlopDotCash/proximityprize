/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.JohnsonBound.ListSize
import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Johnson list-size bound in terms of `Code.minDist`

This connects the isolated Johnson bound (`ArkLib.JohnsonBound.card_ball_le`) to ArkLib's code
vocabulary (`Code.minDist`), the form the proximity / correlated-agreement development consumes.

* `Code.minDist_le_hammingDist` — the defining property of `Code.minDist`: any two distinct
  codewords are at distance at least `Code.minDist`.
* `card_ball_le_minDist` — the **list-decoding ball-size bound** for a finite code, phrased with its
  minimum distance: in the Johnson regime, the number of codewords within Hamming distance `e` of a
  word is at most `n·minDist / ((n - e)² - n·(n - minDist))`. Specialising `minDist` to a Reed–Solomon
  code's distance `n - k + 1` (via `ReedSolomon.minDist_eq'`) gives the RS list-size at the Johnson
  radius — the input to the correlated-agreement "true form".
-/

open scoped BigOperators

namespace ArkLib.JohnsonBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [DecidableEq F]

/-- The defining property of `Code.minDist`: distinct codewords are at distance at least the
minimum distance. -/
theorem minDist_le_hammingDist {C : Set (ι → F)} {u v : ι → F}
    (hu : u ∈ C) (hv : v ∈ C) (huv : u ≠ v) :
    Code.minDist C ≤ hammingDist u v := by
  apply Nat.sInf_le
  exact ⟨u, hu, v, hv, huv, rfl⟩

/-- **List-decoding ball-size bound via `Code.minDist`.** For a finite code `C`, in the Johnson
regime `(n - e)² > n·(n - minDist)`, the number of codewords within Hamming distance `e` of any word
`w` is at most `n·minDist / ((n - e)² - n·(n - minDist))`. -/
theorem card_ball_le_minDist (C : Finset (ι → F)) (w : ι → F) (e : ℕ)
    (hen : e ≤ Fintype.card ι)
    (hdn : Code.minDist (↑C : Set (ι → F)) ≤ Fintype.card ι)
    (hJ : 0 < johnsonDenom (Fintype.card ι) (Code.minDist (↑C : Set (ι → F))) e) :
    ((C.filter (fun c => hammingDist c w ≤ e)).card : ℚ)
      ≤ (Fintype.card ι : ℚ) * (Code.minDist (↑C : Set (ι → F)))
          / johnsonDenom (Fintype.card ι) (Code.minDist (↑C : Set (ι → F))) e := by
  refine card_ball_le C w (Code.minDist (↑C : Set (ι → F))) e ?_ hen hdn hJ
  intro c hc c' hc' hcc
  exact minDist_le_hammingDist (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hcc

end ArkLib.JohnsonBound
