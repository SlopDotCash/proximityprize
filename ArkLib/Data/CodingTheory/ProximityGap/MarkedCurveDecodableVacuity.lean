/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve

/-!
# Non-vacuity fence for marked curve decodability (#389, B2 lane)

The marked-variant sanity fence paralleling `curveDecodable_of_card_lt`: when the marked-set size
`a` exceeds the field size `|F|`, the hypothesis `A₀.card = a` is unsatisfiable (a `Finset F` has at
most `|F|` elements), so `MarkedCurveDecodable C ℓ δ a b` holds vacuously.  The meaningful regimes are
exactly `a ≤ |F|`.  Completes the structural grid of the marked variant alongside
`markedCurveDecodable_mono_marked_set_size`.
-/

set_option linter.unusedSectionVars false


open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Non-vacuity of the marked shape** (sanity fence): with the marked-set size above the field
size the hypothesis `A₀.card = a` is unsatisfiable, so every code is trivially
`(ℓ, δ, a, b)`-marked-curve-decodable — the meaningful regimes are exactly `a ≤ |F|`. -/
theorem markedCurveDecodable_of_card_lt (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {a b : ℕ}
    (ha : Fintype.card F < a) :
    MarkedCurveDecodable (F := F) C ℓ δ a b := by
  intro u f _hf A₀ hcard _hδ
  exfalso
  have hle : A₀.card ≤ Fintype.card F := Finset.card_le_univ A₀
  rw [hcard] at hle
  omega

end ProximityGap
