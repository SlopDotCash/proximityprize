/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve

/-!
# Monotonicity of marked curve decodability in the marked-set size (#389, B2 lane)

[Jo26] Definition 5.1 marked curve decodability `MarkedCurveDecodable C ℓ δ a b` quantifies over a
*specified* close marked set `A₀` of size exactly `a`.  This file proves it is monotone in `a`:
enlarging the marked-set size `a → a'` preserves the property — given a close marked set of size `a'`,
restrict to an `a`-subset (`Finset.exists_subset_card_eq`), apply the hypothesis, and the explaining
curve's `b` points of the subset lie in the larger set.  Mirrors the `curveDecodable_of_marked`
restriction pattern in the same file.
-/

set_option linter.unusedSectionVars false


open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Marked curve decodability is monotone in the marked-set size.**  If `C` is
`(ℓ,δ,a,b)`-marked-curve-decodable and `a ≤ a'`, then it is `(ℓ,δ,a',b)`-marked-curve-decodable. -/
theorem markedCurveDecodable_mono_marked_set_size {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {a a' b : ℕ} (haa : a ≤ a') (h : MarkedCurveDecodable (F := F) C ℓ δ a b) :
    MarkedCurveDecodable (F := F) C ℓ δ a' b := by
  intro u f hf A₀' hcard' hclose'
  have ha' : a ≤ A₀'.card := by rw [hcard']; exact haa
  obtain ⟨A₀, hsub, hcard⟩ := Finset.exists_subset_card_eq ha'
  have hclose : ∀ α ∈ A₀,
      (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ :=
    fun α hα => hclose' α (hsub hα)
  obtain ⟨cs, hcs, hcount⟩ := h u f hf A₀ hcard hclose
  exact ⟨cs, hcs, le_trans hcount (Finset.card_le_card (Finset.filter_subset_filter _ hsub))⟩

end ProximityGap
