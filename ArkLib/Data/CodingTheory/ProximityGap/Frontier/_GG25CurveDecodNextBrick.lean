/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GG25CurveDecodabilityOpener

/-!
# B2 brick L2a — the *f-value* refinement of the curve list-size anchor (issue #334, class B2)

**Where this sits.** The [GG25] (ePrint 2025/2054) Def 3.1 curve-decodability `def`, the forward
pigeonhole reduction `curveDecodable_of_curveListSize`, and the *universal anchor*
`curveListSizeLe_card_le_card` (`CurveListSizeLe C ℓ δ |F|` for every submodule code) are all
already in-tree and axiom-clean (`GG25CurveDecodFromListSize.lean`,
`Frontier/_GG25CurveDecodabilityOpener.lean`). The universal anchor pins the curve list-size at the
trivial level `m = |F|`; the open content of B2 is *how far below `|F|`* the bound can be pushed for
explicit plain RS above Johnson (`RSCurveListSizeResidual` / BChKS Conj 1.12).

**What this file adds (a genuine, unconditional, structured sub-`|F|` refinement).** The universal
anchor proved `m ≤ |F|` by bounding the image of the **constant-curve assignment**
`α ↦ (f α, 0, …, 0)` by `|closeSet| ≤ |F|`. But that image is *more* structured than `closeSet`:
two seeds `α, α'` map to the **same** constant curve iff `f α = f α'`. So the image card is exactly
the number of **distinct codeword values `f` takes on the close set**, `|f '' closeSet|` — which can
be strictly below `|F|` whenever the received word `f` is value-constrained (the structured
sub-cases B2 actually cares about: a small close set, or `f` ranging over a unique-decoding ball /
a short codeword list). This file proves:

* `constCurveAssignment_image_card_le_fclose` — **the refinement**: the constant-curve assignment's
  image has card `≤ |f '' closeSet|` (the f-value count), refining the `|F|` of the anchor;
* `curveListSizeLe_of_fvalue_count` — **the structured sub-`|F|` list-size**: if `f` takes at most
  `s` distinct values on the close set for *every* admissible `(u, f)`, then `CurveListSizeLe C ℓ δ s`
  — a genuine list-size at the f-value count `s`, `≤ |F|` and strictly below it when `s < |F|`;
* `curveListSizeLe_of_close_set_small` — the cleanest closed instance: if the close set never
  exceeds `s` seeds, then `CurveListSizeLe C ℓ δ s` (since `|f '' closeSet| ≤ |closeSet| ≤ s`);
* `curveDecodable_of_fvalue_count` / `curveDecodable_of_close_set_small` — **the payoff**: feeding
  the sub-`|F|` list-size `s` into the forward reduction yields `(ℓ, δ, a, b)`-curve-decodability
  under the *weakened* budget `s · b ≤ a` (instead of `|F| · b ≤ a`). Every `s < |F|` is a strict
  improvement over the universal-anchor baseline `curveDecodable_of_card_le_mul`.

**Honest scope.** This does NOT advance the open plain-RS list-size: bounding `s` below `|F|` for
explicit plain RS above Johnson is exactly the open wall (`RSCurveListSizeResidual`). What this file
proves is that *whenever* the close set / the f-value range is structurally small (the regime where
list-recovery / unique decoding applies), the list-size is provably that small — i.e. the engine's
input is sharp, not just `≤ |F|`. The bound is the value-count `s`, exposed as an explicit, named,
checkable quantity rather than the trivial field size.

Everything here is unconditional and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7. Issue #334, class B2.
-/

open Finset Code
open scoped NNReal

namespace ProximityGap.B2NextBrick

open ProximityGap ProximityGap.B2Opener

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### The f-value refinement of the constant-curve image -/

/-- **The constant-curve assignment is f-value-indexed.** Two seeds map to the same constant
curve `(·, 0, …, 0)` exactly when `f` agrees on them: `chooseCurve α = chooseCurve α' ↔ f α = f α'`.
Hence the image card of the constant-curve assignment over the close set is bounded by the number
of distinct values `f` takes there, `|f '' closeSet|` — the structured refinement of the `|F|`
universal anchor. -/
theorem constCurveAssignment_image_card_le_fclose (C : Submodule F (ι → A)) {ℓ : ℕ} (δ : ℝ≥0)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) (hf : ∀ α, f α ∈ (C : Set (ι → A))) :
    ((curveCloseSet δ u f).image
        (constCurveAssignment C (ℓ := ℓ) (δ := δ) u f hf).chooseCurve).card
      ≤ ((curveCloseSet δ u f).image f).card := by
  classical
  -- The constant-curve assignment factors as `g ∘ f` with `g w = (w, 0, …, 0)`: at every seed
  -- `α`, `chooseCurve α = g (f α)`. So its image over the close set is `g '' (f '' closeSet)`,
  -- whose card is `≤ |f '' closeSet|` by `card_image_le`.
  set g : (ι → A) → (Fin (ℓ + 1) → ι → A) := fun w j => if (j : ℕ) = 0 then w else 0 with hg
  have hfactor : (curveCloseSet δ u f).image
      (constCurveAssignment C (ℓ := ℓ) (δ := δ) u f hf).chooseCurve
      = ((curveCloseSet δ u f).image f).image g := by
    rw [Finset.image_image]
    refine Finset.image_congr (fun α _ => ?_)
    funext j
    simp only [constCurveAssignment, hg, Function.comp_apply]
  rw [hfactor]
  exact Finset.card_image_le

/-! ### The structured sub-`|F|` list-size -/

/-- **The structured sub-`|F|` curve list-size (f-value count).** If, for every admissible
instance `(u, f)`, the received word `f` takes at most `s` distinct values on the close set, then
`C` has curve list-size `≤ s`. Combined with `constCurveAssignment_image_card_le_fclose`, the
constant-curve assignment realizes this bound. This is `≤ |F|` (`s ≤ |F|` always), and strictly
below it exactly when `f` is value-constrained — the structured regime B2 cares about. -/
theorem curveListSizeLe_of_fvalue_count (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {s : ℕ}
    (hs : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ (C : Set (ι → A))) →
      ((curveCloseSet δ u f).image f).card ≤ s) :
    CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ s := by
  classical
  intro u f hf
  refine ⟨constCurveAssignment C (ℓ := ℓ) (δ := δ) u f hf, ?_⟩
  exact le_trans (constCurveAssignment_image_card_le_fclose C δ u f hf) (hs u f hf)

/-- **The cleanest closed sub-`|F|` instance: a small close set.** If the close set never exceeds
`s` seeds (for every admissible instance), then `C` has curve list-size `≤ s` — because
`|f '' closeSet| ≤ |closeSet| ≤ s`. This is the unique-decoding / list-recovery regime made
explicit: a structurally small close set gives a structurally small list-size, `≤ |F|` and below it
whenever `s < |F|`. (For plain RS above Johnson the close set is *not* known to be small — that is
the open wall.) -/
theorem curveListSizeLe_of_close_set_small (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {s : ℕ}
    (hsmall : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ (C : Set (ι → A))) →
      (curveCloseSet δ u f).card ≤ s) :
    CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ s := by
  refine curveListSizeLe_of_fvalue_count C ℓ δ (fun u f hf => ?_)
  exact le_trans Finset.card_image_le (hsmall u f hf)

/-! ### The payoff: curve-decodability under the weakened (sub-`|F|`) budget -/

/-- **Curve-decodability from the f-value count.** Feeding the structured sub-`|F|` list-size `s`
(`curveListSizeLe_of_fvalue_count`) into the forward reduction `curveDecodable_of_curveListSize`:
under the *weakened* budget `s · b ≤ a` (vs the universal `|F| · b ≤ a` of
`curveDecodable_of_card_le_mul`), `C` is `(ℓ, δ, a, b)`-curve-decodable. Every `s < |F|` is a strict
relaxation of the baseline. -/
theorem curveDecodable_of_fvalue_count (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {s a b : ℕ}
    (hs1 : 1 ≤ s) (hsb : s * b ≤ a)
    (hs : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ (C : Set (ι → A))) →
      ((curveCloseSet δ u f).image f).card ≤ s) :
    CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b :=
  curveDecodable_of_curveListSize hs1 hsb (curveListSizeLe_of_fvalue_count C ℓ δ hs)

/-- **Curve-decodability from a small close set.** The cleanest payoff: if the close set never
exceeds `s` seeds, then under `s · b ≤ a` (with `s ≥ 1`) `C` is `(ℓ, δ, a, b)`-curve-decodable. For
`s < |F|` this strictly improves the universal-anchor baseline `curveDecodable_of_card_le_mul`
(`|F| · b ≤ a`). -/
theorem curveDecodable_of_close_set_small (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {s a b : ℕ}
    (hs1 : 1 ≤ s) (hsb : s * b ≤ a)
    (hsmall : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ (C : Set (ι → A))) →
      (curveCloseSet δ u f).card ≤ s) :
    CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b :=
  curveDecodable_of_curveListSize hs1 hsb (curveListSizeLe_of_close_set_small C ℓ δ hsmall)

end ProximityGap.B2NextBrick

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.B2NextBrick.constCurveAssignment_image_card_le_fclose
#print axioms ProximityGap.B2NextBrick.curveListSizeLe_of_fvalue_count
#print axioms ProximityGap.B2NextBrick.curveListSizeLe_of_close_set_small
#print axioms ProximityGap.B2NextBrick.curveDecodable_of_fvalue_count
#print axioms ProximityGap.B2NextBrick.curveDecodable_of_close_set_small
