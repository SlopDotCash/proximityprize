/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent

/-!
# [GG25] curve decodability — the definitional skeleton (issue #334, K5, brick 1)

[GG25] (ePrint 2025/2054) Definition 3.1, in the notation of [Jo26] (ePrint 2026/891)
Definition 2.7: an `F_q`-additive code `C ⊆ Σ^n` is **`(ℓ, δ, a, b)`-curve-decodable** if for
every stack `u = (u₀, …, u_ℓ)` and every codeword-valued function `f : F_q → C`, whenever the
*close set*

  `A_δ(u, f) := {α : Δ(∑ⱼ uⱼ αʲ, f α) ≤ δ}`

has at least `a` elements, there exist codewords `c₀, …, c_ℓ ∈ C` whose curve explains `f` on
at least `b` of those points: `#{α ∈ A_δ(u, f) : f α = ∑ⱼ cⱼ αʲ} ≥ b`.

This file is the **definitional-honesty brick**: the faithful definition against the in-tree
distance (`δᵣ`, `Basic/RelativeDistance.lean`) and curve-combiner conventions
(`mcaEventCurve`'s `∑ j, γ^j • u j`, `MCACurveEvent.lean`), plus the structural lemmas any
consumer needs and a non-vacuity check:

* `CurveDecodable` — the definition;
* `CurveDecodable.mono` — monotonicity in all four parameters (larger `a`, smaller `b`,
  smaller `δ` make the property weaker/the hypothesis stronger as appropriate);
* `curveDecodable_of_card_lt` — the vacuous-threshold sanity instance (`|F| < a` makes the
  hypothesis unsatisfiable), pinning the definitional shape;
* `CurveDecodable.exists_curve_of_close` — the unfolded consumer form.

The substantive [Jo26]/[GG25] transfer theorems over this definition (the curve-decodability
half of the issue's class-B2 item) are follow-up bricks; nothing here claims them.
-/

open Finset Code
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The close set** `A_δ(u, f)` of [GG25] Def 3.1: the seeds `α` where the curve combination
`∑ⱼ αʲ • uⱼ` is `δ`-close (relative Hamming) to the codeword `f α`. -/
noncomputable def curveCloseSet (δ : ℝ≥0) {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) :
    Finset F :=
  univ.filter (fun α : F =>
    (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ)

/-- **[GG25] Definition 3.1 / [Jo26] Definition 2.7 (curve decodability).** `C` is
`(ℓ, δ, a, b)`-curve-decodable if for every `(ℓ+1)`-row stack `u` and every codeword-valued
`f : F → C`: whenever the close set has at least `a` seeds, some single codeword curve
`α ↦ ∑ⱼ αʲ • cⱼ` explains `f` on at least `b` of them. -/
def CurveDecodable (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (a b : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
    a ≤ (curveCloseSet δ u f).card →
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      b ≤ ((curveCloseSet δ u f).filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)).card

/-- The unfolded consumer form: from a concrete close-set bound, the explaining curve. -/
theorem CurveDecodable.exists_curve_of_close {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ}
    (h : CurveDecodable (F := F) C ℓ δ a b)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      b ≤ ((curveCloseSet δ u f).filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)).card :=
  h u f hf hclose

/-- The close set is antitone in `δ` (smaller radius, smaller close set). -/
theorem curveCloseSet_mono {δ δ' : ℝ≥0} (hδ : δ ≤ δ') {ℓ : ℕ}
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) :
    curveCloseSet δ u f ⊆ curveCloseSet δ' u f := by
  intro α hα
  simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hα ⊢
  exact le_trans hα hδ

/-- **Parameter monotonicity**: curve decodability weakens when the close-set threshold `a`
grows or the explanation target `b` shrinks. -/
theorem CurveDecodable.mono {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a a' b b' : ℕ}
    (h : CurveDecodable (F := F) C ℓ δ a b) (ha : a ≤ a') (hb : b' ≤ b) :
    CurveDecodable (F := F) C ℓ δ a' b' := by
  intro u f hf hclose
  obtain ⟨cs, hcs, hcount⟩ := h u f hf (le_trans ha hclose)
  exact ⟨cs, hcs, le_trans hb hcount⟩

/-- **Non-vacuity of the shape** (sanity fence): with the threshold above the field size the
hypothesis is unsatisfiable, so every code is trivially `(ℓ, δ, a, b)`-curve-decodable — the
meaningful regimes are exactly `a ≤ |F|`. -/
theorem curveDecodable_of_card_lt (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {a b : ℕ}
    (ha : Fintype.card F < a) :
    CurveDecodable (F := F) C ℓ δ a b := by
  intro u f _hf hclose
  exfalso
  have hle : (curveCloseSet δ u f).card ≤ Fintype.card F := by
    simpa using Finset.card_filter_le (univ : Finset F) _
  omega

/-- **The decodable-explains-the-close-set corollary at full strength** (`b = a`-shape
consumers): if `C` is `(ℓ, δ, a, a)`-curve-decodable then on any `f` with close set exactly
hitting the threshold, a single curve explains the *whole* close set. Stated for the
threshold case `card = a` (the general `b ≤ card` form is the definition itself). -/
theorem CurveDecodable.full_explanation {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a : ℕ}
    (h : CurveDecodable (F := F) C ℓ δ a a)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : (curveCloseSet δ u f).card = a) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      (curveCloseSet δ u f).filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)
      = curveCloseSet δ u f := by
  obtain ⟨cs, hcs, hcount⟩ := h u f hf (le_of_eq hclose.symm)
  refine ⟨cs, hcs, Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_⟩
  calc (curveCloseSet δ u f).card = a := hclose
  _ ≤ _ := hcount

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.CurveDecodable.mono
#print axioms ProximityGap.curveDecodable_of_card_lt
#print axioms ProximityGap.CurveDecodable.full_explanation
#print axioms ProximityGap.curveCloseSet_mono
