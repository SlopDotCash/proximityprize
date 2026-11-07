/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability

/-!
# Marked curve decodability and the marked/original equivalence (issue #334, K5, brick 2)

[Jo26] (ePrint 2026/891) §5: the **marked** variant of [GG25] curve decodability —
Definition 5.1 — quantifies over a *specified* close subset `A₀` of size exactly `a` (every
point of which is `δ`-close on its curve value) instead of the full close set, and asks the
explaining curve to hit `b` points of `A₀`. This is the form the interleaving transfer
theorems (5.7/5.8) manipulate. This brick:

* `MarkedCurveDecodable` — the faithful Definition 5.1;
* `curveDecodable_of_marked` — **Theorem 5.5, marked → original** (the "immediate" direction):
  the marked property applied at any `a`-subset of the close set gives the original (the close
  set has ≥ a points, choose `a` of them; the explaining curve's `b` points lie in the chosen
  subset ⊆ close set);
* `marked_on_exact_closeSet_of_curveDecodable` — the original property applied to an instance
  whose close set is *exactly* the specified `A₀` explains `b` points of `A₀` (the restricted
  form of the converse).

**Where the full equivalence lives.** This file proves only the two results above. The complete
converse (original → marked) and the two-way statement for an `F`-additive code
(`C : Submodule F (ι → A)`) with `b ≤ a ≤ q` are proved in `GG25MarkedEquivalence.lean`:
`markedCurveDecodable_of_curveDecodable` and `curveDecodable_iff_marked`. That proof splits off
the small-witness regime `b ≤ ℓ + 1` (Lemma 5.2, `markedCurveDecodable_of_small_witness` in
`GG25SmallWitness.lean`) and the zero code, and otherwise uses non-covering (Lemma 5.4,
`exists_far_codeword_of_curveDecodable`) to redefine `f` off `A₀` by far codewords, so that the
close set is exactly `A₀` and `marked_on_exact_closeSet_of_curveDecodable` applies.
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **[Jo26] Definition 5.1 (marked curve decodability).** For every stack, every
codeword-valued `f`, and every *specified* `A₀` of size `a` all of whose points are `δ`-close
on their curve values, some codeword curve explains `f` on at least `b` points **of `A₀`**. -/
def MarkedCurveDecodable (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (a b : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
    ∀ A₀ : Finset F, A₀.card = a →
    (∀ α ∈ A₀, (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ) →
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      b ≤ (A₀.filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)).card

/-- **Theorem 5.5, (marked → original).** The marked property at any `a`-subset of the close
set yields the original: choose `a` close points as `A₀`; the explaining curve's `b` points of
`A₀` are in particular `b` points of the close set. -/
theorem curveDecodable_of_marked {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ}
    (h : MarkedCurveDecodable (F := F) C ℓ δ a b) :
    CurveDecodable (F := F) C ℓ δ a b := by
  intro u f hf hclose
  -- Choose an a-subset of the close set.
  obtain ⟨A₀, hsub, hcard⟩ := Finset.exists_subset_card_eq hclose
  have hδ : ∀ α ∈ A₀, (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0)
      ≤ δ := by
    intro α hα
    have := hsub hα
    simpa [curveCloseSet] using this
  obtain ⟨cs, hcs, hcount⟩ := h u f hf A₀ hcard hδ
  refine ⟨cs, hcs, le_trans hcount (Finset.card_le_card ?_)⟩
  intro α hα
  rw [Finset.mem_filter] at hα ⊢
  exact ⟨hsub hα.1, hα.2⟩

/-- **Theorem 5.5, original → marked, restricted form (close set exactly `A₀`).** If the close
set of the instance `(u, f)` is exactly the specified `A₀` of size `a`, the original property
fires and its `b` explained points of the close set are `b` explained points of `A₀`.

For a general specified `A₀` (only contained in the close set) the explained points of the
original property need not lie in `A₀`; the full converse for an `F`-additive code with
`b ≤ a ≤ q` is `markedCurveDecodable_of_curveDecodable` in `GG25MarkedEquivalence.lean`, which
reduces to this lemma by redefining `f` off `A₀` with far codewords (non-covering, Lemma 5.4) and
handles `b ≤ ℓ + 1` by interpolation (Lemma 5.2) and the zero code separately. -/
theorem marked_on_exact_closeSet_of_curveDecodable {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {a b : ℕ} (h : CurveDecodable (F := F) C ℓ δ a b)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) (hf : ∀ α, f α ∈ C)
    (A₀ : Finset F) (hcard : A₀.card = a)
    (hexact : curveCloseSet δ u f = A₀) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      b ≤ (A₀.filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)).card := by
  obtain ⟨cs, hcs, hcount⟩ := h u f hf (by rw [hexact, hcard])
  exact ⟨cs, hcs, by rwa [hexact] at hcount⟩

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.curveDecodable_of_marked
#print axioms ProximityGap.marked_on_exact_closeSet_of_curveDecodable
