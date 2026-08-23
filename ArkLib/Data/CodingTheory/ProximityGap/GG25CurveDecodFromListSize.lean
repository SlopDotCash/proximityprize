/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import Mathlib.Combinatorics.Pigeonhole

/-!
# Curve decodability from a curve list-size bound — the plain-RS reduction (issue #407, R1)

[GG25] (ePrint 2025/2054) Theorem 3.3 turns **curve decodability** (`CurveDecodable`,
`GG25CurveDecodability.lean`) into mutual correlated agreement via the [GG25] Lemma 3.2 spread
bound (`GG25SpreadBound.lean`, `GG25MCAFromCurveDecodability.lean`, both axiom-clean in-tree).
The remaining gap for **explicit plain Reed–Solomon** is the *input* to that engine:
curve decodability itself. [GG25] supplies it only for folded-RS / multiplicity / random-RS /
subspace-design codes, where a list-recovery / subspace-design argument bounds the number of
distinct close codeword-curves by `O(1/η)` **with field size linear in `n`**.

This file makes the dependence **precise and unconditional**: it isolates the *only* missing
quantity as a **curve list-size bound** and proves the forward reduction

  `curve list-size ≤ m`  ⟹  `(ℓ, δ, a, b)`-curve-decodable whenever `m · b ≤ a`.

The argument is a single pigeonhole: a `CurveAssignment` sends each close seed `α` to a
codeword-curve `cs` through `f α` (these exist seed-by-seed by interpolation); if the assignment's
image has `≤ m` distinct curves, then among the `≥ a` close seeds one curve captures `≥ ⌈a/m⌉ ≥ b`.

## What this does and does NOT close

* **Reduction (this file, axiom-clean):** `curveDecodable_of_curveListSize` — curve decodability
  for *any* `F`-additive code, in the nontrivial regime `b > ℓ + 1`, **reduces exactly** to the
  curve list-size bound `m`. The pigeonhole is lossless: it is the same reduction [GG25] uses, with
  the list-recovery / subspace-design input abstracted to its numerical content `m`.
* **The open core (NOT closed):** for explicit plain RS at the prize point
  (`n = 2^μ`, `ε* = 2^-128`, radius `δ` in the window `(1−√ρ, 1−ρ)` strictly above Johnson), the
  curve list-size `m` is the **open** quantity. It is exactly the in-tree
  `BCIKS20.Curves.ListSizeResidual.RSCurveListSizeResidual` / the BCHKS Conjecture 1.12 floor —
  for `s = 1` (plain RS, fixed field) no `m = poly(n)` bound above Johnson is known. The
  field-linear-in-`n` of [GG25] is precisely what makes `m = O(1/η)` provable for folded/random RS
  and unavailable for plain RS. **This reduction does not advance that open core**; it pins it.

So the honest status of R1: the engine (`curve-decodability ⟹ MCA`) is complete and axiom-clean;
the *only* remaining input for plain RS is the curve list-size, and this file proves that input is
*sufficient* (pigeonhole). The input itself is the recognized open list-size problem.
-/

open Finset Code
open scoped NNReal

set_option linter.unusedSectionVars false

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- A **per-seed curve assignment**: for the data `(u, f)`, a function selecting, for each close
seed `α`, a codeword-curve stack `chooseCurve α` (all rows in `C`) whose curve passes through
`f α`. This is exactly what seed-by-seed interpolation through a single close codeword provides
(degree-`ℓ` curve through `f α`); the *content* of [GG25] / the list-recovery step is bounding the
number of **distinct** stacks in its image. -/
structure CurveAssignment (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) where
  /-- The chosen codeword-curve at each seed. -/
  chooseCurve : F → Fin (ℓ + 1) → ι → A
  /-- Every chosen row is a codeword. -/
  mem_code : ∀ α, ∀ j, chooseCurve α j ∈ C
  /-- At every close seed the chosen curve passes through `f α`. -/
  passes_through : ∀ α ∈ curveCloseSet δ u f,
    f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • chooseCurve α j i

/-- **The curve list-size hypothesis.** Code `C` has *curve list-size `≤ m`* (at parameters
`ℓ, δ`) if for every data `(u, f)` with `f` codeword-valued there is a curve assignment whose image
over the close set contains at most `m` distinct codeword-curves. This is the abstracted numerical
content of the subspace-design / list-recovery step of [GG25]: for folded/random RS, `m = O(1/η)`
(field linear in `n`); for explicit plain RS above Johnson it is the **open** list-size
(`RSCurveListSizeResidual` / BCHKS Conj 1.12). -/
def CurveListSizeLe (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (m : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
    ∃ asgn : CurveAssignment C ℓ δ u f,
      ((curveCloseSet δ u f).image asgn.chooseCurve).card ≤ m

/-- **The forward reduction (R1 engine input), pigeonhole.** If `C` has curve list-size `≤ m` at
`(ℓ, δ)`, and `m · b ≤ a` with `m ≥ 1`, then `C` is `(ℓ, δ, a, b)`-curve-decodable.

This is the *only* step [GG25] supplies differently for the various code families: the pigeonhole
itself is universal; what differs is the value of `m` (small for folded/random RS via list-recovery,
**open** for plain RS above Johnson). Axiom-clean `[propext, Classical.choice, Quot.sound]`. -/
theorem curveDecodable_of_curveListSize {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {m a b : ℕ}
    (hm : 1 ≤ m) (hmb : m * b ≤ a)
    (h : CurveListSizeLe (F := F) C ℓ δ m) :
    CurveDecodable (F := F) C ℓ δ a b := by
  classical
  intro u f hf hclose
  -- Obtain the curve assignment with `≤ m` distinct curves over the close set.
  obtain ⟨asgn, hcard⟩ := h u f hf
  set S := curveCloseSet δ u f with hS
  set L := S.image asgn.chooseCurve with hL
  -- The assignment maps the close set into its (`≤ m`-element) image.
  have hmaps : ∀ α ∈ S, asgn.chooseCurve α ∈ L := fun α hα =>
    Finset.mem_image_of_mem _ hα
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · -- `b = 0`: any single chosen curve trivially explains `≥ 0` seeds.
    subst hb0
    refine ⟨asgn.chooseCurve (Classical.arbitrary F), fun j => asgn.mem_code _ j, ?_⟩
    exact Nat.zero_le _
  · -- `b ≥ 1`, so `a ≥ m·b ≥ 1`, so `S` and hence `L` are nonempty.
    have hSpos : 0 < S.card := by
      have : 0 < a := lt_of_lt_of_le (Nat.mul_pos hm hbpos) hmb
      omega
    have hSne : S.Nonempty := Finset.card_pos.mp hSpos
    have hLne : L.Nonempty := hSne.image _
    -- Pigeonhole: `|L| · b ≤ m · b ≤ a ≤ |S|`, so some curve has a `≥ b` fiber.
    have hmul : L.card * b ≤ S.card := by
      calc L.card * b ≤ m * b := Nat.mul_le_mul_right b hcard
        _ ≤ a := hmb
        _ ≤ S.card := hclose
    obtain ⟨cs, hcsL, hfiber⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hLne hmul
    -- `cs` is a codeword stack (it is some `chooseCurve α₀`).
    rw [hL, Finset.mem_image] at hcsL
    obtain ⟨α₀, _hα₀, rfl⟩ := hcsL
    refine ⟨asgn.chooseCurve α₀, fun j => asgn.mem_code α₀ j, ?_⟩
    refine le_trans hfiber (Finset.card_le_card ?_)
    intro α hα
    rw [Finset.mem_filter] at hα
    obtain ⟨hαS, hαeq⟩ := hα
    rw [Finset.mem_filter]
    refine ⟨hαS, ?_⟩
    have hpt := asgn.passes_through α hαS
    rw [hpt, hαeq]

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.curveDecodable_of_curveListSize
