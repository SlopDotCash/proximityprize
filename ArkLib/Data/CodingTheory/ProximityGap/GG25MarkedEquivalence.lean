/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.GG25SmallWitness
import ArkLib.Data.CodingTheory.ProximityGap.GG25NonCovering
import ArkLib.Data.CodingTheory.ProximityGap.GG25ExactPreservation

/-!
# The marked/original equivalence, completed (issue #334, K5 capstone)

[Jo26] (ePrint 2026/891) **Theorem 5.5** in full: for an `F`-additive code and `b ≤ a ≤ q`,
[GG25] curve decodability and marked curve decodability are **equivalent**. The
marked → original direction is `curveDecodable_of_marked` (`GG25MarkedCurve.lean`); this file
proves the converse by welding the section's own bricks:

* `b ≤ ℓ + 1`: the marked property holds *unconditionally* by interpolation
  (**Lemma 5.2**, `markedCurveDecodable_of_small_witness`);
* `b > ℓ + 1`, `C` nonzero: by **Lemma 5.4** (`exists_far_codeword_of_curveDecodable`) the
  code does not `δ`-cover, so redefining `f` off `A₀` to a far codeword pins the close set to
  *exactly* `A₀`; the restricted original property
  (`marked_on_exact_closeSet_of_curveDecodable`) then explains `b` points of `A₀`, and the
  explanations transfer back since the modified `f` agrees with `f` on `A₀`;
* `b > ℓ + 1`, `C` zero: the zero curve explains everything.

With both directions formal, **Corollary 5.9's parameter-free half** follows: [GG25] curve
decodability itself (not just the marked variant) transfers exactly under interleaving when
`C(a,b) ≤ q` (`curveDecodable_interleaved_of_choose_le`).
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **[Jo26] Theorem 5.5, original → marked.** For an additive code with `b ≤ a ≤ q`, [GG25]
curve decodability implies marked curve decodability. -/
theorem markedCurveDecodable_of_curveDecodable (C : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    {a b : ℕ} (hab : b ≤ a) (ha : a ≤ Fintype.card F)
    (h : CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b) :
    MarkedCurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b := by
  classical
  by_cases hbsmall : b ≤ ℓ + 1
  · -- Small-witness regime: interpolation, unconditionally.
    exact markedCurveDecodable_of_small_witness C δ hbsmall hab
  push Not at hbsmall
  by_cases hCzero : ∀ v ∈ C, v = (0 : ι → A)
  · -- Zero code: the zero curve explains every point of A₀.
    intro u f hf A₀ hcard _hδ
    refine ⟨fun _ => 0, fun _ => C.zero_mem, ?_⟩
    have hall : A₀.filter (fun α => f α = fun i =>
        ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (fun _ => (0 : ι → A)) j i) = A₀ := by
      refine Finset.filter_true_of_mem fun α hα => ?_
      have hf0 : f α = 0 := hCzero (f α) (hf α)
      rw [hf0]
      funext i
      simp
    rw [hall, hcard]
    exact hab
  push Not at hCzero
  obtain ⟨v, hvC, hv⟩ := hCzero
  -- Nonzero code, b > ℓ + 1: pin the close set to exactly A₀ via far codewords (Lemma 5.4).
  intro u f hf A₀ hcard hδ
  -- For each seed, a codeword far from the curve value at that seed.
  have hfar : ∀ α : F, ∃ c ∈ C, ¬ ((δᵣ(
      (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), c) : ℝ≥0) ≤ δ) := fun α =>
    exists_far_codeword_of_curveDecodable h ha hbsmall hvC hv _
  choose far hfarC hfarFar using hfar
  -- The pinned instance: f on A₀, the far codeword off it.
  set f' : F → ι → A := fun α => if α ∈ A₀ then f α else far α with hf'
  have hf'C : ∀ α, f' α ∈ (C : Set (ι → A)) := by
    intro α
    rw [hf']
    beta_reduce
    by_cases hα : α ∈ A₀
    · rw [if_pos hα]; exact hf α
    · rw [if_neg hα]; exact hfarC α
  have hexact : curveCloseSet δ u f' = A₀ := by
    ext α
    simp only [curveCloseSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hclose
      by_contra hα
      rw [hf'] at hclose
      simp only [if_neg hα] at hclose
      exact hfarFar α hclose
    · intro hα
      rw [hf']
      simp only [if_pos hα]
      exact hδ α hα
  obtain ⟨cs, hcs, hcount⟩ :=
    marked_on_exact_closeSet_of_curveDecodable h u f' hf'C A₀ hcard hexact
  refine ⟨cs, hcs, le_trans hcount (le_of_eq ?_)⟩
  -- On A₀, f' = f, so the explained-point filters coincide.
  refine congrArg Finset.card (Finset.filter_congr fun α hα => ?_)
  rw [hf']
  beta_reduce
  rw [if_pos hα]

/-- **[Jo26] Theorem 5.5 (the full equivalence).** For an `F`-additive code with `b ≤ a ≤ q`,
[GG25] curve decodability and marked curve decodability coincide. -/
theorem curveDecodable_iff_marked (C : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    {a b : ℕ} (hab : b ≤ a) (ha : a ≤ Fintype.card F) :
    CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b ↔
      MarkedCurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b :=
  ⟨markedCurveDecodable_of_curveDecodable C hab ha, curveDecodable_of_marked⟩

/-- **[Jo26] Corollary 5.9, parameter-free half: exact [GG25]-curve-decodability transfer.**
If `C` is `(ℓ, δ, a, b)`-curve-decodable in the [GG25] sense, `b ≤ a ≤ q`, and `C(a,b) ≤ q`,
then so is every interleaving `C^{≡s}` (over `rowwiseCode`; convert with
`rowwiseCode_eq_interleave`) — the original-sense transfer obtained by sandwiching
Theorem 5.7 between the two directions of Theorem 5.5. -/
theorem curveDecodable_interleaved_of_choose_le (C : Submodule F (ι → A)) {ℓ s : ℕ}
    (hs : 1 ≤ s) {δ : ℝ≥0} {a b : ℕ} (hb : 1 ≤ b) (hab : b ≤ a) (ha : a ≤ Fintype.card F)
    (h : CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b)
    (hchoose : a.choose b ≤ Fintype.card F) :
    CurveDecodable (F := F) (rowwiseCode (C : Set (ι → A)) s) ℓ δ a b :=
  curveDecodable_of_marked
    (markedCurveDecodable_interleaved_of_choose_le C hs
      (markedCurveDecodable_of_curveDecodable C hab ha h) hchoose)

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.markedCurveDecodable_of_curveDecodable
#print axioms ProximityGap.curveDecodable_iff_marked
#print axioms ProximityGap.curveDecodable_interleaved_of_choose_le
