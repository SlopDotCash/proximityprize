/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodFromListSize
import ArkLib.Data.CodingTheory.ProximityGap.GG25MCAFromCurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._Attack05CurveListSizeReducesToRSList

/-!
# [GG25] B2 curve-decodability — the end-to-end capstone (issue #334, class B item B2)

This file seals the **B2 arrow** the issue-#334 ledger asks for — *"a good interleaved
list-decoding bound implies a good mutual-correlated-agreement (MCA) bound"* — into a single
composed theorem, over the faithful [GG25] (ePrint 2025/2054) Definition 3.1 / [Jo26]
(ePrint 2026/891) Definition 2.7 curve-decodability notion.

The two engine halves were already axiom-clean in-tree:

* **list-size ⟹ curve-decodability** (pigeonhole):
  `ProximityGap.curveDecodable_of_curveListSize` (`GG25CurveDecodFromListSize.lean`);
* **curve-decodability ⟹ MCA** (spread / all-seeds-close, [GG25] Lemma 3.2 & Thm 3.3):
  `ProximityGap.GG25Lemma32.all_seeds_relClose_of_curveDecodable`
  (`GG25MCAFromCurveDecodability.lean`);

and the per-row factorization of the curve list size was landed in
`ProximityGap.Attack05.curveListSize_le_pow_of_rowList_le`
(`Frontier/_Attack05CurveListSizeReducesToRSList.lean`): the number of distinct degree-`ℓ`
codeword-curves in the close-set image is `≤ Lᵈ` where `L` is the per-row (RS) list-decoding
list size at radius `δ` and `d = ℓ+1` is the number of rows.

What was missing — and is supplied here — is the **interface brick** turning a per-row
list-decoding bound into the `CurveListSizeLe` predicate the pigeonhole engine consumes, plus the
composed end-to-end statement.  The result:

> **`curveDecodable_relMCA_of_rowList_le`.**  If, for every stack `u` and every codeword-valued
> `f : F → C`, some curve assignment has *every* row list of size `≤ L` (the per-row list-decoding
> bound at radius `δ`), and the arithmetic `Lᵈ·t ≤ a`, `1 ≤ Lᵈ`, `ℓ < t` holds, then `C` is
> `(ℓ, δ, a, t)`-curve-decodable, and hence for any `(u, f)` with the close set of size `≥ a` there
> is a single codeword-curve within relative Hamming distance `(t/(t−ℓ))·δ` of the tested curve at
> **every** seed — the MCA conclusion.

This is the **complete, un-conditional B2 reduction**: no `δ*` / BGK / Paley input appears.  The
only remaining code-family-specific input is the numeric per-row list size `L`, which is `O(1/η)`
(field size linear in `n`) for folded/random RS via list-recovery, and is the open BCHKS-1.12
line-ball object only for *explicit plain RS above Johnson* (`RSCurveListSizeResidual`) — that
open input is entirely outside this reduction.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Code
open scoped NNReal

namespace ProximityGap

open GG25Lemma32

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The interface brick (the B2 arrow's missing link).**  A per-row list-decoding bound feeds the
curve list-size predicate: if for every data `(u, f)` (codeword-valued) some curve assignment has
*every* row list `rowList … j` of size `≤ L`, then `C` has curve list-size `≤ Lᵈ`, `d = ℓ+1`.

Pure bookkeeping over `Attack05.curveListSize_le_pow_of_rowList_le`: the per-row product bound,
packaged existentially. -/
theorem curveListSizeLe_of_rowList_le (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (L : ℕ)
    (h : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
      ∃ asgn : CurveAssignment C ℓ δ u f,
        ∀ j, (Attack05.rowList C ℓ δ u f asgn j).card ≤ L) :
    CurveListSizeLe (F := F) C ℓ δ (L ^ (ℓ + 1)) := by
  intro u f hf
  obtain ⟨asgn, hrow⟩ := h u f hf
  exact ⟨asgn, Attack05.curveListSize_le_pow_of_rowList_le C ℓ δ u f asgn L hrow⟩

/-- **B2, list-size half sealed:** a per-row list-decoding bound `L` (with `Lᵈ·b ≤ a`, `1 ≤ Lᵈ`,
`d = ℓ+1`) makes `C` `(ℓ, δ, a, b)`-curve-decodable.  Composition of `curveListSizeLe_of_rowList_le`
into the `curveDecodable_of_curveListSize` pigeonhole engine. -/
theorem curveDecodable_of_rowList_le {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {L a b : ℕ}
    (hm : 1 ≤ L ^ (ℓ + 1)) (hmb : L ^ (ℓ + 1) * b ≤ a)
    (h : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
      ∃ asgn : CurveAssignment C ℓ δ u f,
        ∀ j, (Attack05.rowList C ℓ δ u f asgn j).card ≤ L) :
    CurveDecodable (F := F) C ℓ δ a b :=
  curveDecodable_of_curveListSize hm hmb (curveListSizeLe_of_rowList_le C ℓ δ L h)

/-- **B2 END-TO-END CAPSTONE: interleaved list-decoding bound ⟹ MCA bound.**

Assume a per-row list-decoding bound `L` at radius `δ` (for every stack `u` and codeword-valued
`f`), and the arithmetic `1 ≤ Lᵈ`, `Lᵈ·t ≤ a`, `ℓ < t` (`d = ℓ+1`).  Then for *any* data `(u, f)`
with the close set of size `≥ a`, there is a single codeword-curve `cs` (all rows in `C`) within
relative Hamming distance `(t/(t−ℓ))·δ` of the tested curve `∑ⱼ βʲ·uⱼ` at **every** seed `β` — the
mutual-correlated-agreement conclusion of [GG25] Definition 3.1.

This is the full, unconditional B2 reduction; the only code-family input is the numeric `L`. -/
theorem curveDecodable_relMCA_of_rowList_le {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {L a t : ℕ}
    (hm : 1 ≤ L ^ (ℓ + 1)) (hmb : L ^ (ℓ + 1) * t ≤ a) (hlt : ℓ < t)
    (hrows : ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
      ∃ asgn : CurveAssignment C ℓ δ u f,
        ∀ j, (Attack05.rowList C ℓ δ u f asgn j).card ≤ L)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      ∀ β : F, ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
            ≤ ((t : ℝ≥0) / ((t - ℓ : ℕ) : ℝ≥0)) * δ :=
  GG25Lemma32.all_seeds_relClose_of_curveDecodable hlt
    (curveDecodable_of_rowList_le hm hmb hrows) hf hclose

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.curveListSizeLe_of_rowList_le
#print axioms ProximityGap.curveDecodable_of_rowList_le
#print axioms ProximityGap.curveDecodable_relMCA_of_rowList_le
