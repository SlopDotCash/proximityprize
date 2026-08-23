/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The counting question in the unpinned window: refuted top slice, surviving interior (#232)

O84 (`TheoremQUDExtraction.lean`) left exactly one unpinned window for the bad-scalar count
on the unique-decoding side: in `e`-units (`e = n − t`, `t = ⌈(1−δ)n⌉₊`), the regime
`3e ≥ d` (the affine-subtraction proof is unavailable) and `2e ≤ d − 1` (unique decoding
still holds), with the **natural conjecture** `mcaBadCount ≤ 2(n−t)+1` open there — "the
gap is a counting question, not a structure question".

`scripts/probes/probe_counting_gap.py` (exact GF(p) arithmetic, exit 0) settles the shape
of the answer:

* **The natural conjecture is FALSE on the top slice `2e = d − 1` (d odd).**  A
  multi-family Möbius construction (error pair `(e₀,e₁)` supported on an `(e+1)`-set `T₁`,
  equal on `T₁` to codeword pairs `h_j` vanishing off `T₁ ∪ T_j`; each family contributes
  `e+1` cancellation scalars with Möbius-distinct ratios) produces
  `badCount = 6 > 5 = 2e+1` at RS(6,2)/GF(7) (`δ = 1/3`), `10 > 9` at RS(16,8)/GF(97)
  (`δ = 1/4` — inside the δ-window `(d/(3n), (d−1)/(2n)]`, at its included right
  endpoint) and at RS(12,4)/GF(13), and `12 > 3` at RS(12,10)/GF(13) (`e = 1, d = 3`:
  twelve of thirteen scalars bad — **no closed form `f(e)` or `f(n−t)` alone can hold**;
  the count is governed by the m=2-interleaved list size at radius `2e`, the O74/O85
  ceiling `1 + 2(n−t)·Λ₂`).
* **Exhaustively, the top-slice maximum is exactly `2e+2` at the two smallest points**:
  over *all* coset-pair classes of RS(6,2) and RS(7,3) over GF(7) (23,200 affine classes
  each, coverage and invariances machine-checked), the true max badCount is `6 = 2e+2`,
  attained by 20 resp. 140 classes; never `7 = q`.
* **The interior `2e ≤ d − 2` SURVIVES**: 0 violations of `2(n−t)+1` across 1,263
  adversarial stacks (g-planting, 2-g nesting, two-cancel, random, structured-collapse
  shapes) at `(q,n,k,e)` = (97,16,8,3), (13,12,4,3), (13,12,2,4), the even-`d` top
  (13,9,4,2), and a non-MDS (hence non-GRS) `[8,3,5]₇` control; the multi-family
  construction is provably rigid there (the consistency kernel is 1-dimensional, forcing
  proportional rows and a constant ratio — printed by the probe as it blocks).

This file records that split as named statements:

* `GapCountingBoundFullWindow` — the natural conjecture on the **full** UD-side window
  `2(n−t)+1 ≤ d`.  **Expected FALSE** (probe counterexamples above); kept as the named
  falsified surface, not an axiom and never assumed.
* `InteriorCountingBound` — the **surviving** conjecture, window `2(n−t)+2 ≤ d`.  Open;
  every adversarial hunt is consistent with it, and it strictly extends O84's proven
  window `3(n−t) < d` (`interior_window_extends_proven`).
* `interiorCountingBound_of_gapCountingBoundFullWindow` — the (refuted ⇒ surviving)
  monotonicity, so any future proof attempt targets the weaker honest statement.
* `epsMCA_le_of_interiorCountingBound` — the consumer: the surviving conjecture yields
  `ε_mca ≤ (2(n−t)+1)/|F|` on its window, the ABF26 Grand-Challenge `poly/q` shape, via
  `epsMCA_le_of_badCount_le`.
* `gap_trichotomy` / `top_slice_iff_odd` — the e-units bookkeeping: the UD side splits
  exactly into O84's proven window, the surviving interior, and the refuted odd-`d` top
  slice.
* `interior_or_top_slice` / `even_ud_window_is_interior` — convenience forms used to
  route future attempts away from the refuted odd endpoint: any full-window point that is
  not literally top-slice is already in the surviving interior, and every even-`d`
  endpoint is automatically interior.

Provenance: axiom-clean (`[propext, Classical.choice, Quot.sound]`), zero `sorry`.
References: [ABF26] Def 4.3 / Grand Challenge 1; O74/O78/O84/O85 in
`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`; the probe
`scripts/probes/probe_counting_gap.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.CountingGap

open _root_.ProximityGap
open scoped NNReal ENNReal BigOperators

/-- **The natural counting conjecture on the full unique-decoding-side window — expected
FALSE.**  For every `F`-linearly-closed code of minimum distance `≥ d` and every stack,
if `2(n−t)+1 ≤ d` (unique decoding) then `mcaBadCount ≤ 2(n−t)+1`.

`probe_counting_gap.py` refutes this for `(ι, F) = (Fin 6, ZMod 7)` at `δ = 1/3`
(badCount `6 > 5`; exhaustive over all stacks, max exactly `6`), for
`(Fin 16, ZMod 97)` at `δ = 1/4` (`10 > 9`), and catastrophically for
`(Fin 12, ZMod 13)` at `δ = 1/12, d = 3` (`12 > 3`).  Named so the falsified surface has
one canonical statement; do **not** cite as a hypothesis — use `InteriorCountingBound`. -/
def GapCountingBoundFullWindow (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F : Type) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (C : Set (ι → F)) (δ : ℝ≥0) (d : ℕ),
    (∀ (a b : F), ∀ x ∈ C, ∀ y ∈ C, a • x + b • y ∈ C) →
    (∀ c ∈ C, c ≠ 0 → d ≤ (Finset.univ.filter (fun i => c i ≠ 0)).card) →
    2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 1 ≤ d →
    ∀ u₀ u₁ : ι → F,
      mcaBadCount (F := F) C δ u₀ u₁
        ≤ 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 1

/-- **The surviving counting conjecture (OPEN): the strict interior of the
unique-decoding side.**  Same bound, on the window `2(n−t)+2 ≤ d` — i.e. strictly below
the unique-decoding radius, `δ`-units `δ < (d−1)/(2n)` away from the included right
endpoint.  `probe_counting_gap.py`: 0 violations across 1,263 adversarial stacks at four
RS parameter points plus a non-MDS (non-GRS) `[8,3,5]₇` attack-search control, and the
only known violation mechanism (coexisting
`(e+1)`-support decode families) is provably unavailable here, since two such families
differ by an interleaved codeword of column weight `≤ 2(n−t)+2 ≤ d`, forcing equality
except on the refuted top slice. -/
def InteriorCountingBound (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F : Type) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (C : Set (ι → F)) (δ : ℝ≥0) (d : ℕ),
    (∀ (a b : F), ∀ x ∈ C, ∀ y ∈ C, a • x + b • y ∈ C) →
    (∀ c ∈ C, c ≠ 0 → d ≤ (Finset.univ.filter (fun i => c i ≠ 0)).card) →
    2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 2 ≤ d →
    ∀ u₀ u₁ : ι → F,
      mcaBadCount (F := F) C δ u₀ u₁
        ≤ 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 1

/-- The refuted full-window statement is (strictly) stronger than the surviving interior
statement: any future proof attempt should target `InteriorCountingBound`. -/
theorem interiorCountingBound_of_gapCountingBoundFullWindow
    (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (h : GapCountingBoundFullWindow ι F) : InteriorCountingBound ι F := by
  intro C δ d hlin hdist hwin u₀ u₁
  exact h C δ d hlin hdist (by omega) u₀ u₁

/-- **The consumer: the surviving conjecture yields the Grand-Challenge `poly/q` shape on
its window.**  If `InteriorCountingBound` holds, then for every `F`-linearly-closed `C`
of minimum distance `≥ d` with `2(n−t)+2 ≤ d`,
`ε_mca(C, δ) ≤ (2(n−t)+1)/|F|` — the same bound shape as O84's proven
`epsMCA_le_of_uniqueDecoding`, extended from `3(n−t) < d` to the full strict interior. -/
theorem epsMCA_le_of_interiorCountingBound
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hconj : InteriorCountingBound ι F)
    (C : Set (ι → F)) (δ : ℝ≥0) (d : ℕ)
    (hlin : ∀ (a b : F), ∀ x ∈ C, ∀ y ∈ C, a • x + b • y ∈ C)
    (hdist : ∀ c ∈ C, c ≠ 0 → d ≤ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    (hwin : 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 2 ≤ d) :
    epsMCA (F := F) (A := F) C δ
      ≤ ((2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) + 1 : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  classical
  apply epsMCA_le_of_badCount_le
  intro u
  have h := hconj C δ d hlin hdist hwin (u 0) (u 1)
  unfold mcaBadCount at h
  convert h using 2

/-- **The e-units trichotomy of the unique-decoding side** (`e = n − t`).  Every point
with `2e + 1 ≤ d` lies in exactly one of: O84's proven window `3e < d`; the surviving
interior `d ≤ 3e ∧ 2e + 2 ≤ d`; the refuted top slice `2e + 1 = d`. -/
theorem gap_trichotomy (e d : ℕ) (hud : 2 * e + 1 ≤ d) :
    3 * e < d ∨ (d ≤ 3 * e ∧ 2 * e + 2 ≤ d) ∨ 2 * e + 1 = d := by
  omega

/-- The refuted top slice `2e + 1 = d` is realisable exactly for odd `d` — for even `d`
the right endpoint of the unique-decoding window is already in the surviving interior. -/
theorem top_slice_iff_odd (d : ℕ) : (∃ e, 2 * e + 1 = d) ↔ Odd d := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, by omega⟩
  · rintro ⟨e, he⟩
    exact ⟨e, by omega⟩

/-- On the full unique-decoding-side window, the only way to miss the surviving interior
is to be exactly on the refuted top slice `2e+1 = d`.  This is the routing lemma for
future proof attempts: once the top-slice obstruction is excluded, target
`InteriorCountingBound`. -/
theorem interior_or_top_slice (e d : ℕ) (hud : 2 * e + 1 ≤ d) :
    2 * e + 2 ≤ d ∨ 2 * e + 1 = d := by
  omega

/-- If the minimum-distance parameter `d` is even, the refuted top slice cannot occur;
therefore the full unique-decoding-side window is already in the surviving interior. -/
theorem even_ud_window_is_interior (e d : ℕ) (hd : Even d) (hud : 2 * e + 1 ≤ d) :
    2 * e + 2 ≤ d := by
  rcases hd with ⟨r, rfl⟩
  omega

/-- The surviving conjecture window strictly extends O84's proven window: e.g. `e = 3`,
`d = 9` (the probe's interior point at RS(16,8)/GF(97), `δ = 3/16`) satisfies
`2e + 2 ≤ d` but not `3e < d`. -/
theorem interior_window_extends_proven : ∃ e d : ℕ, 2 * e + 2 ≤ d ∧ ¬ 3 * e < d :=
  ⟨3, 9, by omega, by omega⟩

#print axioms interiorCountingBound_of_gapCountingBoundFullWindow
#print axioms epsMCA_le_of_interiorCountingBound
#print axioms gap_trichotomy
#print axioms top_slice_iff_odd
#print axioms interior_or_top_slice
#print axioms even_ud_window_is_interior
#print axioms interior_window_extends_proven

end ArkLib.ProximityGap.CountingGap
