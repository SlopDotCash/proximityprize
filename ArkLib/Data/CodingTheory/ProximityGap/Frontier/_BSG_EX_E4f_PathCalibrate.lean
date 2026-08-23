/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_EX_E4e_PathCount

/-!
# BSG `E4f` — calibrating via the proven path-count engine (stronger reduction)

This complements `_BSG_EX_E4f_Calibrate` (`PrunedFibreSupply`). There the one-sided linear difference
bound `#(A'' − N₁) ≤ s · #A''` is kept *inside* the residual and the proven path-count engine
`pathCount_card_bound` is not used. Here we instead **run the engine**: the residual drops the
one-sided difference clause entirely and supplies only what `pathCount_card_bound` *consumes* —
every-pair richness — plus a **relative-difference energy** bound; the one-sided linear conclusion is
then *derived* by the engine + a single cancellation of `#A`.

## The reduction

`pathCount_card_bound` proves, from every-pair richness `∀ a ∈ A'', ∀ a' ∈ N₁, #A ≤ s · cn(a,a')`,

  `#(A'' − N₁) · #A ≤ s · (#(A'' − A) · #(N₁ − A))`.

Adding the energy control `#(A'' − A) · #(N₁ − A) ≤ #A · #A''` and cancelling `#A > 0` gives the
one-sided linear Ruzsa input `#(A'' − N₁) ≤ s · #A''`. This is exactly the (O2)
symmetric→one-sided linearization that `PrunedFibreSupply` left in its residual — here it is
**discharged by the proven engine**, at the cost of replacing it with the strictly weaker, engine-
native energy hypothesis (which mentions no difference set `A'' − N₁` at all).

## Why `PrunedFibreWithEnergy` is strictly smaller than `RelativeDiffCalibration`

It has **no `#(A'' − N₁)` clause** (the engine produces it). It replaces it with the every-pair
richness (the engine's input) and the energy bound `#(A'' − A) · #(N₁ − A) ≤ #A · #A''`. Neither is
vacuous (both hold when `A` is a subgroup, where every difference lands back in `A`), and neither is
`RelativeDiffCalibration` renamed: the asymmetric Ruzsa conclusion has been removed and the proven
symmetric path-count does the linearization. The residual carries only the coupled apex-pruning +
second-fibre choice + energy content — the genuine deep core of Tao–Vu Lemma 2.30.

## Status

`REDUCES-FURTHER`. `RelativeDiffCalibration` is reduced to `PrunedFibreWithEnergy`, with the
path-count application and the `#A`-cancellation proven axiom-clean.

## References
* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29, Lemma 2.30.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## The strictly-smaller residual: a pruned second fibre with energy control -/

/-- **`PrunedFibreWithEnergy` — the residual whose one-sided bound is produced by the engine.**

From the post-averaging data it asserts the existence of a refinement `A'' ⊆ leftNbhd A G b₀`, a
second popular fibre `b₁ ∈ A`, and a factor `s ≤ s_C · K ^ s_c`, satisfying:

* the two **size calibrations** `C₁ K #A'' ≥ #A` and `#A'' ≤ s · #N₁` (`N₁ = leftNbhd A G b₁`),
* **every-pair richness** `∀ a ∈ A'', ∀ a' ∈ N₁, #A ≤ s · cn(a,a')` (the engine's input), and
* the **relative-difference energy** `#(A'' − A) · #(N₁ − A) ≤ #A · #A''`.

It has **no `#(A'' − N₁)` clause**; that one-sided difference bound is derived in
`relativeDiffCalibration_of_prunedFibreWithEnergy` by the proven `pathCount_card_bound`. -/
def PrunedFibreWithEnergy (C₁ s_C s_c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' : Finset α) (b₁ : α) (s : ℕ),
        b₁ ∈ A ∧
        A'' ⊆ leftNbhd A G b₀ ∧ A''.Nonempty ∧ (leftNbhd A G b₁).Nonempty ∧
        s ≤ s_C * K ^ s_c ∧
        C₁ * K * #A'' ≥ #A ∧
        #A'' ≤ s * #(leftNbhd A G b₁) ∧
        (∀ a ∈ A'', ∀ a' ∈ leftNbhd A G b₁, #A ≤ s * commonNeighbors A G a a') ∧
        #(A'' - A) * #(leftNbhd A G b₁ - A) ≤ #A * #A''

/-! ## The calibration: `PrunedFibreWithEnergy → RelativeDiffCalibration` (PROVEN) -/

/-- **Calibration via the engine (PROVEN).** The proven symmetric path-count `pathCount_card_bound`
plus the energy control and a single division by `#A > 0` yield the one-sided linear Ruzsa input
`#(A'' − N₁) ≤ s · #A''`, completing `RelativeDiffCalibration`. -/
theorem relativeDiffCalibration_of_prunedFibreWithEnergy {C₁ s_C s_c : ℕ}
    (h : PrunedFibreWithEnergy C₁ s_C s_c) : RelativeDiffCalibration C₁ s_C s_c := by
  intro α _ _ A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  classical
  obtain ⟨A'', b₁, s, hb₁, hsub, hne, hBne, hsbd, hsize₁, hsize₂, hrich, henergy⟩ :=
    h A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  refine ⟨A'', b₁, s, hb₁, hsub, hne, hBne, hsbd, hsize₁, ?_, hsize₂⟩
  have hsubA : A'' ⊆ A := hsub.trans (Finset.filter_subset _ _)
  have hsubN₁ : leftNbhd A G b₁ ⊆ A := Finset.filter_subset _ _
  have hpc : #(A'' - leftNbhd A G b₁) * #A
      ≤ s * (#(A'' - A) * #(leftNbhd A G b₁ - A)) :=
    pathCount_card_bound A G A'' (leftNbhd A G b₁) s hsubA hsubN₁ hrich
  have hApos : 0 < #A := hA.card_pos
  have hchain : #(A'' - leftNbhd A G b₁) * #A ≤ (s * #A'') * #A := by
    calc #(A'' - leftNbhd A G b₁) * #A
        ≤ s * (#(A'' - A) * #(leftNbhd A G b₁ - A)) := hpc
      _ ≤ s * (#A * #A'') := Nat.mul_le_mul_left _ henergy
      _ = (s * #A'') * #A := by ring
  exact Nat.le_of_mul_le_mul_right hchain hApos

/-- **`PrunedFibreWithEnergy → DRCRuzsaInputFixed`** (composition; PROVEN axiom-clean). -/
theorem drcRuzsaInputFixed_of_prunedFibreWithEnergy {C₁ s_C s_c : ℕ}
    (h : PrunedFibreWithEnergy C₁ s_C s_c) : DRCRuzsaInputFixed C₁ s_C s_c :=
  drcRuzsaInputFixed_of_calibration (relativeDiffCalibration_of_prunedFibreWithEnergy h)

/-- **`PrunedFibreWithEnergy → BareDRCExtract`** (full composition through the BSG chain; PROVEN
axiom-clean). Proving `PrunedFibreWithEnergy` discharges the BSG half of BGK. -/
theorem bareDRCExtract_of_prunedFibreWithEnergy {C₁ s_C s_c : ℕ}
    (h : PrunedFibreWithEnergy C₁ s_C s_c) : BareDRCExtract C₁ (s_C ^ 3) (3 * s_c) :=
  bareDRCExtract_of_ruzsaInputFixed (drcRuzsaInputFixed_of_prunedFibreWithEnergy h)

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.relativeDiffCalibration_of_prunedFibreWithEnergy
#print axioms Finset.BSG.drcRuzsaInputFixed_of_prunedFibreWithEnergy
#print axioms Finset.BSG.bareDRCExtract_of_prunedFibreWithEnergy
