/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._BSG_EX_E4e_PathCount

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
one-sided linear Ruzsa input `#(A'' − N₁) ≤ s · #A''`. The (O2) symmetric→one-sided linearization
that `PrunedFibreSupply` left in its residual is thereby derived by the proven engine, *given* the
energy hypothesis. That implication is valid; the energy hypothesis itself is not attainable.

## `PrunedFibreWithEnergy` is unsatisfiable (audit 2026-10-28, R-212)

An earlier version of this header called `PrunedFibreWithEnergy` a "strictly weaker", non-vacuous
residual and "the genuine deep core of Tao–Vu Lemma 2.30". That is false. For nonempty
`A'', N₁ ⊆ A`, translating `A` gives `#(A'' − A) ≥ #A` and `#(N₁ − A) ≥ #A`, while `#A'' ≤ #A`;
so the energy clause forces `#A'' = #A`, i.e. `A'' = A` (`energy_forces_full` in
`_BSG_EX_E4g_EnergyDegen.lean`). Since `A''` must also lie in the apex neighbourhood
`leftNbhd A G b₀`, which the density hypotheses allow to be a proper subset, the universally
quantified `Prop` is **false for every choice of constants**:
* `prunedFibreWithEnergy_false_singleton` (below): `A = {0,1} ⊆ ZMod 3`, `G = {(0,0)}`, `b₀ = 0`,
  `K = 1`. The density, cherry and good-fibre hypotheses read `4 ≤ 4`, `16 ≤ 32`, `2 ≤ 4`, but the
  forced choices `A'' = N₁ = {0}` make the energy clause `4 ≤ 2`;
* `prunedFibreWithEnergy_false` in `_BSG_EX_E4g_attempt0.lean`: an independent diagonal-graph
  refutation of the apex-confinement / size-calibration pair.
Hence every theorem below is a valid implication from an unsatisfiable premise: it reduces
nothing. A genuine replacement needs an attainable difference/energy bound with its proper losses
(for example the scaled `PrunedFibreRelEnergy` named in `_BSG_EX_E4g_EnergyDegen.lean`), a
nonvacuity / production theorem under the intended dense-graph hypotheses, and a rederived
calibration; none of that is proved here.

## Status

`REFUTED-TARGET`. The implication `PrunedFibreWithEnergy → RelativeDiffCalibration` (path-count
application and `#A`-cancellation) is proven axiom-clean, but its premise is false
(`prunedFibreWithEnergy_false_singleton`), so it is not a reduction of `RelativeDiffCalibration`.

## References
* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29, Lemma 2.30.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## The (unsatisfiable) residual: a pruned second fibre with energy control -/

/-- **`PrunedFibreWithEnergy` — the residual whose one-sided bound is produced by the engine.**
**Unsatisfiable** for every `C₁ s_C s_c`: see `prunedFibreWithEnergy_false_singleton` below and the
module docstring (R-212). Kept as a specification record, not as an open target.

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
axiom-clean). The premise is false (`prunedFibreWithEnergy_false_singleton`), so this does not
discharge, or reduce, the BSG half of BGK. -/
theorem bareDRCExtract_of_prunedFibreWithEnergy {C₁ s_C s_c : ℕ}
    (h : PrunedFibreWithEnergy C₁ s_C s_c) : BareDRCExtract C₁ (s_C ^ 3) (3 * s_c) :=
  bareDRCExtract_of_ruzsaInputFixed (drcRuzsaInputFixed_of_prunedFibreWithEnergy h)

/-! ## Specification regression: the energy clause is unattainable (R-212) -/

/-- Translation lower bound used by the countermodel: `#A ≤ #(B − A)` for nonempty `B`. -/
private lemma card_le_card_sub_of_nonempty {β : Type*} [AddCommGroup β] [DecidableEq β]
    (A B : Finset β) (hB : B.Nonempty) : #A ≤ #(B - A) := by
  obtain ⟨b, hb⟩ := hB
  refine Finset.card_le_card_of_injOn (fun a => b - a) ?_ ?_
  · intro a ha
    exact Finset.sub_mem_sub hb ha
  · intro a _ a' _ h
    simpa using sub_right_injective h

/-- **`PrunedFibreWithEnergy` is false for every choice of constants (singleton-neighbourhood
countermodel).** Take `A = {0, 1} ⊆ ZMod 3`, `G = {(0, 0)}`, `b₀ = 0`, `K = 1`. The density,
cherry and good-fibre hypotheses hold (`4 ≤ 4`, `16 ≤ 32`, `2 ≤ 4`). Any admissible output has
`A'' ⊆ leftNbhd A G 0 = {0}`, so `#A'' ≤ 1`, and nonempty `A''`, `N₁` give
`#(A'' − A), #(N₁ − A) ≥ #A = 2`; the energy clause would then read `4 ≤ 2`. This holds for all
`C₁ s_C s_c`, so the failure is independent of the calibration constants. -/
theorem prunedFibreWithEnergy_false_singleton (C₁ s_C s_c : ℕ) :
    ¬ PrunedFibreWithEnergy C₁ s_C s_c := by
  intro h
  have hA : ({0, 1} : Finset (ZMod 3)).Nonempty := ⟨0, by simp⟩
  have hGsub : ({((0 : ZMod 3), (0 : ZMod 3))} : Finset (ZMod 3 × ZMod 3)) ⊆
      ({0, 1} : Finset (ZMod 3)) ×ˢ ({0, 1} : Finset (ZMod 3)) := by decide
  have hcardA : #({0, 1} : Finset (ZMod 3)) = 2 := by decide
  have hnb : leftNbhd ({0, 1} : Finset (ZMod 3)) {((0 : ZMod 3), (0 : ZMod 3))} 0 = {0} := by
    decide
  have hdeg : ∀ b : ZMod 3, rDeg ({0, 1} : Finset (ZMod 3)) {((0 : ZMod 3), (0 : ZMod 3))} b =
      if b = 0 then 1 else 0 := by decide
  have hsum : ∑ b ∈ ({0, 1} : Finset (ZMod 3)),
      rDeg ({0, 1} : Finset (ZMod 3)) {((0 : ZMod 3), (0 : ZMod 3))} b ^ 2 = 1 := by
    simp [hdeg]
  obtain ⟨A'', b₁, s, -, hsub, hne, hBne, -, -, -, -, henergy⟩ :=
    h (α := ZMod 3) {0, 1} 1 {((0 : ZMod 3), (0 : ZMod 3))} 0 one_pos hA hGsub (by simp)
      (by rw [hcardA]; decide) (by rw [hcardA, hsum]; decide)
      (by rw [hcardA, hdeg]; decide)
  have h1 : #A'' ≤ 1 := by
    have := Finset.card_le_card hsub
    rwa [hnb, Finset.card_singleton] at this
  have h2 := card_le_card_sub_of_nonempty ({0, 1} : Finset (ZMod 3)) A'' hne
  have h3 := card_le_card_sub_of_nonempty ({0, 1} : Finset (ZMod 3)) _ hBne
  rw [hcardA] at h2 h3 henergy
  have h4 := Nat.mul_le_mul h2 h3
  omega

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.relativeDiffCalibration_of_prunedFibreWithEnergy
#print axioms Finset.BSG.drcRuzsaInputFixed_of_prunedFibreWithEnergy
#print axioms Finset.BSG.bareDRCExtract_of_prunedFibreWithEnergy
#print axioms Finset.BSG.prunedFibreWithEnergy_false_singleton
