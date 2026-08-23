/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonPackageSupply

/-!
# The production-regime `δ*` bracket (#357): what is verified at deployed scale

The production shape: smooth evaluation domain (`n = 2^a`), `|F| = q` up to `2^256`,
error budget `ε* = 2^{−128}` — so `q ≥ n·2^{128}` puts every count up to `n` strictly
below budget (`n/q ≤ 2^{−128}`).  This file states what is machine-checked about
`mcaDeltaStar` exactly there, with each conditional layer carrying its named price.

* `production_good_ladder` — **unconditional**: `δ* ≥ j/n` whenever `j ≤ n`,
  `3(j−1) + k ≤ n`, and `j/q ≤ ε*`.  At production (`n/q ≤ ε*`) this holds up to the
  full ladder reach `j_max = ⌊(n−k)/3⌋ + 1`, i.e. `δ* ≥ ((n−k)/3 + 1)/n ≈ (1−ρ)/3`.
* `production_good_johnson_of_packageSupply` — **conditional on exactly
  `CellPackageSupply`** (the one named residual of the Johnson lane) plus the
  explicit budget inequality `johnsonBoundReal ≤ ε*`: every Johnson-range radius
  is good, i.e. `δ* ≥ 1 − √ρ − η` territory.

**The bad side at production, honestly:** every landed lower-bound family (spike
floor, sunflower/window families at capacity, the pencil supply, the widened-pin
stacks) produces at most `O(n)` bad scalars, i.e. mass `O(n)/q ≤ ε*` — **silent** at
production budget.  No radius `< 1` is currently certified bad at `ε* = 2^{−128}`
for `q ≥ n·2^{128}`; certifying any would require a family with `> q·2^{−128} ≥ 2^{128}`
bad scalars at one stack, which is exactly the above-Johnson construction question
(equivalently: beating `√q` on smooth subgroups — `SubgroupGaussSumWorstCase`).  The
production bracket therefore stands at

  `[(1−ρ)/3  (unconditional) · 1−√ρ−η  (mod CellPackageSupply),   1]`

with the entire remaining gap concentrated in the two named objects above.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.ProductionRegime

open ProximityGap.SpikeFloor ProximityGap.MCAThresholdLedger
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open BCIKS20.CellPencilJohnson

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The unconditional production good side (ladder reach).**  For smooth RS at any
rate, every radius below the band edge `j/n` is good as soon as the band mass `j/q`
fits the budget — at production shape (`n/q ≤ ε*`) this holds for every ladder band.
Hence `δ* ≥ j/n` for every `j ≤ n` with `3(j−1) + k ≤ n`. -/
theorem production_good_ladder (dom : Fin n ↪ F) {k j : ℕ}
    (hj1 : 1 ≤ j) (hd3 : 3 * (j - 1) + k ≤ n) (hjn : j ≤ n) {εstar : ℝ≥0∞}
    (hbudget : (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    (j : ℝ≥0) / (n : ℝ≥0)
      ≤ mcaDeltaStar (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by
    have := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  by_contra h
  push Not at h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  -- c is a good radius: ε_mca(c) ≤ j/q ≤ ε*
  have hcn : c * (Fintype.card (Fin n) : ℝ≥0) < j := by
    rw [Fintype.card_fin]
    exact (lt_div_iff₀ hn0).mp hc2
  have hgood : epsMCA (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) c ≤ εstar :=
    le_trans (epsMCA_le_j_div_card (rsCode dom k)
      (rsCode_noWeightLE dom (by omega)) hcn) hbudget
  have hcle1 : c ≤ 1 := by
    refine le_of_lt (lt_of_lt_of_le hc2 ?_)
    rw [div_le_one hn0]
    exact_mod_cast hjn
  exact absurd (le_mcaDeltaStar_of_good (F := F) (A := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar hcle1 hgood)
    (not_le.mpr hc1)

/-- The production-shape corollary at the full ladder reach: `δ* ≥ (⌊(n−k)/3⌋ + 1)/n`
whenever `n/q ≤ ε*` (true at `ε* = 2^{−128}` for every `q ≥ n·2^{128}`). -/
theorem production_good_ladder_reach (dom : Fin n ↪ F) {k : ℕ} (hk : k ≤ n)
    {εstar : ℝ≥0∞}
    (hprod : (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    (((n - k) / 3 + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)
      ≤ mcaDeltaStar (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine production_good_ladder dom (by omega) (by omega) (by omega) ?_
  refine le_trans ?_ hprod
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast (by omega : (n - k) / 3 + 1 ≤ n)

/-- **The conditional production good side (Johnson reach).**  Conditional on exactly
the named `CellPackageSupply` residual and the explicit numeric budget
`johnsonBoundReal ≤ ε*`, every Johnson-range radius is good:
`δ ≤ δ*` for every `δ < 1 − √ρ₊ − η` in the discharge regime. -/
theorem production_good_johnson_of_packageSupply
    (hsupply : ∀ (n k m : ℕ) (_ : NeZero n) (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀)
      (_ : DecidableEq F₀) (domain : Fin n ↪ F₀) (δ : ℝ≥0),
      2 ≤ k → k + 1 ≤ n → 12 ≤ m → δ ≤ 1 →
      CellPackageSupply domain k δ
        (max (n * (GuruswamiSudan.constraintIndices m).card
          * (gs_degree_bound k n m / (k - 1))) n))
    {n k m : ℕ} [NeZero n] {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
    (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm12 : 12 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < _root_.gs_johnson k n m)
    (hmle : (m : ℝ) ≤
      max (⌈((((k : ℝ) / n + 1 / n)) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3)
    {εstar : ℝ≥0∞}
    (hbudget : ENNReal.ofReal (johnsonBoundReal domain k η δ) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F₀) (A := F₀)
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) εstar := by
  have hjnb := johnsonDischargeStatement_of_packageSupply hsupply n k m ‹_› F₀ ‹_› ‹_›
    ‹_› domain η δ hk2 hkn hm12 hδ1 hδJ hmle
  exact le_mcaDeltaStar_of_good (F := F₀) (A := F₀)
    ((ReedSolomon.code domain k : Set (Fin n → F₀))) εstar hδ1
    (le_trans hjnb hbudget)

end ProximityGap.ProductionRegime

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.ProductionRegime.production_good_ladder
#print axioms ProximityGap.ProductionRegime.production_good_ladder_reach
#print axioms ProximityGap.ProductionRegime.production_good_johnson_of_packageSupply
