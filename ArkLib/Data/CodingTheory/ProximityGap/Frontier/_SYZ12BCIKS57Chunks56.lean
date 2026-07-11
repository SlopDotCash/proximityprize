/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ11BCIKS57Chunk3
import ArkLib.ToMathlib.DiscriminantBadSet

/-!
# SYZ12 — BCIKS20 Claim 5.7 program, Chunks C5 (matching-fold) and C6 (heavy-pin)

This file continues the multi-chunk program (SYZ10/SYZ11) discharging the strictly-smaller
Johnson-lane residual `CellPackageSupplyDiscLocus`
(`Frontier/_SYZ8CellPackageSupply.lean`).  SYZ11 partitioned the `DiscLocusCellData` fields
into five chunk-output interfaces and machine-checked the composition; C3 (the §5 weighted
grading) was the last chunk with a *proved* derivation.  This file resolves the two remaining
downstream chunks, both taken **after** a `DiscBudgetSupply` (i.e. a nonzero discriminant with
base/separability certificates and the degree budget already exists):

* **C6 `HeavyPinSupply` — DISCHARGED (given one named budget inequality).**
  `heavyPinSupply_of_discBudget`.  The heavy set `S₀` is the discriminant non-vanishing locus
  itself, so `hS₀sub` is definitional; the `X`-degree ceiling `Bw` for the Taylor coefficients
  of the `Y`-root divisor `w` is built canonically (the support-sup), so `hBw` is definitional;
  and the pigeonhole `max Bw 1 < |S₀|` is `card_nonvanishing_gt`.  The *entire* C6 content is
  thereby reduced to the single honest counting hypothesis
  `max Bw 1 + natDegree disc < |F₀|` — no branch mathematics remains in C6.

* **C5 `MatchingFoldSupply` — GENUINE CORE ISOLATED (ξ-weight obligation discharged).**
  The fold agreement `hfold` (each matching point folds linearly through `w`) is the genuine
  BCIKS §6 α-series matching, so the matching data `e, u₀, u₁, matchingSet, hmatchSub, hfold`
  and the count `hcard` cannot be produced from the disc budget alone — they are collected in
  the minimal named Prop `FoldMatchingCore`.  Around that core,
  `matchingFoldSupply_of_foldMatchingCore` **discharges the ξ-weight field** `xw, hξw`: the
  canonical `xw` is the value of the ξ-weight itself (`unbot' 0`), and `hξw` holds by a
  `WithBot` case split.  So the C5 producer no longer has to exhibit a ξ-weight witness; only
  the α-series fold-matching data and its count remain.

Together with SYZ11 this leaves the genuine open mathematics of the Claim 5.7 per-cell package
exactly as: **C2** (place-curve / Hensel branch data) and the **C4** discriminant nonvanishing
half, plus the **C5** fold-matching core `FoldMatchingCore` and two honest counting budget
inequalities (the C6 heavy budget and the C5 fold count).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal ENNReal
open ArkLib

namespace BCIKS20.CellPencilJohnson.SYZ12

open BCIKS20.CellPencilJohnson.SYZ11

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable {n : ℕ} [NeZero n]

/-! ## C6 — the heavy-pin supply, discharged from the disc budget -/

/-- The canonical `X`-degree ceiling for the Taylor coefficients of the `Y`-root divisor `w`
of a `GradedYRootSupply`: the support-sup of the per-coefficient `natDegree`.  With this
choice the `HeavyPinSupply.hBw` field is definitional. -/
noncomputable def taylorWCeil
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H) : ℕ :=
  (Polynomial.taylor (Polynomial.C g.x₀) g.w).support.sup
    (fun t => ((Polynomial.taylor (Polynomial.C g.x₀) g.w).coeff t).natDegree)

/-- **Chunk 6 (discharged).**  Given a `DiscBudgetSupply` (a nonzero discriminant with its
certificates and the degree budget already in hand) and the single honest counting hypothesis
`max (taylorWCeil g) 1 + natDegree disc < |F₀|`, produce the entire `HeavyPinSupply`.

The heavy set `S₀` is the discriminant non-vanishing locus, so membership in the locus
(`hS₀sub`) is by `Finset.mem_filter`; the ceiling `Bw := taylorWCeil g` makes `hBw`
definitional (support-sup, off-support coefficients vanish); and the pigeonhole
`max Bw 1 < |S₀|` is exactly `card_nonvanishing_gt`.  No branch mathematics is used: the whole
of C6 is this one pigeonhole over the locus. -/
noncomputable def heavyPinSupply_of_discBudget
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H g)
    (hHeavyBudget :
      max (taylorWCeil g) 1 + db.disc.natDegree < Fintype.card F₀) :
    HeavyPinSupply domain k δ u R H g db where
  S₀ := Finset.univ.filter (fun z : F₀ => db.disc.eval z ≠ 0)
  hS₀sub := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  Bw := taylorWCeil g
  hBw := by
    intro t
    by_cases ht : t ∈ (Polynomial.taylor (Polynomial.C g.x₀) g.w).support
    · exact Finset.le_sup
        (f := fun t => ((Polynomial.taylor (Polynomial.C g.x₀) g.w).coeff t).natDegree) ht
    · rw [Polynomial.mem_support_iff, not_not] at ht
      simp [ht]
  hS₀ := ArkLib.Match304.card_nonvanishing_gt db.hdisc hHeavyBudget

/-! ## C5 — the genuine fold-matching core, and the ξ-weight discharge around it -/

/-- The canonical ξ-weight ceiling: the value of `weight_Λ_over_𝒪 … (ξ …) D` itself
(`unbot' 0`).  Used to discharge the `MatchingFoldSupply.hξw` field around the genuine core. -/
noncomputable def xiWeightCeil
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H) : ℕ :=
  (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree)) (ξ g.x₀ R H g.hHyp) g.D).unbotD 0

/-- **The genuine BCIKS §6 fold-matching core (C5).**  This is the minimal named Prop carrying
the α-series heavy-agreement matching data that the disc budget cannot supply: injective
evaluation points `e`, the linear-fold values `u₀, u₁`, the per-coordinate matching sets sitting
in the disc non-vanishing locus (`hmatchSub`) folding linearly through the `Y`-root divisor `w`
(`hfold`), and the `killBudget` count `hcard` — stated at the **canonical** ξ-weight
`xiWeightCeil g`.  The fold agreement `hfold` is the genuine open mathematics; everything else
in `MatchingFoldSupply` is built around this core. -/
structure FoldMatchingCore
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H g) : Type where
  e : Fin n → F₀
  he : Function.Injective e
  u₀ : Fin n → F₀
  u₁ : Fin n → F₀
  matchingSet : Fin n → Finset F₀
  hmatchSub : ∀ j, ∀ z ∈ matchingSet j, db.disc.eval z ≠ 0
  hfold : ∀ j, ∀ z ∈ matchingSet j,
    (g.w.eval (Polynomial.C (e j) + Polynomial.C g.x₀)).eval z = u₀ j + z * u₁ j
  hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n g.D H.natDegree
      (Bivariate.natDegreeY R) (xiWeightCeil g) * H.natDegree < (matchingSet j).card

/-- **Chunk 5 (genuine core + ξ-weight discharge).**  From a `FoldMatchingCore` produce a full
`MatchingFoldSupply`: the fold-matching data passes through unchanged, and the ξ-weight field
`xw, hξw` is **discharged** by taking `xw := xiWeightCeil g` (the ξ-weight's own value) and
proving `hξw` by a `WithBot` case split (`⊥ ≤ _` by `bot_le`; `some m ≤ some m` by reflexivity).
No new §6 mathematics is claimed — only the ξ-weight bookkeeping obligation is removed. -/
noncomputable def matchingFoldSupply_of_foldMatchingCore
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {g : GradedYRootSupply domain k δ u R H}
    {db : DiscBudgetSupply domain k δ u R H g}
    (c : FoldMatchingCore domain k δ u R H g db) :
    MatchingFoldSupply domain k δ u R H g db where
  e := c.e
  he := c.he
  u₀ := c.u₀
  u₁ := c.u₁
  matchingSet := c.matchingSet
  hmatchSub := c.hmatchSub
  hfold := c.hfold
  xw := xiWeightCeil g
  hξw := by
    unfold xiWeightCeil
    cases h : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree)) (ξ g.x₀ R H g.hHyp) g.D with
    | bot => exact bot_le
    | coe m => simp [WithBot.unbotD_coe]
  hcard := c.hcard

/-! ## The reduced per-cell assembly off the two discharged chunks -/

/-- **The per-cell assembly off the reduced surface.**  Combines the SYZ11 C3 grading
derivation with the C5 fold-matching core and the C6 heavy-pin discharge: from a
`PlaceCurveSupply`, a `DiscBudgetSupply`, a `FoldMatchingCore`, and the single C6 heavy-budget
inequality, produce the entire `DiscLocusCellData`.  Compared with SYZ11's
`discLocusCellData_of_placeCurve`, the C6 input structure is gone (fully discharged) and the C5
input is narrowed from `MatchingFoldSupply` to its genuine `FoldMatchingCore`. -/
noncomputable def discLocusCellData_of_core
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (p : PlaceCurveSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H (gradedYRootSupply_of_placeCurve p))
    (c : FoldMatchingCore domain k δ u R H (gradedYRootSupply_of_placeCurve p) db)
    (hHeavyBudget :
      max (taylorWCeil (gradedYRootSupply_of_placeCurve p)) 1 + db.disc.natDegree
        < Fintype.card F₀) :
    DiscLocusCellData domain k δ u R H :=
  discLocusCellData_of_supplies (gradedYRootSupply_of_placeCurve p) db
    (matchingFoldSupply_of_foldMatchingCore c)
    (heavyPinSupply_of_discBudget (gradedYRootSupply_of_placeCurve p) db hHeavyBudget)

end BCIKS20.CellPencilJohnson.SYZ12

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ12.heavyPinSupply_of_discBudget
#print axioms BCIKS20.CellPencilJohnson.SYZ12.matchingFoldSupply_of_foldMatchingCore
#print axioms BCIKS20.CellPencilJohnson.SYZ12.discLocusCellData_of_core
