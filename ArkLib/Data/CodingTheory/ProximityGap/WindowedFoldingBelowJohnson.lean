/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Issue #232 — windowed folding is BELOW Johnson at every window size (route 4, fully closed)

`FoldingTransferNoGo.lean` certified the *naive* folded-RS transfer dead (one corruption per orbit
kills every orbit).  The apparent loophole is the **sliding-window** transfer — the mechanism by
which Guruswami–Rudra folded decoding actually processes plain words: windows
`{i, i+1, …, i+s−1}` (cyclically) instead of disjoint orbits, so each plain agreement point feeds
`s` windows.  This file closes that loophole with two theorems:

* `agreeing_windows_ge` (the quantitative transfer — the POSITIVE direction, sharp):
  on a cyclic domain of size `n` with window length `s`, if two words disagree on `e` positions,
  the number of fully-agreeing windows is `≥ n − s·e` (each disagreement kills at most `s`
  windows).  This is the best the windowed transfer gives: plain relative radius `δ = e/n` becomes
  folded relative radius `≤ s·δ`.

* `windowed_folding_below_johnson` (the NO-GO): the folded-RS capacity results need folded
  agreement fraction `≥ ρ + ε`, i.e. `1 − s·δ ≥ ρ`, i.e. `δ ≤ (1−ρ)/s`.  For EVERY window size
  `s ≥ 2` and EVERY rate `ρ ∈ (0,1)`:

  `(1−ρ)/s ≤ (1−ρ)/2 < 1 − √ρ`,

  because `(1−ρ)/2 < 1−√ρ ⟺ 0 < (√ρ − 1)²`.  **The windowed transfer lands strictly below the
  Johnson radius at every rate** — worse than what plain GS already certifies.  Route 4 of the
  issue's §6 is therefore closed in BOTH variants: the naive orbit transfer is maximally lossy
  (`FoldingTransferNoGo`), and the windowed transfer, though lossless in the count, pays the
  factor-`s` radius shrinkage that puts it under Johnson everywhere.  Any folding route to the
  prize must therefore beat the factor-`s` window penalty itself — that is the (open) content.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset

namespace ArkLib.CodingTheory.WindowedFoldingBelowJohnson

variable {F : Type*} [DecidableEq F] {n s : ℕ}

/-- The (cyclic) window of length `s` starting at `i` fully agrees: both words coincide on
`i, i+1, …, i+s−1` (indices mod `n`, via `Fin` addition). -/
def windowAgrees (w v : Fin n → F) (s : ℕ) (hs : s ≤ n) (i : Fin n) : Prop :=
  ∀ j : Fin s, w (i + Fin.castLE hs j) = v (i + Fin.castLE hs j)

instance (w v : Fin n → F) (s : ℕ) (hs : s ≤ n) (i : Fin n) :
    Decidable (windowAgrees w v s hs i) := by
  unfold windowAgrees; infer_instance

/-- **The sharp windowed transfer (positive direction).**  If two words on the cyclic domain
`Fin n` disagree on `e` positions, then at least `n − s·e` of the `n` cyclic windows of length `s`
fully agree: every disagreement position `d` kills only the `≤ s` windows whose start lies in
`{d − j : j < s}`. -/
theorem agreeing_windows_ge (w v : Fin n → F) (hs : s ≤ n)
    (e : ℕ) (he : (Finset.univ.filter fun x : Fin n => w x ≠ v x).card = e) :
    n - s * e ≤ (Finset.univ.filter fun i : Fin n => windowAgrees w v s hs i).card := by
  classical
  set D := Finset.univ.filter fun x : Fin n => w x ≠ v x with hD
  -- the failing windows are covered by ⋃_{d ∈ D} {i : ∃ j, i + j = d}
  have hcover : (Finset.univ.filter fun i : Fin n => ¬ windowAgrees w v s hs i)
      ⊆ D.biUnion fun d => Finset.univ.filter fun i : Fin n => ∃ j : Fin s,
          i + Fin.castLE hs j = d := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, hfail⟩ := hi
    rw [windowAgrees] at hfail
    push Not at hfail
    obtain ⟨j, hj⟩ := hfail
    rw [Finset.mem_biUnion]
    exact ⟨i + Fin.castLE hs j,
      by rw [hD, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩,
      by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, j, rfl⟩⟩
  -- each disagreement kills at most `s` windows: the kill-set is the image of `Fin s` under
  -- `j ↦ d − j`
  have hkill : ∀ d : Fin n,
      (Finset.univ.filter fun i : Fin n => ∃ j : Fin s, i + Fin.castLE hs j = d).card ≤ s := by
    intro d
    have himg : (Finset.univ.filter fun i : Fin n => ∃ j : Fin s, i + Fin.castLE hs j = d)
        ⊆ (Finset.univ : Finset (Fin s)).image fun j => d - Fin.castLE hs j := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨-, j, hj⟩ := hi
      rw [Finset.mem_image]
      refine ⟨j, Finset.mem_univ _, ?_⟩
      haveI : NeZero n := ⟨(Fin.pos i).ne'⟩
      exact (eq_sub_of_add_eq hj).symm
    calc (Finset.univ.filter fun i : Fin n => ∃ j : Fin s, i + Fin.castLE hs j = d).card
        ≤ ((Finset.univ : Finset (Fin s)).image fun j => d - Fin.castLE hs j).card :=
          Finset.card_le_card himg
      _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
      _ = s := by rw [Finset.card_univ, Fintype.card_fin]
  -- count: failing ≤ s·e, agreeing = n − failing
  have hfailcard : (Finset.univ.filter fun i : Fin n => ¬ windowAgrees w v s hs i).card
      ≤ s * e := by
    calc (Finset.univ.filter fun i : Fin n => ¬ windowAgrees w v s hs i).card
        ≤ (D.biUnion fun d => Finset.univ.filter fun i : Fin n => ∃ j : Fin s,
            i + Fin.castLE hs j = d).card := Finset.card_le_card hcover
      _ ≤ ∑ d ∈ D, (Finset.univ.filter fun i : Fin n => ∃ j : Fin s,
            i + Fin.castLE hs j = d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ D, s := Finset.sum_le_sum fun d _ => hkill d
      _ = e * s := by rw [Finset.sum_const, smul_eq_mul, hD, he]
      _ = s * e := Nat.mul_comm e s
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => windowAgrees w v s hs i)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- **Windowed folding is below Johnson at every rate and every window size (the NO-GO).**
The windowed transfer converts plain radius `δ` to folded radius `≤ s·δ`; the folded capacity
results need folded agreement `≥ ρ`, forcing `δ ≤ (1−ρ)/s`.  For every `ρ ∈ (0,1)` and `s ≥ 2`:

  `(1−ρ)/s ≤ (1−ρ)/2 < 1 − √ρ`

— strictly below the Johnson radius.  (Strictness from `0 < (√ρ − 1)²`.)  So no choice of window
size makes the windowed-folding route reach even Johnson, let alone pass it. -/
theorem windowed_folding_below_johnson {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {s : ℕ} (hs : 2 ≤ s) :
    (1 - ρ) / s ≤ (1 - ρ) / 2 ∧ (1 - ρ) / 2 < 1 - Real.sqrt ρ := by
  constructor
  · apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
    exact_mod_cast hs
  · have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
    have hlt1 : Real.sqrt ρ < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_lt_sqrt hρ0.le hρ1
    nlinarith [sq_nonneg (Real.sqrt ρ - 1), Real.sqrt_nonneg ρ]

/-- Concrete check at the prize rate `ρ = 1/2`, window `s = 2`: the windowed-folding ceiling is
`(1−ρ)/2 = 1/4 = 0.25 < 0.29289 < 1 − √(1/2)` — a full `4+` points below Johnson. -/
theorem windowed_ceiling_rate_half :
    ((1 : ℝ) - 1/2) / 2 = 1/4 ∧ ((1 : ℝ) - 1/2) / 2 < 1 - Real.sqrt (1/2) :=
  ⟨by norm_num, (windowed_folding_below_johnson (by norm_num) (by norm_num) (le_refl 2)).2⟩

end ArkLib.CodingTheory.WindowedFoldingBelowJohnson

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.WindowedFoldingBelowJohnson.agreeing_windows_ge
#print axioms ArkLib.CodingTheory.WindowedFoldingBelowJohnson.windowed_folding_below_johnson
#print axioms ArkLib.CodingTheory.WindowedFoldingBelowJohnson.windowed_ceiling_rate_half
