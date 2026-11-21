/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitConverse
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorOneHole
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitPencil

/-! # Exact failure criterion at 447392428 quarter-rate errors -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitCriterion

open Polynomial Finset Code _root_.ProximityGap HalfPredecessorBadEventRichPointBridge
open HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorRateQuarterDeterminantCollapse
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

open scoped Classical in
/-- The zero, pole and unit fibers of a rational function, each with the full
prescribed number of distinct coordinates of the supplied domain. -/
def splitPencil (dom : I ↪ F) : Prop :=
  ∃ P Q : F[X], P.natDegree ≤ 268435454 ∧ Q.natDegree ≤ 268435454 ∧
    (univ.filter fun i => P.eval (dom i) = 0).card = 268435454 ∧
    (univ.filter fun i => Q.eval (dom i) = 0).card = 268435454 ∧
    (univ.filter fun i => P.eval (dom i) = Q.eval (dom i)).card = 268435454 ∧
    ∀ i, P.eval (dom i) = 0 → Q.eval (dom i) ≠ 0

/-- Without a split pencil every genuine received pair meets the budget of `2³⁰`
at the first integer above the exact two-head population. -/
theorem safe_of_no_pencil {p : ℕ} [CharP F p] (hp : 132 < p) (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (no : ¬splitPencil dom) :
    epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) (447392428 / 1073741824) ≤
      (1073741824 : ℝ≥0∞) / Fintype.card F := by
  classical
  apply epsMCA_le_of_badCount_le _ _ 1073741824
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (447392428 / 1073741824) u
    (by decide : 1 ≤ 268435456)
  change fam.G.card ≤ 1073741824
  by_contra! big
  have ht : ⌈(1 - (447392428 / 1073741824 : ℝ≥0)) * (Fintype.card I : ℝ≥0)⌉₊ = 626349396 := by
    rw [hn]
    change ⌈(1 - ((447392428 : ℕ) : ℝ≥0) / ((1073741824 : ℕ) : ℝ≥0)) *
      ((1073741824 : ℕ) : ℝ≥0)⌉₊ = 626349396
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num), ← Nat.cast_tsub, Nat.ceil_natCast]
  obtain ⟨a,b,c,ab,ac,bc,valid,det,dir,_,_,_,empty,_,_,_,pairs⟩ :=
    QuarterSuccessorOneHole.one_hole hp fam hn ht big
  apply no
  apply QuarterSuccessorSplitConverse.split_of_saturated_cores dom (u 0) (u 1) a b c ab ac bc
    (by simpa only [threeLineDeterminant, lineDeterminant, mul_comm] using det) _ dir
  · exact ⟨pairs.1,pairs.2.1,pairs.2.2,empty⟩
  · intro h hh
    obtain ⟨h₁,h₂⟩ := lineParameter_degree_lt fam (valid h hh).1
    exact ⟨by omega,by omega⟩

/-- On fields large enough for the construction, an overflow occurs exactly when
a split pencil exists. Every overflow has the same worst-case mass `(2³⁰+2)/q`. -/
theorem failure_iff {p : ℕ} [CharP F p] (hp : 132 < p) (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (hq : 1073741826 ^ 2 < Fintype.card F)
    (width : ℕ) [NeZero width] :
    let mass := epsMCA (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      (447392428 / 1073741824)
    ((1073741824 : ℝ≥0∞) / Fintype.card F < mass ↔ splitPencil dom) ∧
      (splitPencil dom → mass = (1073741826 : ℝ≥0∞) / Fintype.card F) := by
  classical
  dsimp only
  rw [epsMCA_interleaved_eq]
  have big (hs : splitPencil dom) : (1073741826 : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) (447392428 / 1073741824) := by
    obtain ⟨P,Q,dp,dq,zp,zq,ze,dis⟩ := hs
    exact QuarterSuccessorSplitPencil.mass_of_split_polynomials dom hn hq P Q dp dq zp zq ze dis
  constructor
  · constructor
    · intro hm
      by_contra no
      exact hm.not_ge (safe_of_no_pencil hp dom hn no)
    · intro hs
      apply lt_of_lt_of_le _ (big hs)
      apply (ENNReal.div_lt_div_iff_left _ _).2 (by norm_num)
      · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F).ne'
      · exact ENNReal.natCast_ne_top _
  · intro hs
    exact le_antisymm (QuarterSuccessorOneHole.mass_bounds hp dom hn).2 (big hs)

end ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitCriterion
