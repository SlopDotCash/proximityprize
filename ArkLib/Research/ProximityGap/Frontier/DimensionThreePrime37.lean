/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionThreeInvolution

/-! # Changing one evaluation site changes the exact dimension-three mass -/

namespace ProximityGap.DimensionThreePrime37
open Finset DimensionThreeInvolution DimensionThreePairCriterion MCAThresholdLedger
open scoped NNReal ENNReal

private abbrev F := ZMod 37
private abbrev I := Fin 12
private instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- The twelve consecutive residues in the field of order 37. -/
def consecutive : I ↪ F := ⟨fun i => (i.val:F),by decide⟩

/-- Replace the final residue 11 by 12. -/
def replaced : I ↪ F := ⟨fun i => if i.val=11 then 12 else (i.val:F),by decide⟩

private def test (a b c : F) : Bool :=
  (List.finRange 12).all fun i => (List.finRange 12).any fun j =>
    decide (i≠j ∧ a*replaced i*replaced j+b*(replaced i+replaced j)+c=0)

private theorem test_iff {a b c : F} : test a b c=true ↔
    ∀ i, ∃ j, i≠j ∧ a*replaced i*replaced j+b*(replaced i+replaced j)+c=0 := by
  simp [test]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem check : (List.finRange 37).all (fun x =>
    !test 0 1 (x.val:F) && (List.finRange 37).all fun y =>
      decide ((y.val:F)=(x.val:F)^2) || !test 1 (x.val:F) (y.val:F))=true := by decide

private theorem no_reflection : ¬Reflects replaced := by
  rintro ⟨a,b,c,nonsing,partners⟩
  have all := check
  simp only [List.all_eq_true,List.mem_finRange,forall_const,Bool.and_eq_true,Bool.not_eq_true',
    Bool.or_eq_true,decide_eq_true_eq] at all
  have row (x : F) : test 0 1 x=false ∧ ∀ y : F, y=x^2 ∨ test 1 x y=false := by
    let i : Fin 37 := ⟨x.val,x.val_lt⟩
    have hi := all i
    refine ⟨by simpa [i] using hi.1,?_⟩
    intro y
    let j : Fin 37 := ⟨y.val,y.val_lt⟩
    simpa [i,j] using hi.2 j
  by_cases ha : a=0
  · have hb : b≠0 := by intro eq;simp [ha,eq] at nonsing
    have ht : test 0 1 (c/b)=true := test_iff.mpr (by
      intro i
      obtain ⟨j,ij,eq⟩ := partners i
      refine ⟨j,ij,?_⟩
      rw [ha] at eq
      field_simp [hb]
      linear_combination eq)
    rw [(row _).1] at ht
    contradiction
  · have good : c/a ≠ (b/a)^2 := by
      intro equal
      apply nonsing
      field_simp [ha] at equal
      linear_combination equal
    have ht : test 1 (b/a) (c/a)=true := test_iff.mpr (by
      intro i
      obtain ⟨j,ij,eq⟩ := partners i
      refine ⟨j,ij,?_⟩
      field_simp [ha]
      linear_combination eq)
    rw [((row (b/a)).2 (c/a)).resolve_left good] at ht
    contradiction

private theorem symmetric : Reflects consecutive := by
  refine ⟨0,1,-11,by norm_num,?_⟩
  decide

/-- The same prime, dimension and length give the two distinct endpoint
numerators. Only the final evaluation site changes. -/
theorem masses :
    epsMCA (F:=F) (ReedSolomon.code consecutive 3 : Set (I → F)) ((4:ℝ≥0)/12)=6/37 ∧
    epsMCA (F:=F) (ReedSolomon.code replaced 3 : Set (I → F)) ((4:ℝ≥0)/12)=5/37 := by
  classical
  have mass₁ := DimensionThreePairCriterion.mass (h:=5) consecutive (by decide) (by decide) (by decide)
  have mass₂ := DimensionThreePairCriterion.mass (h:=5) replaced (by decide) (by decide) (by decide)
  rw [ite_eq_left (DimensionThreeInvolution.sufficient consecutive (by decide : Fintype.card I=2*5+2) symmetric)] at mass₁
  rw [ite_eq_right (fun h => no_reflection (DimensionThreeInvolution.necessary replaced
    (by decide : Fintype.card I=2*5+2) (by decide) h))] at mass₂
  simpa only [ZMod.card,Nat.reduceSub,Nat.reduceAdd,Nat.cast_ofNat] using And.intro mass₁ mass₂

/-- Replacing 11 by 12 moves the first failing count from four errors to five
at tolerance 1/7, simultaneously at every positive interleaving width. -/
theorem thresholds (width : ℕ) [NeZero width] :
    ∀ δ : ℝ≥0,
      (epsMCA (F:=F) ((ReedSolomon.code consecutive 3 : Set (I → F)) ^⋈ (Fin width)) δ ≤ 1/7 ↔
        δ<4/12) ∧
      (epsMCA (F:=F) ((ReedSolomon.code replaced 3 : Set (I → F)) ^⋈ (Fin width)) δ ≤ 1/7 ↔
        δ<5/12) := by
  intro δ
  have eq₁ := (DimensionThreeInvolution.classification (Q:=7) (h:=5) consecutive (by decide)
    (by decide) (by decide) (by decide) (by rw [ZMod.card]) width).2 δ
  have eq₂ := (DimensionThreeInvolution.classification (Q:=7) (h:=5) replaced (by decide)
    (by decide) (by decide) (by decide) (by rw [ZMod.card]) width).2 δ
  simpa only [ite_eq_left symmetric,ite_eq_right no_reflection,Nat.reduceSub,Nat.cast_ofNat]
    using And.intro eq₁ eq₂

end ProximityGap.DimensionThreePrime37
#print axioms ProximityGap.DimensionThreePrime37.masses
#print axioms ProximityGap.DimensionThreePrime37.thresholds
