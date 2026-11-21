/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FullFiberMcaLift
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26

/-! # One additional bad scalar at odd half-distance on every smooth domain

For odd redundancy 2h−1 and odd h, squaring pairs the sites of the
smooth coset. The two-head construction on the quotient lifts to the
upstairs dimension, one less than twice the downstairs dimension.
-/
set_option autoImplicit false
namespace ProximityGap.OddRedundancySquareLift
open Finset Polynomial MCAThresholdLedger
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]

/-- At h−1 errors the h+1 labels from the quotient all remain bad on the
original smooth domain. The number h is half the redundancy rounded up. -/
theorem mass (D : I ↪ F) [ReedSolomon.Smooth D] {n k h : ℕ} (sites : Fintype.card I=n)
    (even : n%2=0) (hk : 3≤k) (large : 3≤h) (length : n=k+2*h-1) (odd : h%2=1) :
    ((h+1:ℕ):ℝ≥0∞)/(Fintype.card F) ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  classical
  let m := n/2
  let b := (k+1)/2
  let e := (h-1)/2
  have split : Fintype.card I=2*m := by dsimp [m];omega
  obtain ⟨V,hcard,hmem,hfib,-⟩ := CodingTheory.AdditiveSetListDecoding.Smooth.exists_pow_projection_structure D split
  let E := Function.Embedding.subtype (· ∈ V)
  let π (i : I) : V := ⟨D i ^ 2,hmem i⟩
  have fibers (v : V) : (univ.filter (fun i => π i=v)).card=2 := by
    rw [show univ.filter (fun i => π i=v) = univ.filter (fun i => D i^2=(v:F)) by
      ext i; simp [π,Subtype.ext_iff]]
    exact hfib v v.property
  have hv : Fintype.card V=m := (Fintype.card_coe V).trans hcard
  have mp : 0 < m := by dsimp [m];omega
  let : Nonempty V := Fintype.card_pos_iff.mp (hv.symm ▸ mp)
  have size : Fintype.card V=b+2*e := by dsimp only [m,e,b] at *;omega
  have base := TwoHeadLinearBudget.errors (k:=b) (e:=e) E
    (by dsimp only [b] at *;omega) (by omega) (by dsimp only [e] at *;omega)
  have lift := FullFiberMcaLift.epsMCA_le_band (k:=b) (m:=2) (K:=k) D E π (Polynomial.X ^ 2)
    (by decide) (by dsimp [b];omega) (by dsimp [b];omega) (by dsimp [b];omega)
    (by simp) (fun i => by simp [E,π]) fibers ((e:ℝ≥0)/(Fintype.card V))
  have n2 : n=2*m := sites ▸ split
  have e2 : h-1=2*e := by dsimp [e];omega
  have rad : ((h-1:ℕ):ℝ≥0)/n=(e:ℝ≥0)/(Fintype.card V) := by
    rw [hv,e2,n2,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_div_mul_left _ _ (by norm_num : (2:ℝ≥0)≠0)
  rw [rad,show h+1=2*(e+1) by omega]
  exact base.trans lift

end ProximityGap.OddRedundancySquareLift
#print axioms ProximityGap.OddRedundancySquareLift.mass
