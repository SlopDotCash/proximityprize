/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorQuadraticObstruction
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-! # A successor interpolation obstruction with many genuine MCA bad scalars

The three received blocks follow the polynomial heads zero, coordinate minus scalar,
and twice coordinate minus scalar. On every tail coordinate, the corresponding
scalar makes the zero head agree there as well as on the first block.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorMovingObstruction

open Polynomial Finset QuarterSuccessorQuadraticObstruction SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal

variable {F : Type} [Field F]

/-- The coefficient of the coordinate-minus-scalar head on each of the three blocks. -/
def scale (i : Fin 1073741824) : F :=
  if i.val < 626349396 then 0 else if i.val < 984263337 then 1 else 2

/-- The intercept of the moving three-head pair. -/
def intercept (D : Fin 1073741824 ↪ F) (i : Fin 1073741824) : F := scale i * D i

/-- The slope of the moving three-head pair. -/
def slope (i : Fin 1073741824) : F := -scale i

private theorem fold (D : Fin 1073741824 ↪ F) (i : Fin 1073741824) :
    C (intercept D i) + X * C (slope i) = C (scale i) * (C (D i) - X) := by
  simp only [intercept, slope, map_mul, map_neg]
  ring

/-- Even on these moving rows, the campaign's entire successor quadratic kernel vanishes
for every scalar degree cap. -/
theorem simple_kernel {s : ℕ} (D : Fin 1073741824 ↪ F) (htwo : (2 : F) ≠ 0)
    (c : Monomials s 2 268435455 626349396 → F)
    (hall : ∀ i, receivedLine c (D i) (intercept D i) (slope i) = 0) : c = 0 := by
  apply kernel_of_coordinate_test D _ _ _ c hall
  intro A B T hAdeg hBdeg hTdeg hall
  let E := D.trans (⟨C, C_injective⟩ : F ↪ F[X])
  let L : F[X][X] := X - C X
  let ell (i : Fin 1073741824) : F[X] := C (D i) - X
  have hL (i) : L.eval (E i) = ell i := by simp [L, E, ell]
  have hell (i) : ell i ≠ 0 := sub_ne_zero.mpr ((X_ne_C (D i)).symm)
  have hfit (i : Fin 1073741824) :
      A.eval (E i) + B.eval (E i) * (C (scale i) * ell i) +
        T.eval (E i) * (C (scale i) * ell i) ^ 2 = 0 := by
    have h := hall i
    dsimp only at h
    rw [fold] at h
    exact h
  have hA : A = 0 := by
    apply zero_on_block E 0 626349396 (by decide) A hAdeg
    intro i _ hi
    simpa [scale, hi] using hfit i
  subst A
  have hBT : B + T * L = 0 := by
    apply zero_on_block E 626349396 357913941 (by decide) (B + T * L)
    · have h := natDegree_mul_le (p := T) (q := L)
      have hLdeg : L.natDegree = 1 := natDegree_X_sub_C _
      exact lt_of_le_of_lt (natDegree_add_le ..) (max_lt (by omega) (by omega))
    · intro i hi hj
      have hr := hfit i
      simp only [eval_zero, zero_add, scale, ite_eq_right (by omega : ¬ i.val < 626349396),
        ite_eq_left (by omega : i.val < 984263337), map_one, one_mul] at hr
      rw [eval_add, eval_mul, hL]
      apply (mul_eq_zero.mp (show (B.eval (E i) + T.eval (E i) * ell i) * ell i = 0 by
        linear_combination hr)).resolve_right (hell i)
  have h2 : (2 : F[X]) ≠ 0 := by
    intro h
    have hh := congrArg (fun p : F[X] => p.eval 0) h
    exact htwo (by simpa using hh)
  have hT : T = 0 := by
    apply zero_on_block E 984263337 89478486 (by decide) T (by omega)
    intro i hi _
    have hr := hfit i
    simp only [eval_zero, zero_add, scale, ite_eq_right (by omega : ¬ i.val < 626349396),
      ite_eq_right (by omega : ¬ i.val < 984263337), map_ofNat] at hr
    have hs := congrArg (fun P : F[X][X] => P.eval (E i)) hBT
    rw [eval_add, eval_mul, hL, eval_zero] at hs
    have h : T.eval (E i) * (2 * ell i * ell i) = 0 := by
      linear_combination hr - 2 * ell i * hs
    exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero (mul_ne_zero h2 (hell i)) (hell i))
  exact ⟨rfl, by simpa only [hT, zero_mul, add_zero] using hBT, hT⟩

/-- Every coordinate outside the zero block supplies its own genuine bad scalar
already at the predecessor, on exactly the pair with trivial successor kernel. -/
theorem tail_bad (D : Fin 1073741824 ↪ F) (htwo : (2 : F) ≠ 0)
    (i : Fin 1073741824) (hi : 626349396 ≤ i.val) :
    _root_.ProximityGap.mcaEvent (F := F) (ReedSolomon.code D 268435456 : Set (_ → F))
      (447392427 / 1073741824) (intercept D) slope (D i) := by
  classical
  let j : Fin 626349396 ↪ Fin 1073741824 := Fin.castLEEmb (by decide)
  let T := univ.map j
  have hT : T.card = 626349396 := by simp [T]
  have memT (l : Fin 1073741824) (hl : l ∈ T) : l.val < 626349396 := by
    obtain ⟨t, _, rfl⟩ := mem_map.mp hl
    exact t.isLt
  have hiT : i ∉ T := fun h => (memT _ h).not_ge hi
  have hscale (l : Fin 1073741824) (hl : l ∈ T) : (scale l : F) = 0 := by
    simp [scale, memT _ hl]
  have hsi : (scale i : F) ≠ 0 := by
    rw [scale, ite_eq_right (by omega : ¬ i.val < 626349396)]
    split <;> simp_all
  refine ⟨insert i T, ?_, ⟨0, (ReedSolomon.code D 268435456).zero_mem, ?_⟩, ?_⟩
  · rw [Fintype.card_fin, card_insert_of_notMem hiT, hT]
    change (1 - 447392427 / 1073741824 : ℝ≥0) * 1073741824 ≤ 626349397
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num : (1073741824 : ℝ≥0) ≠ 0)]
    exact ((tsub_eq_iff_eq_add_of_le (by norm_num)).mpr (by norm_num)).le
  · intro l hl
    change 0 = scale l * D l + D i * -scale l
    rcases mem_insert.mp hl with rfl | h
    · ring
    · simp [hscale _ h]
  · rintro ⟨_, _, v, hv, hit⟩
    have eq : v = 0 := ReedSolomon.eq_of_agree_of_card_le hv
      (ReedSolomon.code D 268435456).zero_mem (by rw [hT]; decide) fun l hl => by
        simpa [slope, hscale _ hl] using (hit l (mem_insert_of_mem hl)).2
    have h := (hit i (mem_insert_self i T)).2
    simp [eq, slope, hsi] at h

/-- There are at least 447392428 different predecessor bad scalars on this particular
interpolation obstruction, for every injective domain over a finite odd field. -/
theorem bad_count [Fintype F] (D : Fin 1073741824 ↪ F) (htwo : (2 : F) ≠ 0) :
    447392428 ≤ (badScalars D 268435456 (447392427 / 1073741824) ![intercept D, slope]).card := by
  classical
  let tail : Fin 447392428 ↪ Fin 1073741824 :=
    ⟨fun t => ⟨626349396 + t.val, by omega⟩, fun a b h => Fin.ext (by
      have hh := congrArg Fin.val h
      change 626349396 + a.val = 626349396 + b.val at hh
      omega)⟩
  have hsub : univ.map (tail.trans D) ⊆
      badScalars D 268435456 (447392427 / 1073741824) ![intercept D, slope] := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := mem_map.mp hz
    apply (mem_badScalars_iff ..).mpr
    exact tail_bad D htwo (tail i) (by change 626349396 ≤ 626349396 + i.val; omega)
  simpa using card_le_card hsub

end ArkLib.ProximityGap.Frontier.QuarterSuccessorMovingObstruction
