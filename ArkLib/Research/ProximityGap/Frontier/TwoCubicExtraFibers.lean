/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoProjectiveExtraColors
import ArkLib.Research.ProximityGap.Frontier.TwoCubicExtraSeed

/-! # The two cubic pencils on an order-64 quotient -/
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TwoCubicExtraFibers
open TwoProjectiveExtraColors SmoothFourHeadFibers

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

private def raw (i : Fin 64) : Fin 9 :=
  if i = 0 ∨ i = 4 ∨ i = 32 then 0
  else if i = 8 ∨ i = 40 then 1
  else if i = 12 ∨ i = 20 then 2
  else if i = 24 ∨ i = 56 then 3
  else if i = 44 ∨ i = 52 then 4
  else if i = 28 then 5
  else if i = 36 then 6
  else if i = 60 then 7 else 8

private def primary : Fin 9 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 11]
private def collapse : Fin 12 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8]
private def combine (r : Fin 9) (v : Fin 4) : Fin 12 :=
  if r = 8 then ![8, 9, 10, 11] v else primary r

private def colorPattern : Fin 12 → Fin 4 → Fin 4 :=
  ![![0, 0, 2, 3], ![0, 1, 0, 3], ![0, 1, 1, 3], ![0, 1, 2, 0], ![0, 1, 2, 1],
    ![0, 1, 1, 1], ![0, 1, 0, 0], ![0, 1, 2, 2],
    ![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]

private def colors : Layout 12 := {
  pattern := colorPattern
  owners := fun j => ![0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, if j = 0 then 2 else 3]
  cores := ![{0, 1, 3, 6, 7, 8, 9}, {0, 2, 4, 5, 8, 10}]
  supports := ![{1, 2, 5, 6, 8, 11}, {3, 4, 5, 6, 8, 11}]
  outside := 11, horizontal := 2, vertical := 4 }

private def weight (s R P T : ℕ) : Fin 12 → ℕ :=
  ![3 * s, 2 * s, 2 * s, 2 * s, 2 * s, s, s, s, R, P, P + s, T]

omit [Nonempty I] [DecidableEq I] in
private theorem refine_regions (b : I → Fin 9) (D R P T : ℕ)
    (sizes : ∀ j, (univ.filter (fun x => b x = j)).card = (![3 * D, 2 * D, 2 * D, 2 * D, 2 * D, D, D, D, R + 2 * P + D + T] : Fin 9 → ℕ) j) :
    ∃ col : I → Fin 12, (∀ i, collapse (col i) = b i) ∧
      ∀ j, (univ.filter (fun x => col x = j)).card = weight D R P T j := by
  classical
  let rest := univ.filter fun x => b x = 8
  let w : Fin 4 → ℕ := ![R, P, P + D, T]
  obtain ⟨v, hv⟩ := partition_fibers rest w (by
    change (univ.filter _).card = _
    rw [sizes]
    simp [w, Fin.sum_univ_succ]
    omega)
  let col (i : I) := combine (b i) (v i)
  refine ⟨col, fun i => (by decide : ∀ r v, collapse (combine r v) = r) _ _, fun j => ?_⟩
  have low (j : Fin 12) (r : Fin 9) (eq : ∀ a b, combine a b = j ↔ a = r) :
      (univ.filter (fun i => col i = j)).card = (![3 * D, 2 * D, 2 * D, 2 * D, 2 * D, D, D, D, R + 2 * P + D + T] : Fin 9 → ℕ) r := by
    simpa only [col, eq] using sizes r
  have high (j : Fin 12) (r : Fin 4) (eq : ∀ a b, combine a b = j ↔ a = 8 ∧ b = r) :
      (univ.filter (fun i => col i = j)).card = w r := by
    convert hv r using 2
    ext i; simp [col, rest, eq]
  fin_cases j
  · exact low _ 0 (by decide)
  · exact low _ 1 (by decide)
  · exact low _ 2 (by decide)
  · exact low _ 3 (by decide)
  · exact low _ 4 (by decide)
  · exact low _ 5 (by decide)
  · exact low _ 6 (by decide)
  · exact low _ 7 (by decide)
  · exact high _ 0 (by decide)
  · exact high _ 1 (by decide)
  · exact high _ 2 (by decide)
  · exact high _ 3 (by decide)

omit [Fintype F] [DecidableEq F] in
private theorem table (v : F) (hv : orderOf v = 64) (i : Fin 64) (j l : Fin 4) :
    TwoCubicExtraSeed.values (v ^ 4) (v ^ i.val) j = TwoCubicExtraSeed.values (v ^ 4) (v ^ i.val) l ↔
    colorPattern (primary (raw i)) j = colorPattern (primary (raw i)) l := by
  let w := v ^ 4
  let t := v ^ i.val
  have hw : orderOf w = 16 := by
    change orderOf (v ^ 4) = 16
    rw [orderOf_pow_of_dvd (by decide : 4 ≠ 0) (by rw [hv]; decide), hv]
  obtain ⟨wn, one, sc, so, different⟩ := TwoCubicExtraSeed.units w hw
  have h8 : w ^ 8 = -1 := by
    have sq : (w ^ 8) ^ 2 = 1 := by rw [← pow_mul, show 8 * 2 = orderOf w by omega, pow_orderOf_eq_one]
    exact (sq_eq_one_iff.mp sq).resolve_left (fun h => by
      have ord := orderOf_dvd_of_pow_eq_one h
      rw [hw] at ord; exact (by decide : ¬16 ∣ 8) ord)
  have root (a : ℕ) (ha : a < 16) : t = w ^ a ↔ i.val = 4 * a := by
    change v ^ i.val = (v ^ 4) ^ a ↔ _
    rw [← pow_mul]
    exact ⟨fun e => pow_injOn_Iio_orderOf (x := v) (by change i.val < orderOf v; simp [hv])
      (by change 4 * a < orderOf v; omega) e, fun e => congrArg (v ^ ·) e⟩
  have cubic (a b c : ℕ) (ha : a < 16) (hb : b < 16) (hc : c < 16) :
      TwoCubicExtraSeed.cubic w t a b c = 0 ↔ i.val = 4 * a ∨ i.val = 4 * b ∨ i.val = 4 * c := by
    simp only [TwoCubicExtraSeed.cubic, mul_eq_zero, sub_eq_zero, root a ha, root b hb, root c hc, or_assoc]
  let z := TwoCubicExtraSeed.values w t
  have p01 : z 0 = z 1 ↔ i.val = 0 ∨ i.val = 4 ∨ i.val = 32 := by
    rw [eq_comm (a := z 0)]
    change TwoCubicExtraSeed.cubic w t 0 1 8 = 0 ↔ _
    exact cubic 0 1 8 (by decide) (by decide) (by decide)
  have p02 : z 0 = z 2 ↔ i.val = 8 ∨ i.val = 36 ∨ i.val = 40 := by
    rw [eq_comm (a := z 0)]
    change w ^ 2 * TwoCubicExtraSeed.cubic w t 2 9 10 = 0 ↔ _
    rw [mul_eq_zero, or_iff_right (pow_ne_zero _ wn)]
    exact cubic 2 9 10 (by decide) (by decide) (by decide)
  have p03 : z 0 = z 3 ↔ i.val = 24 ∨ i.val = 36 ∨ i.val = 56 := by
    rw [eq_comm (a := z 0)]
    change TwoCubicExtraSeed.scale w * TwoCubicExtraSeed.cubic w t 6 9 14 = 0 ↔ _
    rw [mul_eq_zero, or_iff_right sc]
    exact cubic 6 9 14 (by decide) (by decide) (by decide)
  have p12 : z 1 = z 2 ↔ i.val = 12 ∨ i.val = 20 ∨ i.val = 28 := by
    rw [← sub_eq_zero]
    change TwoCubicExtraSeed.cubic w t 0 1 8 - w ^ 2 * TwoCubicExtraSeed.cubic w t 2 9 10 = 0 ↔ _
    have split : TwoCubicExtraSeed.cubic w t 0 1 8 - w ^ 2 * TwoCubicExtraSeed.cubic w t 2 9 10 =
      (1 - w ^ 2) * TwoCubicExtraSeed.cubic w t 3 5 7 := by simpa [TwoCubicExtraSeed.cubic] using SmoothCosetCubicSeed.split w t h8
    rw [split, mul_eq_zero, or_iff_right (sub_ne_zero.mpr one.symm)]
    exact cubic 3 5 7 (by decide) (by decide) (by decide)
  have p13 : z 1 = z 3 ↔ i.val = 28 ∨ i.val = 44 ∨ i.val = 52 := by
    rw [← sub_eq_zero]
    change TwoCubicExtraSeed.cubic w t 0 1 8 - TwoCubicExtraSeed.scale w * TwoCubicExtraSeed.cubic w t 6 9 14 = 0 ↔ _
    rw [TwoCubicExtraSeed.w_minus_v w t h8, mul_eq_zero, or_iff_right (sub_ne_zero.mpr so.symm)]
    exact cubic 7 11 13 (by decide) (by decide) (by decide)
  have p23 : z 2 = z 3 ↔ i.val = 28 ∨ i.val = 36 ∨ i.val = 60 := by
    rw [← sub_eq_zero]
    change w ^ 2 * TwoCubicExtraSeed.cubic w t 2 9 10 - TwoCubicExtraSeed.scale w * TwoCubicExtraSeed.cubic w t 6 9 14 = 0 ↔ _
    rw [TwoCubicExtraSeed.q_minus_v w t h8, mul_eq_zero, or_iff_right (sub_ne_zero.mpr different)]
    exact cubic 7 9 15 (by decide) (by decide) (by decide)
  change z j = z l ↔ _
  fin_cases j <;> fin_cases l
  all_goals try exact iff_of_true rfl rfl
  all_goals first
    | refine p01.trans ?_
    | refine p02.trans ?_
    | refine p03.trans ?_
    | refine p12.trans ?_
    | refine p13.trans ?_
    | refine p23.trans ?_
    | refine (eq_comm.trans p01).trans ?_
    | refine (eq_comm.trans p02).trans ?_
    | refine (eq_comm.trans p03).trans ?_
    | refine (eq_comm.trans p12).trans ?_
    | refine (eq_comm.trans p13).trans ?_
    | refine (eq_comm.trans p23).trans ?_
  all_goals generalize i = a; revert a; decide

set_option maxRecDepth 25000 in
private theorem sizes64 (j : Fin 9) :
    (univ.filter (fun i : Fin 64 => raw i = j)).card = (![3, 2, 2, 2, 2, 1, 1, 1, 50] : Fin 9 → ℕ) j := by
  fin_cases j <;> decide

/-- The two cubic pencils and a shared locator give two extra projective directions
on each indexed power coset. -/
theorem mass {s : ℕ} [NeZero s] (hs : 0 < s)
    (dom : Fin (s * 64) ↪ F) (c g : F) (hc : c ≠ 0) (hg : orderOf g = s * 64)
    (hdom : ∀ i, dom i = c * g ^ i.val) (k R P T : ℕ) (δ : ℝ≥0)
    (part : 50 * s = R + 2 * P + s + T) (degree : R + 3 * s + 1 < k) (rank : k ≤ R + 9 * s + P) (hout : k ≤ T)
    (big : (1 - δ) * (s * 64:ℕ) ≤ ((R + 9 * s + P + 1:ℕ):ℝ≥0)) (height : (1 - δ) * (s * 64:ℕ) ≤ ((R + 6 * s + T:ℕ):ℝ≥0))
    (hq : (2 * (s * 64 - (R + 9 * s + P)) + 1).choose 2 < Fintype.card F)
    (room : 2 * (s * 64 - (R + 9 * s + P)) + 1 < Fintype.card F) :
    ((2 * (s * 64 - (R + 9 * s + P)) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin (s * 64) → F)) δ := by
  classical
  let cls (i : Fin (s * 64)) := raw i.modNat
  have count (j : Fin 9) : (univ.filter (fun i => cls i = j)).card =
      (![3 * s, 2 * s, 2 * s, 2 * s, 2 * s, s, s, s, R + 2 * P + s + T] : Fin 9 → ℕ) j := by
    change (univ.filter (fun i : Fin (s * 64) => raw i.modNat = j)).card = _
    rw [count_blocks, sizes64]
    fin_cases j <;> dsimp <;> omega
  obtain ⟨col, hcol, counts⟩ := refine_regions cls s R P T count
  let v := g ^ s
  have hv : orderOf v = 64 := by
    change orderOf (g ^ s) = 64
    rw [orderOf_pow_of_dvd (by omega : s ≠ 0) (hg ▸ dvd_mul_right s 64),
      hg, Nat.mul_div_cancel_left _ hs]
  let w := v ^ 4
  let variableX : F[X] := (C c⁻¹ * (Polynomial.X : F[X])) ^ s
  let fac (i : ℕ) := variableX - C (w ^ i)
  let cubic (a b c : ℕ) := fac a * fac b * fac c
  let seed : Fin 4 → F[X] := ![0, cubic 0 1 8, C (w ^ 2) * cubic 2 9 10,
    C (TwoCubicExtraSeed.scale w) * cubic 6 9 14]
  have xeval (i : Fin (s * 64)) : variableX.eval (dom i) = v ^ i.modNat.val := by
    simp only [variableX, eval_pow, eval_mul, eval_C, eval_X, hdom, inv_mul_cancel_left₀ hc]
    rw [← pow_mul, mul_comm, pow_mul]
    change v ^ i.val = v ^ (i.val % 64)
    simpa only [hv] using (pow_mod_orderOf v i.val).symm
  have seed_eval (j : Fin 4) (i : Fin (s * 64)) : (seed j).eval (dom i) =
      TwoCubicExtraSeed.values w (v ^ i.modNat.val) j := by
    fin_cases j <;> simp [seed, TwoCubicExtraSeed.values, TwoCubicExtraSeed.cubic, cubic, fac, xeval]
  have ndx : variableX.natDegree ≤ s := by
    have h := (natDegree_C_mul_le c⁻¹ (Polynomial.X : F[X])).trans natDegree_X_le
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left s h)
  have small (a : ℕ) : (fac a).natDegree ≤ s :=
    (natDegree_sub_le ..).trans (max_le ndx (by simp))
  have cubic_small (a b c : ℕ) : (cubic a b c).natDegree ≤ 3 * s := by
    have ab := (natDegree_mul_le (p := fac a) (q := fac b)).trans (add_le_add (small a) (small b))
    have abc := (natDegree_mul_le (p := fac a * fac b) (q := fac c)).trans (add_le_add ab (small c))
    change (fac a * fac b * fac c).natDegree ≤ _
    omega
  have nd (j : Fin 4) : (seed j).natDegree ≤ 3 * s := by
    fin_cases j
    · simp [seed]
    · exact cubic_small 0 1 8
    · exact (natDegree_C_mul_le ..).trans (cubic_small 2 9 10)
    · exact (natDegree_C_mul_le ..).trans (cubic_small 6 9 14)
  let padding := univ.filter fun i => col i = 8
  let H := Lagrange.nodal padding (fun i => dom i)
  let f (j : Fin 4) := H * seed j
  have degH : H.natDegree = R := Lagrange.natDegree_nodal.trans (counts 8)
  have deg (j : Fin 4) : (f j).natDegree + 1 < k := by
    have h := natDegree_mul_le (p := H) (q := seed j)
    have h' := nd j
    rw [degH] at h
    change (H * seed j).natDegree + 1 < _
    omega
  have equal (j l : Fin 4) (i : Fin (s * 64)) :
      (f j).eval (dom i) = (f l).eval (dom i) ↔ colorPattern (col i) j = colorPattern (col i) l := by
    simp only [f, eval_mul]
    by_cases hi : col i = 8
    · have atnode : H.eval (dom i) = 0 := Lagrange.eval_nodal_at_node (mem_filter.mpr ⟨mem_univ _, hi⟩)
      rw [atnode, zero_mul, zero_mul, hi]
      exact iff_of_true rfl ((by decide : ∀ a b, colorPattern 8 a = colorPattern 8 b) j l)
    · have nz : H.eval (dom i) ≠ 0 := Lagrange.eval_nodal_not_at_node (fun y hy h => hi
          (dom.injective h ▸ (mem_filter.mp hy).2))
      rw [mul_right_inj' nz, seed_eval, seed_eval, table v hv i.modNat]
      change colorPattern (primary (cls i)) j = colorPattern (primary (cls i)) l ↔ _
      rw [← hcol]
      exact (by decide : ∀ a j l, a ≠ 8 → (colorPattern (primary (collapse a)) j =
        colorPattern (primary (collapse a)) l ↔ colorPattern a j = colorPattern a l)) (col i) j l hi
  suffices ((2 * (Fintype.card (Fin (s * 64)) - (R + 9 * s + P)) + 2 : ℕ) : ℝ≥0∞) /
      (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin (s * 64) → F)) δ by
    simpa only [Fintype.card_fin] using this
  apply colors.mass (by decide) dom k (R + 9 * s + P) δ f col (weight s R P T) deg equal counts
  · intro j
    fin_cases j <;> simp [colors, weight] <;> omega
  · exact rank
  · exact hout
  · simpa only [Fintype.card_fin] using big
  · intro j
    simp only [Fintype.card_fin]
    convert height using 1
    congr 1
    fin_cases j <;> simp [colors, weight] <;> omega
  · change 0 < 2 * s; omega
  · change 0 < 2 * s; omega
  · simpa only [Fintype.card_fin] using hq
  · simpa only [Fintype.card_fin] using room

#print axioms mass
end ArkLib.ProximityGap.Frontier.TwoCubicExtraFibers
