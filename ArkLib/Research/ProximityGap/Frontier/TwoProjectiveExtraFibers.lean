/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoProjectiveExtraColors
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadFibers

/-! # Four split power fibers on every smooth order-32 quotient -/
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TwoProjectiveExtraFibers
open TwoProjectiveExtraColors SmoothFourHeadFibers

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

private def raw (j : Fin 32) : Fin 5 :=
  if j = 0 then 0 else if j = 16 then 1 else if j = 8 then 2 else if j = 24 then 3 else 4

private def primary : Fin 5 → Fin 8 := ![0, 1, 2, 3, 7]
private def collapse : Fin 8 → Fin 5 := ![0, 1, 2, 3, 4, 4, 4, 4]
private def combine : Fin 5 → Fin 4 → Fin 8 :=
  fun r v => if r = 4 then ![4, 5, 6, 7] v else primary r

omit [Nonempty I] [DecidableEq I] in
private theorem refine_regions (b : I → Fin 5) (D R P T : ℕ)
    (sizes : ∀ j, (univ.filter (fun x => b x = j)).card = (![D, D, D, D, R + 2 * P + D + T] : Fin 5 → ℕ) j) :
    ∃ col : I → Fin 8, (∀ i, collapse (col i) = b i) ∧
      ∀ j, (univ.filter (fun x => col x = j)).card = TwoProjectiveExtraColors.weight D R P T j := by
  classical
  let rest := univ.filter fun x => b x = 4
  let w : Fin 4 → ℕ := ![R, P + D, P, T]
  obtain ⟨v, hv⟩ := partition_fibers rest w (by
    change (univ.filter _).card = _
    rw [sizes]
    simp [w, Fin.sum_univ_succ]
    omega)
  let col (i : I) := combine (b i) (v i)
  refine ⟨col, fun i => (by decide : ∀ r v, collapse (combine r v) = r) _ _, fun j => ?_⟩
  have low (j : Fin 8) (r : Fin 5) (eq : ∀ a b, combine a b = j ↔ a = r) :
      (univ.filter (fun i => col i = j)).card = (![D, D, D, D, R + 2 * P + D + T] : Fin 5 → ℕ) r := by
    simpa only [col, eq] using sizes r
  have high (j : Fin 8) (r : Fin 4) (eq : ∀ a b, combine a b = j ↔ a = 4 ∧ b = r) :
      (univ.filter (fun i => col i = j)).card = w r := by
    convert hv r using 2
    ext i; simp [col, rest, eq]
  fin_cases j
  · exact low _ 0 (by decide)
  · exact low _ 1 (by decide)
  · exact low _ 2 (by decide)
  · exact low _ 3 (by decide)
  · exact high _ 0 (by decide)
  · exact high _ 1 (by decide)
  · exact high _ 2 (by decide)
  · exact high _ 3 (by decide)

private def values (w t : F) : Fin 4 → F := ![0, t - 1, w * (t + 1), (-w) * (t + 1)]

omit [Fintype F] [DecidableEq F] in
private theorem table (v : F) (hv : orderOf v = 32) (i : Fin 32) (j l : Fin 4) :
    values (v ^ 8) (v ^ i.val) j = values (v ^ 8) (v ^ i.val) l ↔
      pattern (primary (raw i)) j = pattern (primary (raw i)) l := by
  let w := v ^ 8
  let t := v ^ i.val
  have eqv (a : Fin 32) : t = v ^ a.val ↔ i = a := by
    constructor
    · intro e
      exact Fin.ext (pow_injOn_Iio_orderOf (x := v) (by change i.val < orderOf v; simp [hv])
        (by change a.val < orderOf v; simp [hv]) e)
    · rintro rfl; rfl
  have half : v ^ 16 = -1 := by
    have sq : (v ^ 16) ^ 2 = 1 := by rw [← pow_mul, show 16 * 2 = orderOf v by omega, pow_orderOf_eq_one]
    exact (sq_eq_one_iff.mp sq).resolve_left (fun h => by
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [hv] at hd; exact (by decide : ¬32 ∣ 16) hd)
  have im : w ^ 2 = -1 := by change (v ^ 8) ^ 2 = -1; rw [← pow_mul]; exact half
  have in0 : w ≠ 0 := by intro z; simp [z] at im
  have units : (1 : F) ≠ -1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one (half.trans h.symm)
    rw [hv] at hd; exact (by decide : ¬32 ∣ 16) hd
  have ip : w ≠ 1 := fun h => units (by simpa [h] using im)
  have ineg : w ≠ -1 := fun h => units (by simpa [h] using im)
  have op : w ≠ -w := by
    intro h
    exact units (mul_right_cancel₀ in0 (by simpa using h : (1:F) * w = (-1) * w))
  have e0 : t = 1 ↔ i = 0 := by simpa using eqv 0
  have e1 : t = -1 ↔ i = 16 := by simpa [half] using eqv 16
  have e2 : t = w ↔ i = 8 := eqv 8
  have other : v ^ 24 = -w := by rw [show 24 = 16 + 8 by decide, pow_add, half]; simp [w]
  have e3 : t = -w ↔ i = 24 := by simpa [other] using eqv 24
  have eq1 : t - 1 = w * (t + 1) ↔ t = w := by
    have identity : (t - 1) - w * (t + 1) = (1 - w) * (t - w) := by linear_combination -im
    rw [← sub_eq_zero, identity, mul_eq_zero, or_iff_right (sub_ne_zero.mpr ip.symm), sub_eq_zero]
  have eq2 : t - 1 = (-w) * (t + 1) ↔ t = -w := by
    have identity : (t - 1) - (-w) * (t + 1) = (1 + w) * (t- -w) := by linear_combination -im
    have nz : 1 + w ≠ 0 := by intro h; exact ineg (by linear_combination h)
    rw [← sub_eq_zero, identity, mul_eq_zero, or_iff_right nz, sub_eq_zero]
  have eq3 : w * (t + 1) = (-w) * (t + 1) ↔ t = -1 := by
    rw [← sub_eq_zero, ← sub_mul, mul_eq_zero, or_iff_right (sub_ne_zero.mpr op)]
    exact add_eq_zero_iff_eq_neg
  have eps (a : F) (nz : a ≠ 0) : (0 : F) = a * (t + 1) ↔ t = -1 := by
    rw [eq_comm, mul_eq_zero, or_iff_right nz]
    exact add_eq_zero_iff_eq_neg
  have n01 : values w t 0 = values w t 1 ↔ i = 0 := by
    change 0 = t - 1 ↔ _
    rw [eq_comm, sub_eq_zero, e0]
  have n02 : values w t 0 = values w t 2 ↔ i = 16 := (eps w in0).trans e1
  have n03 : values w t 0 = values w t 3 ↔ i = 16 := (eps _ (neg_ne_zero.mpr in0)).trans e1
  have n12 : values w t 1 = values w t 2 ↔ i = 8 := eq1.trans e2
  have n13 : values w t 1 = values w t 3 ↔ i = 24 := eq2.trans e3
  have n23 : values w t 2 = values w t 3 ↔ i = 16 := eq3.trans e1
  change values w t j = values w t l ↔ _
  fin_cases j <;> fin_cases l
  all_goals try exact iff_of_true rfl rfl
  all_goals first
    | refine n01.trans ?_
    | refine n02.trans ?_
    | refine n03.trans ?_
    | refine n12.trans ?_
    | refine n13.trans ?_
    | refine n23.trans ?_
    | refine (eq_comm.trans n01).trans ?_
    | refine (eq_comm.trans n02).trans ?_
    | refine (eq_comm.trans n03).trans ?_
    | refine (eq_comm.trans n12).trans ?_
    | refine (eq_comm.trans n13).trans ?_
    | refine (eq_comm.trans n23).trans ?_
  all_goals generalize i = a; revert a; decide

set_option maxRecDepth 10000 in
private theorem sizes32 (j : Fin 5) :
    (univ.filter (fun i : Fin 32 => raw i = j)).card = (![1, 1, 1, 1, 28] : Fin 5 → ℕ) j := by
  fin_cases j <;> decide

/-- The normalized power variable and the square root of minus one realize the
four coincidence fibers, with multiplicities lifted by the power map. -/
theorem mass {s : ℕ} [NeZero s] (hs : 0 < s)
    (dom : Fin (s * 32) ↪ F) (c g : F) (hc : c ≠ 0) (hg : orderOf g = s * 32)
    (hdom : ∀ i, dom i = c * g ^ i.val) (k R P T : ℕ) (δ : ℝ≥0)
    (part : 28 * s = R + 2 * P + s + T) (degree : R + s + 1 < k) (rank : k ≤ R + 3 * s + P) (hout : k ≤ T)
    (big : (1 - δ) * (s * 32:ℕ) ≤ ((R + 3 * s + P + 1:ℕ):ℝ≥0)) (height : (1 - δ) * (s * 32:ℕ) ≤ ((R + 2 * s + T:ℕ):ℝ≥0))
    (hq : (2 * (s * 32 - (R + 3 * s + P)) + 1).choose 2 < Fintype.card F)
    (room : 2 * (s * 32 - (R + 3 * s + P)) + 1 < Fintype.card F) :
    ((2 * (s * 32 - (R + 3 * s + P)) + 2:ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin (s * 32) → F)) δ := by
  classical
  let cls (i : Fin (s * 32)) := raw i.modNat
  have count (j : Fin 5) : (univ.filter (fun i => cls i = j)).card =
      (![s, s, s, s, R + 2 * P + s + T] : Fin 5 → ℕ) j := by
    change (univ.filter (fun i : Fin (s * 32) => raw i.modNat = j)).card = _
    rw [count_blocks, sizes32]
    fin_cases j <;> dsimp <;> omega
  obtain ⟨col, hcol, counts⟩ := refine_regions cls s R P T count
  let v := g ^ s
  have hv : orderOf v = 32 := by
    change orderOf (g ^ s) = 32
    rw [orderOf_pow_of_dvd (by omega : s ≠ 0) (hg ▸ dvd_mul_right s 32),
      hg, Nat.mul_div_cancel_left _ hs]
  let w := v ^ 8
  let variableX : F[X] := (C c⁻¹ * (Polynomial.X : F[X])) ^ s
  let seed : Fin 4 → F[X] := ![0, variableX - 1, C w * (variableX + 1), C (-w) * (variableX + 1)]
  have xeval (i : Fin (s * 32)) : variableX.eval (dom i) = v ^ i.modNat.val := by
    simp only [variableX, eval_pow, eval_mul, eval_C, eval_X, hdom, inv_mul_cancel_left₀ hc]
    rw [← pow_mul, mul_comm, pow_mul]
    change v ^ i.val = v ^ (i.val%32)
    simpa only [hv] using (pow_mod_orderOf v i.val).symm
  have seed_eval (j : Fin 4) (i : Fin (s * 32)) : (seed j).eval (dom i) =
      values w (v ^ i.modNat.val) j := by
    fin_cases j <;> simp [seed, values, xeval]
  have nd (j : Fin 4) : (seed j).natDegree ≤ s := by
    have ndx : variableX.natDegree ≤ s := by
      have h := (natDegree_C_mul_le c⁻¹ (Polynomial.X : F[X])).trans natDegree_X_le
      exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left s h)
    have add : (variableX + 1).natDegree ≤ s :=
      (natDegree_add_le ..).trans (max_le ndx (by simp))
    have sub : (variableX - 1).natDegree ≤ s :=
      (natDegree_sub_le ..).trans (max_le ndx (by simp))
    fin_cases j
    · simp [seed]
    · exact sub
    · exact (natDegree_C_mul_le ..).trans add
    · exact (natDegree_C_mul_le ..).trans add
  let padding := univ.filter fun i => col i = 4
  let H := Lagrange.nodal padding (fun i => dom i)
  let f (j : Fin 4) := H * seed j
  have degH : H.natDegree = R := Lagrange.natDegree_nodal.trans (counts 4)
  have deg (j : Fin 4) : (f j).natDegree + 1 < k := by
    have h := natDegree_mul_le (p := H) (q := seed j)
    have h' := nd j
    rw [degH] at h
    change (H * seed j).natDegree + 1 < _
    omega
  have equal (j l : Fin 4) (i : Fin (s * 32)) :
      (f j).eval (dom i) = (f l).eval (dom i) ↔ pattern (col i) j = pattern (col i) l := by
    simp only [f, eval_mul]
    by_cases hi : col i = 4
    · have atnode : H.eval (dom i) = 0 := Lagrange.eval_nodal_at_node (mem_filter.mpr ⟨mem_univ _, hi⟩)
      rw [atnode, zero_mul, zero_mul, hi]
      exact iff_of_true rfl ((by decide : ∀ a b, pattern 4 a = pattern 4 b) j l)
    · have nz : H.eval (dom i) ≠ 0 := Lagrange.eval_nodal_not_at_node (fun y hy h => hi
          (dom.injective h ▸ (mem_filter.mp hy).2))
      rw [mul_right_inj' nz, seed_eval, seed_eval, table v hv i.modNat]
      change pattern (primary (cls i)) j = pattern (primary (cls i)) l ↔ _
      rw [← hcol]
      exact (by decide : ∀ a j l, a ≠ 4 → (pattern (primary (collapse a)) j =
        pattern (primary (collapse a)) l ↔ pattern a j = pattern a l)) (col i) j l hi
  simpa only [Fintype.card_fin] using TwoProjectiveExtraColors.mass dom k s R P T δ f col deg
    equal counts hs rank hout (by simpa only [Fintype.card_fin] using big)
    (by simpa only [Fintype.card_fin] using height) (by simpa only [Fintype.card_fin] using hq)
    (by simpa only [Fintype.card_fin] using room)

#print axioms mass
end ArkLib.ProximityGap.Frontier.TwoProjectiveExtraFibers
