/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.RateHalfMobiusProduction
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSixteenFiber
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # The first over-budget 1 × 2 hyperbola grid on the first production prime -/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.FirstPrimeHyperbolaGrid
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open _root_.ProximityGap.RateHalfMobiusProduction (F dom)
private abbrev N : ℕ := 2^30
open SecondPrimeSixteenFiber (Grid index card_selected)
open PrizeShapePrimeP30 (P prime_P orderOf_g)
local instance : Fact P.Prime := ⟨prime_P⟩
private abbrev S : ℕ := 67108864

private abbrev D : ℕ := 134217728
private def w : F := 18943363311336672863882327061011457227257409586

private theorem power (u : Grid) : dom (index u) ^ D = w ^ u.1.val := by
  change (PrizeShapePrimeP30.g ^ (u.1.val + 16*u.2.val)) ^ D=_
  have hg : PrizeShapePrimeP30.g ^ N=1 := by
    simpa only [orderOf_g] using pow_orderOf_eq_one PrizeShapePrimeP30.g
  have hr : (PrizeShapePrimeP30.g^(16*u.2.val))^D=1 := by
    have h : (16*u.2.val)*D=N*(2*u.2.val) := by dsimp [N, D]; omega
    rw [← pow_mul,h,pow_mul,hg,one_pow]
  have hw : PrizeShapePrimeP30.g ^ D=w := by
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  rw [pow_add,mul_pow,hr,mul_one,← pow_mul,Nat.mul_comm,pow_mul,hw]

/-- One vertical ruling and two horizontal rulings meet over 1 and w. -/
private def first : Fin 3 → Fin 2 → F := ![![1, 0], ![0, 1], ![0, w^7]]
private def second : Fin 3 → Fin 2 → F := ![![0, 1], ![1, 0], ![w, 0]]

private def val (A : Fin 2 → F) (t : F) := A 1 * t + A 0
private def f (A : Fin 2 → F) : F[X] := C (A 1) * Polynomial.X^1 + C (A 0)
private def lift (A : Fin 2 → F) : F[X] := (f A).comp (Polynomial.X^D)

private theorem deg (A : Fin 2 → F) : (lift A).natDegree ≤ D := by
  have h : (f A).natDegree ≤ 1 := by
    unfold f
    exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le ..) (by simp)
  unfold lift
  apply natDegree_comp_le.trans
  exact (Nat.mul_le_mul h (natDegree_X_pow_le D)).trans_eq (one_mul D)

private def own : Fin 16 → Fin 3 := ![0,0,0,1,1,1,2,2,0,0,2,0,0,0,0,0]
private def group : Fin 16 → Finset (Fin 3) :=
  ![{0,1},{0,2},{0},{1},{1},{1},{2},{2},{0,1},{0,2},{2},{0},{0},{0},{0},{0}]

private def V (i : Fin 3) (j : Fin 16) : F := val (second i) (w^j.val)
private def U (i : Fin 3) (j : Fin 16) : F := val (first i) (w^j.val)

private theorem agrees : ∀ j i, i∈group j →
    U i j=U (own j) j ∧ V i j=V (own j) j := by decide
private theorem misses : ∀ j i, i∉group j → V i j≠V (own j) j := by decide
private theorem determinant : ∀ r i j, i∉group r → j∉group r → i≠j →
    (U (own r) r-U i r)*(V j r-V (own r) r)≠(U (own r) r-U j r)*(V i r-V (own r) r) := by
  decide

private def cut : Fin 16 → ℕ :=
  ![0,0,S-44739244,0,0,S-44739243,0,0,0,0,S-44739243,S,S,S,S,S]
private theorem cut_le : ∀ j, cut j ≤ S := by decide

private abbrev roots := SecondPrimeSixteenFiber.roots cut
private abbrev core := SecondPrimeSixteenFiber.core cut group

private theorem root_count : roots.card=402653182 := by
  rw [roots, SecondPrimeSixteenFiber.roots, card_selected cut cut_le]; decide
private theorem core_count (j : Fin 3) : (core j).card=(![715827882,715827881,715827881] : Fin 3 → ℕ) j := by
  rw [core, SecondPrimeSixteenFiber.core, card_selected cut cut_le]; fin_cases j <;> decide

private theorem lifted (A : Fin 2 → F) (u : Grid) :
    (lift A).eval (dom (index u)) = val A (w ^ u.1.val) := by
  rw [lift, eval_comp, eval_pow, eval_X, power]
  simp [f, val]

/-- One received stack exceeds the first-prime budget at every dimension in this
interval, including half rate, and every positive interleaving width. -/
theorem label_mass {k : ℕ} (hk : 536870912 ≤ k) (hc : k ≤ 715827881) (width : ℕ) [NeZero width] :
    (1073741828:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (357913942/1073741824) := by
  have counts : (∑ i, (core i)ᶜ.card)=1073741828 := by
    simp only [card_compl,core_count,Fintype.card_fin,Fin.sum_univ_succ]
    decide
  have count_min (i : Fin 3) : 715827881 ≤ (core i).card := by rw [core_count]; fin_cases i <;> decide
  rw [epsMCA_interleaved_eq]
  have hm := SecondPrimeSixteenFiber.mass cut group own dom k D (357913942/1073741824)
    (fun i => lift (first i)) (fun i => lift (second i)) U V
    (fun i u => lifted (first i) u) (fun i u => lifted (second i) u)
    agrees misses determinant
    (by rw [← show roots = SecondPrimeSixteenFiber.roots cut from rfl, root_count]; dsimp [D]; omega)
    (fun _ => deg _) (fun _ => deg _)
    (fun i => hc.trans (count_min i)) (by
      intro i
      rw [Fintype.card_fin]
      apply le_trans (b:=((715827881+1:ℕ):ℝ≥0))
      · rw [tsub_mul,one_mul]; norm_num [N,tsub_le_iff_right]
      · exact_mod_cast Nat.add_le_add_right (count_min i) 1)
    (by rw [counts,Nat.card_eq_fintype_card,ZMod.card,Nat.choose_two_right]; decide)
  rw [counts,ZMod.card] at hm
  simpa only [Nat.cast_ofNat] using hm

/-- Strict failure at 357,913,942 errors and the resulting operational upper bound. -/
theorem half (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 536870912 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128
    tol < epsMCA (F:=F) code (357913942/1073741824) ∧
      mcaDeltaStar (F:=F) code tol ≤ 357913942/1073741824 := by
  dsimp only
  have hb : 1/(2:ℝ≥0∞)^128 < (1073741828:ℝ≥0∞)/(P:ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h : ((1073741828:ℕ):ℝ≥0∞)/P ≤ 1/((2^128:ℕ):ℝ≥0∞))
    exact (by decide : ¬ 1073741828 ≤ P/2^128) hh
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad,mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms label_mass
#print axioms half
end ArkLib.ProximityGap.Frontier.FirstPrimeHyperbolaGrid
