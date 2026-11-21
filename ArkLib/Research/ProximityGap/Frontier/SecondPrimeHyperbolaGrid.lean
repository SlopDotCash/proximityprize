/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSixteenFiber
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Six heads on a hyperbola at the second production prime -/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimeHyperbolaGrid
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed (F N dom w)
open SecondPrimeSixteenFiber (Grid index Selection selected card_selected mem_selected power)
open PrizeShapePrimeP30Second (P prime_P orderOf_g)
local instance : Fact P.Prime := ⟨prime_P⟩
private abbrev S : ℕ := 67108864

/-- On the three vertical rulings the point is (a,t/a); on the three horizontal rulings
it is (t/b,b). Their nine meetings occur in distinct sixteenth-root fibers. -/
private def first : Fin 6 → Fin 2 → F :=
  ![![1, 0], ![w, 0], ![w^2, 0], ![0, 1], ![0, w^13], ![0, w^10]]

private def second : Fin 6 → Fin 2 → F :=
  ![![0, 1], ![0, w^15], ![0, w^14], ![1, 0], ![w^3, 0], ![w^6, 0]]

private def val (A : Fin 2 → F) (t : F) := A 1 * t + A 0
private def f (A : Fin 2 → F) : F[X] := C (A 1) * Polynomial.X^1 + C (A 0)
private def lift (A : Fin 2 → F) : F[X] := (f A).comp (Polynomial.X^S)

private theorem deg (A : Fin 2 → F) : (lift A).natDegree ≤ S := by
  have h : (f A).natDegree ≤ 1 := by
    unfold f
    exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le ..) (by simp)
  unfold lift
  apply natDegree_comp_le.trans
  exact (Nat.mul_le_mul h (natDegree_X_pow_le S)).trans_eq (one_mul S)

private def own : Fin 16 → Fin 6 := ![0,1,2,0,1,2,0,1,2,0,0,0,0,0,0,0]
private def group : Fin 16 → Finset (Fin 6) :=
  ![{0,3},{1,3},{2,3},{0,4},{1,4},{2,4},{0,5},{1,5},{2,5},{0},{0},{0},{0},{0},{0},{0}]

private def V (i : Fin 6) (j : Fin 16) : F := val (second i) (w^j.val)
private def U (i : Fin 6) (j : Fin 16) : F := val (first i) (w^j.val)

private theorem agrees : ∀ j i, i∈group j →
    U i j=U (own j) j ∧ V i j=V (own j) j := by decide
private theorem misses : ∀ j i, i∉group j → V i j≠V (own j) j := by decide
private theorem determinant : ∀ r i j, i∉group r → j∉group r → i≠j →
    (U (own r) r-U i r)*(V j r-V (own r) r)≠(U (own r) r-U j r)*(V i r-V (own r) r) := by
  decide

private def cut (j : Fin 16) : ℕ :=
  if j.val < 9 then 0 else if j.val = 15 then S - 2 else S
private theorem cut_le : ∀ j, cut j ≤ S := by decide

private abbrev roots := SecondPrimeSixteenFiber.roots cut
private abbrev core := SecondPrimeSixteenFiber.core cut group

private theorem root_count : roots.card=469762046 := by
  rw [roots, SecondPrimeSixteenFiber.roots, card_selected cut cut_le]; decide
private theorem core_count (j : Fin 6) : (core j).card=(![671088640,671088638,671088638,671088638,671088638,671088638] : Fin 6 → ℕ) j := by
  rw [core, SecondPrimeSixteenFiber.core, card_selected cut cut_le]; fin_cases j <;> decide

private theorem lifted (A : Fin 2 → F) (u : Grid) :
    (lift A).eval (dom (index u)) = val A (w ^ u.1.val) := by
  rw [lift, eval_comp, eval_pow, eval_X, power]
  simp [f, val]

/-- One received stack exceeds the second-prime budget at every dimension in this
interval, including half rate, and every positive interleaving width. -/
theorem label_mass {k : ℕ} (hk : 536870912 ≤ k) (hc : k ≤ 671088638) (width : ℕ) [NeZero width] :
    (2415919114:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (402653185/1073741824) := by
  have counts : (∑ i, (core i)ᶜ.card)=2415919114 := by
    simp only [card_compl,core_count,Fintype.card_fin,Fin.sum_univ_succ]
    decide
  have count_min (i : Fin 6) : 671088638 ≤ (core i).card := by rw [core_count]; fin_cases i <;> decide
  rw [epsMCA_interleaved_eq]
  have hm := SecondPrimeSixteenFiber.mass cut group own dom k S (402653185/1073741824)
    (fun i => lift (first i)) (fun i => lift (second i)) U V
    (fun i u => lifted (first i) u) (fun i u => lifted (second i) u)
    agrees misses determinant
    (by rw [← show roots = SecondPrimeSixteenFiber.roots cut from rfl, root_count]; dsimp [S]; omega)
    (fun _ => deg _) (fun _ => deg _)
    (fun i => hc.trans (count_min i)) (by
      intro i
      rw [Fintype.card_fin]
      apply le_trans (b:=((671088638+1:ℕ):ℝ≥0))
      · rw [tsub_mul,one_mul]; norm_num [N,tsub_le_iff_right]
      · exact_mod_cast Nat.add_le_add_right (count_min i) 1)
    (by rw [counts,Nat.card_eq_fintype_card,ZMod.card,Nat.choose_two_right]; decide)
  rw [counts,ZMod.card] at hm
  simpa only [Nat.cast_ofNat] using hm

/-- Strict failure at 402,653,185 errors and the resulting operational upper bound. -/
theorem half (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 536870912 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128
    tol < epsMCA (F:=F) code (402653185/1073741824) ∧
      mcaDeltaStar (F:=F) code tol ≤ 402653185/1073741824 := by
  dsimp only
  have hb : 1/(2:ℝ≥0∞)^128 < (2415919114:ℝ≥0∞)/(P:ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h : ((2415919114:ℕ):ℝ≥0∞)/P ≤ 1/((2^128:ℕ):ℝ≥0∞))
    exact (by decide : ¬ 2415919114 ≤ P/2^128) hh
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad,mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms label_mass
#print axioms half
end ArkLib.ProximityGap.Frontier.SecondPrimeHyperbolaGrid
