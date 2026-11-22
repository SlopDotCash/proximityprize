/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSixteenFiber
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Six tetrahedron edges improve the second-prime half-rate MCA bound -/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SecondPrimeTetrahedron

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed (F N dom w)
open SecondPrimeSixteenFiber (Grid index card_selected power)
open PrizeShapePrimeP30Second (P prime_P)

local instance : Fact P.Prime := ⟨prime_P⟩
private abbrev D : ℕ := 134217728
private abbrev S : ℕ := 67108864
private def z : F := 684944486517762849622048856798491974355853664681

private theorem quotient (x : Grid) : dom (index x) ^ D = z ^ x.1.val := by
  change dom (index x) ^ (S*2) = z ^ x.1.val
  rw [pow_mul, power, ← pow_mul, Nat.mul_comm, pow_mul]
  have hz : w^2 = z := by decide
  rw [hz]

/-- Each section joins two vertices (a,a²,a³). The second coordinate includes
a linear multiple of the first to avoid vertical foreign directions. -/
private def ends : Fin 6 → Fin 4 × Fin 4 := ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
private def secantFirst (a b : F) : Fin 2 → F := ![-a*b, a+b]
private def secantSecond (a b : F) : Fin 2 → F :=
  ![-a*b*(a+b)+7*secantFirst a b 0, a^2+a*b+b^2+7*secantFirst a b 1]
private def first (i : Fin 6) := secantFirst (z ^ (ends i).1.val) (z ^ (ends i).2.val)
private def second (i : Fin 6) := secantSecond (z ^ (ends i).1.val) (z ^ (ends i).2.val)

private def affine (A : Fin 2 → F) : F[X] := C (A 1)*Polynomial.X^1 + C (A 0)
private def lift (A : Fin 2 → F) : F[X] := (affine A).comp (Polynomial.X^D)
private def val (A : Fin 2 → F) (j : Fin 16) : F := A 1 * z^j.val + A 0

private theorem deg (A : Fin 2 → F) : (lift A).natDegree ≤ D := by
  have h : (affine A).natDegree ≤ 1 := by
    unfold affine
    exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le ..) (by simp)
  unfold lift
  exact natDegree_comp_le.trans ((Nat.mul_le_mul h (natDegree_X_pow_le D)).trans_eq (one_mul D))

private theorem lifted (A : Fin 2 → F) (x : Grid) :
    (lift A).eval (dom (index x)) = val A x.1 := by
  rw [lift, eval_comp, eval_pow, eval_X, quotient]
  simp [affine, val]

private def group : Fin 16 → Finset (Fin 6) :=
  ![{0,1,2}, {0,3,4}, {1,3,5}, {2,4,5}, {0}, {1}, {2}, {3},
    {0,1,2}, {0,3,4}, {1,3,5}, {2,4,5}, {4}, {5}, ∅, ∅]
private def labels : Fin 16 → Finset (Fin 6) :=
  ![{3,4,5}, {1,2,5}, {0,2,4}, {0,1,3}, {1,2,5}, {0,2,4}, {0,1,3}, {0,2,4},
    {3,4,5}, {1,2,5}, {0,2,4}, {0,1,3}, {0,1,3}, {0,1,3}, {0,1,2,3,4,5}, {0,1,2,3,4,5}]
private def owners : Fin 16 → Fin 7 := ![0, 0, 1, 2, 0, 1, 2, 3, 0, 0, 1, 2, 4, 5, 6, 6]

private def received (A : Fin 6 → Fin 2 → F) (outside : F) (j : Fin 16) : F :=
  if h : (owners j).val < 6 then val (A ⟨(owners j).val, h⟩) j else outside
private abbrev u := received first 17
private abbrev v := received second 29

private theorem agrees : ∀ j i, i ∈ group j → val (first i) j = u j ∧ val (second i) j = v j := by decide
private theorem misses : ∀ j i, i ∈ labels j → val (second i) j ≠ v j := by decide
private theorem determinant : ∀ r i j, i ∈ labels r → j ∈ labels r → i ≠ j →
    (u r-val (first i) r)*(val (second j) r-v r) ≠ (u r-val (first j) r)*(val (second i) r-v r) := by
  decide

private def dx (r : Fin 16) (i j : Fin 6) := val (first i) r-val (first j) r
private def dy (r : Fin 16) (i j : Fin 6) := val (second j) r-val (second i) r
/-- A neighboring edge lies in one of the owner's two faces. The opposite
edge gives the third class of possible directions. -/
private def face : Fin 6 → Fin 6 → Fin 3 :=
  ![![0, 0, 1, 0, 1, 2], ![0, 0, 1, 0, 2, 1], ![0, 1, 0, 2, 0, 1], ![0, 0, 2, 0, 1, 1], ![0, 2, 0, 1, 0, 1], ![2, 0, 0, 1, 1, 0]]

private theorem face_det : ∀ (r : Fin 16) (i j k : Fin 6), i ≠ j → i ≠ k → j ≠ k →
    face i j = face i k → dx r i j*dy r i k = dx r i k*dy r i j := by decide

/-- At an owned point, the six edges supply at most three finite foreign
directions. Multiple owners can occur only at one of the four vertex fibers. -/
theorem owned_limits (r : Fin 16) (i : Fin 6) :
    ((univ.filter fun j : Fin 6 =>
      val (first j) r = val (first i) r ∧ val (second j) r = val (second i) r).card ≤
      if r.val % 8 < 4 then 3 else 1) ∧
    (((univ.filter fun j : Fin 6 => dy r i j ≠ 0).image fun j => dx r i j / dy r i j).card ≤ 3) := by
  constructor
  · exact (by decide : ∀ (r : Fin 16) (i : Fin 6),
      (univ.filter fun j : Fin 6 => val (first j) r = val (first i) r ∧
        val (second j) r = val (second i) r).card ≤ if r.val % 8 < 4 then 3 else 1) r i
  · classical
    let S := univ.filter fun j : Fin 6 => dy r i j ≠ 0
    let slope (j : Fin 6) := dx r i j / dy r i j
    let pick (e : Fin 3) : F :=
      if h : ∃ j ∈ S, face i j = e then slope h.choose else 0
    suffices h : S.image slope ⊆ (univ : Finset (Fin 3)).image pick from
      (card_le_card h).trans (card_image_le.trans (by simp))
    intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    have he : ∃ k ∈ S, face i k = face i j := ⟨j,hj,rfl⟩
    refine mem_image.mpr ⟨face i j, mem_univ _, ?_⟩
    simp only [pick, dite_eq_left he]
    have hk := he.choose_spec
    have hdj := (mem_filter.mp hj).2
    have hdk := (mem_filter.mp hk.1).2
    by_cases hkj : he.choose = j
    · rw [hkj]
    apply (div_eq_div_iff hdk hdj).mpr
    apply face_det _ _ _ _ _ _ hkj hk.2
    · rintro h
      exact hdk (by rw [← h]; simp [dy])
    · rintro h
      exact hdj (by rw [← h]; simp [dy])

/-- The slot counts at roots, vertex fibers and owned ordinary sites place a
sharp bound on the smallest active core of any over-budget six-edge allocation. -/
theorem allocation_limit {r a o c l : ℕ} (hr : r ≤ 402653182) (ha : a ≤ 536870912)
    (hcores : 6*c ≤ 6*r+2*a+o) (hlabels : l+3*o+6*r ≤ 6*1073741824)
    (hbudget : 2147483648 < l) : c ≤ 686001719 := by omega

private def cut : Fin 16 → ℕ :=
  ![0, 0, 0, 0, 52195782, 52195782, 52195782, 52195783, 0, 0, 0, 0, 52195783, 52195783, 22369623, 67108864]
private theorem cut_le : ∀ j, cut j ≤ S := by decide

private abbrev roots := SixteenFiberMass.roots S cut
private abbrev core := SixteenFiberMass.core S cut group
private abbrev fresh := SixteenFiberMass.fresh S cut labels

private theorem root_count : roots.card = 402653182 := by
  rw [roots, SixteenFiberMass.card_roots S cut cut_le]; decide
private theorem core_count (j : Fin 6) : (core j).card = (![686001720, 686001720, 686001720, 686001719, 686001719, 686001719] : Fin 6 → ℕ) j := by
  rw [core, SixteenFiberMass.card_core S cut group cut_le]; fin_cases j <;> decide
private theorem fresh_count (j : Fin 6) : (fresh j).card = (![387740104, 372827023, 357913942, 357913941, 343000860, 328087779] : Fin 6 → ℕ) j := by
  rw [fresh, SixteenFiberMass.fresh, SixteenFiberMass.card_selected S cut cut_le]; fin_cases j <;> decide

/-- All selected foreign directions produce distinct actual bad scalars for
one pair at every indicated dimension and positive width. -/
theorem label_mass {k : ℕ} (hk : 536870912 ≤ k) (hc : k ≤ 686001719) (width : ℕ) [NeZero width] :
    (2147483649:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (387740104/1073741824) := by
  have counts : (∑ i, (fresh i).card) = 2147483649 := by
    simp only [fresh_count, Fin.sum_univ_succ]; decide
  have least (i : Fin 6) : 686001719 ≤ (core i).card := by rw [core_count]; fin_cases i <;> decide
  rw [epsMCA_interleaved_eq]
  have h := SixteenFiberMass.selected_mass S cut group dom k D (387740104/1073741824)
    (fun i => lift (first i)) (fun i => lift (second i)) (fun i => val (first i)) (fun i => val (second i))
    u v labels (fun i x => lifted (first i) x) (fun i x => lifted (second i) x)
    agrees misses determinant
    (by rw [show (SixteenFiberMass.roots S cut).card = 402653182 from root_count]; dsimp [D]; omega)
    (fun i => deg _) (fun i => deg _) (fun i => hc.trans (least i)) (by
      intro i
      rw [Fintype.card_fin]
      apply le_trans (b:=((686001719+1:ℕ):ℝ≥0))
      · rw [tsub_mul,one_mul]; norm_num [N,tsub_le_iff_right]
      · exact_mod_cast Nat.add_le_add_right (least i) 1)
    (by rw [counts,Nat.card_eq_fintype_card,ZMod.card,Nat.choose_two_right]; decide)
  rw [counts, ZMod.card] at h
  simpa only [Nat.cast_ofNat] using h

/-- At half rate, the second named smooth domain exceeds its budget one
scalar above the allowed count at 387740104 errors. -/
theorem half (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 536870912 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128
    tol < epsMCA (F:=F) code (387740104/1073741824) ∧
      mcaDeltaStar (F:=F) code tol ≤ 387740104/1073741824 := by
  dsimp only
  have hb : 1/(2:ℝ≥0∞)^128 < (2147483649:ℝ≥0∞)/(P:ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h : ((2147483649:ℕ):ℝ≥0∞)/P ≤ 1/((2^128:ℕ):ℝ≥0∞))
    exact (by decide : ¬ 2147483649 ≤ P/2^128) hh
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad,mcaDeltaStar_le_of_bad _ _ bad⟩

namespace FiveVertices

private def edges : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
private def A (i : Fin 10) := secantFirst (z ^ (edges i).1.val) (z ^ (edges i).2.val)
private def B (i : Fin 10) := secantSecond (z ^ (edges i).1.val) (z ^ (edges i).2.val)
private def incident (j : Fin 16) : Finset (Fin 10) :=
  univ.filter fun i => (edges i).1.val = j.val % 8 ∨ (edges i).2.val = j.val % 8
private def foreign (j : Fin 16) : Finset (Fin 10) := univ \ incident j
private def pivot : Fin 8 → Fin 10 := ![0,0,1,2,3,0,0,0]
private def center (f : Fin 10 → Fin 2 → F) (outside : F) (j : Fin 16) :=
  if j.val % 8 < 5 then val (f (pivot ⟨j.val % 8, by omega⟩)) j else outside
private abbrev firstCenter := center A 17
private abbrev secondCenter := center B 29

private theorem hits : ∀ j i, i ∈ incident j →
    val (A i) j = firstCenter j ∧ val (B i) j = secondCenter j := by decide
private theorem nonzero : ∀ j i, i ∈ foreign j → val (B i) j ≠ secondCenter j := by decide
private theorem different : ∀ r i j, i ∈ foreign r → j ∈ foreign r → i ≠ j →
    (firstCenter r-val (A i) r)*(val (B j) r-secondCenter r) ≠
      (firstCenter r-val (A j) r)*(val (B i) r-secondCenter r) := by decide

/-- The five vertex fibers are intact. The other three fibers consist of
common roots except for two off-head sites in the first remaining block. -/
private def common (j : Fin 16) : ℕ :=
  if j.val % 8 < 5 then 0 else if j.val = 5 then S-2 else S
private theorem common_le : ∀ j, common j ≤ S := by decide

private theorem common_count : (SixteenFiberMass.roots S common).card = 402653182 := by
  rw [SixteenFiberMass.card_roots S common common_le]; decide
private theorem joint_count (i : Fin 10) : (SixteenFiberMass.core S common incident i).card = 671088638 := by
  rw [SixteenFiberMass.card_core S common incident common_le]; fin_cases i <;> decide
private theorem foreign_count (i : Fin 10) : (SixteenFiberMass.fresh S common foreign i).card = 402653186 := by
  rw [SixteenFiberMass.fresh, SixteenFiberMass.card_selected S common common_le]; fin_cases i <;> decide

/-- All ten secants on five vertices attain every available one-fresh label
at 402653185 errors. The bound holds for all indicated dimensions and widths. -/
theorem label_mass {k : ℕ} (hk : 536870912 ≤ k) (hc : k ≤ 671088638) (width : ℕ) [NeZero width] :
    (4026531860:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (402653185/1073741824) := by
  have counts : (∑ i, (SixteenFiberMass.fresh S common foreign i).card) = 4026531860 := by
    simp [foreign_count]
  rw [epsMCA_interleaved_eq]
  have h := SixteenFiberMass.selected_mass S common incident dom k D (402653185/1073741824)
    (fun i => lift (A i)) (fun i => lift (B i)) (fun i => val (A i)) (fun i => val (B i))
    firstCenter secondCenter foreign (fun i x => lifted (A i) x) (fun i x => lifted (B i) x)
    hits nonzero different (by rw [common_count]; dsimp [D]; omega)
    (fun i => deg _) (fun i => deg _) (fun i => (joint_count i).symm ▸ hc) (by
      intro i
      rw [Fintype.card_fin, joint_count]
      norm_num [N,tsub_mul,tsub_le_iff_right])
    (by rw [counts,Nat.card_eq_fintype_card,ZMod.card,Nat.choose_two_right]; decide)
  rw [counts, ZMod.card] at h
  simpa only [Nat.cast_ofNat] using h

#print axioms label_mass
end FiveVertices

#print axioms allocation_limit
#print axioms owned_limits
#print axioms label_mass
#print axioms half
end ArkLib.ProximityGap.Frontier.SecondPrimeTetrahedron
