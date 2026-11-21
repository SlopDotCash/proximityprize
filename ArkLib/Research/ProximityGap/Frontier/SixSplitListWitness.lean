/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SixSplitPencil
import ArkLib.Research.ProximityGap.Frontier.ReciprocalFiberLists
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.LinearAlgebra.Lagrange

/-! # Fifteen simultaneously split pairwise differences on a smooth evaluation domain

A common locator reserves part of the unused power fibers. Three four-fiber heads
split the remaining sites, while the three five-fiber heads already meet the radius.
-/
namespace ProximityGap.SixSplitListWitness

open Finset Polynomial SixSplitPencil
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I] [DecidableEq F]

private def unused : Finset (Fin 16) := {6, 13, 14}
private def weak : Finset (Fin 6) := {1, 4, 5}

private def incident : Fin 6 → Finset (Fin 16) :=
  ![{0,1,3,7,8}, {0,2,4,9}, {1,2,5,11,10}, {3,4,5,15,12}, {7,9,11,15}, {8,9,10,12}]

private def owner : Fin 16 → Fin 6 := ![0,0,1,0,1,2,0,0,0,1,2,2,3,0,0,3]

/-- Union of the fibers selected by a set of labels. -/
def sitesOn (π : I → Fin 16) (s : Finset (Fin 16)) := univ.filter fun i => π i ∈ s

omit [DecidableEq I] in
/-- Equal power fibers contribute their full size for each selected label. -/
theorem sitesOn_card {π : I → Fin 16} {d : ℕ}
    (hf : ∀ j, (univ.filter fun i => π i = j).card = d) (s : Finset (Fin 16)) :
    (sitesOn π s).card = s.card*d := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := sitesOn π s) (f := π) (t := s) (fun _ h => (mem_filter.mp h).2)]
  have he (j : Fin 16) (hj : j ∈ s) :
      ((sitesOn π s).filter fun i => π i = j) = univ.filter fun i => π i = j := by
    ext i
    simp only [sitesOn, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    exact fun h => h ▸ hj
  simp_rw [sum_congr rfl (fun j hj => (congrArg Finset.card (he j hj)).trans (hf j))]
  simp

/-- Given equal sixteenth-root fibers of a polynomial of degree at most d,
produce six distinct RS words and a center. Each pair agrees with that center
on exactly 2d−1 sites. At the production d all six words reach 380,283,562 sites. -/
theorem on_fibers (D : I ↪ F) {d : ℕ} (hd : 0 < d) (π : I → Fin 16)
    (hf : ∀ j, (univ.filter fun i => π i = j).card = d) (Y : F[X]) (hy : Y.natDegree ≤ d)
    {z : F} (hz : IsPrimitiveRoot z 16) (hY : ∀ i, Y.eval (D i) = z^(π i).val) :
    ∃ (w : Fin 6 ↪ (I → F)) (center : I → F),
      (∀ j, w j ∈ (ReedSolomon.code D (2*d) : Set (I → F))) ∧
      (∀ j, 5*d-1+(2*d+1)/3 ≤ (univ.filter fun i => center i = w j i).card) ∧
      ∀ j l, j ≠ l →
        (univ.filter fun i => center i = w j i ∧ center i = w l i).card = 2*d-1 := by
  classical
  let pool := sitesOn π unused
  have hpool : pool.card = 3*d := (sitesOn_card hf unused).trans (by rfl)
  obtain ⟨common, hcommon, hc⟩ := Finset.exists_subset_card_eq
    (show d-1 ≤ pool.card by rw [hpool]; omega)
  let spare := pool \ common
  have hspare : spare.card = 2*d+1 := by
    rw [Finset.card_sdiff_of_subset hcommon, hpool, hc]
    omega
  let P := Lagrange.nodal common D
  have hP (i : I) : P.eval (D i) = 0 ↔ i ∈ common := by
    simp [P, Lagrange.eval_nodal, Finset.prod_eq_zero_iff, sub_eq_zero, D.injective.eq_iff]
  let message (j : Fin 6) : F[X] := P*(C (v z j)-C (u z j)*Y)
  let w (j : Fin 6) (i : I) : F := (message j).eval (D i)
  have hdeg (j : Fin 6) : (message j).natDegree < 2*d := by
    have ha : (C (u z j)*Y).natDegree ≤ d := (natDegree_C_mul_le _ _).trans hy
    have hb : (C (v z j)-C (u z j)*Y).natDegree ≤ d :=
      (natDegree_sub_le _ _).trans (max_le (by simp) ha)
    have hp : P.natDegree = d-1 := Lagrange.natDegree_nodal.trans hc
    exact (natDegree_mul_le.trans (Nat.add_le_add (Nat.le_of_eq hp) hb)).trans_lt (by omega)
  have heq (j l : Fin 6) (hjl : j ≠ l) (i : I) :
      w j i = w l i ↔ i ∈ common ∨ π i = fiber j l := by
    simp only [w, message, eval_mul, eval_sub, eval_C, hY, mul_eq_mul_left_iff,
      SixSplitPencil.agree_iff hz hjl, hP]
    rw [show (z^(π i).val = z^(fiber j l).val) ↔ π i = fiber j l from
      ⟨fun h => Fin.ext (hz.pow_inj (π i).isLt (fiber j l).isLt h), fun h => by rw [h]⟩]
    tauto
  have hother {j l : Fin 6} (hne : j ≠ l) : fiber j l ∉ unused :=
    (by decide : ∀ j l : Fin 6, j ≠ l → fiber j l ∉ unused) j l hne
  have hdis (j : Fin 6) : Disjoint pool (sitesOn π (incident j)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (by decide : ∀ j : Fin 6, ∀ b ∈ unused, b ∉ incident j) j (π i)
      (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have hits (j : Fin 6) {i : I} (hi : i ∈ sitesOn π (incident j)) :
      w (owner (π i)) i = w j i := by
    have hm := (mem_filter.mp hi).2
    have hk := (by decide : ∀ j : Fin 6, ∀ b ∈ incident j,
      owner b = j ∨ b = fiber (owner b) j) j (π i) hm
    rcases hk with hk|hk
    · rw [hk]
    by_cases hn : owner (π i) = j
    · rw [hn]
    exact (heq _ _ hn _).2 (Or.inr hk)
  obtain ⟨center, outside, extra⟩ := ReciprocalFiberLists.split_fiber spare weak ((2*d+1)/3)
    (fun i => w (owner (π i)) i) w (by rw [hspare]; change 3*((2*d+1)/3) ≤ _; omega)
  have onCommon (i : I) (hi : i ∈ common) (j : Fin 6) : center i = w j i := by
    rw [outside i (fun h => (mem_sdiff.mp h).2 hi)]
    simp only [w, message, eval_mul, (hP i).2 hi, zero_mul]
  have onIncident (j : Fin 6) {i : I} (hi : i ∈ sitesOn π (incident j)) : center i = w j i := by
    rw [outside i (fun h => disjoint_left.mp (hdis j) (mem_sdiff.mp h).1 hi)]
    exact hits j hi
  have pair (j l : Fin 6) (hne : j ≠ l) :
      (univ.filter fun i => center i = w j i ∧ center i = w l i) =
        common ∪ (univ.filter fun i => π i = fiber j l) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨hj,hl⟩
      exact (heq j l hne i).mp (hj.symm.trans hl)
    · rintro (hi|hi)
      · exact ⟨onCommon i hi j, onCommon i hi l⟩
      have hpair := (by decide : ∀ j l : Fin 6, j ≠ l →
        fiber j l ∈ incident j ∧ fiber j l ∈ incident l) j l hne
      exact ⟨onIncident j (mem_filter.mpr ⟨mem_univ _,hi ▸ hpair.1⟩),
        onIncident l (mem_filter.mpr ⟨mem_univ _,hi ▸ hpair.2⟩)⟩
  have inj : Function.Injective w := by
    intro j l hh
    by_contra hne
    obtain ⟨i', hi'⟩ := card_pos.mp (hd.trans_eq (hf (if fiber j l = 0 then 1 else 0)).symm)
    have hlabel := (mem_filter.mp hi').2
    rcases (heq j l hne i').mp (congrFun hh i') with h|h
    · have : π i' ∈ unused := (mem_filter.mp (hcommon h)).2
      rw [hlabel] at this
      split at this
      · exact (by decide : (1 : Fin 16) ∉ unused) this
      · exact (by decide : (0 : Fin 16) ∉ unused) this
    · rw [hlabel] at h
      split at h <;> omega
  refine ⟨⟨w,inj⟩, center, fun j =>
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ (hdeg j) (fun _ => rfl), ?_, ?_⟩
  · intro j
    let base := common ∪ sitesOn π (incident j)
    have dis : Disjoint common (sitesOn π (incident j)) := (hdis j).mono_left hcommon
    have hbase : base.card = d-1+(incident j).card*d := by
      rw [Finset.card_union_of_disjoint dis, hc, sitesOn_card hf]
    let agree := univ.filter fun i => center i = w j i
    have sub : base ⊆ agree := by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _, (mem_union.mp hi).elim (fun h => onCommon i h j)
        (onIncident j)⟩
    change _ ≤ agree.card
    by_cases hj : j ∈ weak
    · have h4 := (by decide : ∀ j ∈ weak, (incident j).card = 4) j hj
      let more := spare.filter fun i => center i = w j i
      have hm : (2*d+1)/3 ≤ more.card := extra j hj
      have dis' : Disjoint base more := by
        apply disjoint_left.mpr
        intro i hb hm
        have hi := mem_sdiff.mp (mem_filter.mp hm).1
        exact (mem_union.mp hb).elim hi.2 (fun h => disjoint_left.mp (hdis j) hi.1 h)
      have le := card_le_card (Finset.union_subset sub (show more ⊆ agree from
        fun i h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩))
      rw [card_union_of_disjoint dis', hbase, h4] at le
      omega
    · have h5 := (by decide : ∀ j : Fin 6, j ∉ weak → (incident j).card = 5) j hj
      have le := card_le_card sub
      rw [hbase,h5] at le
      omega
  · intro j l hne
    change (univ.filter fun i => center i = w j i ∧ center i = w l i).card = _
    rw [pair j l hne, card_union_of_disjoint, hc, hf]
    · omega
    apply disjoint_left.mpr
    intro i hi hj
    exact hother hne ((mem_filter.mp hj).2 ▸ (mem_filter.mp (hcommon hi)).2)

section Smooth
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
  [Nonempty I]

/-- A scaled power polynomial on a size-16d smooth coset has d sites on each of the
sixteen root-of-unity fibers. -/
theorem exists_coordinates (D : I ↪ F) [ReedSolomon.Smooth D] {d : ℕ} (hd : 0 < d)
    (hn : Fintype.card I = d*16) :
    ∃ (π : I → Fin 16) (Y : F[X]) (z : F),
      (∀ j, (univ.filter fun i => π i = j).card = d) ∧ Y.natDegree ≤ d ∧
      IsPrimitiveRoot z 16 ∧ ∀ i, Y.eval (D i) = z^(π i).val := by
  classical
  obtain ⟨V,hV,hmem,hfib,⟨sm⟩,-⟩ := SmoothPowerMcaDescent.exists_smooth_base D hd hn
    (show ∃ b : ℕ, 16 = 2^b from ⟨4,rfl⟩)
  let E := Function.Embedding.subtype (· ∈ V)
  let H := ReedSolomon.Smooth.H E
  let a := ReedSolomon.Smooth.a E
  obtain ⟨coord, he⟩ := SmoothDomainMcaEquivalence.coset_equiv E
  let : Fintype H := Fintype.ofFinite H
  have hcard : Fintype.card H = 16 := (Fintype.card_congr coord).symm.trans
    ((Fintype.card_coe V).trans hV)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have horder : orderOf u = 16 := hu.trans (Nat.card_eq_fintype_card.trans hcard)
  let z : F := ((u : Fˣ) : F)
  have hz : IsPrimitiveRoot z 16 := IsPrimitiveRoot.coe_units_iff.mpr <|
    IsPrimitiveRoot.coe_submonoidClass_iff.mpr (horder ▸ IsPrimitiveRoot.orderOf u)
  let powers (j : Fin 16) : H := u^j.val
  have hpow : Function.Injective powers := by
    intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf (x := u) (by change i.val < orderOf u; simp [horder])
      (by change j.val < orderOf u; simp [horder]) hij)
  let e := Equiv.ofBijective powers ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hpow, by rw [Fintype.card_fin, hcard]⟩)
  let index (i : I) : V := ⟨D i ^ d, hmem i⟩
  let π (i : I) := e.symm (coord (index i))
  have hf (j : Fin 16) : (univ.filter fun i => π i = j).card = d := by
    let α := coord.symm (e j)
    have heq : (univ.filter fun i => π i = j) = (univ.filter fun i => D i ^ d = α.val) := by
      ext i
      simp only [mem_filter,mem_univ,true_and]
      change e.symm (coord (index i)) = j ↔ (index i).val = α.val
      rw [← Subtype.ext_iff, Equiv.symm_apply_eq, ← Equiv.eq_symm_apply]
    rw [heq]
    exact hfib α α.property
  let Y : F[X] := C (↑a⁻¹ : F) * X^d
  have hY (i : I) : Y.eval (D i) = z^(π i).val := by
    have heq : coord (index i) = u^(π i).val := (e.apply_symm_apply (coord (index i))).symm
    have h := he (index i)
    change D i ^ d = (a : F) * ((coord (index i) : Fˣ) : F) at h
    simp only [Y,eval_mul,eval_C,eval_pow,eval_X,h,← mul_assoc,Units.inv_mul,one_mul,heq]
    rfl
  exact ⟨π,Y,z,hf,(natDegree_C_mul_le _ _).trans (by simp),hz,hY⟩

/-- Every smooth coset of size 16d supplies the equal fibers needed by the construction. -/
theorem smooth (D : I ↪ F) [ReedSolomon.Smooth D] {d : ℕ} (hd : 0 < d)
    (hn : Fintype.card I = d*16) :
    ∃ (w : Fin 6 ↪ (I → F)) (center : I → F),
      (∀ j, w j ∈ (ReedSolomon.code D (2*d) : Set (I → F))) ∧
      (∀ j, 5*d-1+(2*d+1)/3 ≤ (univ.filter fun i => center i = w j i).card) ∧
      ∀ j l, j ≠ l →
        (univ.filter fun i => center i = w j i ∧ center i = w l i).card = 2*d-1 := by
  obtain ⟨π,Y,z,hf,hy,hz,hY⟩ := exists_coordinates D hd hn
  exact on_fibers D hd π hf Y hy hz hY

/-- At the rate-one-eighth production length the six fully saturated words belong to
one actual list at 693,458,262 errors on every smooth domain. -/
theorem production (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824) :
    6 ≤ Code.Lambda (ReedSolomon.code D 134217728 : Set (I → F)) (693458262 / 1073741824) := by
  classical
  obtain ⟨w,y,hmem,hagree,-⟩ := smooth D (d := 67108864) (by decide) hn
  have h (j : Fin 6) : 380283562 ≤ Code.agree (w j) y := by
    simpa only [Code.agree, eq_comm] using hagree j
  have hh := Code.encard_setOf_le_agree_encode_le_Lambda
    (ReedSolomon.code D 134217728 : Set (I → F)) y 380283562 (S := Set.univ)
    w.injective.injOn (fun j _ => hmem j)
  rw [show {j : Fin 6 | j ∈ (Set.univ : Set (Fin 6)) ∧ 380283562 ≤ Code.agree (w j) y} =
    Set.univ by ext j; simp [h j], hn] at hh
  norm_num at hh ⊢
  exact hh

end Smooth

#print axioms on_fibers
#print axioms smooth
#print axioms production

end ProximityGap.SixSplitListWitness
