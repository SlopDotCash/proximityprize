/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralOverlapPacking
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Two-core scalar packing up to the entire field

A pole at a leftover site lets the first challenges use every field label associated with
the evaluation domain. Additional challenges outside that set extend the construction
as far as the field cardinality permits.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.OptimalOverlapPacking
open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal ENNReal
open HalfPredecessorCoreFreshDecode

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

private theorem small_of_rotate_fixed {n : ℕ} (i : Fin n) (h : finRotate n i = i) :
    n ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    split at hv
    · rename_i hi
      subst i
      simp only [Fin.val_last] at hv
      omega
    · omega

private theorem rotating {J : Type*} [Fintype J] (j₀ : J) :
    ∃ π : Equiv.Perm J, ∀ j, π j = j → j = j₀ := by
  classical
  let f := Fintype.equivFin J
  let π := (f.trans (finRotate _)).trans f.symm
  refine ⟨π,fun j hj ↦ ?_⟩
  have hh : finRotate _ (f j) = f j := by simpa [π] using congrArg f hj
  let : Subsingleton J := Fintype.card_le_one_iff_subsingleton.mp (small_of_rotate_fixed _ hh)
  exact Subsingleton.elim _ _

/-- Every finite field and evaluation embedding admit at least the smaller of the field
size and $2(e+1)$ bad scalars on a common stack. -/
theorem errors (dom : I ↪ F) (k e : ℕ) (hk : 2 ≤ k)
    (hhalf : Fintype.card I ≤ 2*(e+1)) (hcap : e+k+1 ≤ Fintype.card I) :
    ((min (Fintype.card F) (2*(e+1)) : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) ((e:ℝ≥0)/Fintype.card I) := by
  classical
  let n := Fintype.card I
  let q := Fintype.card F
  have hnq : n ≤ q := Fintype.card_le_of_injective dom dom.injective
  by_cases hfull : 2*(e+1) ≤ n
  · rw [min_eq_right (hfull.trans hnq)]
    exact GeneralOverlapPacking.errors dom k e hk hhalf hcap (by dsimp [n,q] at *; omega)
  let t := n-e-1
  let c := 2*(e+1)-n
  have hc : 0 < c := by dsimp [c]; omega
  have hn : 0 < n := Fintype.card_pos
  have ht : k ≤ t := by dsimp [t,n]; omega
  have h2 : 2*t ≤ n := by dsimp [t,n]; omega
  obtain ⟨A,_,hA⟩ := exists_subset_card_eq (s := (univ : Finset I))
    (show t ≤ univ.card by rw [card_univ]; omega)
  obtain ⟨B,hBA,hB⟩ := exists_subset_card_eq (s := Aᶜ)
    (show t ≤ Aᶜ.card by rw [card_compl,hA]; omega)
  have hd : Disjoint A B := disjoint_left.mpr fun i hi hj ↦ (mem_compl.mp (hBA hj)) hi
  let T := (A ∪ B)ᶜ
  have hT : T.card = c := by
    dsimp only [T]
    rw [card_compl,card_union_of_disjoint hd,hA,hB]
    dsimp [c,t,n] at *; omega
  obtain ⟨pole,hpole⟩ := card_pos.mp (hT ▸ hc)
  obtain ⟨π,hπ⟩ := rotating (⟨pole,hpole⟩ : ↥T)
  let v (i : I) := dom i - dom pole
  let lab (i : I) := -(v i)⁻¹
  have hinj : Function.Injective lab := fun i j hij ↦
    dom.injective (sub_left_inj.mp (inv_injective (neg_injective hij)))
  have unit (i : I) (hi : i ≠ pole) : v i ≠ 0 :=
    sub_ne_zero.mpr fun hh ↦ hi (dom.injective hh)
  have intersect (i : I) (hi : i ≠ pole) : lab i * v i = -1 := by
    dsimp only [lab]; rw [neg_mul, inv_mul_cancel₀ (unit i hi)]
  have apart (i : I) (a : F) (ha : i = pole ∨ a ≠ lab i) : 1 + a*v i ≠ 0 := by
    by_cases hh : i = pole
    · subst i; simp [v]
    · intro he
      apply ha.resolve_left hh
      apply mul_right_cancel₀ (unit i hh)
      rw [intersect i hh]; linear_combination he
  let first (i : ↥T) := lab (π i)
  have along (i : ↥T) : 1+first i * v i ≠ 0 := by
    apply apart
    by_cases hh : i.val = pole
    · exact Or.inl hh
    · exact Or.inr fun he ↦ hh (congrArg Subtype.val (hπ i (Subtype.ext (hinj he))))
  let base := univ.image lab
  have hbase : base.card = n := by dsimp only [base]; rw [card_image_of_injective _ hinj,card_univ]
  obtain ⟨T',hT',ht'⟩ := exists_subset_card_eq (s := T) (n := min c (q-n))
    (by rw [hT]; exact min_le_left _ _)
  obtain ⟨fresh,hfresh⟩ := Function.Embedding.exists_of_card_le_finset (s := baseᶜ)
    (show Fintype.card ↥T' ≤ baseᶜ.card by
      rw [Fintype.card_coe,ht',card_compl,hbase]; exact min_le_right _ _)
  have off (i : ↥T') (j : I) : fresh i ≠ lab j := by
    intro he
    exact (mem_compl.mp (hfresh ⟨i,rfl⟩)) (mem_image.mpr ⟨j,mem_univ _,he.symm⟩)
  let incl (i : ↥T') : ↥T := ⟨i,hT' i.2⟩
  let d (i : ↥T') := (1+fresh i*v i)/(fresh i - first (incl i))
  have denom (i : ↥T') : fresh i - first (incl i) ≠ 0 := sub_ne_zero.mpr (off i _)
  have eqd (i : ↥T') : (fresh i - first (incl i))*d i = 1+fresh i*v i := by
    dsimp only [d]; field_simp [denom i]
  let slope (i : ↥T) := if h : i.val ∈ T' then d ⟨i.val,h⟩ else 1
  have hsel (i : ↥T') : slope (incl i) = d i := by simp [slope,incl,i.2]
  have hs0 (i : ↥T) : slope i ≠ 0 := by
    dsimp only [slope]
    split
    · exact div_ne_zero (apart i _ (Or.inr (off _ _))) (denom _)
    · exact one_ne_zero
  let point (i : I) : F × F :=
    if h : i∈T then (-first ⟨i,h⟩*slope ⟨i,h⟩, slope ⟨i,h⟩)
    else if i∈A then (0,0) else (1,v i)
  let rows : WordStack F (Fin 2) I := ![fun i ↦ (point i).1,fun i ↦ (point i).2]
  have valA (i : I) (hi : i∈A) : point i = (0,0) := by
    have hh : i∉T := fun h ↦ (mem_compl.mp h) (mem_union_left _ hi)
    simp [point,hi,hh]
  have valB (i : I) (hi : i∈B) : point i = (1,v i) := by
    have hh : i∉T := fun h ↦ (mem_compl.mp h) (mem_union_right _ hi)
    simp [point,hh,mem_compl.mp (hBA hi)]
  have valT (i : ↥T) : point i = (-first i * slope i,slope i) := by simp [point,i.2]
  let δ := (e:ℝ≥0)/n
  have size : (1-δ)*(Fintype.card I:ℝ≥0) = ((t+1 : ℕ):ℝ≥0) := by
    have hn' : (n:ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have ht0 : t+1=n-e := by dsimp [t,n]; omega
    dsimp only [δ]
    rw [ht0,Nat.cast_tsub,show (Fintype.card I:ℝ≥0)=(n:ℝ≥0) from rfl,
      tsub_mul,one_mul,div_mul_cancel₀ _ hn']
  let event := mcaEvent (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ (rows 0) (rows 1)
  have h0 : (0:F[X]).degree < (k:WithBot ℕ) := by simp
  have h1 : (1:F[X]).degree < (k:WithBot ℕ) := by simpa using (show 0 < k by omega)
  let Q : F[X] := X - C (dom pole)
  have hQ : Q.degree < (k:WithBot ℕ) := by
    simpa [Q] using (show 1 < k by omega)
  have evQ (i : I) : Q.eval (dom i) = v i := by simp [Q,v]
  have atA (i : I) (hi : i∉A) (a : F)
      (hs : (point i).1 + a*(point i).2 = 0) (hm : (point i) ≠ (0,0)) : event a := by
    apply mcaEvent_of_affine_core_fresh dom k δ rows a A i 0 0 hi h0 h0
    · simp
    · omega
    · rw [size,hA]
    · intro j hj; simp [rows,valA j hj]
    · simpa [rows] using hs.symm
    · simpa [rows,ne_comm] using hm
  have atB (i : I) (hi : i∉B) (a : F)
      (hs : (point i).1 + a*(point i).2 = 1+a*v i) (hm : (point i) ≠ (1,v i)) : event a := by
    apply mcaEvent_of_affine_core_fresh dom k δ rows a B i 1 Q hi h1 hQ
    · by_cases ha : a=0
      · simpa [ha] using h1
      · exact (degree_add_le _ _).trans_lt (max_lt h1 (by simpa [degree_C_mul ha] using hQ))
    · omega
    · rw [size,hB]
    · intro j hj; simp [rows,valB j hj,evQ]
    · simpa [rows,evQ] using hs.symm
    · simpa [rows,evQ,ne_comm] using hm
  have every (i : I) : event (lab i) := by
    by_cases ha : i∈A
    · have hi : i ≠ pole := fun he ↦ (mem_compl.mp hpole) (mem_union_left _ (he ▸ ha))
      apply atB i (fun h ↦ disjoint_left.mp hd ha h)
      · simp [valA i ha,intersect i hi]
      · simp [valA i ha]
    by_cases hb : i∈B
    · have hi : i ≠ pole := fun he ↦ (mem_compl.mp hpole) (mem_union_right _ (he ▸ hb))
      apply atA i ha
      · simp [valB i hb,intersect i hi]
      · simp [valB i hb]
    have hi : i∈T := mem_compl.mpr (fun h ↦ (mem_union.mp h).elim ha hb)
    let j := π.symm ⟨i,hi⟩
    have hj : first j = lab i := by simp [first,j]
    rw [←hj]
    apply atA j (fun h ↦ (mem_compl.mp j.2) (mem_union_left _ h))
    · rw [valT]; dsimp; ring
    · intro he; apply hs0 j; simpa [valT] using congrArg Prod.snd he
  have extra (i : ↥T') : event (fresh i) := by
    let j := incl i
    have hi : i.val∉B := fun h ↦ (mem_compl.mp j.2) (mem_union_right _ h)
    have he := eqd i
    have hj : point i = (-first j * d i,d i) := by rw [←hsel]; exact valT j
    apply atB i hi
    · rw [hj]; dsimp only; linear_combination he
    · intro hx
      have hs : d i = v i := by simpa [hj] using congrArg Prod.snd hx
      apply along j
      rw [hs] at he
      dsimp only [j,incl] at *
      linear_combination -he
  let V := univ.image fresh
  have hdis : Disjoint base V := by
    apply disjoint_left.mpr
    rintro g hg hj
    obtain ⟨j,_,rfl⟩ := mem_image.mp hg
    obtain ⟨i,_,he⟩ := mem_image.mp hj
    exact off i j he
  have hcard : (base ∪ V).card = min q (2*(e+1)) := by
    rw [card_union_of_disjoint hdis,hbase,show V.card=T'.card by
      dsimp only [V]; rw [card_image_of_injective _ fresh.injective,card_univ,Fintype.card_coe],ht']
    dsimp [c,n,q] at *; omega
  rw [← hcard]
  apply MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ rows
  intro g hg
  rcases mem_union.mp hg with h | h
  · obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact every i
  · obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact extra i

/-- When the field fits in the two-head count, the MCA failure probability equals one. -/
theorem epsMCA_eq_one (dom : I ↪ F) (k e : ℕ) (hk : 2 ≤ k)
    (hfield : Fintype.card F ≤ 2*(e+1)) (hcap : e+k+1 ≤ Fintype.card I) :
    epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F))
      ((e : ℝ≥0)/Fintype.card I) = 1 := by
  have hhalf := (Fintype.card_le_of_injective dom dom.injective).trans hfield
  have h := errors dom k e hk hhalf hcap
  have nz : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply le_antisymm (epsMCA_le_one _ _)
  simpa only [min_eq_left hfield, ENNReal.div_self nz (ENNReal.natCast_ne_top _)] using h

#print axioms errors
#print axioms epsMCA_eq_one

end ArkLib.ProximityGap.Frontier.OptimalOverlapPacking
