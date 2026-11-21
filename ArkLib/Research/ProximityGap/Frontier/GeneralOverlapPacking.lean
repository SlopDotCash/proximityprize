/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import Mathlib.Tactic

/-!
# Two disjoint agreement cores on an arbitrary evaluation domain

The two core pencils have rows $(0,0)$ and $(X,1)$. Each core site gives its own
challenge against the opposite pencil. Every remaining site supports two fresh
challenges, one for each pencil, by solving two scalar affine equations.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.GeneralOverlapPacking

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal ENNReal
open HalfPredecessorCoreFreshDecode

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- At integer error count $e$, arbitrary distinct evaluation points admit a single
stack witnessing $2(e+1)$ distinct bad challenges. -/
theorem errors (dom : I ↪ F) (k e : ℕ) (hk : 2 ≤ k)
    (hhalf : Fintype.card I ≤ 2*(e+1)) (hcap : e+k+1 ≤ Fintype.card I)
    (hsupply : Fintype.card I + 2*(2*(e+1)-Fintype.card I) ≤ Fintype.card F) :
    ((2*(e+1) : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F))
        ((e : ℝ≥0)/Fintype.card I) := by
  classical
  let n := Fintype.card I
  let t := n-e-1
  have hn : 0 < n := Fintype.card_pos
  have ht : k ≤ t := by dsimp [t,n]; omega
  have h2 : 2*t ≤ n := by dsimp [t,n]; omega
  obtain ⟨A,_,hA⟩ := exists_subset_card_eq (s := (univ : Finset I))
    (show t ≤ univ.card by rw [card_univ]; omega)
  obtain ⟨B,hBA,hB⟩ := exists_subset_card_eq (s := Aᶜ)
    (show t ≤ Aᶜ.card by rw [card_compl,hA]; omega)
  have hd : Disjoint A B := disjoint_left.mpr fun i hi hj ↦ (mem_compl.mp (hBA hj)) hi
  let T := (A ∪ B)ᶜ
  have hT : T.card = 2*(e+1)-n := by
    dsimp only [T]
    rw [card_compl, card_union_of_disjoint hd, hA, hB]
    dsimp [t,n] at *
    omega
  let forbidden := univ.image (fun i : I ↦ -dom i)
  have inj : Function.Injective (fun i : I ↦ -dom i) := fun _ _ h ↦ dom.injective (neg_injective h)
  have hforb : forbidden.card = n := by
    dsimp only [forbidden]; rw [card_image_of_injective _ inj,card_univ]
  obtain ⟨fresh,hfresh⟩ := Function.Embedding.exists_of_card_le_finset (s := forbiddenᶜ)
    (show Fintype.card (Fin 2 × ↥T) ≤ forbiddenᶜ.card by
      rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,hT,card_compl,hforb]
      dsimp [n] at *; omega)
  have off (a : Fin 2) (i : ↥T) (j : I) : fresh (a,i) ≠ -dom j := by
    intro he
    have hh := mem_compl.mp (hfresh ⟨(a,i),rfl⟩)
    exact hh (mem_image.mpr ⟨j,mem_univ _,he.symm⟩)
  have diff (i : ↥T) : fresh (1,i) - fresh (0,i) ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ (by decide : (1:Fin 2) ≠ 0) (congrArg Prod.fst (fresh.injective h))
  let slope (i : ↥T) := (dom i + fresh (1,i))/(fresh (1,i)-fresh (0,i))
  let point (i : I) : F × F :=
    if h : i ∈ T then (-fresh (0,⟨i,h⟩)*slope ⟨i,h⟩, slope ⟨i,h⟩)
    else if i ∈ A then (0,0) else (dom i,1)
  let rows : WordStack F (Fin 2) I := ![fun i ↦ (point i).1,fun i ↦ (point i).2]
  have valA (i : I) (hi : i ∈ A) : point i = (0,0) := by
    have hh : i ∉ T := fun h ↦ (mem_compl.mp h) (mem_union_left _ hi)
    simp [point,hi,hh]
  have valB (i : I) (hi : i ∈ B) : point i = (dom i,1) := by
    have hh : i ∉ T := fun h ↦ (mem_compl.mp h) (mem_union_right _ hi)
    simp [point,hh,mem_compl.mp (hBA hi)]
  let δ := (e:ℝ≥0)/n
  have size : (1-δ)*(Fintype.card I:ℝ≥0) = ((t+1 : ℕ):ℝ≥0) := by
    have he : e ≤ n := by dsimp [n]; omega
    have hn' : (n:ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have ht' : t+1=n-e := by dsimp [t,n]; omega
    dsimp only [δ]
    rw [ht',Nat.cast_tsub,show (Fintype.card I:ℝ≥0)=(n:ℝ≥0) from rfl,
      tsub_mul, one_mul, div_mul_cancel₀ _ hn']
  let event := mcaEvent (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ (rows 0) (rows 1)
  have h0 : (0:F[X]).degree < (k:WithBot ℕ) := by simp
  have h1 : (1:F[X]).degree < (k:WithBot ℕ) := by simpa using (show 0 < k by omega)
  have hX : (X:F[X]).degree < (k:WithBot ℕ) := by simpa using (show 1 < k by omega)
  have atA (i : I) (hi : i ∉ A) (a : F)
      (hs : (point i).1 + a*(point i).2 = 0) (hv : (point i).2 ≠ 0) : event a := by
    apply mcaEvent_of_affine_core_fresh dom k δ rows a A i 0 0 hi h0 h0
    · simp
    · omega
    · rw [size,hA]
    · intro j hj
      simp [rows,valA j hj]
    · simpa [rows] using hs.symm
    · intro he
      apply hv
      simpa [rows] using (congrArg Prod.snd he).symm
  have atB (i : I) (hi : i ∉ B) (a : F)
      (hs : (point i).1 + a*(point i).2 = dom i + a) (hv : (point i).2 ≠ 1) : event a := by
    apply mcaEvent_of_affine_core_fresh dom k δ rows a B i X 1 hi hX h1
    · simp only [mul_one, degree_X_add_C]
      exact_mod_cast (show 1 < k by omega)
    · omega
    · rw [size,hB]
    · intro j hj
      simp [rows,valB j hj]
    · simpa [rows] using hs.symm
    · intro he
      apply hv
      simpa [rows] using (congrArg Prod.snd he).symm
  have inside (i : I) (hi : i ∈ A ∪ B) : event (-dom i) := by
    rcases mem_union.mp hi with ha | hb
    · apply atB i (fun h ↦ disjoint_left.mp hd ha h) _ <;> simp [valA i ha]
    · apply atA i (mem_compl.mp (hBA hb)) _ <;> simp [valB i hb]
  have outside (a : Fin 2) (i : ↥T) : event (fresh (a,i)) := by
    have hab : i.val ∉ A ∪ B := mem_compl.mp i.2
    have hiA : i.val ∉ A := fun h ↦ hab (mem_union_left _ h)
    have hiB : i.val ∉ B := fun h ↦ hab (mem_union_right _ h)
    have hp : point i = (-fresh (0,i)*slope i,slope i) := by simp [point,i.2]
    have hs : (fresh (1,i)-fresh (0,i))*slope i = dom i + fresh (1,i) := by
      dsimp [slope]
      field_simp [diff i]
    fin_cases a
    · apply atA i hiA
      · rw [hp]; dsimp; ring
      · rw [hp]; dsimp only
        intro hz
        rw [hz,mul_zero] at hs
        have he : fresh (1,i) = -dom i := by linear_combination -hs
        exact off 1 i i he
    · apply atB i hiB
      · rw [hp]; dsimp; linear_combination hs
      · rw [hp]; dsimp only
        intro hz
        rw [hz,mul_one] at hs
        exact off 0 i i (by linear_combination -hs)
  let U := (A ∪ B).image (fun i ↦ -dom i)
  let V := univ.image fresh
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    rintro g hg hj
    obtain ⟨j,_,rfl⟩ := mem_image.mp hg
    obtain ⟨⟨a,i⟩,_,he⟩ := mem_image.mp hj
    exact off a i j he
  have hcard : (U ∪ V).card = 2*(e+1) := by
    rw [card_union_of_disjoint hUV, show U.card = (A ∪ B).card from card_image_of_injective _ inj,
      card_union_of_disjoint hd,hA,hB,show V.card = Fintype.card (Fin 2 × ↥T) by
        dsimp only [V]; rw [card_image_of_injective _ fresh.injective,card_univ],
      Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,hT]
    dsimp [t,n] at *; omega
  rw [←hcard]
  apply MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ rows
  intro g hg
  rcases mem_union.mp hg with h | h
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact inside i hi
  · obtain ⟨⟨a,i⟩,_,rfl⟩ := mem_image.mp h
    exact outside a i

/-- The same lower bound expressed using the complement of the required agreement
fraction. -/
theorem mass (dom : I ↪ F) (k e : ℕ) (hk : 2 ≤ k)
    (hhalf : Fintype.card I ≤ 2*(e+1)) (hcap : e+k+1 ≤ Fintype.card I)
    (hsupply : Fintype.card I + 2*(2*(e+1)-Fintype.card I) ≤ Fintype.card F) :
    ((2*(e+1) : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F))
        (1-((Fintype.card I-e : ℕ) : ℝ≥0)/Fintype.card I) := by
  have hn : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : e ≤ Fintype.card I := by omega
  have hbound : (e : ℝ≥0) / Fintype.card I ≤ 1 :=
    (div_le_one (by positivity)).mpr (by exact_mod_cast he)
  rw [Nat.cast_tsub, tsub_div, div_self hn, tsub_tsub_cancel_of_le hbound]
  exact errors dom k e hk hhalf hcap hsupply

#print axioms mass

#print axioms errors

end ArkLib.ProximityGap.Frontier.GeneralOverlapPacking
