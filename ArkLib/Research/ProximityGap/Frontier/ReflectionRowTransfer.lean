/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryReflectionRow

/-! # Classification of three equal pair products by pair-preserving transfer -/
namespace ProximityGap.ReflectionRowTransfer

open Finset TwoErrorSlice

/-- A reflection product determines the sum of the paired exponents. -/
theorem pair_iff_sum {K : Type*} [Field K] (D : Fin 128 ↪ K)
    (z : K) (hz : IsPrimitiveRoot z 128) (hD : ∀ i,D i=z^(i : ℕ))
    (u v a b : Fin 128) (huv : u≠v) (ha : a≠v) (hb : b≠v) :
    ratio D u v a * ratio D u v b = D u/D v ↔ a+b=u+v := by
  have nz : z≠0 := hz.ne_zero (by decide)
  rw [ratio,ratio,AuxiliaryReflectionRow.product_eq_reflection_iff (D.injective.ne huv)
    (hD v ▸ pow_ne_zero v.val nz) (D.injective.ne ha.symm) (D.injective.ne hb.symm)]
  rw [hD,hD,hD,hD,←power_add hz,←power_add hz]
  exact ⟨fun he => Fin.ext (hz.pow_inj (a+b).isLt (u+v).isLt he),fun he => by rw [he]⟩

/-- A transfer criterion for product comparisons between two lists of two sites.
Only the fixed nonzero row and the six primitive auxiliary substitutions occur. -/
def TransfersPairs {K L : Type*} [Field K] [Field L] (z : K) : Prop :=
  ∀ s : L, IsPrimitiveRoot s 128 → ∀ d : Fin 128, d≠0 →
    ∀ a b : Fin 2 → ℕ,
    (∀ i, z^(a i)≠z^d.val) → (∀ i, z^(b i)≠z^d.val) →
    (∀ i, s^(a i)≠s^d.val) → (∀ i, s^(b i)≠s^d.val) →
    RatioProductNorm.profile z d.val a = RatioProductNorm.profile z d.val b →
    RatioProductNorm.profile s d.val a = RatioProductNorm.profile s d.val b

/-- If equal pair products transfer to the six auxiliary rows, three distinct
representations force the reflection product on every nonantipodal source row. -/
theorem classify {K L : Type*} [Field K] [Field L]
    (D : Fin 128 ↪ K) (E : Fin 128 ↪ L) (z : K) (w : L)
    (hz : IsPrimitiveRoot z 128) (hw : IsPrimitiveRoot w 128)
    (hD : ∀ i,D i=z^(i : ℕ)) (hE : ∀ i,E i=w^(i : ℕ))
    (htr : TransfersPairs (L:=L) z)
    (six : ∀ d : Fin 128, StandardRow d → ∀ t : L, 3 ≤ (alternatives E 0 d t).card → t=(E d)⁻¹)
    (u v : Fin 128) (hne : u≠v) (hanti : D u ≠ -D v) (t : K)
    (big : 3 ≤ (alternatives D u v t).card) : t=D u/D v := by
  classical
  obtain ⟨e,s,hs,eu,std,rD,rE,back⟩ := normalize_pair D E z w hz hw hD hE u v hne hanti
  let U := ((univ : Finset (Fin 128)).erase u).erase v
  let ix (i : Fin 128) := (i-u).val
  let d := v-u
  have hd : d≠0 := sub_ne_zero.mpr hne.symm
  have trans (A B : Finset (Fin 128)) (ha : A∈U.powersetCard 2) (hb : B∈U.powersetCard 2)
      (same : (∏ i ∈ A,ratio D u v i)=∏ i ∈ B,ratio D u v i) :
      (∏ i ∈ A,ratio E (e u) (e v) (e i))=∏ i ∈ B,ratio E (e u) (e v) (e i) := by
    obtain ⟨hA,ac⟩ := mem_powersetCard.mp ha
    obtain ⟨hB,bc⟩ := mem_powersetCard.mp hb
    obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp ac
    obtain ⟨f,g,fg,rfl⟩ := card_eq_two.mp bc
    let X : Fin 2 → Fin 128 := ![a,b]
    let Y : Fin 2 → Fin 128 := ![f,g]
    have hX (i : Fin 2) : X i ∈ U := by
      fin_cases i
      · exact hA (mem_insert_self ..)
      · exact hA (mem_insert_of_mem (mem_singleton_self _))
    have hY (i : Fin 2) : Y i ∈ U := by
      fin_cases i
      · exact hB (mem_insert_self ..)
      · exact hB (mem_insert_of_mem (mem_singleton_self _))
    have out := htr s hs d hd (fun i => ix (X i)) (fun i => ix (Y i))
      (fun i => shift_den hz u v _ (mem_erase.mp (hX i)).1)
      (fun i => shift_den hz u v _ (mem_erase.mp (hY i)).1)
      (fun i => shift_den hs u v _ (mem_erase.mp (hX i)).1)
      (fun i => shift_den hs u v _ (mem_erase.mp (hY i)).1) (by
        simp only [prod_pair ab,prod_pair fg,rD] at same
        simpa [RatioProductNorm.profile,Fin.prod_univ_succ,X,Y,ix,d,div_mul_div_comm] using same)
    simp only [prod_pair ab,prod_pair fg,rE]
    simpa [RatioProductNorm.profile,Fin.prod_univ_succ,X,Y,ix,d,div_mul_div_comm] using out
  obtain ⟨A,ha⟩ := card_pos.mp (show 0 < (alternatives D u v t).card by omega)
  let q := ∏ i ∈ A,ratio E (e u) (e v) (e i)
  obtain ⟨ham,hap⟩ := mem_alternatives_iff.mp ha
  have cap : (alternatives D u v t).card ≤ (alternatives E (e u) (e v) q).card := by
    apply card_le_card_of_injOn (fun S => S.map e) _ (Finset.map_injective e).injOn
    intro B hB
    obtain ⟨hbm,hbp⟩ := mem_alternatives_iff.mp hB
    apply mem_alternatives_iff.mpr
    obtain ⟨sub,bc⟩ := mem_powersetCard.mp hbm
    refine ⟨mem_powersetCard.mpr ⟨?_,by simpa using bc⟩,?_⟩
    · intro j hj
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hj
      have h := sub hi
      simp only [mem_erase,mem_univ,and_true] at h ⊢
      exact ⟨e.injective.ne h.1,e.injective.ne h.2⟩
    · rw [Finset.prod_map]
      exact trans B A hbm ham (hbp.trans hap.symm)
  have qt : q=E (e u)/E (e v) := by
    have zero : E (0 : Fin 128)=1 := by rw [hE]; exact pow_zero _
    rw [eu,zero,one_div]
    rw [eu] at cap
    exact six _ std q (big.trans cap)
  obtain ⟨sub,ac⟩ := mem_powersetCard.mp ham
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp ac
  have av := (mem_erase.mp (sub (mem_insert_self ..))).1
  have bv := (mem_erase.mp (sub (mem_insert_of_mem (mem_singleton_self _)))).1
  simp only [q,prod_pair ab] at qt
  simp only [prod_pair ab] at hap
  have eq := (pair_iff_sum E w hw hE _ _ _ _ (e.injective.ne hne) (e.injective.ne av)
    (e.injective.ne bv)).mp qt
  exact hap.symm.trans ((pair_iff_sum D z hz hD u v a b hne av bv).mpr (back _ _ eq))

end ProximityGap.ReflectionRowTransfer

#print axioms ProximityGap.ReflectionRowTransfer.classify
