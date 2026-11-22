/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HorizontalJetObstruction
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon

/-! # Persistence of an ordinary jet obstruction in every received direction

The scalar-coefficient matrix is triangular in the explicit scalar exponent.
Its diagonal at every exponent is the matrix at zero direction.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DirectionalJetObstruction
open Polynomial Finset SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
variable {F I : Type} [Field F] {s v d A : ℕ}

private theorem at_label (m : Monomials s v d A) (i j : ℕ) (x y b : F) :
    (jetTerm m i j x y b).coeff m.2.1.val = (jetTerm m i j x y 0).coeff m.2.1.val := by
  simp only [jetTerm, ← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self, coeff_zero_eq_eval_zero,
    eval_pow, eval_add, eval_mul, eval_C, eval_X, zero_mul]

private theorem before_label (m : Monomials s v d A) (i j l : ℕ) (x y b : F)
    (h : l < m.2.1.val) : (jetTerm m i j x y b).coeff l = 0 := by
  simp only [jetTerm, ← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', ite_eq_right h.not_ge, mul_zero]

private theorem horizontal_off (m : Monomials s v d A) (i j l : ℕ) (x y : F)
    (h : m.2.1.val ≠ l) : (jetTerm m i j x y 0).coeff l = 0 := by
  simp only [jetTerm,map_zero,mul_zero,add_zero,← C_pow,coeff_mul_C,coeff_monomial,
    ite_eq_right h,zero_mul]

/-- If the zero-direction matrix is injective, its analogue in every received
direction is injective with the same weight, monomials and multiplicity. -/
theorem kernel_eq_zero (dom : I ↪ F) (u w : I → F) (s v d t r : ℕ)
    (hor : ∀ a : Monomials s v d (r*t) → F,
      (jetMatrix dom u (fun _ => 0) s v d t r).mulVec a = 0 → a=0)
    (c : Monomials s v d (r*t) → F) (hc : (jetMatrix dom u w s v d t r).mulVec c=0) : c=0 := by
  classical
  have all (l : ℕ) : ∀ m : Monomials s v d (r*t), m.2.1.val=l → c m=0 := by
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro m hm
      let a (m : Monomials s v d (r*t)) := if m.2.1.val=l then c m else 0
      have hz : (jetMatrix dom u (fun _ => 0) s v d t r).mulVec a = 0 := by
        funext z
        obtain ⟨x,⟨j,i,k⟩⟩ := z
        by_cases hk : k.val=l
        · have row := congrFun hc (x,⟨j,i,k⟩)
          change ∑ m', (jetTerm m' i.val j.val (dom x) (u x) 0).coeff k.val * a m' = 0
          change ∑ m', (jetTerm m' i.val j.val (dom x) (u x) (w x)).coeff k.val * c m' = 0 at row
          apply Eq.trans _ row
          apply sum_congr rfl
          intro m' _
          rcases lt_trichotomy m'.2.1.val l with h | h | h
          · simp [a,ih _ h m' rfl]
          · rw [show a m'=c m' by simp [a,h], hk.trans h.symm,
              at_label m' i.val j.val (dom x) (u x) (w x)]
          · have hb := before_label m' i.val j.val k.val (dom x) (u x) (w x) (by omega)
            simp [a,h.ne',hb]
        · change ∑ m', (jetTerm m' i.val j.val (dom x) (u x) 0).coeff k.val * a m' = 0
          apply sum_eq_zero
          intro m' _
          by_cases he : m'.2.1.val=l
          · rw [horizontal_off _ _ _ _ _ _ (by omega)]
            exact zero_mul _
          · simp [a,he]
      simpa [a,hm] using congrFun (hor a hz) m
  funext m
  exact all _ m rfl

open scoped NNReal

private theorem two_level (dom : Fin 128 ↪ F) (B : Finset (Fin 128)) (hBc : B.card=62)
    (v : Fin 128 → F) (r s b : ℕ) (c : Monomials s b 31 (r*62) → F)
    (hc : (jetMatrix dom (fun i => if i∈B then 0 else 1) v s b 31 62 r).mulVec c=0) : c=0 := by
  classical
  let u (i : Fin 128) : F := if i∈B then 0 else 1
  apply kernel_eq_zero dom u v s b 31 62 r ?_ c hc
  apply HorizontalJetObstruction.kernel_eq_zero dom u (by decide) ({0,1} : Finset F)
    (fun y => if y=0 then B else Bᶜ)
  · simp
  · intro y _
    by_cases he : y=0 <;> simp [he,hBc,card_compl]
  · intro y hy i hi
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl
    · simp only [ite_true] at hi
      simp [u,hi]
    · simp [u,show i ∉ B from mem_compl.mp (by simpa using hi)]

/-- The first-order beyond-Johnson parameters admit a pair with 67 literal MCA
bad scalars and trivial ordinary jet kernels at every choice of cutoffs. -/
theorem rich_obstruction [Fintype F] [DecidableEq F] (dom : Fin 128 ↪ F) :
    ∃ u v : Fin 128 → F, (∃ G : Finset F, G.card=67 ∧ ∀ z ∈ G,
        _root_.ProximityGap.mcaEvent (ReedSolomon.code dom 32 : Set (Fin 128 → F))
          (66 / 128 : ℝ≥0) u v z) ∧
      ∀ r s b : ℕ, ∀ c : Monomials s b 31 (r*62) → F,
        (jetMatrix dom u v s b 31 62 r).mulVec c=0 → c=0 := by
  classical
  let T : Finset (Fin 128) := univ.filter (fun i => i.val < 61)
  let B : Finset (Fin 128) := univ.filter (fun i => i.val < 62)
  let a : Fin 128 := 61
  let label (i : Fin 128) := dom i - dom a
  let u (i : Fin 128) : F := if i ∈ B then 0 else 1
  let v (i : Fin 128) : F := if i ∈ T then 0 else if i=a then 1 else -(label i)⁻¹
  have hTc : T.card=61 := by decide
  have hBc : B.card=62 := by decide
  have hinj : Function.Injective label := fun i j h => dom.injective (sub_left_inj.mp h)
  have hTa : a ∉ T := by decide
  have hBa : a ∈ B := by decide
  let code := ReedSolomon.code dom 32
  have fresh (i : Fin 128) (hi : i ∉ T) : v i ≠ 0 ∧ u i + label i * v i=0 := by
    by_cases he : i=a
    · subst i
      simp [u,v,hBa,hTa,label]
    · have hi' : ¬ i.val < 61 := by simpa [T] using hi
      have ha : i.val ≠ 61 := fun h => he (Fin.ext (by simpa [a] using h))
      have hb : i ∉ B := by simpa [B] using (show ¬ i.val<62 by omega)
      have hn : label i ≠ 0 := sub_ne_zero.mpr (fun h => he (dom.injective h))
      simp [u,v,hi,he,hb,hn]
  refine ⟨u,v,⟨Tᶜ.image label,?_,?_⟩,?_⟩
  · rw [card_image_of_injective _ hinj,card_compl]
    simpa using (show 128-T.card=67 by omega)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have hout := mem_compl.mp hi
    have hcard : (insert i T).card=62 := by rw [card_insert_of_notMem hout,hTc]
    refine ⟨insert i T,?_,⟨0,code.zero_mem,?_⟩,?_⟩
    · rw [hcard]
      have hs : (66/128 : ℝ≥0) ≤ 1 := by
        apply (div_le_iff₀ (by norm_num : 0 < (128 : ℝ≥0))).mpr
        norm_num
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_mul,NNReal.coe_sub hs,NNReal.coe_div]
      norm_num
    · intro j hj
      rcases mem_insert.mp hj with hji | h
      · subst j
        exact (fresh i hout).2.symm
      · have jt : j.val<61 := (mem_filter.mp h).2
        have jb : j ∈ B := mem_filter.mpr ⟨mem_univ _,by omega⟩
        simp [u,v,h,jb]
    · rintro ⟨_,_,w,hw,pair⟩
      obtain ⟨P,hp,hwP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
      have vanish : P=0 := by
        apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f:=fun j:T => dom j.val)
          (dom.injective.comp Subtype.val_injective)
        · intro j
          rw [hwP,(pair j.val (mem_insert_of_mem j.property)).2]
          simp [v,j.property]
        · simpa [hTc] using (show P.natDegree < T.card by omega)
      have at_i := (pair i (mem_insert_self _ _)).2
      rw [← hwP,vanish,eval_zero] at at_i
      exact (fresh i hout).1 at_i.symm
  · exact two_level dom B hBc v

private theorem crossing_bad [Fintype F] [DecidableEq F] (dom : Fin 128 ↪ F)
    (u v : Fin 128 → F) (T : Finset (Fin 128)) (ht : 62 ≤ T.card) (i : Fin 128)
    (z a : F) (hT : ∀ x∈T, u x=a) (hi : u i ≠ a)
    (P : F[X]) (hp : P.natDegree<32)
    (onT : ∀ x∈T, P.eval (dom x) = u x+z*v x)
    (onI : P.eval (dom i) = u i+z*v i) :
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom 32 : Set (Fin 128 → F))
      (66/128 : ℝ≥0) u v z := by
  classical
  refine ⟨insert i T,?_,⟨ReedSolomon.evalOnPoints dom P,
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨P,hp,fun _ => rfl⟩,?_⟩,?_⟩
  · have hs : (66/128 : ℝ≥0) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by norm_num)
    have hc := ht.trans (card_le_card (subset_insert i T))
    apply (show (1-66/128 : ℝ≥0)*(Fintype.card (Fin 128)) ≤ 62 by
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_mul,NNReal.coe_sub hs,NNReal.coe_div]
      norm_num).trans
    exact_mod_cast hc
  · intro x hx
    rcases mem_insert.mp hx with h | h
    · exact h ▸ onI
    · exact onT x h
  · rintro ⟨w,hw,_,_,pair⟩
    obtain ⟨P₀,hp₀,evalP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
    have eq : P₀-C a=0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f:=fun x:T => dom x.val)
        (dom.injective.comp Subtype.val_injective)
      · intro x
        simp [evalP,(pair x.val (mem_insert_of_mem x.property)).1,hT x.val x.property]
      · have hlow := natDegree_sub_le P₀ (C a)
        simp only [natDegree_C,_root_.max_zero] at hlow
        simpa using (show (P₀-C a).natDegree < T.card by omega)
    have hj := ((evalP i).trans (pair i (mem_insert_self _ _)).1).symm
    rw [sub_eq_zero.mp eq,eval_C] at hj
    exact hi hj

/-- With an off-domain offset, two competing polynomial lines realize a
different bad scalar for every site while every ordinary jet kernel is
trivial. Every prime field admitting 128 sites admits such an offset. -/
theorem two_head_obstruction [Fintype F] [DecidableEq F] (dom : Fin 128 ↪ F)
    (α : F) (hoff : ∀ i, dom i ≠ α) :
    ∃ u v : Fin 128 → F, (∃ G : Finset F, G.card=128 ∧ ∀ z∈G,
      _root_.ProximityGap.mcaEvent (ReedSolomon.code dom 32 : Set (Fin 128 → F))
        (66/128 : ℝ≥0) u v z) ∧
      ∀ r s b : ℕ, ∀ c : Monomials s b 31 (r*62) → F,
        (jetMatrix dom u v s b 31 62 r).mulVec c=0 → c=0 := by
  classical
  let B : Finset (Fin 128) := univ.filter (fun i => i.val < 62)
  have hBc : B.card=62 := by decide
  let u (i : Fin 128) : F := if i∈B then 0 else 1
  let v (i : Fin 128) : F := if i∈B then 0 else dom i-α
  let z (i : Fin 128) : F := -(dom i-α)⁻¹
  have hinj : Function.Injective z := by
    intro x y h
    exact dom.injective (sub_left_inj.mp (inv_inj.mp (neg_inj.mp h)))
  refine ⟨u,v,⟨univ.image z,by simp [card_image_of_injective _ hinj],?_⟩,two_level dom B hBc v⟩
  intro z₀ hz
  obtain ⟨i,_,rfl⟩ := mem_image.mp hz
  by_cases hi : i∈B
  · let P := 1+C (z i)*(X-C α)
    apply crossing_bad dom u v Bᶜ (by simp [card_compl,hBc]) i (z i) 1
      (fun x hx => by simp [u,mem_compl.mp hx]) (by simp [u,hi]) P
    · have h := natDegree_add_le (1 : F[X]) (C (z i)*(X-C α))
      have h' := natDegree_C_mul_le (z i) (X-C α)
      simp only [natDegree_X_sub_C,natDegree_one,zero_le,max_eq_right] at h h'
      dsimp [P]
      omega
    · intro x hx
      simp [P,u,v,mem_compl.mp hx]
    · simp [P,u,v,z,hi,sub_ne_zero.mpr (hoff i)]
  · apply crossing_bad dom u v B hBc.ge i (z i) 0
      (fun x hx => by simp [u,hx]) (by simp [u,hi]) 0 (by simp)
    · intro x hx
      simp [u,v,hx]
    · simp [u,v,z,hi,sub_ne_zero.mpr (hoff i)]

/-- Every prime field supporting this domain supplies the offset used by the
two-head witness. -/
theorem prime_offset {p : ℕ} [Fact p.Prime] (dom : Fin 128 ↪ ZMod p) :
    ∃ α : ZMod p, ∀ i, dom i ≠ α := by
  by_contra! h
  have hi := Fintype.card_le_of_injective dom dom.injective
  have hs := Fintype.card_le_of_surjective dom h
  rw [Fintype.card_fin,ZMod.card] at hi hs
  have hp := Fact.out (p:=p.Prime)
  have eq : p=128 := by omega
  rw [eq] at hp
  exact (by decide : ¬Nat.Prime 128) hp

#print axioms prime_offset
#print axioms two_head_obstruction
#print axioms rich_obstruction
#print axioms kernel_eq_zero
end ArkLib.ProximityGap.Frontier.DirectionalJetObstruction
