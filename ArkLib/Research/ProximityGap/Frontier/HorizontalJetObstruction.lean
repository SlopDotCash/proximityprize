/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarReciprocalCharts
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation

/-! # Actual interpolation obstruction on horizontal received-value fibers

The leading coefficient in the evaluation coordinate accumulates high-multiplicity
roots at every received height. This rules out nonzero bounded-weight jet
interpolants, regardless of the number of equations a dimension count predicts.
-/
set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.HorizontalJetObstruction
open ArkLib.GS
variable {K : Type} [Field K]

private theorem slice_monomial (A : K[X]) (k i : ℕ) :
    (Bivariate.swap (monomial i A)).coeff k = monomial i (A.coeff k) := by
  ext j
  rw [ApolarReciprocalCharts.swap_coeff]
  by_cases h : i=j <;> simp [coeff_monomial,h]

private theorem slice_taylor (Q : K[X][X]) (y : K) (j k : ℕ) :
    (innerTaylorCoeff Q y j).coeff k = (taylor y ((Bivariate.swap Q).coeff k)).coeff j := by
  induction Q using Polynomial.induction_on' with
  | add A B ha hb => simp only [innerTaylorCoeff_add,map_add,coeff_add,ha,hb]
  | monomial i A =>
    rw [slice_monomial,innerTaylorCoeff,taylor_coeff,taylor_coeff,hasseDeriv_monomial,hasseDeriv_monomial,
      eval_monomial,eval_monomial,← Polynomial.C_pow,coeff_mul_C]
    simp

/-- If each of the indicated heights occurs on at least `t` distinct sites and
`t ≤ d * (# heights)`, the actual interpolation conditions have no nonzero
bivariate solution of weight strictly less than `r*t`, at any multiplicity. -/
theorem eq_zero (Q : K[X][X]) (d t r : ℕ) (ht : 0<t) (levels : Finset K) (sites : K → Finset K)
    (hcover : t ≤ levels.card*d) (hrich : ∀ y ∈ levels, t ≤ (sites y).card)
    (hweight : ∀ j a, (Q.coeff j).coeff a ≠ 0 → a+j*d < r*t)
    (hjet : ∀ y ∈ levels, ∀ x ∈ sites y, vanishesToOrder r Q x y) : Q=0 := by
  classical
  by_contra hQ
  let k := (Bivariate.swap Q).natDegree
  let L := (Bivariate.swap Q).coeff k
  have hswap : Bivariate.swap Q ≠ 0 := fun h => hQ (Bivariate.swap.injective (by simpa using h))
  have hL : L ≠ 0 := leadingCoeff_ne_zero.mpr hswap
  have hlead : (Q.coeff L.natDegree).coeff k ≠ 0 := by
    rw [← ApolarReciprocalCharts.swap_coeff]
    exact leadingCoeff_ne_zero.mpr hL
  have hW := hweight L.natDegree k hlead
  have hk : k/t < r := (Nat.div_lt_iff_lt_mul ht).mpr (by omega)
  have hX (y : K) (j : ℕ) : (innerTaylorCoeff Q y j).natDegree ≤ k := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [slice_taylor,coeff_eq_zero_of_natDegree_lt hi,map_zero,coeff_zero]
  have hroot (y : K) (hy : y ∈ levels) : (X-C y)^(r-k/t) ∣ L := by
    rw [X_sub_C_pow_dvd_iff_X_pow_dvd_taylor,X_pow_dvd_iff]
    intro j hj
    change (taylor y ((Bivariate.swap Q).coeff k)).coeff j=0
    rw [← slice_taylor]
    have hlow : k < (r-j)*t := (Nat.div_lt_iff_lt_mul ht).mp (by omega)
    have hz : innerTaylorCoeff Q y j=0 :=
      eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn id (sites y) (r-j) t
        Function.injective_id.injOn (hrich y hy) (fun x hx => hjet y hy x hx j)
        (degree_le_natDegree.trans_lt (by exact_mod_cast (hX y j).trans_lt hlow))
    rw [hz,coeff_zero]
  have hdeg : L.natDegree < (r-k/t)*levels.card := by
    by_contra! hb
    have hsub : r-k/t+k/t=r := Nat.sub_add_cancel hk.le
    have hcost : (r-k/t)*t ≤ L.natDegree*d :=
      (Nat.mul_le_mul_left _ hcover).trans (by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right d hb)
    have hprod := congrArg (fun z => z*t) hsub
    change (r-k/t+k/t)*t = r*t at hprod
    rw [Nat.add_mul] at hprod
    have := Nat.div_mul_le_self k t
    omega
  exact hL (eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn id levels (r-k/t) levels.card
    Function.injective_id.injOn le_rfl hroot (degree_le_natDegree.trans_lt (by exact_mod_cast hdeg)))

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
variable {s v d t r : ℕ}

private noncomputable def scalarSlice (c : Monomials s v d t → K) (l : ℕ) : K[X][X] :=
  ∑ m, monomial m.1.val (monomial m.2.2.val (if m.2.1.val=l then c m else 0))

private theorem scalar_coeff (c : Monomials s v d t → K) (j l a : ℕ) :
    ((scalarSlice c l).coeff j).coeff a =
      ∑ m, if m.1.val=j ∧ m.2.1.val=l ∧ m.2.2.val=a then c m else 0 := by
  simp only [scalarSlice,finsetSum_coeff]
  apply sum_congr rfl
  intro m _
  by_cases h₁ : m.1.val=j <;> by_cases h₂ : m.2.1.val=l <;> by_cases h₃ : m.2.2.val=a <;>
    simp [coeff_monomial,h₁,h₂,h₃]

private theorem scalar_jet (c : Monomials s v d t → K) (l i j : ℕ) (x y : K) :
    hasseCoeff i j (scalarSlice c l) x y = (∑ m, C (c m)*jetTerm m i j x y 0).coeff l := by
  change hasseCoeffLinearMap i j x y (scalarSlice c l) = _
  simp only [scalarSlice,map_sum,hasseCoeffLinearMap_apply,finsetSum_coeff]
  apply sum_congr rfl
  intro m _
  rw [hasseCoeff_monomial]
  by_cases h : m.2.1.val=l <;>
    simp only [jetTerm,map_zero,mul_zero,add_zero,← Polynomial.C_pow,coeff_C_mul,coeff_mul_C,coeff_monomial,h,ite_true,ite_false] <;> ring

/-- For every received pair `(y,0)` with the required horizontal populations, the
actual mixed-jet matrix has trivial kernel at every multiplicity and every degree
cutoff. The argument takes a separate coefficient of the scalar indeterminate. -/
theorem kernel_eq_zero {I : Type} [Fintype I] (dom : I ↪ K) (y : I → K)
    (ht : 0<t) (levels : Finset K) (S : K → Finset I) (hcover : t ≤ levels.card*d)
    (hrich : ∀ b ∈ levels, t ≤ (S b).card) (hsite : ∀ b ∈ levels, ∀ x ∈ S b, y x=b)
    (c : Monomials s v d (r*t) → K) (hc : (jetMatrix dom y (fun _ => 0) s v d t r).mulVec c=0) : c=0 := by
  classical
  let sites (b : K) := (S b).image dom
  have hs : ∀ l, scalarSlice c l = 0 := by
    intro l
    apply eq_zero _ d t r ht levels sites hcover
    · intro b hb
      simpa [sites,card_image_of_injective _ dom.injective] using hrich b hb
    · intro j a he
      by_contra! hbad
      apply he
      rw [scalar_coeff]
      apply sum_eq_zero
      intro m _
      split
      next hn =>
        have hx := Nat.lt_sub_iff_add_lt.mp m.2.2.isLt
        obtain ⟨h₁,_,h₃⟩ := hn
        subst a; subst j
        omega
      next => rfl
    · intro b hb x hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      rw [← hsite b hb z hz]
      apply (vanishesToOrder_iff_hasseCoeff ..).mpr
      intro i j hij
      rw [scalar_jet,finsetSum_coeff]
      by_cases hl : l<s+1-j
      · have he := congrFun hc (z,⟨⟨j,by omega⟩,⟨i,by change i<r-j; omega⟩,⟨l,hl⟩⟩)
        simpa only [jetMatrix,Matrix.mulVec,dotProduct,Pi.zero_apply,coeff_C_mul,mul_comm] using he
      · apply sum_eq_zero
        intro m _
        by_cases hj : m.1.val<j
        · simp [jetTerm,Nat.choose_eq_zero_of_lt hj]
        · have hne : m.2.1.val ≠ l := by have hm := m.2.1.isLt; omega
          simp only [jetTerm,map_zero,mul_zero,add_zero,← Polynomial.C_pow,coeff_C_mul,coeff_mul_C,coeff_monomial,ite_eq_right hne,zero_mul]
  funext m
  have h := congrArg (fun Q : K[X][X] => (Q.coeff m.1.val).coeff m.2.2.val) (hs m.2.1.val)
  rw [scalar_coeff] at h
  rw [sum_eq_single m] at h
  · simpa using h
  · intro m' _ hne
    split
    next he =>
      exfalso
      apply hne
      rcases m with ⟨⟨j,hj⟩,⟨i,hi⟩,⟨a,ha⟩⟩
      rcases m' with ⟨⟨j',hj'⟩,⟨i',hi'⟩,⟨a',ha'⟩⟩
      obtain ⟨rfl,rfl,rfl⟩ := he
      rfl
    next => rfl
  · simp

/-- Every prescribed domain with `h*t` sites admits a single received pair `(y,0)`
whose jet matrix has trivial kernel simultaneously for every multiplicity and
degree cutoff, provided `t ≤ h*d`. -/
theorem exists_trivial_kernels {I : Type} [Fintype I] (dom : I ↪ K) (d t h : ℕ)
    (hh : 0<h) (ht : 0<t) (hsize : h*t ≤ Fintype.card I) (hcover : t ≤ h*d) :
    ∃ y : I → K, ∀ r s v : ℕ, ∀ c : Monomials s v d (r*t) → K,
      (jetMatrix dom y (fun _ => 0) s v d t r).mulVec c=0 → c=0 := by
  classical
  obtain ⟨alloc⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin h × Fin t) ≤ Fintype.card I by simpa using hsize)
  letI : Nonempty (Fin h × Fin t) := ⟨⟨⟨0,hh⟩,⟨0,ht⟩⟩⟩
  let tag (j : Fin h) := dom (alloc (j,⟨0,ht⟩))
  have htag : Function.Injective tag := fun i j he => congrArg Prod.fst (alloc.injective (dom.injective he))
  let y (z : I) := tag (Function.invFun alloc z).1
  let H := univ.image tag
  let S (b : K) := univ.filter fun z => y z=b
  have hHs : H.card=h := by simp [H,card_image_of_injective _ htag]
  have hS (b : K) (hb : b ∈ H) : t ≤ (S b).card := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hb
    let f (j : Fin t) := alloc (i,j)
    have hinj : Function.Injective f := fun j k he => congrArg Prod.snd (alloc.injective he)
    have sub : univ.image f ⊆ S (tag i) := by
      intro x hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      apply mem_filter.mpr
      exact ⟨mem_univ _, congrArg (fun z => tag z.1) (Function.leftInverse_invFun alloc.injective (i,j))⟩
    simpa [card_image_of_injective _ hinj] using card_le_card sub
  exact ⟨y,fun _ _ _ c hc => kernel_eq_zero dom y ht H S (hHs ▸ hcover) hS
    (fun _ _ _ hx => (mem_filter.mp hx).2) c hc⟩

#print axioms eq_zero
#print axioms kernel_eq_zero
#print axioms exists_trivial_kernels
end ArkLib.ProximityGap.Frontier.HorizontalJetObstruction
