/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TangentVeronesePacking
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Fixed rows in a homogeneous evaluation determinant -/
namespace ArkLib.ProximityGap.Frontier.AnchoredVeronese
open Finset Matrix Module Submodule TangentVeronesePacking
set_option autoImplicit false
variable {K I J : Type*} [Field K]

/-- Complete independent anchors to a basis chosen from their union with the
allowed rows. The determinant test can be restricted to matrices with distinct
rows and with every anchor present. -/
theorem anchored_annihilator [Fintype J] [DecidableEq J]
    (A : I → J → K) (ind : LinearIndependent K A) (cheap : Set (J → K))
    (zero : ∀ M : Matrix J J K, Function.Injective M.row →
      Set.range A ⊆ Set.range M.row → Set.range M.row ⊆ Set.range A ∪ cheap → M.det=0) :
    ∃ c : J → K, c≠0 ∧ ∀ v ∈ Set.range A ∪ cheap, ∑ j, v j*c j=0 := by
  classical
  let S := Set.range A ∪ cheap
  have proper : span K S ≠ ⊤ := by
    intro full
    have sub : Set.range A ⊆ S := Set.subset_union_left
    let b := Basis.extendLe ind.linearIndepOn_id sub full.ge
    let e := b.indexEquiv (Pi.basisFun K J)
    let B := b.reindex e
    let M : Matrix J J K := fun i => B i
    have range_eq : Set.range M.row = Set.range b := by
      change Set.range (b.reindex e) = _
      rw [Basis.coe_reindex, EquivLike.range_comp]
    have singular := zero M B.injective
      (range_eq.symm ▸ Basis.subset_extendLe ind.linearIndepOn_id sub full.ge)
      (range_eq.symm ▸ Basis.extendLe_subset ind.linearIndepOn_id sub full.ge)
    have unit := Matrix.linearIndependent_row_iff_isUnit.mp
      (show LinearIndependent K M.row from B.linearIndependent)
    exact ((Matrix.isUnit_iff_isUnit_det M).mp unit).ne_zero singular
  obtain ⟨f,nf,kernel⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top proper.lt_top inferInstance
  let c (j : J) := f (Pi.single j 1)
  have apply_form (v : J → K) : f v = ∑ j, v j*c j := by
    have basis := (Pi.basisFun K J).sum_repr v
    calc
      f v = f (∑ j, (Pi.basisFun K J).repr v j • Pi.basisFun K J j) := congrArg f basis.symm
      _ = _ := by simp [c]
  refine ⟨c,?_,?_⟩
  · intro z
    apply nf
    ext v
    simp [apply_form,z]
  · intro v hv
    rw [←apply_form, ← Submodule.mem_bot K, ←kernel]
    exact ⟨v, subset_span hv, rfl⟩

/-- The actual homogeneous monomial evaluation row used by the tangent determinant. -/
def row (s : ℕ) (h x y : K) (j : ↥(monomials s)) : K := monomial s j.val h x y

private theorem included {s i j : ℕ} (h : i+j≤s) : (i,j)∈monomials s := by
  simp only [monomials, mem_filter, mem_product, mem_range]
  omega

/-- A moment relation among affine Veronese rows also annihilates every
polynomial of total degree at most the Veronese degree. -/
private theorem relation_eval {r s : ℕ} (p : Fin r → K × K) (w : Fin r → K)
    (rel : ∑ i, w i • row s 1 (p i).1 (p i).2 = 0)
    (f : MvPolynomial (Fin 2) K) (degree : f.totalDegree≤s) :
    ∑ i, w i * MvPolynomial.eval ![(p i).1,(p i).2] f = 0 := by
  classical
  have moment {a b : ℕ} (h : a+b≤s) :
      ∑ i, w i*((p i).1^a*(p i).2^b)=0 := by
    have eq := congrFun rel ⟨(a,b),included h⟩
    simpa [row,monomial,Finset.sum_apply,mul_assoc] using eq
  conv_lhs => enter [2,i,2]; rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro m hm
  have bound := (MvPolynomial.le_totalDegree hm).trans degree
  have size : m 0+m 1≤s := by
    simpa [Finsupp.sum_fintype,Fin.sum_univ_two] using bound
  simp only [MvPolynomial.eval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_two]
  have eq := congrArg (fun t : K => f.coeff m*t) (moment size)
  rw [Finset.mul_sum] at eq
  simpa [mul_comm,mul_left_comm,mul_assoc] using eq

/-- Any `r` distinct affine points have independent degree-`s` homogeneous
evaluation rows as soon as `r≤s+1`. For each target point, a product of
coordinate differences separates it from the other points over any field. -/
theorem independent_anchors {r s : ℕ} (size : r≤s+1) (p : Fin r → K × K)
    (distinct : Function.Injective p) :
    LinearIndependent K (fun i => row s 1 (p i).1 (p i).2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w rel i
  let coord (k : Fin r) : Fin 2 → K := ![(p k).1,(p k).2]
  let var (k : Fin r) : Fin 2 := if (p i).1 = (p k).1 then 1 else 0
  have separates (k : Fin r) (ne : k≠i) : coord i (var k) ≠ coord k (var k) := by
    by_cases eq : (p i).1 = (p k).1
    · have nd : (p i).2 ≠ (p k).2 := fun e => ne (distinct (Prod.ext eq e)).symm
      simpa [var,coord,eq] using nd
    · simp [var,coord,eq]
  let l (k : Fin r) : MvPolynomial (Fin 2) K :=
    MvPolynomial.X (var k) + MvPolynomial.C (-(coord k (var k)))
  let f := ∏ k ∈ univ.erase i, l k
  have degree : f.totalDegree≤s := by
    have dl (j : Fin r) : (l j).totalDegree≤1 :=
      (MvPolynomial.totalDegree_add ..).trans (max_le (by rw [MvPolynomial.totalDegree_X])
        (by rw [MvPolynomial.totalDegree_C]; omega))
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    have bound := sum_le_sum (s:=univ.erase i) (g:=fun _ => 1) (fun j _ => dl j)
    simp only [sum_const,card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one] at bound
    omega
  have nf : MvPolynomial.eval (coord i) f ≠ 0 := by
    simp only [f,map_prod,Finset.prod_ne_zero_iff]
    intro k hk
    simpa [l,←sub_eq_add_neg] using sub_ne_zero.mpr (separates k (mem_erase.mp hk).1)
  have van (k : Fin r) (ne : k≠i) : MvPolynomial.eval (coord k) f = 0 := by
    simp only [f,map_prod]
    apply prod_eq_zero (mem_erase.mpr ⟨ne,mem_univ _⟩)
    simp [l]
  have eq := relation_eval p w rel f degree
  change ∑ k, w k * MvPolynomial.eval (coord k) f = 0 at eq
  rw [sum_eq_single_of_mem i (mem_univ _) (fun k _ ne => by rw [van k ne,mul_zero])] at eq
  exact (mul_eq_zero.mp eq).resolve_right nf

/-- Three or fewer anchors in the fifteen quartic columns. -/
theorem quartic_anchors {r : ℕ} (size : r≤3) (p : Fin r → K × K) (inj : Function.Injective p) :
    LinearIndependent K (fun i => row 4 1 (p i).1 (p i).2) :=
  independent_anchors (by omega) p inj

/-- Two or fewer anchors in the three linear columns. -/
theorem linear_anchors {r : ℕ} (size : r≤2) (p : Fin r → K × K) (inj : Function.Injective p) :
    LinearIndependent K (fun i => row 1 1 (p i).1 (p i).2) :=
  independent_anchors size p inj

private noncomputable def exponent (s : ℕ) (ij : ↥(monomials s)) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![s-(ij.val.1+ij.val.2),ij.val.1,ij.val.2]

private theorem exponent_inj (s : ℕ) : Function.Injective (exponent s) := by
  intro i j eq
  apply Subtype.ext
  exact Prod.ext (congrArg (fun p : Fin 3 →₀ ℕ => p 1) eq)
    (congrArg (fun p : Fin 3 →₀ ℕ => p 2) eq)

/-- The homogeneous polynomial having the indicated coefficients in the
determinant's monomial order. -/
noncomputable def form (s : ℕ) (c : ↥(monomials s) → K) : MvPolynomial (Fin 3) K :=
  ∑ j, MvPolynomial.monomial (exponent s j) (c j)

theorem form_ne_zero {s : ℕ} {c : ↥(monomials s) → K} (nc : c≠0) : form s c≠0 := by
  classical
  intro zero
  apply nc
  funext j
  have val := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (exponent s j)) zero
  simpa [form,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,(exponent_inj s).eq_iff] using val

theorem form_homogeneous (s : ℕ) (c : ↥(monomials s) → K) : (form s c).IsHomogeneous s := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  apply MvPolynomial.isHomogeneous_monomial
  have bound := (mem_filter.mp j.property).2
  simp only [Finsupp.degree_eq_sum,exponent,Finsupp.equivFunOnFinite_symm_apply_apply,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.isValue, Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero]
  omega

theorem eval_form (s : ℕ) (c : ↥(monomials s) → K) (p : Fin 3 → K) :
    MvPolynomial.eval p (form s c) = ∑ j, row s (p 0) (p 1) (p 2) j*c j := by
  classical
  simp [form,exponent,row,monomial,MvPolynomial.eval_monomial,Finsupp.prod_fintype,
    Fin.prod_univ_succ,mul_assoc]
  apply sum_congr rfl
  intro j _
  ring

/-- Version specifying which row indices are occupied by the anchors. Exactly
the complementary indices must be supplied by the allowed family. -/
theorem anchored_slots [Fintype J] [DecidableEq J] (A : I → J → K)
    (ind : LinearIndependent K A) (cheap : Set (J → K))
    (zero : ∀ (M : Matrix J J K) (e : I ↪ J), Function.Injective M.row →
      (∀ i, M (e i)=A i) →
      (∀ j, j∉Set.range e → M j∈cheap) → M.det=0) :
    ∃ c : J → K, c≠0 ∧ ∀ v ∈ Set.range A ∪ cheap, ∑ j, v j*c j=0 := by
  classical
  apply anchored_annihilator A ind cheap
  intro M inj contain inside
  choose f hf using fun i : I => contain (Set.mem_range_self i)
  let e : I ↪ J := ⟨f, fun i j eq => ind.injective ((hf i).symm.trans ((congrArg M eq).trans (hf j)))⟩
  apply zero M e inj hf
  intro j out
  rcases inside (Set.mem_range_self j) with ⟨i,hi⟩ | yes
  · exact False.elim (out ⟨i,inj ((hf i).trans hi)⟩)
  · exact yes

/-- A single nonzero homogeneous plane polynomial vanishes at all fixed
affine points and all the supplied homogeneous tangent points. The determinant
hypothesis only uses matrices whose other slots are filled with these tangents. -/
theorem anchored_curve {r s : ℕ} (size : r≤s+1) (fixed : Fin r → K × K)
    (distinct : Function.Injective fixed) (cheap : Set (Fin 3 → K))
    (zero : ∀ (M : Matrix ↥(monomials s) ↥(monomials s) K)
      (e : Fin r ↪ ↥(monomials s)), Function.Injective M.row →
      (∀ i, M (e i)=row s 1 (fixed i).1 (fixed i).2) →
      (∀ j, j∉Set.range e → ∃ p ∈ cheap, M j=row s (p 0) (p 1) (p 2)) → M.det=0) :
    ∃ f : MvPolynomial (Fin 3) K, f≠0 ∧ f.IsHomogeneous s ∧
      (∀ i, MvPolynomial.eval ![1,(fixed i).1,(fixed i).2] f=0) ∧
      ∀ p ∈ cheap, MvPolynomial.eval p f=0 := by
  classical
  let A i := row s 1 (fixed i).1 (fixed i).2
  let S := (fun p : Fin 3 → K => row s (p 0) (p 1) (p 2)) '' cheap
  obtain ⟨c,nc,hc⟩ := anchored_slots A (independent_anchors size fixed distinct) S
    (fun M e inj ha h => zero M e inj ha (fun j hj => by
      obtain ⟨p,hp,eq⟩ := h j hj
      exact ⟨p,hp,eq.symm⟩))
  refine ⟨form s c,form_ne_zero nc,form_homogeneous s c,?_,?_⟩
  · intro i
    rw [eval_form]
    exact hc (A i) (Or.inl (Set.mem_range_self i))
  · intro p hp
    rw [eval_form]
    exact hc _ (Or.inr ⟨p,hp,rfl⟩)

/-- The two matrix sizes used by the linear and quartic tangent windows. -/
theorem column_counts : (monomials 1).card=3 ∧ (monomials 4).card=15 := by decide

/-- Every anchor occupies a distinct slot, so the complementary rows can be
priced using precisely their cardinality. -/
theorem complementary_slots {r s : ℕ} (e : Fin r ↪ ↥(monomials s)) :
    (univ.filter fun j => j ∉ (univ.image e)).card = (monomials s).card-r := by
  classical
  rw [filter_notMem_eq_sdiff,card_sdiff_of_subset (subset_univ _)]
  simp [card_image_of_injective _ e.injective]

#print axioms complementary_slots
#print axioms anchored_annihilator
#print axioms quartic_anchors
#print axioms linear_anchors
#print axioms anchored_slots
#print axioms anchored_curve
end ArkLib.ProximityGap.Frontier.AnchoredVeronese
