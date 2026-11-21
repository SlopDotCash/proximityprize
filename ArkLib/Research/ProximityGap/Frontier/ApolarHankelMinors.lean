/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedLocator
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.GroupTheory.Perm.Fin

/-! # Consecutive Hankel determinants of a syndrome pencil

The extreme coefficients of a common recurrence control how the successive
Hankel minors change. Coprime extremes force a power of the last coefficient
to divide the initial minor.
-/

open Polynomial Matrix Finset
namespace ProximityGap.ApolarHankelMinors

variable {R : Type*} [CommRing R]

/-- Consecutive square blocks in a sequence of rows. -/
def block {r : ℕ} (v : ℕ → Fin (r+1) → R) (j : ℕ) : Matrix (Fin (r+1)) (Fin (r+1)) R :=
  fun i => v (j + i.val)

private def rotationFactor (r : ℕ) : R := -(((Equiv.Perm.sign (finRotate (r+1)).symm : ℤˣ) : ℤ) : R)

/-- One step of the sliding determinant recurrence, valid over a commutative ring. -/
theorem slide {r : ℕ} (v : ℕ → Fin (r+1) → R) (c : Fin (r+1) → R)
    (z : R) (j : ℕ) (hrec : ∑ i, c i • v (j+i.val) = (-z) • v (j+r+1)) :
    c 0 * (block v j).det = (z * rotationFactor r) * (block v (j+1)).det := by
  let A := block v j
  have hu := Matrix.det_updateRow_sum A 0 c
  change (A.updateRow 0 (∑ i, c i • v (j+i.val))).det = c 0 * A.det at hu
  rw [hrec, Matrix.det_updateRow_smul] at hu
  have hh : A.updateRow 0 (v (j+r+1)) =
      (block v (j+1)).submatrix (finRotate (r+1)).symm id := by
    ext i k
    by_cases hi : i=0
    · subst i
      have hrot : (finRotate (r+1)).symm 0 = Fin.last r := (finRotate _).symm_apply_eq.mpr finRotate_last.symm
      rw [Matrix.updateRow_self,Matrix.submatrix_apply,hrot]
      change v (j+r+1) k = v (j+1+r) k
      rw [show j+r+1=j+1+r by omega]
    · have hrot := coe_finRotate_symm_of_ne_zero hi
      rw [Matrix.updateRow_ne hi,Matrix.submatrix_apply]
      have hi' : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
      have he : j+i.val = j+1+((finRotate (r+1)).symm i).val := by omega
      change v (j+i.val) k = v (j+1+((finRotate (r+1)).symm i).val) k
      rw [he]
  rw [hh, Matrix.det_permute] at hu
  dsimp only [rotationFactor]
  change c 0 * A.det = _
  linear_combination -hu

/-- Iterating the recurrence gives the exact high-power divisibility needed for the
degree bound, without dividing in the coefficient ring. -/
theorem endpoint_dvd {r : ℕ} (v : ℕ → Fin (r+1) → R) (c : Fin (r+1) → R) (z : R)
    (a : ℕ) (hrec : ∀ j < a, ∑ i, c i • v (j+i.val) = (-z) • v (j+r+1)) :
    z^a ∣ (c 0)^a * (block v 0).det := by
  have h (j : ℕ) (hj : j ≤ a) :
      (c 0)^j * (block v 0).det = (z*rotationFactor r)^j * (block v j).det := by
    induction j with
    | zero => simp
    | succ j ih =>
      have step := slide v c z j (hrec j (by omega))
      calc
        _ = c 0 * ((c 0)^j * (block v 0).det) := by ring
        _ = (z*rotationFactor r)^j * (c 0 * (block v j).det) := by rw [ih (by omega)]; ring
        _ = _ := by rw [step, pow_succ]; ring
  rw [h a le_rfl, mul_pow]
  exact ⟨_, mul_assoc _ _ _⟩

/-- If the rectangular block has trivial kernel, its first square block already
has trivial kernel. The locator recurrence propagates row annihilation forward. -/
theorem first_minor_ne_zero [IsDomain R] {r a : ℕ} (v : ℕ → Fin (r+1) → R)
    (c : Fin (r+1) → R) {z : R} (hz : z ≠ 0)
    (hrec : ∀ j < a, ∑ i, c i • v (j+i.val) = (-z) • v (j+r+1))
    (hinj : ∀ p : Fin (r+1) → R, (∀ k < a+r+1, v k ⬝ᵥ p = 0) → p=0) :
    (block v 0).det ≠ 0 := by
  intro hd
  obtain ⟨p, hp, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  apply hp
  apply hinj
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hsmall : k < r+1
    · have he := congrFun hzero (⟨k,hsmall⟩ : Fin (r+1))
      simpa [Matrix.mulVec,block] using he
    · let j := k-(r+1)
      have hj : j < a := by dsimp only [j]; omega
      have he : j+r+1 = k := by dsimp only [j]; omega
      have hc := congrArg (fun row => row ⬝ᵥ p) (hrec j hj)
      simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, he] at hc
      have hh : (∑ i : Fin (r+1), c i * (v (j+i.val) ⬝ᵥ p)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [ih (j+i.val) (by have := i.isLt; omega) (by have := i.isLt; omega), mul_zero]
      rw [hh] at hc
      exact (mul_eq_zero.mp hc.symm).resolve_left (neg_ne_zero.mpr hz)

variable {K : Type*} [Field K]

/-- The moment polynomial of the received pair on degree j. -/
noncomputable def moment (H : Finset K) (u v : K → K) (j : ℕ) : K[X] :=
  X * C (ApolarDividedLocator.syndrome H (RingHom.id K) v (X^j)) +
    C (ApolarDividedLocator.syndrome H (RingHom.id K) u (X^j))

/-- All consecutive Hankel blocks of the actual syndrome pencil have determinant
of parameter degree at most their dimension. -/
theorem moment_block_degree (H : Finset K) (u v : K → K) (r j : ℕ) :
    (block (r := r) (fun k i => moment H u v (k+i.val)) j).det.natDegree ≤ r+1 := by
  let M (w : K → K) : Matrix (Fin (r+1)) (Fin (r+1)) K :=
    fun a b => ApolarDividedLocator.syndrome H (RingHom.id K) w (X^(j+a.val+b.val))
  have he : block (r := r) (fun k i => moment H u v (k+i.val)) j =
      (X : K[X]) • (M v).map C + (M u).map C := by
    apply Matrix.ext
    intro i b
    rfl
  rw [he]
  simpa only [Fintype.card_fin] using natDegree_det_X_add_C_le (M v) (M u)

/-- Extreme coefficients in a coprime coordinate chart satisfy the determinant
degree constraint on the actual received-word pencil. -/
theorem moment_locator_degree (H : Finset K) (u v : K → K) (r a : ℕ)
    (c : Fin (r+1) → K[X]) (z : K[X]) (hcop : IsCoprime z (c 0))
    (hz : z ≠ 0)
    (hinj : ∀ p : Fin (r+1) → K[X], (∀ k < a+r+1,
      (fun i : Fin (r+1) => moment H u v (k+i.val)) ⬝ᵥ p = 0) → p = 0)
    (hrec : ∀ j < a, ∑ i : Fin (r+1), c i • (fun b : Fin (r+1) => moment H u v (j+i.val+b.val)) =
      (-z) • (fun b : Fin (r+1) => moment H u v (j+r+1+b.val))) :
    a*z.natDegree ≤ r+1 := by
  let vs (k : ℕ) (i : Fin (r+1)) := moment H u v (k+i.val)
  have hminor := first_minor_ne_zero vs c hz hrec hinj
  have h := endpoint_dvd vs c z a hrec
  have hd := natDegree_le_of_dvd (hcop.pow.dvd_of_dvd_mul_left h) hminor
  rw [natDegree_pow] at hd
  exact hd.trans (moment_block_degree H u v r 0)

/-- A primitive parameter family admits two coordinate points away from any
prescribed finite set where evaluation preserves parameter degree and the two
specializations are coprime. They can be used as the endpoints of a new chart. -/
theorem exists_coprime_chart [IsAlgClosed K] [Infinite K] (f : K[X][X]) (avoid : Finset K)
    (hprim : ∀ t : K, f.eval (C t) ≠ 0) :
    ∃ x ∉ avoid, ∃ y ∉ avoid, x ≠ y ∧
      (f.map (evalRingHom x)).natDegree = f.natDegree ∧
      (f.map (evalRingHom y)).natDegree = f.natDegree ∧
      IsCoprime (f.map (evalRingHom x)) (f.map (evalRingHom y)) := by
  classical
  have hf : f ≠ 0 := fun h => hprim 0 (by simp [h])
  have hlead : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let bad := avoid ∪ f.leadingCoeff.roots.toFinset
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset bad
  have havoid {a : K} (ha : a ∉ bad) : a ∉ avoid ∧ f.leadingCoeff.eval a ≠ 0 := by
    refine ⟨fun h => ha (mem_union_left _ h), fun h => ?_⟩
    exact ha (mem_union_right _ (Multiset.mem_toFinset.mpr ((mem_roots hlead).mpr h)))
  let fx := f.map (evalRingHom x)
  have hxlead := (havoid hx).2
  have hfx : fx ≠ 0 := by
    intro he
    have hc : (f.map (evalRingHom x)).coeff f.natDegree = 0 := by
      rw [show f.map (evalRingHom x) = 0 from he, coeff_zero]
    rw [coeff_map] at hc
    exact hxlead hc
  let roots := fx.roots.toFinset
  let bad₂ := insert x (bad ∪ roots.biUnion (fun t => (f.eval (C t)).roots.toFinset))
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset bad₂
  have hxy : x ≠ y := by intro h; exact hy (h ▸ mem_insert_self ..)
  have hybad : y ∉ bad := fun h => hy (mem_insert_of_mem (mem_union_left _ h))
  refine ⟨x,(havoid hx).1,y,(havoid hybad).1,hxy,
    natDegree_map_eq_iff.mpr (Or.inl hxlead), natDegree_map_eq_iff.mpr (Or.inl (havoid hybad).2), ?_⟩
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).2
  intro t
  by_cases ht : t ∈ roots
  · right
    have hh : (f.eval (C t)).eval y ≠ 0 := by
      intro h
      exact hy (mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr
        ⟨t,ht,Multiset.mem_toFinset.mpr ((mem_roots (hprim t)).mpr h)⟩)))
    have comm : (f.map (evalRingHom y)).eval t = (f.eval (C t)).eval y := by
      rw [eval_map]
      simpa using (eval₂_hom (p := f) (f := evalRingHom y) (C t))
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, comm] using hh
  · left
    have hne : fx.eval t ≠ 0 := fun h => ht (Multiset.mem_toFinset.mpr ((mem_roots hfx).mpr h))
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, fx] using hne

#print axioms exists_coprime_chart

#print axioms slide
#print axioms moment_locator_degree

end ProximityGap.ApolarHankelMinors
