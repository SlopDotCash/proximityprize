/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ToricGraphMinorTransfer
import ArkLib.Data.CodingTheory.AGL24Submatrix

/-! # Transporting a rational interpolation constraint between root grids -/
namespace ProximityGap.ToricInterpolationKernel
open Finset Polynomial ToricGraphMinorTransfer
noncomputable section

/-- Common labels for the two blocks of polynomial coefficients. -/
private def label (t : ℕ) : Fin (2*t) ≃ Fin 2 × Fin t := (finProdFinEquiv (m:=2) (n:=t)).symm

private def ux {t : ℕ} (j : Fin (2*t)) : ℕ := ((label t j).2).val
private def vy {t : ℕ} (j : Fin (2*t)) : ℕ := ((label t j).1).val

private def reversal (t : ℕ) : Equiv.Perm (Fin (2*t)) :=
  ((label t).trans (Equiv.prodCongr Fin.revPerm Fin.revPerm)).trans (label t).symm

private theorem ux_reverse {d : ℕ} (j : Fin (2*(d+1))) :
    ux j+ux (reversal (d+1) j)=d := by
  simp [ux,reversal,Fin.rev];omega

private theorem vy_reverse {t : ℕ} (j : Fin (2*t)) : vy j+vy (reversal t j)=1 := by
  simp [vy,reversal,Fin.rev];omega

private def poly {K : Type*} [Field K] {t : ℕ} (v : Fin (2*t) → K) (b : Fin 2) : K[X] :=
  ∑ j : Fin t, C (v ((label t).symm (b,j)))*X^j.val

private theorem poly_coeff {K : Type*} [Field K] {t : ℕ} (v : Fin (2*t) → K) (b : Fin 2) (i : Fin t) :
    (poly v b).coeff i.val=v ((label t).symm (b,i)) := by
  simp only [poly,finsetSum_coeff,coeff_C_mul,coeff_X_pow]
  rw [sum_eq_single i]
  · simp
  · intro j _ ne
    have h : i.val≠j.val := fun eq => ne (Fin.ext eq.symm)
    simp [h]
  · simp

private theorem deg {K : Type*} [Field K] {d : ℕ} (v : Fin (2*(d+1)) → K) (b : Fin 2) :
    (poly v b).natDegree≤d := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le ..).trans (by simpa using j.isLt)

private theorem kernel_eval {K : Type*} [Field K] {t : ℕ}
    (z : K) (a b : ℕ) (v : Fin (2*t) → K) :
    ∑ j, z^(a*ux j+b*vy j)*v j =
      (poly v 0).eval (z^a)+z^b*(poly v 1).eval (z^a) := by
  classical
  rw [← (label t).symm.sum_comp (fun j => z^(a*ux j+b*vy j)*v j),Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [ux,vy,Equiv.apply_symm_apply,Fin.val_zero,Fin.val_one,mul_zero,add_zero,mul_one,pow_add,pow_mul]
  simp only [poly,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Finset.mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro j _ <;> ring

private def coeffs {K : Type*} [Field K] (d : ℕ) (P Q : K[X]) (j : Fin (2*(d+1))) : K :=
  if (label (d+1) j).1=0 then P.coeff (ux j) else -Q.coeff (ux j)

private theorem realize {K : Type*} [Field K] {d : ℕ} (P Q : K[X])
    (p : P.natDegree≤d) (q : Q.natDegree≤d) :
    poly (coeffs d P Q) 0=P ∧ poly (coeffs d P Q) 1= -Q := by
  have eq (b : Fin 2) (S : K[X]) (sd : S.natDegree≤d)
      (same : ∀ j : Fin (d+1), coeffs d P Q ((label _).symm (b,j))=S.coeff j.val) :
      poly (coeffs d P Q) b=S := by
    ext j
    by_cases h : j<d+1
    · exact (poly_coeff _ b ⟨j,h⟩).trans (same ⟨j,h⟩)
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (deg ..) (by omega)),
        coeff_eq_zero_of_natDegree_lt (by omega : S.natDegree<j)]
  exact ⟨eq 0 P p (by intro j;simp [coeffs,ux]),eq 1 (-Q) (by simpa using q)
    (by intro j;simp [coeffs,ux])⟩

/-- The same pattern of finite matches has a nonzero degree-d polynomial
relation on any comparison orbit. Base points of the transported pair are
allowed. -/
theorem transport {n p d : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    {K : Type*} [Field K] [NeZero (n : K)] {F : Type*} [Fintype F] [DecidableEq F]
    {z : ZMod p} {w : K} (hn : 2<n) (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (large : (2*(d+1))^((d+1)*n.totient)<p^2) (A B : F → ℕ)
    (P Q : (ZMod p)[X]) (pd : P.natDegree≤d) (qd : Q.natDegree≤d) (qn : Q≠0)
    (law : ∀ i, P.eval (z^(A i)) = z^(B i)*Q.eval (z^(A i))) :
    ∃ S T : K[X], (S≠0 ∨ T≠0) ∧ S.natDegree≤d ∧ T.natDegree≤d ∧
      ∀ i, S.eval (w^(A i))=w^(B i)*T.eval (w^(A i)) := by
  classical
  let t := d+1
  let M : Matrix F (Fin (2*t)) K := fun i j => w^(A i*ux j+B i*vy j)
  have input := realize P Q pd qd
  have cv : coeffs d P Q≠0 := by
    intro eq
    apply qn
    have h := input.2
    rw [eq] at h
    simpa [poly] using h.symm
  have ker : ∃ g : Fin (2*t) → K, g≠0 ∧ M.mulVec g=0 := by
    by_contra! full
    obtain ⟨rows,_,hd⟩ := AGL24.exists_square_submatrix_det_ne_zero M
      (fun v hn => by by_contra! ne;exact full _ ne hn)
    apply hd
    change (matrix w (A ∘ rows) (B ∘ rows) ux vy).det=0
    apply ToricGraphMinorTransfer.transfer hn hz hw _ _ _ _ (reversal t) ux_reverse vy_reverse _ large
    by_contra! det
    apply cv
    apply Matrix.eq_zero_of_mulVec_eq_zero det
    funext i
    change (∑ j, z^(A (rows i)*ux j+B (rows i)*vy j)*coeffs d P Q j)=0
    rw [kernel_eval,input.1,input.2,eval_neg,law]
    ring
  obtain ⟨g,gn,kg⟩ := ker
  refine ⟨poly g 0,-poly g 1,?_,deg ..,by simpa using deg g 1,?_⟩
  · by_contra! bad
    apply gn
    funext j
    rcases hpair : label t j with ⟨b,i⟩
    have back : (label t).symm (b,i)=j := by rw [←hpair,Equiv.symm_apply_apply]
    rw [←back,←poly_coeff g b i]
    fin_cases b <;> simp_all
  · intro i
    have h := congrFun kg i
    change (∑ j, w^(A i*ux j+B i*vy j)*g j)=0 at h
    rw [kernel_eval] at h
    rw [eval_neg]; linear_combination h

end
end ProximityGap.ToricInterpolationKernel
#print axioms ProximityGap.ToricInterpolationKernel.transport
