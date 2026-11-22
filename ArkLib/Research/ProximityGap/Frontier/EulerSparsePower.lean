/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! # Two concentrated powers cannot agree in all middle coefficients

The operator X∂−j kills the j-th coefficient, preserves all other supports,
and lowers a positive root multiplicity away from zero by exactly one while
the multiplicity is invertible. Killing the two endpoint blocks forces three
large coprime powers to divide the same surviving polynomial.
-/

namespace ProximityGap.EulerSparsePower
open Polynomial
variable {F : Type} [Field F]

private noncomputable def euler (j : ℕ) (P : F[X]) := X*P.derivative-C (j:F)*P

private theorem coeff_euler (j i : ℕ) (P : F[X]) :
    (euler j P).coeff i=((i:F)-j)*P.coeff i := by
  cases i with
  | zero => simp [euler]
  | succ i => simp only [euler,coeff_sub,coeff_X_mul,coeff_C_mul,coeff_derivative];push_cast;ring

private noncomputable def cut (J : List ℕ) (P : F[X]) : F[X] :=
  match J with
  | [] => P
  | j::K => cut K (euler j P)

private theorem coeff_cut (J : List ℕ) (P : F[X]) (i : ℕ) :
    (cut J P).coeff i = ((J.map fun j : ℕ => (i:F)-(j:F)).prod)*P.coeff i := by
  induction J generalizing P with
  | nil => simp [cut]
  | cons j K ih => rw [cut,ih,coeff_euler];simp;ring

private theorem killed {J : List ℕ} (P : F[X]) {i : ℕ} (hi : i∈J) : (cut J P).coeff i=0 := by
  rw [coeff_cut,show ((J.map fun j : ℕ => (i:F)-(j:F)).prod)=0 by
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨i,hi,sub_self _⟩,zero_mul]

private def ExactOrder (x : F) (m : ℕ) (P : F[X]) : Prop :=
  ∃ A : F[X], P=(X-C x)^m*A ∧ A.eval x≠0

private theorem drop {x : F} (nx : x≠0) {m : ℕ} (nonzero : ((m+1:ℕ):F)≠0)
    {P : F[X]} (ord : ExactOrder x (m+1) P) (j : ℕ) : ExactOrder x m (euler j P) := by
  obtain ⟨A,rfl,nonvanish⟩ := ord
  refine ⟨X*(C ((m+1:ℕ):F)*A+(X-C x)*A.derivative)-C (j:F)*(X-C x)*A,?_,?_⟩
  · rw [euler,derivative_mul,derivative_X_sub_C_pow]
    simp only [Nat.add_sub_cancel,pow_succ]
    ring
  · rw [Nat.cast_add_one] at nonzero
    simp [nx,nonzero,nonvanish]

private theorem order_cut {x : F} (nx : x≠0) (J : List ℕ) {m : ℕ} (enough : J.length≤m)
    (units : ∀ i : ℕ, 0 < i → i ≤ m → (i:F)≠0) {P : F[X]} (ord : ExactOrder x m P) :
    ExactOrder x (m-J.length) (cut J P) := by
  induction J generalizing m P with
  | nil => simpa [cut] using ord
  | cons j K ih =>
    cases m with
    | zero => simp at enough
    | succ m =>
      have next := drop nx (units _ (by omega) le_rfl) ord j
      have len : K.length≤m := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using enough
      have reduced := ih (m:=m) (P:=euler j P) len (fun i hi hm => units i hi (Nat.le_succ_of_le hm)) next
      simpa only [List.length_cons,Nat.succ_sub_succ_eq_sub,cut] using reduced

private theorem survives {x : F} (nx : x≠0) {N M : ℕ} (J : List ℕ) (enough : J.length≤N)
    (units : ∀ i : ℕ, 0 < i → i ≤ M → (i:F)≠0) {P : F[X]} (nz : P≠0) (degree : P.natDegree≤M)
    (factor : (X-C x)^N ∣ P) : cut J P≠0 ∧ (X-C x)^(N-J.length) ∣ cut J P := by
  let m := P.rootMultiplicity x
  have lower : N≤m := (le_rootMultiplicity_iff nz).mpr factor
  have upper : m≤P.natDegree := by
    have bound := natDegree_le_of_dvd (P.pow_rootMultiplicity_dvd x) nz
    simpa only [natDegree_pow,natDegree_X_sub_C,mul_one] using bound
  obtain ⟨A,hA,notDvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd nz x
  obtain ⟨B,hB,good⟩ := order_cut nx J (by omega : J.length≤m)
    (fun i hi him => units i hi (by omega)) (show ExactOrder x m P from
      ⟨A,hA,fun z => notDvd (dvd_iff_isRoot.mpr z)⟩)
  have bNZ : B≠0 := fun eq => good (by simp [eq])
  rw [hB]
  exact ⟨mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) bNZ,
    (pow_dvd_pow _ (Nat.sub_le_sub_right lower J.length)).trans (dvd_mul_right ..)⟩

private def slots (n r : ℕ) := List.range (r+1) ++ (List.range (r+1)).map (n+·)

private theorem low {n r i : ℕ} (h : i ≤ r) : i∈slots n r :=
  List.mem_append_left _ (List.mem_range.mpr (by omega))

private theorem high {n r i : ℕ} (h : n ≤ i) (bound : i ≤ n+r) : i∈slots n r :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i-n,List.mem_range.mpr (by omega),by omega⟩)

/-- If two nonzero degree-at-most n+r polynomials have n-fold roots at
separate nonzero centers, their coefficients differ somewhere strictly between
r and n, as soon as 3r+2<n. -/
theorem middle_differs {n r : ℕ} (gap : 3*r+2<n)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+r → (i:F)≠0)
    {x y : F} (nx : x≠0) (ny : y≠0) (xy : x≠y) {P Q : F[X]}
    (nzP : P≠0) (nzQ : Q≠0) (degP : P.natDegree≤n+r) (degQ : Q.natDegree≤n+r)
    (fx : (X-C x)^n∣P) (fy : (X-C y)^n∣Q) :
    ∃ i : ℕ, r < i ∧ i < n ∧ P.coeff i≠Q.coeff i := by
  by_contra! same
  let J := slots n r
  have size : J.length=2*r+2 := by simp [J,slots];omega
  let Z := cut J P
  have eq : Z=cut J Q := by
    ext i
    by_cases inJ : i∈J
    · exact (killed P inJ).trans (killed Q inJ).symm
    change (cut J P).coeff i=(cut J Q).coeff i
    rw [coeff_cut,coeff_cut]
    congr 1
    by_cases beyond : n+r < i
    · rw [coeff_eq_zero_of_natDegree_lt (degP.trans_lt beyond),coeff_eq_zero_of_natDegree_lt (degQ.trans_lt beyond)]
    exact same i (by by_contra! small;exact inJ (low small))
      (by by_contra! big;exact inJ (high big (by omega)))
  have ⟨nz,dx⟩ := survives nx J (by omega : J.length≤n) units nzP degP fx
  have dy := (survives ny J (by omega : J.length≤n) units nzQ degQ fy).2
  rw [←eq] at dy
  have dz : (X:F[X])^(r+1)∣Z := X_pow_dvd_iff.mpr (fun i hi => killed P (low (by omega)))
  have top : Z.natDegree<n := by
    by_contra! big
    apply coeff_natDegree (p:=Z) ▸ (leadingCoeff_ne_zero.mpr nz)
    by_cases beyond : n+r<Z.natDegree
    · rw [show Z=cut J P from rfl,coeff_cut]
      exact mul_eq_zero_of_right _ (coeff_eq_zero_of_natDegree_lt (degP.trans_lt beyond))
    exact killed P (high big (by omega))
  let t := n-J.length
  have cp {u v : F} (uv : u≠v) (s t : ℕ) : IsCoprime ((X-C u)^s) ((X-C v)^t) :=
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr uv).isUnit).pow
  have zeroCP {w : F} (hw : w≠0) : IsCoprime ((X:F[X])^(r+1)) ((X-C w)^t) := by
    simpa only [map_zero,sub_zero] using cp hw.symm (r+1) t
  have divide := ((zeroCP ny).mul_left (cp xy t t)).mul_dvd ((zeroCP nx).mul_dvd dz dx) dy
  have degree := natDegree_le_of_dvd divide nz
  have dx0 := pow_ne_zero t (X_sub_C_ne_zero x)
  have dy0 := pow_ne_zero t (X_sub_C_ne_zero y)
  have d00 := pow_ne_zero (r+1) (X_ne_zero (R:=F))
  simp only [natDegree_mul (mul_ne_zero d00 dx0) dy0,natDegree_mul d00 dx0,natDegree_pow,
    natDegree_X,natDegree_X_sub_C,mul_one] at degree
  dsimp only [t] at degree
  omega

/-- The same middle band contains a nonzero coefficient for each nonzero
polynomial concentrated at a finite nonzero center. -/
theorem middle_nonzero {n r : ℕ} (gap : 2*r+2≤n)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+r → (i:F)≠0)
    {x : F} (nx : x≠0) {P : F[X]} (nz : P≠0) (degree : P.natDegree≤n+r)
    (factor : (X-C x)^n∣P) : ∃ i : ℕ, r < i ∧ i < n ∧ P.coeff i≠0 := by
  by_contra! same
  let J := slots n r
  have size : J.length=2*r+2 := by simp [J,slots];omega
  apply (survives nx J (by omega : J.length≤n) units nz degree factor).1
  ext i
  rw [coeff_zero]
  by_cases hi : i∈J
  · exact killed P hi
  rw [coeff_cut]
  apply mul_eq_zero_of_right
  by_cases beyond : n+r < i
  · exact coeff_eq_zero_of_natDegree_lt (degree.trans_lt beyond)
  exact same i (by by_contra! small;exact hi (low small))
    (by by_contra! big;exact hi (high big (by omega)))

end ProximityGap.EulerSparsePower
#print axioms ProximityGap.EulerSparsePower.middle_differs
#print axioms ProximityGap.EulerSparsePower.middle_nonzero
