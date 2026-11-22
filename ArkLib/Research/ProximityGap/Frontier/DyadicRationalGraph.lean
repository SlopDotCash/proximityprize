/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicRationalDegree
import Mathlib.RingTheory.EuclideanDomain

/-! # Dense dyadic graphs with possible common interpolation zeros -/

namespace ProximityGap.DyadicRationalGraph
open Finset Polynomial DyadicRationalDegree
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [Normal ℚ K]

/-- More than twelve times the degree in distinct dyadic samples forces a
monomial on a subset larger than twice the original degree. Common zeros of
the interpolating pair may occur among the discarded samples. -/
theorem dense {d m n : ℕ} {z : K} (hz : IsPrimitiveRoot z (2^m))
    (S T : K[X]) (nonzero : S≠0 ∨ T≠0) (sd : S.natDegree≤d) (td : T.natDegree≤d)
    (A B : Fin n → ℕ) (inj : Function.Injective (fun i => z^(A i)))
    (law : ∀ i, S.eval (z^(A i))=z^(B i)*T.eval (z^(A i))) (many : 12*d<n) :
    ∃ (good : Finset (Fin n)) (r s : ℕ) (c : K), 2*d<good.card ∧ r≤d ∧ s≤d ∧ c≠0 ∧
      ∀ i ∈ good, z^(B i)*(z^(A i))^s=c*(z^(A i))^r := by
  classical
  let x (i : Fin n) := z^(A i)
  let y (i : Fin n) := z^(B i)
  have zn := hz.ne_zero (by positivity)
  have yn (i) : y i≠0 := pow_ne_zero _ zn
  have any_zero (H : K[X]) (hd : H.natDegree≤d) (roots : ∀ i, H.eval (x i)=0) : H=0 := by
    by_contra ne
    have bound := DyadicRationalSites.zeros ne x inj univ (fun i _ => roots i)
    simp only [card_univ,Fintype.card_fin] at bound
    omega
  have tn : T≠0 := by
    intro zero
    have es := any_zero S sd (fun i => by simpa [zero] using law i)
    exact nonzero.elim (fun h => h es) (fun h => h zero)
  have sn : S≠0 := by
    intro zero
    apply tn
    apply any_zero _ td
    intro i
    have h := law i
    rw [zero,eval_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (yn i)
  let G := GCDMonoid.gcd S T
  let U := S/G
  let V := T/G
  have gn : G≠0 := gcd_ne_zero_of_right tn
  have un : U≠0 := left_div_gcd_ne_zero sn
  have vn : V≠0 := right_div_gcd_ne_zero tn
  have cop : IsCoprime U V := isCoprime_div_gcd_div_gcd tn
  have gu : G*U=S := EuclideanDomain.mul_div_cancel' gn (gcd_dvd_left S T)
  have gv : G*V=T := EuclideanDomain.mul_div_cancel' gn (gcd_dvd_right S T)
  have du := natDegree_mul gn un
  have dv := natDegree_mul gn vn
  rw [gu] at du
  rw [gv] at dv
  let bad := univ.filter fun i => G.eval (x i)=0
  let good := univ \ bad
  have cb : bad.card≤G.natDegree := DyadicRationalSites.zeros gn x inj bad
    (fun i hi => (mem_filter.mp hi).2)
  have size : good.card+bad.card=n := by
    simpa [good] using card_sdiff_add_card_eq_card (s:=bad) (t:=univ) (subset_univ _)
  have red (i) (hi : i ∈ good) : U.eval (x i)=y i*V.eval (x i) := by
    have h := law i
    rw [←gu,←gv,eval_mul,eval_mul] at h
    apply mul_left_cancel₀ (a:=G.eval (x i))
    · simpa [bad] using (mem_sdiff.mp hi).2
    · change G.eval (x i)*U.eval (x i)=G.eval (x i)*(y i*V.eval (x i))
      linear_combination h
  have denom (i) (hi : i ∈ good) : V.eval (x i)≠0 := by
    intro ev
    obtain ⟨u,v,bez⟩ := cop
    have h := congrArg (eval (x i)) bez
    simp [red i hi,ev] at h
  have singles : Single U ∧ Single V := by
    by_contra nonsingle
    obtain ⟨f,hf⟩ := DyadicSevenCombinatorics.select good good.card le_rfl
    have cap := DyadicRationalDegree.bound hz U V (d:=d-G.natDegree) (by omega) (by omega)
      un vn cop nonsingle (A ∘ f) (B ∘ f) (inj.comp f.injective)
      (fun i => denom _ (hf i)) (fun i => red _ (hf i))
    omega
  obtain ⟨⟨a,r,ur⟩,b,s,vs⟩ := singles
  have an : a≠0 := fun eq => un (by simp [ur,eq])
  have bn : b≠0 := fun eq => vn (by simp [vs,eq])
  have rd : U.natDegree=r := by rw [ur,natDegree_C_mul an,natDegree_X_pow]
  have ss : V.natDegree=s := by rw [vs,natDegree_C_mul bn,natDegree_X_pow]
  refine ⟨good,r,s,a/b,by omega,by omega,by omega,div_ne_zero an bn,?_⟩
  intro i hi
  have h := red i hi
  rw [ur,vs,eval_mul,eval_mul,eval_C,eval_C,eval_pow,eval_X] at h
  simp only [eval_pow,eval_X] at h
  change y i*x i^s=a/b*x i^r
  field_simp
  linear_combination -h

end ProximityGap.DyadicRationalGraph
#print axioms ProximityGap.DyadicRationalGraph.dense
