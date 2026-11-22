/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CyclotomicPairDeterminant

/-! # Transport of unsigned transposition minors without a chosen anchor -/

namespace ProximityGap.DyadicPairMinorTransfer
open RatioProductNorm
variable {K : Type*} [Field K]

/-- Three unordered pairs determine three coefficient rows (1,x+y,xy). -/
def minor {R : Type*} [CommRing R] (u v x y s t : R) : R :=
  (x+y-u-v)*(s*t-u*v)-(s+t-u-v)*(x*y-u*v)

private theorem profile_iff {z : K} (d : ℕ) (a b : Fin 2 → ℕ) (dv : z^d≠1)
    (da : ∀ i, z^(a i)≠z^d) (db : ∀ i, z^(b i)≠z^d) :
    profile z d a=profile z d b ↔ minor 1 (z^d) (z^(a 0)) (z^(a 1)) (z^(b 0)) (z^(b 1))=0 := by
  rw [profile,profile,Fin.prod_univ_two,Fin.prod_univ_two,div_mul_div_comm,div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (sub_ne_zero.mpr (da 0)) (sub_ne_zero.mpr (da 1)))
      (mul_ne_zero (sub_ne_zero.mpr (db 0)) (sub_ne_zero.mpr (db 1)))]
  constructor
  · intro eq
    apply mul_left_cancel₀ (sub_ne_zero.mpr dv)
    dsimp only [minor]
    linear_combination eq
  · intro eq
    dsimp only [minor] at eq
    linear_combination (z^d-1)*eq

private theorem shifted {n : ℕ} [NeZero n] {z : K} (hw : IsPrimitiveRoot z n)
    (u v x y s t : Fin n) (uv : u≠v) (xv : x≠v) (yv : y≠v) (sv : s≠v) (tv : t≠v) :
    let k := n-u.val
    let d := v.val+k
    let a : Fin 2 → ℕ := ![x.val+k,y.val+k]
    let b : Fin 2 → ℕ := ![s.val+k,t.val+k]
    (¬n∣d) ∧ (∀ i,z^(a i)≠z^d) ∧ (∀ i,z^(b i)≠z^d) ∧
    (profile z d a=profile z d b ↔ minor (z^u.val) (z^v.val) (z^x.val) (z^y.val) (z^s.val) (z^t.val)=0) := by
  dsimp only
  let k := n-u.val
  have nz := hw.ne_zero (NeZero.ne n)
  have kn := pow_ne_zero k nz
  have scaled : z^u.val*z^k=1 := by rw [←pow_add,show u.val+k=n by dsimp [k];omega];exact hw.pow_eq_one
  have sep (i j : Fin n) (ij : i≠j) : z^(i.val+k)≠z^(j.val+k) := by
    rw [pow_add,pow_add]
    exact fun eq => ij (Fin.ext (hw.pow_inj i.isLt j.isLt (mul_right_cancel₀ kn eq)))
  have dv : z^(v.val+k)≠1 := by rw [←scaled,←pow_add]; exact sep v u uv.symm
  have den (i j : Fin n) (hi : i≠v) (hj : j≠v) (e : Fin 2) :
      z^(![i.val+k,j.val+k] e)≠z^(v.val+k) := by fin_cases e <;> first | exact sep i v hi | exact sep j v hj
  refine ⟨fun h => dv ((hw.pow_eq_one_iff_dvd _).mpr h),den x y xv yv,den s t sv tv,?_⟩
  rw [profile_iff _ _ _ dv (den x y xv yv) (den s t sv tv)]
  change minor 1 (z^(v.val+k)) (z^(x.val+k)) (z^(y.val+k)) (z^(s.val+k)) (z^(t.val+k))=0 ↔ _
  have factor : minor 1 (z^(v.val+k)) (z^(x.val+k)) (z^(y.val+k)) (z^(s.val+k)) (z^(t.val+k))=
      (z^k)^3*minor (z^u.val) (z^v.val) (z^x.val) (z^y.val) (z^s.val) (z^t.val) := by
    rw [←scaled]
    simp only [pow_add,minor]
    ring
  rw [factor,mul_eq_zero]
  simp [nz]

/-- A vanishing minor for three transpositions transfers to any second primitive
root. Shifting all six exponents to anchor the first source at one preserves
the zero and uses the stronger height 12 of the pair determinant. -/
theorem transfer {n p : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n:ZMod p)] [NeZero (n:K)]
    {z : ZMod p} {w : K} (length : 2<n) (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (u v x y s t : Fin n) (uv : u≠v) (xv : x≠v) (yv : y≠v) (sv : s≠v) (tv : t≠v)
    (relation : minor (z^u.val) (z^v.val) (z^x.val) (z^y.val) (z^s.val) (z^t.val)=0)
    (large : 12^n.totient<p^2) : minor (w^u.val) (w^v.val) (w^x.val) (w^y.val) (w^s.val) (w^t.val)=0 := by
  obtain ⟨nd,za,zb,pz⟩ := shifted hz u v x y s t uv xv yv sv tv
  obtain ⟨_,wa,wb,pw⟩ := shifted hw u v x y s t uv xv yv sv tv
  exact pw.mp (CyclotomicPairDeterminant.transfer length hz hw _ nd _ _ za zb wa wb (pz.mpr relation) large)

end ProximityGap.DyadicPairMinorTransfer
#print axioms ProximityGap.DyadicPairMinorTransfer.transfer
