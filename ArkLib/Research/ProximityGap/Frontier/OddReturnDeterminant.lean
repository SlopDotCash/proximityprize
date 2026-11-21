/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DyadicOddMomentVanishing
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ArkLib.Research.ProximityGap.Frontier._G86HadamardSupportSix
import Mathlib.Tactic
/-!
# Horizontal prime budget for odd additive returns of dyadic roots

The integer determinant of the identity plus the coordinate shifts on a power of
the cyclic grid is nonzero for odd relation length. Its prime valuations count
the modular Fourier zero modes, and Hadamard bounds its size. Combining these
facts gives an exact integer inequality for any finite set of split primes.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OddReturnDeterminant
open Finset Matrix

variable {m n : ℕ} [NeZero n]
abbrev I (m n : ℕ) := Fin m → ZMod n
variable {K : Type*} [Field K]

/-- Tensor Fourier matrix of the additive grid. -/
def charMatrix (χ : AddChar (ZMod n) K) : Matrix (I m n) (I m n) K :=
  Matrix.of fun i j ↦ ∏ l, χ (i l * j l)

theorem det_charMatrix {χ : AddChar (ZMod n) K} (hχ : χ.IsPrimitive) (hn : (n:K) ≠ 0) :
    (charMatrix (m := m) χ).det ≠ 0 := by
  classical
  let V := charMatrix (m := m) χ
  let W : Matrix (I m n) (I m n) K := Matrix.of fun i j ↦ V (-j) i
  have hgap (i j k : I m n) : V i k * W k j = ∏ l, χ (k l * (i l - j l)) := by
    change (∏ l, χ (i l*k l))*(∏ l, χ ((-j l)*k l))=_
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro l _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have horth : V*W = diagonal (fun _ ↦ (n:K)^m) := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [hgap]
    rw [← Fintype.prod_sum (fun l (x : ZMod n) ↦ χ (x*(i l-j l)))]
    simp_rw [AddChar.sum_mulShift _ hχ, ZMod.card]
    by_cases hij : i=j
    · subst j
      simp
    · rw [diagonal_apply_ne _ hij]
      obtain ⟨l,hl⟩ : ∃ l, i l ≠ j l := by simpa [funext_iff] using hij
      exact prod_eq_zero (mem_univ l) (by simp [hl, sub_eq_zero])
  have hd := congrArg det horth
  rw [det_mul, det_diagonal] at hd
  have hne : (∏ _i : I m n, (n:K)^m) ≠ 0 := prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ hn
  exact fun hv ↦ hne (by rw [← hd, show V.det=0 from hv, zero_mul])

def unitVec (h : Fin m) : I m n := Pi.single h 1

/-- Sum of the identity and the positive coordinate translations. -/
def shifts (K : Type*) [CommRing K] (m n : ℕ) [NeZero n] : Matrix (I m n) (I m n) K :=
  1 + ∑ h : Fin m, Matrix.of fun i j ↦ if j=i+unitVec h then 1 else 0

theorem diagonalize (χ : AddChar (ZMod n) K) :
    shifts K m n * charMatrix χ =
      charMatrix χ * diagonal (fun j : I m n ↦ 1 + ∑ h, χ (j h)) := by
  classical
  have htrans (i j : I m n) (h : Fin m) :
      charMatrix χ (i+unitVec h) j = charMatrix χ i j * χ (j h) := by
    have hcoord (l : Fin m) :
        χ ((i l + unitVec (n := n) h l)*j l)=χ (i l*j l)*χ (unitVec (n := n) h l*j l) := by
      rw [add_mul, AddChar.map_add_eq_mul]
    have he : (∏ l, χ (unitVec (n := n) h l * j l))=χ (j h) := by
      rw [prod_eq_single h]
      · simp [unitVec]
      · intro l _ hl
        simp [unitVec, Pi.single_eq_of_ne hl]
      · simp
    change (∏ l, χ ((i l+unitVec (n := n) h l)*j l))=_
    simp_rw [hcoord]
    rw [prod_mul_distrib, he]
    rfl
  ext i j
  rw [shifts, add_mul, one_mul, Matrix.sum_mul, Matrix.add_apply, Matrix.sum_apply,
    Matrix.mul_diagonal, mul_add, mul_one, mul_sum]
  apply congrArg (_ + ·)
  apply sum_congr rfl
  intro h _
  rw [Matrix.mul_apply]
  simp [Matrix.of_apply, ite_mul, htrans]


theorem shifts_map (K : Type*) [CommRing K] :
    (Int.castRingHom K).mapMatrix (shifts ℤ m n) = shifts K m n := by
  classical
  unfold shifts
  rw [map_add, map_one, map_sum]
  apply congrArg (1 + ·)
  apply sum_congr rfl
  intro h _
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem det_shifts_eq_prod {χ : AddChar (ZMod n) K} (hχ : χ.IsPrimitive) (hn : (n:K) ≠ 0) :
    (shifts K m n).det = ∏ j : I m n, (1 + ∑ h, χ (j h)) := by
  have h := congrArg det (diagonalize (m := m) χ)
  rw [det_mul, det_mul, det_diagonal, mul_comm (shifts K m n).det] at h
  exact mul_left_cancel₀ (det_charMatrix hχ hn) h

theorem modular_dvd {p : ℕ} [Fact p.Prime] (χ : AddChar (ZMod n) (ZMod p)) (hχ : χ.IsPrimitive)
    (hn : (n : ZMod p) ≠ 0) :
    (p:ℤ)^(univ.filter (fun j : I m n ↦ 1+ ∑ h,χ (j h)=0)).card ∣ (shifts ℤ m n).det := by
  classical
  let S := univ.filter (fun j : I m n ↦ 1+ ∑ h,χ (j h)=0)
  let D := shifts ℤ m n
  let f := Int.castRingHom (ZMod p)
  let V := charMatrix (m := m) χ
  let A : Matrix (I m n) (I m n) ℤ := Matrix.of fun i j ↦ ((V i j).val : ℤ)
  have hA : f.mapMatrix A = V := by ext i j; simp [A,f,RingHom.mapMatrix_apply]
  have hd : ¬(p:ℤ) ∣ A.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hh : f A.det = V.det := (f.map_det A).trans (congrArg det hA)
    change f A.det ≠ 0
    rw [hh]
    exact det_charMatrix hχ hn
  have hcol : ∀ j ∈ S, ∀ i, (p:ℤ) ∣ (D*A) i j := by
    intro j hj i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change f.mapMatrix (D*A) i j=0
    rw [map_mul, hA, show f.mapMatrix D=shifts (ZMod p) m n from shifts_map _, diagonalize (m:=m) χ,
      Matrix.mul_diagonal, (mem_filter.mp hj).2, mul_zero]
  have hboth := Matrix.pow_dvd_det_of_forall_mem_col_dvd (D*A) (p:ℤ) S hcol
  rw [det_mul] at hboth
  exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).pow_dvd_of_dvd_mul_right S.card hd hboth

theorem det_ne_zero_dyadic (e m : ℕ) (hodd : Odd (m+1)) :
    (shifts ℤ m (2^e)).det ≠ 0 := by
  classical
  let n := 2^e
  have hn : n ≠ 0 := by dsimp [n]; positivity
  let : NeZero n := ⟨hn⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  let χ := AddChar.zmodChar n hζ.pow_eq_one
  have hχ : χ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root n hζ
  have hK : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : (shifts ℂ m n).det ≠ 0 := by
    rw [det_shifts_eq_prod hχ hK]
    apply prod_ne_zero_iff.mpr
    intro j _ hj
    let T : Multiset ℂ := 1 ::ₘ (univ.val.map (fun h : Fin m ↦ χ (j h)))
    have hroot : ∀ z ∈ T, z^(2^e)=1 := by
      intro z hz
      rcases Multiset.mem_cons.mp hz with rfl | hz
      · simp
      · obtain ⟨l,_,rfl⟩ := Multiset.mem_map.mp hz
        change (ζ ^ (j l).val)^n=1
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hs : T.sum = 0 := by
      change 1 + (univ.val.map (fun h : Fin m ↦ χ (j h))).sum=0
      exact hj
    have hev := DyadicOddMomentVanishing.even_card_of_vanishing_dyadic_multiset hroot hs
    have hcard : T.card=m+1 := by simp [T]
    rw [hcard] at hev
    exact (Nat.not_even_iff_odd.mpr hodd) hev
  intro h
  apply hc
  rw [←shifts_map ℂ, ← (Int.castRingHom ℂ).map_det]
  change ((shifts ℤ m (2^e)).det : ℂ)=0
  rw [h,Int.cast_zero]

/-- Each row has exactly the identity shift and the distinct coordinate shifts. -/
theorem row_sq_sum [Nontrivial (ZMod n)] (i : I m n) :
    ∑ j, shifts ℤ m n i j ^ 2 = (m:ℤ)+1 := by
  classical
  let t := fun h : Fin m ↦ i + unitVec (n := n) h
  have hi (h : Fin m) : t h ≠ i := by
    intro hh
    have hh' : unitVec (n := n) h = 0 := by simpa [t] using hh
    have hx := congrFun hh' h
    simp [unitVec] at hx
  have hinj : Function.Injective t := by
    intro h l he
    obtain hh : unitVec (n := n) h = unitVec l := add_left_cancel he
    by_contra hne
    have hx := congrFun hh h
    simp [unitVec, Pi.single_eq_of_ne hne] at hx
  have hentry (j : I m n) : shifts ℤ m n i j =
      (if i=j then 1 else 0) + ∑ h, (if j=t h then 1 else 0) := by
    simp [shifts, Matrix.one_apply, Matrix.sum_apply, t]
  have hidem (j : I m n) : shifts ℤ m n i j ^ 2 = shifts ℤ m n i j := by
    rw [hentry]
    by_cases je : j=i
    · subst j
      simp [fun h ↦ Ne.symm (hi h)]
    · by_cases he : ∃ h, j=t h
      · obtain ⟨h,rfl⟩ := he
        rw [sum_eq_single h]
        · simp [Ne.symm (hi h)]
        · intro l _ hl
          simp [show t h ≠ t l from fun eq ↦ hl (hinj eq).symm]
        · simp
      · push Not at he
        simp [he,Ne.symm je]
  simp_rw [hidem,hentry]
  rw [sum_add_distrib, sum_comm]
  simp [add_comm]

theorem det_sq_bound [Nontrivial (ZMod n)] :
    (shifts ℤ m n).det ^ 2 ≤ ((m:ℤ)+1)^(n^m) := by
  classical
  let E := Fintype.equivFin (I m n)
  let D := shifts ℤ m n
  have hcard : Fintype.card (I m n) = n^m := by simp [I,ZMod.card]
  have hh := G86HadamardSupportSix.sq_det_le_pow_of_row_sq_sum_le (Matrix.reindex E E D) (m+1) (by
    intro i
    change (∑ j, D (E.symm i) (E.symm j)^2) ≤ _
    rw [Equiv.sum_comp E.symm (fun j ↦ D (E.symm i) j ^ 2), show (∑ j, D (E.symm i) j ^ 2)=(m:ℤ)+1 from row_sq_sum _]
    simp)
  rw [Matrix.det_reindex_self, hcard] at hh
  exact_mod_cast hh
/-- Number of ordered normalized additive relations amongst the field's actual roots. -/
noncomputable def returnCount (m n p : ℕ) : ℕ :=
  Nat.card {x : Fin m → {z : ZMod p // z^n=1} // 1 + ∑ h, (x h : ZMod p) = 0}

theorem prime_dvd {p : ℕ} [Fact p.Prime] (hsplit : n ∣ p-1) :
    (p:ℤ)^(returnCount m n p) ∣ (shifts ℤ m n).det := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hgen : IsPrimitiveRoot (g : ZMod p) (p-1) := IsPrimitiveRoot.coe_units_iff.mpr <|
    IsPrimitiveRoot.iff_orderOf.mpr (by simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hg)
  have hle := Nat.le_of_dvd (show 0<p-1 by omega) hsplit
  obtain ⟨c,hc⟩ := hsplit
  let ζ := (g : ZMod p)^c
  have hζ : IsPrimitiveRoot ζ n := hgen.pow (by omega) (by simpa [Nat.mul_comm] using hc)
  let χ := AddChar.zmodChar n hζ.pow_eq_one
  let P := {z : ZMod p // z ^ n = 1}
  let f : ZMod n → P := fun j ↦ ⟨χ j, by
    change (ζ^j.val)^n=1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j he
      apply ZMod.val_injective n
      exact hζ.pow_inj i.val_lt j.val_lt (congrArg Subtype.val he)
    · intro z
      obtain ⟨v,hv,he⟩ := hζ.eq_pow_of_pow_eq_one z.property
      refine ⟨(v : ZMod n),Subtype.ext ?_⟩
      change ζ ^ (v : ZMod n).val = z.val
      rwa [ZMod.val_natCast_of_lt hv]
  let E := Equiv.piCongrRight (fun _ : Fin m ↦ Equiv.ofBijective f hbij)
  have hc' : returnCount m n p =
      (univ.filter (fun j : I m n ↦ 1+∑ h,χ (j h)=0)).card := by
    let M := E.subtypeEquiv (p := fun j ↦ 1+∑ h,χ (j h)=0)
      (q := fun x ↦ 1+∑ h,(x h : ZMod p)=0) (fun _ ↦ Iff.rfl)
    unfold returnCount
    rw [← Nat.card_congr M, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  rw [hc']
  apply modular_dvd χ (AddChar.zmodChar_primitive_of_primitive_root n hζ)
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact fun hd ↦ (not_le_of_gt (show n<p by omega)) (Nat.le_of_dvd (NeZero.pos n) hd)

/-- Simultaneous finite-prime budget, squared to give an integer form of the half-log bound. -/
theorem split_prime_product_sq_le (e m : ℕ) (he : 0<e) (ho : Odd (m+1)) (P : Finset ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p) (hs : ∀ p ∈ P, 2^e ∣ p-1) :
    (∏ p ∈ P, p^(returnCount m (2^e) p))^2 ≤ (m+1)^((2^e)^m) := by
  classical
  let n := 2^e
  let D := (shifts ℤ m n).det
  have hx : 1<n := Nat.one_lt_pow he.ne' (by decide)
  let : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hx.ne'
  have hd : (∏ p ∈ P, p^(returnCount m n p)) ∣ D.natAbs :=
    prod_dvd_of_isRelPrime (fun p hp' q hq' hne ↦
      Nat.coprime_iff_isRelPrime.mp (((Nat.coprime_primes (hp p hp') (hp q hq')).mpr hne).pow _ _))
      (fun p hmem ↦ by
        let : Fact p.Prime := ⟨hp p hmem⟩
        apply Int.natCast_dvd_natCast.mp
        rw [Nat.cast_pow]
        exact Int.dvd_natAbs.mpr (prime_dvd (m := m) (hs p hmem)))
  have hle := Nat.pow_le_pow_left (Nat.le_of_dvd
    (Int.natAbs_pos.mpr (det_ne_zero_dyadic e m ho)) hd) 2
  apply hle.trans
  have hh := det_sq_bound (m := m) (n := n)
  zify
  rw [sq_abs]
  simpa [D] using hh

#print axioms prime_dvd
#print axioms split_prime_product_sq_le
#print axioms modular_dvd
#print axioms det_ne_zero_dyadic

end ArkLib.ProximityGap.Frontier.OddReturnDeterminant
