/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SylvesterLocalMultiplicity
import ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-! # Determinant charges for rational tangent heads

A column of weight w vanishes to order w in every row agreeing with the received
pair after translation. A nonzero minor limits the total number of agreements
once the numerator and denominator heights of its rows are known.
-/
set_option autoImplicit false
open Finset Matrix Polynomial
namespace ArkLib.ProximityGap.Frontier.TangentVeronesePacking

variable {K I J : Type*} [Field K] [Fintype J] [DecidableEq J]

/-- Local divisibility for any translated evaluation matrix with column weights.
The finite sum on the left accounts for the columns lighter than a. -/
theorem local_charge (M : Matrix J J K[X]) (x : K) (S : Finset J) (w : J → ℕ) (a : ℕ)
    (h : ∀ i ∈ S, ∀ j, (X - C x) ^ (w j) ∣ M i j) :
    (X - C x)^(a*S.card-∑ j, (a-w j)) ∣ M.det := by
  classical
  rw [det_apply]
  apply dvd_sum
  intro σ _
  let v := fun j => if σ j ∈ S then w j else 0
  have hs := Equiv.sum_comp σ (fun j => if j ∈ S then a else 0 : J → ℕ)
  have hcount : (∑ j, if σ j ∈ S then a else 0) = a*S.card := by
    rw [hs]
    simp [Nat.mul_comm]
  have pointwise (j : J) : (if σ j ∈ S then a else 0) ≤ v j + (a-w j) := by
    by_cases hj : σ j ∈ S
    · simp only [v,hj,ite_true]; omega
    · simp [v,hj]
  have hsum := sum_le_sum (s:=univ) (fun j _ => pointwise j)
  rw [hcount,sum_add_distrib] at hsum
  have hd : (X - C x)^(a*S.card-∑ j, (a-w j)) ∣ ∏ j, M (σ j) j := by
    apply (pow_dvd_pow (X - C x) (show a*S.card-∑ j, (a-w j) ≤ ∑ j, v j by omega)).trans
    rw [← prod_pow_eq_pow_sum]
    apply prod_dvd_prod_of_dvd
    intro j _
    by_cases hj : σ j ∈ S
    · simpa only [v,hj,ite_true] using h (σ j) hj j
    · simp [v,hj]
  obtain ⟨b,hb⟩ := hd
  exact ⟨Equiv.Perm.sign σ • b, by rw [hb,mul_smul_comm]⟩

/-- Row heights and column degrees add separately in each Leibniz term. -/
theorem degree_bound (M : Matrix J J K[X]) (row col : J → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ row i + col j) :
    M.det.natDegree ≤ (∑ i, row i)+(∑ j, col j) := by
  classical
  rw [det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le ..).trans <| (natDegree_prod_le ..).trans ?_
  exact (sum_le_sum (s:=univ) (fun j _ => h (σ j) j)).trans
    (by rw [sum_add_distrib,Equiv.sum_comp])

/-- Sum the local charges at distinct sites and combine with the polynomial
degree of the original minor. Factoring the original evaluation matrix through
the translated one suffices at each site. -/
theorem incidence [Fintype I] (dom : I ↪ K) (M : Matrix J J K[X]) (hn : M.det ≠ 0)
    (w row : J → ℕ) (d a : ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ row i + w j * d)
    (S : I → Finset J) (localM basis : I → Matrix J J K[X])
    (heq : ∀ x, M = localM x * basis x)
    (hvan : ∀ x, ∀ i ∈ S x, ∀ j, (X - C (dom x)) ^ (w j) ∣ localM x i j) :
    a*(∑ x, (S x).card) ≤
      Fintype.card I*(∑ j, (a-w j)) + (∑ i, row i) + (∑ j, w j)*d := by
  classical
  have hrt (x : I) : a*(S x).card - ∑ j, (a-w j) ≤ M.det.rootMultiplicity (dom x) := by
    apply (le_rootMultiplicity_iff hn).mpr
    have hh := local_charge (localM x) (dom x) (S x) w a (hvan x)
    have hmul : M.det = (localM x).det * (basis x).det := by rw [heq x,det_mul]
    rw [hmul]
    exact dvd_mul_of_dvd_left hh _
  have hs := sum_le_sum (s:=univ) (fun x _ =>
    show a*(S x).card ≤ (∑ j, (a-w j)) + M.det.rootMultiplicity (dom x) by
      have := hrt x
      omega)
  rw [← mul_sum,sum_add_distrib] at hs
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have hu : (∑ x, M.det.rootMultiplicity (dom x)) ≤ M.det.natDegree := by
    calc
      _ = ∑ x ∈ univ.image dom, M.det.rootMultiplicity x := by rw [sum_image dom.injective.injOn]
      _ ≤ _ := Polynomial.sum_rootMultiplicity_le_natDegree _
  have hd := degree_bound M row (fun j => w j * d) hdeg
  rw [← sum_mul] at hd
  calc
    _ ≤ _ := hs
    _ ≤ Fintype.card I*(∑ j, (a-w j)) + ((∑ i, row i)+(∑ j, w j)*d) :=
      Nat.add_le_add_left (hu.trans hd) _
    _ = _ := by omega

/-- Exponents of the full homogeneous plane evaluation basis, using the
exponents of the last two coordinates. -/
def monomials (s : ℕ) : Finset (ℕ × ℕ) :=
  ((range (s+1)) ×ˢ (range (s+1))).filter fun ij => ij.1+ij.2 ≤ s

private theorem mem_monomials (s i j : ℕ) : (i,j) ∈ monomials s ↔ i+j ≤ s := by
  simp only [monomials,mem_filter,mem_product,mem_range]
  omega

variable {R : Type*} [CommRing R]

/-- A degree-s homogeneous evaluation at the point (h,x,y). -/
def monomial (s : ℕ) (ij : ℕ × ℕ) (h x y : R) :=
  h^(s-(ij.1+ij.2))*x^ij.1*y^ij.2

private def translateCoeff (u v : R) (ab ij : ℕ × ℕ) : R :=
  if ij.1 ≤ ab.1 ∧ ij.2 ≤ ab.2 then
    u^(ab.1-ij.1)*v^(ab.2-ij.2)*(ab.1.choose ij.1)*(ab.2.choose ij.2) else 0

/-- Translating the two affine coordinates gives a common column transformation
for every homogeneous row, including rows with different denominators. -/
theorem translate_row (s a b : ℕ) (hab : a + b ≤ s) (h x y u v : R) :
    monomial s (a,b) h x y = ∑ ij ∈ monomials s,
      monomial s ij h (x-u*h) (y-v*h)*translateCoeff u v (a,b) ij := by
  classical
  let T := range (a+1) ×ˢ range (b+1)
  have sub : T ⊆ monomials s := by
    rintro ⟨i,j⟩ hij
    simp only [T,mem_product,mem_range] at hij
    apply (mem_monomials ..).mpr
    omega
  rw [← sum_subset sub (fun ij _ hn => ?_)]
  · rw [sum_product]
    calc
      monomial s (a,b) h x y =
          h^(s-(a+b))*((x-u*h)+u*h)^a*((y-v*h)+v*h)^b := by simp [monomial]
      _ = _ := by
        rw [add_pow,add_pow,Finset.mul_sum (range (a+1)),sum_mul]
        apply sum_congr rfl
        intro i hi
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        have ha : i ≤ a := by simpa only [mem_range,Nat.lt_succ_iff] using hi
        have hb : j ≤ b := by simpa only [mem_range,Nat.lt_succ_iff] using hj
        have powH : h^(s-(i+j)) = h^(s-(a+b))*h^(a-i)*h^(b-j) := by
          rw [← pow_add,← pow_add]
          congr 1
          omega
        simp only [monomial, translateCoeff,ha,hb,and_self,ite_true,mul_pow]
        rw [powH]
        ring
  · rcases ij with ⟨i,j⟩
    simp only [T,mem_product,mem_range,Nat.lt_succ_iff] at hn
    simp [translateCoeff,hn]

/-- Apply the determinant estimate to actual rational tangent numerators and
denominators. The received values may vary arbitrarily by site. -/
theorem tangent_incidence [Fintype I] (s d a : ℕ) (dom : I ↪ K) (u v : I → K)
    (h x y : ↥(monomials s) → K[X]) (c : ↥(monomials s) → ℕ)
    (hd : ∀ i, (h i).natDegree ≤ c i ∧ (x i).natDegree ≤ d + c i ∧ (y i).natDegree ≤ d + c i)
    (hn : Matrix.det (fun i j : ↥(monomials s) => monomial s j.val (h i) (x i) (y i)) ≠ 0)
    (S : I → Finset ↥(monomials s))
    (hs : ∀ z, ∀ i ∈ S z, (x i).eval (dom z) = u z * (h i).eval (dom z) ∧
      (y i).eval (dom z) = v z * (h i).eval (dom z)) :
    a*(∑ z, (S z).card) ≤ Fintype.card I*(∑ j : ↥(monomials s), (a-(j.val.1+j.val.2))) +
      (∑ i, s*c i) + (∑ j : ↥(monomials s), (j.val.1+j.val.2))*d := by
  classical
  let M : Matrix ↥(monomials s) ↥(monomials s) K[X] :=
    fun i j => monomial s j.val (h i) (x i) (y i)
  let L : I → Matrix ↥(monomials s) ↥(monomials s) K[X] := fun z i j =>
    monomial s j.val (h i) (x i-C (u z)*h i) (y i-C (v z)*h i)
  let B : I → Matrix ↥(monomials s) ↥(monomials s) K[X] := fun z i j =>
    translateCoeff (C (u z)) (C (v z)) j.val i.val
  apply incidence dom M hn (fun j => j.val.1+j.val.2) (fun i => s*c i) d a _ S L B
  · intro z
    apply Matrix.ext
    intro i j
    have hj := (mem_monomials s j.val.1 j.val.2).mp j.property
    change monomial s j.val (h i) (x i) (y i) = (L z * B z) i j
    rw [Matrix.mul_apply]
    exact (translate_row s _ _ hj _ _ _ (C (u z)) (C (v z))).trans
      ((monomials s).sum_coe_sort _).symm
  · intro z i hi j
    have hz := hs z i hi
    have hx : X - C (dom z) ∣ x i-C (u z)*h i := dvd_iff_isRoot.mpr (by simp [IsRoot,hz.1])
    have hy : X - C (dom z) ∣ y i-C (v z)*h i := dvd_iff_isRoot.mpr (by simp [IsRoot,hz.2])
    unfold L monomial
    rw [pow_add,mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul (pow_dvd_pow_of_dvd hx _) (pow_dvd_pow_of_dvd hy _)) _
  · intro i j
    change (monomial s j.val (h i) (x i) (y i)).natDegree ≤ _
    unfold monomial
    rcases hd i with ⟨h₀,h₁,h₂⟩
    have hj := (mem_monomials s j.val.1 j.val.2).mp j.property
    have hh : s-(j.val.1+j.val.2)+(j.val.1+j.val.2)=s := Nat.sub_add_cancel hj
    calc
      _ ≤ _ := natDegree_mul_le
      _ ≤ ((s-(j.val.1+j.val.2))*c i + j.val.1*(d + c i)) + j.val.2*(d + c i) := by
        apply Nat.add_le_add
        · apply natDegree_mul_le.trans
          apply Nat.add_le_add
          · exact (natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ h₀)
          · exact (natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ h₁)
        · exact (natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ h₂)
      _ = (s-(j.val.1+j.val.2)+(j.val.1+j.val.2))*c i + (j.val.1+j.val.2)*d := by ring
      _ = _ := by rw [hh]

#print axioms tangent_incidence
#print axioms incidence
end ArkLib.ProximityGap.Frontier.TangentVeronesePacking
