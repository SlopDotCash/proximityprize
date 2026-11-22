/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic

/-! # Dyadic classification of alternating cyclic correlations -/

namespace ProximityGap.PaleyDyadicMasks

open Polynomial Finset

/-- Divisibility by a dyadic period tests each cyclotomic scale exactly once. -/
theorem period_dvd_iff (r : ℕ) (F : ℚ[X]) :
    X^(2^r)-1 ∣ F ↔ ∀ j≤r, cyclotomic (2^j) ℚ ∣ F := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one (show 0<2^r by positivity),
    Nat.prod_divisors_prime_pow Nat.prime_two]
  constructor
  · intro h j hj
    exact (dvd_prod_of_mem (fun i : ℕ => cyclotomic (2^i) ℚ) (s:=range (r+1))
      (mem_range.mpr (by omega : j<r+1))).trans h
  · intro h
    apply prod_dvd_of_coprime _ (fun j hj => h j (by
      simpa only [mem_range, Nat.lt_succ_iff] using hj))
    intro a _ b _ hab
    apply cyclotomic.isCoprime_rat
    exact (Nat.pow_right_injective (by decide : 2≤2)).ne hab

/-- On primitive dyadic orders at least four, twisting all odd coefficients
fixes the cyclotomic factor and hence preserves its divisibility test. -/
theorem twist_high (j : ℕ) (F : ℚ[X]) :
    cyclotomic (2^(j+2)) ℚ ∣ F.comp (-X) ↔ cyclotomic (2^(j+2)) ℚ ∣ F := by
  rw [dvd_comp_neg_X_iff]
  have he : cyclotomic (2^(j+2)) ℚ = 1+(X:ℚ[X])^(2^(j+1)) := by
    rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [sum_range_succ]
  rw [he]
  simp only [add_comp,one_comp,pow_comp,X_comp]
  simp only [pow_succ' (2:ℕ) j,pow_mul,neg_sq]

private theorem low_plus (F : ℚ[X]) :
    cyclotomic 1 ℚ ∣ F ↔ F.eval 1=0 := by
  simpa [cyclotomic_one,IsRoot] using (dvd_iff_isRoot (p:=F) (a:=(1:ℚ)))

private theorem low_minus (F : ℚ[X]) :
    cyclotomic 2 ℚ ∣ F ↔ F.eval (-1)=0 := by
  simpa [cyclotomic_two,IsRoot,sub_eq_add_neg] using
    (dvd_iff_isRoot (p:=F) (a:=(-1:ℚ)))

/-- For nonempty masks the alternating cyclic product vanishes exactly when
both masks balance parity and at every higher scale one mask supplies the
cyclotomic zero. The source polynomial may already have its indices reversed. -/
theorem twisted_period_iff (r : ℕ) (A B : ℚ[X]) (ha : A.eval 1 ≠ 0) (hb : B.eval 1 ≠ 0) :
    X^(2 ^ (r + 1))-1 ∣ A.comp (-X)*B ↔
      A.eval (-1)=0 ∧ B.eval (-1)=0 ∧ ∀ j, j+2≤r+1 →
        (cyclotomic (2^(j+2)) ℚ ∣ A ∨ cyclotomic (2^(j+2)) ℚ ∣ B) := by
  rw [period_dvd_iff]
  have hi (j : ℕ) : cyclotomic (2^(j+2)) ℚ ∣ A.comp (-X)*B ↔
      (cyclotomic (2^(j+2)) ℚ ∣ A ∨ cyclotomic (2^(j+2)) ℚ ∣ B) := by
    rw [(cyclotomic.irreducible_rat (by positivity : 0<2^(j+2))).prime.dvd_mul,twist_high]
  have hz : cyclotomic (2^0) ℚ ∣ A.comp (-X)*B ↔ A.eval (-1)=0 := by
    rw [pow_zero,low_plus]
    simp [eval_comp,hb]
  have ho : cyclotomic (2^1) ℚ ∣ A.comp (-X)*B ↔ B.eval (-1)=0 := by
    rw [pow_one,low_minus]
    simp [eval_comp,ha]
  constructor
  · intro h
    exact ⟨hz.mp (h 0 (by omega)), ho.mp (h 1 (by omega)), fun j hj => (hi j).mp (h _ hj)⟩
  · rintro ⟨h₀,h₁,h₂⟩ (_|_|j) hj
    · exact hz.mpr h₀
    · exact ho.mpr h₁
    · exact (hi j).mpr (h₂ j hj)

section Masks

variable {n : ℕ} [NeZero n]

/-- The polynomial of one period of coefficients in canonical exponent order. -/
noncomputable def encode (a : ZMod n → ℚ) : ℚ[X] := ∑ i, C (a i)*X^i.val

/-- Coefficient extraction recovers the original cyclic vector. -/
theorem encode_coeff (a : ZMod n → ℚ) (d : ZMod n) : (encode a).coeff d.val = a d := by
  classical
  simp [encode,finsetSum_coeff,
    (ZMod.val_injective n).eq_iff]

private theorem encode_lt (a : ZMod n → ℚ) : (encode a).degree < n :=
  (degree_sum_le _ _).trans_lt <| (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2
    (fun i _ => (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.2 i.val_lt))

private theorem bounded_dvd_encode (a : ZMod n → ℚ) (P : ℚ[X]) (hm : P.Monic)
    (hd : P.degree = n) : P ∣ encode a ↔ ∀ d, a d=0 := by
  constructor
  · intro h d
    have hh : encode a=0 := by
      by_contra hn
      exact hm.not_dvd_of_degree_lt hn (hd.symm ▸ encode_lt a) h
    simpa [hh] using (encode_coeff a d).symm
  · intro h
    simp [encode,h]

private theorem encode_zero (a : ZMod n → ℚ) :
    X^n-1 ∣ encode a ↔ ∀ d, a d=0 := by
  apply bounded_dvd_encode _ _ (monic_X_pow_sub_one (NeZero.ne n))
  simpa using degree_X_pow_sub_C (NeZero.pos n) (1:ℚ)

private theorem encode_product_mk (a b : ZMod n → ℚ) :
    AdjoinRoot.mk (X^n-1 : ℚ[X]) (encode a*encode b) =
      AdjoinRoot.mk (X^n-1 : ℚ[X]) (encode (fun d => ∑ i, a i*b (d-i))) := by
  let P : ℚ[X] := X^n-1
  let M := AdjoinRoot.mk P
  let w := M X
  have hw : w^n=1 := by
    have hz := AdjoinRoot.mk_self (f:=P)
    change M (X^n-1)=0 at hz
    simpa only [map_sub,map_one,map_pow,sub_eq_zero] using hz
  have hadd (i j : ZMod n) : w^i.val*w^j.val=w^(i+j).val := by
    rw [←pow_add,ZMod.val_add]
    exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _).symm hw
  have hm (f : ZMod n → ℚ) : M (encode f)=∑ i, M (C (f i))*w^i.val := by
    simp only [encode,map_sum,map_mul,map_pow,w]
  have hmul : M (encode a*encode b)=M (encode (fun d => ∑ i, a i*b (d-i))) := by
    rw [map_mul,hm,hm,hm,sum_mul]
    simp only [mul_sum,map_sum,sum_mul,map_mul]
    rw [sum_comm (s:=univ) (t:=univ) (f:=fun d i : ZMod n =>
      M (C (a i)) * M (C (b (d-i))) * w ^ d.val)]
    apply sum_congr rfl
    intro i _
    apply Fintype.sum_equiv (Equiv.addRight i)
    intro j
    simp only [Equiv.coe_addRight,add_sub_cancel_right]
    rw [show M (C (a i))*w^i.val*(M (C (b j))*w^j.val)=
      M (C (a i))*M (C (b j))*(w^i.val*w^j.val) by ring,hadd,add_comm i j]
  exact hmul

/-- Multiplication of the two coefficient polynomials modulo the period is
ordinary cyclic convolution, including all wraps of the exponent. -/
theorem encode_product (a b : ZMod n → ℚ) :
    X^n-1 ∣ encode a*encode b ↔ ∀ d, (∑ i, a i*b (d-i))=0 := by
  rw [←AdjoinRoot.mk_eq_zero,←encode_zero,←AdjoinRoot.mk_eq_zero,encode_product_mk]

private theorem encode_twist (a : ZMod n → ℚ) :
    (encode a).comp (-X) = encode (fun i => (-1:ℚ)^i.val*a i) := by
  classical
  simp only [encode, Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp,
    map_mul, map_pow, map_neg, map_one]
  apply sum_congr rfl
  intro i _
  rw [show -(X:ℚ[X])=(-1)*X by ring,mul_pow]
  ring

/-- For any nonempty rational masks, a directly computed signed sum on every
lag vanishes exactly under the characterizations by dyadic scale. The argument
of the first mask is the reversed source coordinate. -/
theorem mask_classification (r : ℕ) (a b : ZMod (2 ^ (r + 1)) → ℚ)
    (ha : (encode a).eval 1 ≠ 0) (hb : (encode b).eval 1 ≠ 0) :
    (∀ d, (∑ i, ((-1:ℚ)^i.val*a i)*b (d-i))=0) ↔
      (encode a).eval (-1)=0 ∧ (encode b).eval (-1)=0 ∧ ∀ j, j+2≤r+1 →
        (cyclotomic (2^(j+2)) ℚ ∣ encode a ∨ cyclotomic (2^(j+2)) ℚ ∣ encode b) := by
  rw [←encode_product,←encode_twist,twisted_period_iff _ _ _ ha hb]

/-- The difference between the total weights in opposite residues modulo
`2m`, indexed by the common residue modulo `m`. -/
def folded {m : ℕ} [NeZero m] (a : ZMod n → ℚ) (t : ZMod m) : ℚ :=
  ∑ i, if (i.val : ZMod m)=t then (-1:ℚ)^(i.val/m)*a i else 0

/-- Reduction modulo `X^m+1` recovers exactly the differences of the sums of
weights at the two halves of every residue class modulo `2m`. -/
theorem fold_test (m : ℕ) [NeZero m] (a : ZMod n → ℚ) :
    (X^m+1 : ℚ[X]) ∣ encode a ↔ ∀ t : ZMod m, folded a t=0 := by
  let P : ℚ[X] := X^m+1
  let M := AdjoinRoot.mk P
  let w := M X
  have hw : w^m= -1 := by
    have hz := AdjoinRoot.mk_self (f:=P)
    change M (X^m+1)=0 at hz
    exact eq_neg_of_add_eq_zero_left (by simpa only [map_add,map_one,map_pow] using hz)
  have hp (k : ℕ) : w^k=(-1)^(k/m)*w^((k:ZMod m).val) := by
    rw [ZMod.val_natCast,←hw,←pow_mul,←pow_add,Nat.add_comm,Nat.mod_add_div]
  have hfold : M (encode a)=M (encode (folded a : ZMod m → ℚ)) := by
    classical
    simp only [encode,folded,map_sum,map_mul,map_pow,sum_mul]
    rw [sum_comm (s:=univ) (t:=univ) (f:=fun t i =>
      M (C (if (i.val:ZMod m)=t then (-1:ℚ)^(i.val/m)*a i else 0))*M X^t.val)]
    apply sum_congr rfl
    intro i _
    rw [sum_eq_single (i.val:ZMod m)]
    · simp only [ite_true,map_mul,map_pow,map_neg,map_one]
      change M (C (a i))*w^i.val = _
      rw [hp]
      ring
    · intro t _ ht
      rw [ite_eq_right (Ne.symm ht),map_zero,map_zero,zero_mul]
    · simp
  have hf : P ∣ encode (folded a : ZMod m → ℚ) ↔ ∀ t : ZMod m, folded a t=0 := by
    apply bounded_dvd_encode
    · simpa [P] using (monic_X_pow_add_C (1:ℚ) (NeZero.ne m))
    · simpa [P] using degree_X_pow_add_C (NeZero.pos m) (1:ℚ)
  rw [←hf,←AdjoinRoot.mk_eq_zero (f:=P),←AdjoinRoot.mk_eq_zero (f:=P)]
  exact iff_of_eq (congrArg (· = 0) hfold)

/-- Classification directly in terms of finite residue sums with no polynomial
divisibility conditions on the right. -/
theorem residue_classification (r : ℕ) (a b : ZMod (2 ^ (r + 1)) → ℚ)
    (ha : (encode a).eval 1 ≠ 0) (hb : (encode b).eval 1 ≠ 0) :
    (∀ d, (∑ i, ((-1:ℚ)^i.val*a i)*b (d-i))=0) ↔
      (encode a).eval (-1)=0 ∧ (encode b).eval (-1)=0 ∧ ∀ j, j+2≤r+1 →
        ((∀ t : ZMod (2^(j+1)), folded a t=0) ∨ (∀ t : ZMod (2^(j+1)), folded b t=0)) := by
  rw [mask_classification _ _ _ ha hb]
  have hstep (j : ℕ) : cyclotomic (2^(j+2)) ℚ = (X:ℚ[X])^(2^(j+1))+1 := by
    rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [sum_range_succ,add_comm]
  simp_rw [hstep,fold_test]

private theorem flat_product (a b : ZMod n → ℚ) (hn : n ≠ 1) :
    X^n-1 ∣ (X-1)*(encode a*encode b) ↔
      ∀ d, (∑ i, a i*b (d-i))=∑ i, a i*b (0-i) := by
  classical
  let u (d : ZMod n) := ∑ i, a i*b (d-i)
  let k (i : ZMod n) : ℚ := (if i=1 then 1 else 0)-(if i=0 then 1 else 0)
  have hdelta (d : ZMod n) : (∑ i : ZMod n, C (if i=d then (1:ℚ) else 0)*X^i.val) =
      X^d.val := by
    rw [sum_eq_single d]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hk : encode k=X-1 := by
    simp only [encode,k,map_sub,sub_mul,sum_sub_distrib,hdelta,ZMod.val_one'' hn,
      ZMod.val_zero,pow_one,pow_zero]
  have hku (d : ZMod n) : (∑ i, k i*u (d-i))=u (d-1)-u d := by
    simp [k,sub_mul,ite_mul,sum_sub_distrib]
  have hm : AdjoinRoot.mk (X^n-1 : ℚ[X]) ((X-1)*(encode a*encode b))=
      AdjoinRoot.mk (X^n-1 : ℚ[X]) (encode k*encode u) := by
    rw [hk,map_mul,encode_product_mk a b,map_mul (AdjoinRoot.mk _) _ (encode u)]
  rw [←AdjoinRoot.mk_eq_zero,hm,AdjoinRoot.mk_eq_zero,encode_product]
  simp_rw [hku,sub_eq_zero]
  change (∀ d, u (d-1)=u d) ↔ ∀ d, u d=u 0
  constructor
  · intro h d
    have hh (j : ℕ) : u (j:ZMod n)=u 0 := by
      induction j with
      | zero => simp
      | succ j ih => rw [Nat.cast_succ,←h (_+1),add_sub_cancel_right,ih]
    simpa using hh d.val
  · intro h d
    rw [h (d-1),h d]

/-- Vanishing of every signed lag is equivalent to ordinary representations
having constant multiplicity over the cycle and parity balance in each mask. -/
theorem uniform_representation_iff (r : ℕ) (a b : ZMod (2 ^ (r + 1)) → ℚ)
    (ha : (encode a).eval 1 ≠ 0) (hb : (encode b).eval 1 ≠ 0) :
    (∀ d, (∑ i, ((-1:ℚ)^i.val*a i)*b (d-i))=0) ↔
      (encode a).eval (-1)=0 ∧ (encode b).eval (-1)=0 ∧
        ∀ d, (∑ i, a i*b (d-i))=∑ i, a i*b (0-i) := by
  have hn : 2 ^ (r + 1)≠1 := by rw [pow_succ]; omega
  rw [mask_classification _ _ _ ha hb,←flat_product _ _ hn,period_dvd_iff]
  have hhi (j : ℕ) : cyclotomic (2^(j+2)) ℚ ∣ (X-1)*(encode a*encode b) ↔
      cyclotomic (2^(j+2)) ℚ ∣ encode a ∨ cyclotomic (2^(j+2)) ℚ ∣ encode b := by
    have hne : 2^(j+2)≠1 := by rw [pow_succ]; omega
    have hc := cyclotomic.isCoprime_rat hne
    rw [cyclotomic_one] at hc
    rw [hc.dvd_mul_left_iff,(cyclotomic.irreducible_rat (by positivity : 0<2^(j+2))).prime.dvd_mul]
  constructor
  · rintro ⟨h₀,h₁,hhi'⟩
    refine ⟨h₀,h₁,?_⟩
    rintro (_|_|j) hj
    · simp [dvd_mul_right]
    · rw [show 2^(0+1)=2 by decide,low_minus]
      simp [h₀]
    · exact (hhi j).mpr (hhi' j hj)
  · rintro ⟨h₀,h₁,h⟩
    exact ⟨h₀,h₁,fun j hj => (hhi j).mp (h (j+2) hj)⟩

/-- Testing every possible lag function is equivalent to testing each coefficient. -/
theorem all_lag_rows_iff {I : Type*} [Fintype I] (v : I → ℚ) :
    (∀ h : I → ℚ, (∑ d, v d*h d)=0) ↔ ∀ d, v d=0 := by
  classical
  constructor
  · intro h d
    simpa [mul_ite] using h (fun j => if j=d then 1 else 0)
  · intro h v'
    simp [h]

/-- Integer masks with nonzero total weights and identically vanishing signed
lags have product of total weights divisible by twice the full period. -/
theorem twice_period_dvd (r : ℕ) (a b : ZMod (2 ^ (r + 1)) → ℤ)
    (ha : (∑ i, a i) ≠ 0) (hb : (∑ i, b i) ≠ 0)
    (hz : ∀ d, (∑ i, ((-1 : ℤ) ^ i.val * a i) * b (d - i)) = 0) :
    (2*(2:ℤ)^(r+1)) ∣ (∑ i, a i)*(∑ i, b i) := by
  let qa (i : ZMod (2 ^ (r + 1))) : ℚ := a i
  let qb (i : ZMod (2 ^ (r + 1))) : ℚ := b i
  have eval_one (f : ZMod (2 ^ (r + 1)) → ℚ) : (encode f).eval 1=∑ i, f i := by
    simp [encode,eval_finsetSum]
  have hqa : (encode qa).eval 1 ≠ 0 := by rw [eval_one]; dsimp [qa]; exact_mod_cast ha
  have hqb : (encode qb).eval 1 ≠ 0 := by rw [eval_one]; dsimp [qb]; exact_mod_cast hb
  have hq (d) : (∑ i, ((-1:ℚ)^i.val*qa i)*qb (d-i))=0 := by
    dsimp [qa,qb]; exact_mod_cast hz d
  have hflat (d) : (∑ i, a i*b (d-i))=∑ i, a i*b (0-i) := by
    have hh := ((uniform_representation_iff r qa qb hqa hqb).mp hq).2.2 d
    dsimp [qa,qb] at hh
    exact_mod_cast hh
  let M := ∑ i, if Even i.val then a i*b (0-i) else 0
  have he : (∑ i, a i*b (0-i))=2*M := by
    calc
      _ = (∑ i, a i*b (0-i))+(∑ i, ((-1:ℤ)^i.val*a i)*b (0-i)) := by rw [hz 0,add_zero]
      _ = _ := by
        rw [←sum_add_distrib]
        dsimp [M]; rw [mul_sum]
        apply sum_congr rfl
        intro i _
        by_cases h : Even i.val
        · simp [h,h.neg_one_pow,two_mul]
        · simp [h,(Nat.not_even_iff_odd.mp h).neg_one_pow]
  have ht (i : ZMod (2 ^ (r + 1))) : (∑ d, b (d-i))=∑ j, b j := by
    simpa only [sub_eq_add_neg] using
      Fintype.sum_equiv (Equiv.addRight (-i)) (fun j => b (j+ -i)) b (fun _ => rfl)
  refine ⟨M,?_⟩
  calc
    _ = ∑ d, ∑ i, a i*b (d-i) := by
      rw [sum_comm,sum_mul]; simp_rw [←mul_sum,ht]
    _ = _ := by
      simp_rw [hflat,he]
      simp [ZMod.card]
      ring

end Masks

end ProximityGap.PaleyDyadicMasks

#print axioms ProximityGap.PaleyDyadicMasks.twisted_period_iff
#print axioms ProximityGap.PaleyDyadicMasks.mask_classification
#print axioms ProximityGap.PaleyDyadicMasks.residue_classification
#print axioms ProximityGap.PaleyDyadicMasks.uniform_representation_iff
#print axioms ProximityGap.PaleyDyadicMasks.twice_period_dvd
