/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyMixedProductTraces
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Independent selections in a run of mixed product strata -/

namespace ProximityGap.PaleyMaskedStrata

open Finset

/-- The two Rudin–Shapiro coefficient sequences at dyadic length. -/
def signs : ℕ → ℕ → ℤ × ℤ
  | 0, _ => (1,1)
  | r+1, j => if j<2^r then ((signs r j).1,(signs r j).1)
    else ((signs r (j-2^r)).2,-(signs r (j-2^r)).2)

theorem signs_sq (r j : ℕ) : (signs r j).1^2=1 ∧ (signs r j).2^2=1 := by
  induction r generalizing j with
  | zero => simp [signs]
  | succ r ih =>
    by_cases h : j<2^r
    · simp [signs,h,(ih j).1]
    · simp [signs,h,(ih (j-2^r)).2]

variable {G : Type*} [AddCommGroup G]

/-- Apply a finite coefficient sequence to all translates of a test vector. -/
def applyRow (c : ℤ × ℤ → ℤ) (r : ℕ) (s : G) (v : G → ℤ) (d : G) : ℤ :=
  ∑ j ∈ range (2^r), c (signs r j)*v (d+j • s)

private theorem nextRow (r : ℕ) (s : G) (v : G → ℤ) (d : G) :
    applyRow Prod.fst (r+1) s v d =
        applyRow Prod.fst r s v d + applyRow Prod.snd r s v (d+2^r • s) ∧
    applyRow Prod.snd (r+1) s v d =
        applyRow Prod.fst r s v d - applyRow Prod.snd r s v (d+2^r • s) := by
  have hi (c : ℤ × ℤ → ℤ) (hc : ∀ z, c (z,z)=z) :
      (∑ j ∈ range (2^r), c (signs (r+1) j)*v (d+j • s)) =
        applyRow Prod.fst r s v d := by
    apply sum_congr rfl
    intro j hj
    simp only [signs,mem_range.mp hj,ite_true,hc]
  have h₂ (j : ℕ) : signs (r+1) (2^r+j) = ((signs r j).2,-(signs r j).2) := by
    simp only [signs,show ¬ 2^r+j<2^r by omega,ite_false,Nat.add_sub_cancel_left]
  have h₃ (j : ℕ) : d+(2^r+j) • s = d+2^r • s+j • s := by rw [add_nsmul,add_assoc]
  constructor
  · unfold applyRow at ⊢
    rw [show 2^(r+1)=2^r+2^r by ring,sum_range_add, hi Prod.fst (fun _ => rfl)]
    simp only [h₂,h₃,applyRow]
  · unfold applyRow at ⊢
    rw [show 2^(r+1)=2^r+2^r by ring,sum_range_add, hi Prod.snd (fun _ => rfl)]
    simp only [h₂,h₃,neg_mul,sum_neg_distrib,sub_eq_add_neg,applyRow]

variable [Fintype G]

/-- The complementary convolutions have exact total squared energy for every
input vector and every shift on a finite abelian group. -/
theorem complementary_energy (r : ℕ) (s : G) (v : G → ℤ) :
    (∑ d, (applyRow Prod.fst r s v d)^2) + (∑ d, (applyRow Prod.snd r s v d)^2) =
      2*(2:ℤ)^r * ∑ d, (v d)^2 := by
  induction r with
  | zero => simp [applyRow,signs,two_mul]
  | succ r ih =>
    rw [←sum_add_distrib]
    have hpoint (d : G) : (applyRow Prod.fst (r+1) s v d)^2 +
        (applyRow Prod.snd (r+1) s v d)^2 =
        2*(applyRow Prod.fst r s v d)^2 + 2*(applyRow Prod.snd r s v (d+2^r • s))^2 := by
      rw [(nextRow r s v d).1,(nextRow r s v d).2]
      ring
    simp_rw [hpoint]
    rw [sum_add_distrib,←mul_sum,←mul_sum]
    have he : (∑ d, (applyRow Prod.snd r s v (d+2^r • s))^2) =
        ∑ d, (applyRow Prod.snd r s v d)^2 :=
      Fintype.sum_equiv (Equiv.addRight (2^r • s)) _ _ (fun _ => rfl)
    rw [he,←mul_add,ih,pow_succ]
    ring

/-- The residual estimate keeps the actual energy of the lag sequence. -/
theorem residual_by_energy (r : ℕ) (s : G) (v h : G → ℤ)
    (c : ℤ × ℤ → ℤ) (hc : c=Prod.fst ∨ c=Prod.snd) :
    (∑ d, h d*applyRow c r s v d)^2 ≤ (∑ d, (h d)^2)*(2*(2:ℤ)^r*∑ d, (v d)^2) := by
  have he := complementary_energy r s v
  have hp : 0 ≤ ∑ d, (applyRow Prod.fst r s v d)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hq : 0 ≤ ∑ d, (applyRow Prod.snd r s v d)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hu : (∑ d, (applyRow c r s v d)^2) ≤ 2*(2:ℤ)^r * ∑ d, (v d)^2 := by
    rcases hc with rfl|rfl <;> omega
  apply (sum_mul_sq_le_sq_mul_sq univ h (applyRow c r s v)).trans
  exact mul_le_mul_of_nonneg_left hu (sum_nonneg (fun _ _ => sq_nonneg _))

/-- The cyclic group of order twice the run length accommodates its lags. -/
theorem residual_sq (r : ℕ) (s : G) (v h : G → ℤ) (hh : ∑ d, (h d)^2 ≤ 2*(2:ℤ)^r)
    (c : ℤ × ℤ → ℤ) (hc : c=Prod.fst ∨ c=Prod.snd) :
    (∑ d, h d*applyRow c r s v d)^2 ≤ 4*(2:ℤ)^(2*r)*∑ d, (v d)^2 := by
  apply (residual_by_energy r s v h c hc).trans
  calc
    _ ≤ (2*(2:ℤ)^r)*(2*2^r*∑ d, (v d)^2) := by gcongr
    _ = _ := by rw [Nat.mul_comm 2 r,pow_mul]; ring

/-- Reindexing by the difference of the two sites identifies the literal
double sum with the complementary convolution. -/
theorem lag_reindex (r : ℕ) (s : G) (v h : G → ℤ) (c : ℤ × ℤ → ℤ) :
    (∑ i, v i*∑ j∈range (2^r), c (signs r j)*h (j • s-i)) =
      ∑ d, h (-d)*applyRow c r s v d := by
  have he (j : ℕ) : (∑ i, v i*(c (signs r j)*h (j • s-i))) =
      ∑ d, h (-d)*(c (signs r j)*v (d+j • s)) := by
    symm
    apply Fintype.sum_equiv (Equiv.addRight (j • s))
    intro d
    change h (-d)*(c (signs r j)*v (d+j • s)) =
      v (d+j • s)*(c (signs r j)*h (j • s-(d+j • s)))
    rw [show j • s-(d+j • s)= -d by abel]
    ring
  simp only [applyRow,mul_sum]
  rw [sum_comm]
  simp_rw [he]
  rw [sum_comm]

/-- The power bound on the signed mixed double sum for either complementary
mask, with arbitrary values for the lag character and arbitrary source weights. -/
theorem masked_lag_sq (r : ℕ) (s : G) (v h : G → ℤ) (hh : ∑ d, (h d)^2 ≤ 2*(2:ℤ)^r)
    (c : ℤ × ℤ → ℤ) (hc : c=Prod.fst ∨ c=Prod.snd) :
    (∑ i, v i*∑ j∈range (2^r), c (signs r j)*h (j • s-i))^2 ≤
      4*(2:ℤ)^(2*r)*∑ d, (v d)^2 := by
  rw [lag_reindex]
  apply residual_sq r s v (fun d => h (-d)) _ c hc
  exact (show (∑ d, (h (-d))^2) = ∑ d, (h d)^2 from
    Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ => rfl)).le.trans hh

/-- A full period of lags halves the squared error bound. -/
theorem full_masked_lag_sq (r : ℕ) (s : G) (v h : G → ℤ)
    (hh : ∑ d, (h d)^2 ≤ (2:ℤ)^r) (c : ℤ × ℤ → ℤ) (hc : c=Prod.fst ∨ c=Prod.snd) :
    (∑ i, v i*∑ j∈range (2^r), c (signs r j)*h (j • s-i))^2 ≤
      2*(2:ℤ)^(2*r)*∑ d, (v d)^2 := by
  rw [lag_reindex]
  apply (residual_by_energy r s v (fun d => h (-d)) c hc).trans
  have hh' : (∑ d, (h (-d))^2) ≤ (2:ℤ)^r :=
    (Fintype.sum_equiv (Equiv.neg G) (fun d => (h (-d))^2) (fun d => (h d)^2)
      (fun _ => rfl)).le.trans hh
  calc
    _ ≤ (2:ℤ)^r*(2*2^r*∑ d, (v d)^2) := by gcongr
    _ = _ := by rw [Nat.mul_comm 2 r,pow_mul]; ring

/-- On a full exponent orbit the constant-target contribution depends only
on the total sign imbalance of the source, with no positional restrictions. -/
theorem full_constant (a h : G → ℤ) :
    (∑ i, a i*∑ j, h (j-i)) = (∑ i, a i)*∑ d, h d := by
  have ht (i : G) : (∑ j, h (j-i)) = ∑ d, h d := by
    simpa only [sub_eq_add_neg] using
      Fintype.sum_equiv (Equiv.addRight (-i)) (fun j => h (j+ -i)) h (fun _ => rfl)
  simp_rw [ht]
  rw [sum_mul]

/-- Exact cancellation for arbitrary choices with equal source residue counts
and independently chosen balanced periodic target masks. -/
theorem uniform_periodic_cancellation {D : Type*} [AddCommGroup D] [Fintype D]
    [DecidableEq D] (π : G →+ D) (a : Finset G) (count : ℕ)
    (ha : ∀ r, (a.filter (fun i => π i=r)).card=count)
    (e b : D → ℤ) (he : ∀ r t, e (r+t)=e r*e t) (hu : ∀ t, (e t)^2=1)
    (hb : ∑ r, e r*b r=0) (h : G → ℤ) :
    (∑ i∈a, ∑ j, (e (π i)*b (π j))*h (j-i)) = 0 := by
  classical
  have hf (f : D → ℤ) : (∑ i∈a, f (π i)) = count * ∑ r, f r := by
    rw [← sum_fiberwise_of_maps_to' (s:=a) (t:=univ)
      (fun i _ => mem_univ (π i)) f]
    simp only [sum_const,nsmul_eq_mul]
    simp_rw [ha]
    rw [mul_sum]
  have hz (t : D) : ∑ r, e r*b (r+t)=0 := by
    have hp (r : D) : e r*b (r+t)=e t*(e (r+t)*b (r+t)) := by
      rw [he,show e t*(e r*e t*b (r+t))=e r*b (r+t)*(e t)^2 by ring,hu,mul_one]
    simp_rw [hp]
    rw [←mul_sum]
    have hre : (∑ r, e (r+t)*b (r+t)) = ∑ r, e r*b r :=
      Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
    rw [hre,hb,mul_zero]
  have hr (i : G) : (∑ j, (e (π i)*b (π j))*h (j-i)) =
      ∑ d, (e (π i)*b (π i+π d))*h d := by
    symm
    apply Fintype.sum_equiv (Equiv.addRight i)
    intro d
    simp [add_comm]
  simp_rw [hr]
  rw [sum_comm]
  apply sum_eq_zero
  intro d _
  rw [←sum_mul,hf (fun r => e r*b (r+π d)),hz,mul_zero,zero_mul]

/-- The constant target cancels throughout the interior of a selected adjacent
pair. Only the two endpoints of its lag interval remain. -/
theorem paired_interval (h : ℤ → ℤ) (a : ℤ) (k : ℕ) :
    (∑ j ∈ range k, (h (a+j+1)-h (a+j))) = h (a+k)-h a := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ,ih,Nat.cast_succ]; ring_nf

/-- The Paley character on two runs of dilates supplies the alternating row
sign, independently of the two initial sites and their products. -/
theorem lag_character {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {q : F} (hq : q ≠ 0) (hs : quadraticChar F q = -1) (x y : F) (i j : ℕ) :
    quadraticChar F (q^i*x-q^j*y) =
      (-1:ℤ)^i*quadraticChar F (x-q^((j:ℤ)-(i:ℤ))*y) := by
  have he : q^i*q^((j:ℤ)-(i:ℤ))=q^j := by
    rw [← zpow_natCast q i,← zpow_add₀ hq,add_sub_cancel, zpow_natCast]
  rw [show q^i*x-q^j*y=q^i*(x-q^((j:ℤ)-(i:ℤ))*y) by rw [mul_sub,←mul_assoc,he],
    map_mul,map_pow,hs]

/-- Cauchy–Schwarz combines independent choices at all pairs of initial sites.
Only the total source count remains on the right. -/
theorem aggregate_sq {I J : Type*} [Fintype I] [Fintype J] (K : ℕ)
    (R : I × J → ℤ) (a : I → ℕ)
    (h : ∀ z, (R z)^2 ≤ 4*(K:ℤ)^2*a z.1) :
    (∑ z, R z)^2 ≤ 4*(K:ℤ)^2*(Fintype.card J)^2*(Fintype.card I)*∑ i, (a i:ℤ) := by
  have hh := sum_mul_sq_le_sq_mul_sq univ (fun _ : I × J => (1:ℤ)) R
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one] at hh
  apply hh.trans
  calc
    _ ≤ (Fintype.card (I × J):ℤ)*∑ z : I × J, 4*(K:ℤ)^2*a z.1 :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun z _ => h z)) (by positivity)
    _ = _ := by
      rw [Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type]
      simp only [sum_const,card_univ,nsmul_eq_mul]
      simp_rw [← mul_assoc]
      rw [← mul_sum]
      ring

/-- At length `2^20`, a half-dense paired source and either complementary
target mask have relative discrepancy strictly below 0.0028. Here `C` is
the constant-target term and `R` the signed remainder in the doubled sum. -/
theorem named_mask_bound (X Y A B C R S : ℤ) (_hX : 0≤X) (hY : 0<Y) (hA : 0<A)
    (ha : 524288*X≤A) (hb : 523776*Y≤B) (hconst : |C|≤A*Y)
    (hres : R^2 ≤ 4*(1048576:ℤ)^2*Y^2*X*A) (hs : 2*S=C+R) :
    10000*|S| < 28*A*B := by
  have hload : 724^2*X≤A := by omega
  have hr : 724*|R|≤(2*1048576)*Y*A := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,sq_abs]
    calc
      _ ≤ 724^2*(4*(1048576:ℤ)^2*Y^2*X*A) := by gcongr
      _ = (4*(1048576:ℤ)^2*Y^2*A)*(724^2*X) := by ring
      _ ≤ (4*(1048576:ℤ)^2*Y^2*A)*A := mul_le_mul_of_nonneg_left hload (by positivity)
      _ = _ := by ring
  have ht := abs_add_le C R
  rw [← hs,abs_mul] at ht
  norm_num at ht
  have hS : 1448*|S| ≤ (724+2*1048576)*(A*Y) := by nlinarith
  have hp : 0<A*Y := mul_pos hA hY
  have hB := mul_le_mul_of_nonneg_left hb (show 0≤A by omega)
  nlinarith only [hS,hp,hB]

/-- A sign-reversing transport cancels every member of the overlap, at a
loss of at most one per site remaining on either side. -/
theorem sign_reversing_overlap {I : Type*} [DecidableEq I] (S T : Finset I)
    (v : I → ℤ) (hv : ∀ x, |v x|≤1) (hc : S.card=T.card)
    (hs : (∑ x ∈ T, v x) = -(∑ x ∈ S, v x)) :
    |∑ x ∈ S, v x| ≤ (S.card:ℤ)-(S∩T).card := by
  have h₁ := sum_inter_add_sum_sdiff S T v
  have h₂ := sum_inter_add_sum_sdiff T S v
  rw [inter_comm T S] at h₂
  have hd : (∑ x ∈ S \ T, v x)-(∑ x ∈ T \ S, v x)=2*∑ x ∈ S, v x := by omega
  have hbound (U : Finset I) : |∑ x ∈ U, v x| ≤ U.card :=
    (abs_sum_le_sum_abs ..).trans (by simpa using sum_le_sum (s:=U) (fun x _ => hv x))
  have ha := (abs_sub _ _).trans (add_le_add (hbound (S \ T)) (hbound (T \ S)))
  rw [hd,abs_mul] at ha
  have he := card_sdiff_comm hc
  have hf := card_sdiff_add_card_inter S T
  norm_num at ha
  omega

/-- The overlap of a Paley rectangle with its nonsquare dilation factors into
the two independent coordinate overlaps. -/
theorem rectangle_overlap {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (A B : Finset F) {q : F} (hq : quadraticChar F q = -1) :
    |∑ x ∈ A, ∑ y ∈ B, quadraticChar F (x-y)| ≤
      (A.card:ℤ)*B.card - ((A∩A.image (q*·)).card:ℤ)*(B∩B.image (q*·)).card := by
  have q₀ : q≠0 := by rintro rfl; simp at hq
  let v (z : F × F) := quadraticChar F (z.1-z.2)
  have hv (z : F × F) : |v z|≤1 := by
    by_cases he : z.1-z.2=0
    · simp [v,he]
    change |quadraticChar F (z.1-z.2)|≤1
    rcases quadraticChar_dichotomy he with hp|hn
    · rw [hp]; decide
    · rw [hn]; decide
  have hh := sign_reversing_overlap (A ×ˢ B) (A.image (q*·) ×ˢ B.image (q*·)) v hv
    (by simp [card_image_of_injective _ (mul_right_injective₀ q₀)]) (by
      simp_rw [sum_product, sum_image (mul_right_injective₀ q₀).injOn]
      simp only [v,← mul_sub,map_mul,hq,neg_one_mul,sum_neg_distrib])
  simpa only [sum_product,v,product_inter_product,card_product,Nat.cast_mul] using hh

/-- In ratio-product coordinates every genuinely different multiplicative
translate of a mixed trace factor has a different rational root in the
product variable. Equality at the pole and at zero recovers the parameters. -/
theorem translated_roots {F : Type*} [Field F] {A B A' B' s t : F}
    (ha : A ≠ 0) (hb' : B' ≠ 0) (hs : s ≠ 0) (ht : t ≠ s)
    (he : ∀ u : F, B'*(A'*u-1)*(t*(A*u)-s)=B*(A*u-1)*(t*(A'*u)-s)) :
    A=A' ∧ B=B' := by
  have hp := he A⁻¹
  rw [mul_inv_cancel₀ ha,mul_one,sub_self,mul_zero,zero_mul] at hp
  have hz := (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr ht)
  have ha' := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hb')
  have hx := congrArg (· * A) ha'
  rw [mul_assoc,inv_mul_cancel₀ ha,mul_one,one_mul] at hx
  have hzero := he 0
  simp only [mul_zero,zero_sub] at hzero
  have hzero' : B'*s=B*s := by linear_combination hzero
  exact ⟨hx.symm,(mul_right_cancel₀ hs hzero').symm⟩

section SecondPrime

open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open ArkLib.ProximityGap.BinaryPower (binaryPow binaryPow_eq_pow)

local instance : Fact P.Prime := ⟨prime_P⟩

/-- A site in the odd product stratum used for the half-density control. -/
def witnessSite : ZMod P := 426431179702536630437099641987827200018168889315

theorem witness_product : witnessSite = g^(44718:ℕ)+g^(2^30+1-44718:ℕ) := by
  simp only [← binaryPow_eq_pow]
  decide

private def witnessEntry (k : Fin 15) : ZMod P :=
  2*binaryPow g 14-witnessSite*binaryPow g (2*k.val)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem witness_powers :
    ∀ k : Fin 15, witnessEntry k ≠ 0 ∧ binaryPow (witnessEntry k) (P/2) ≠ 1 := by decide

/-- The even layers of two length-sixteen runs on the named prime form an
actual all-nonsquare rectangle at independent density one half. -/
theorem second_half_density (i j : Fin 8) :
    quadraticChar (ZMod P) (2*g^(2*i.val)-witnessSite*g^(2*j.val)) = -1 := by
  let k : Fin 15 := ⟨j.val+7-i.val,by omega⟩
  have hk := witness_powers k
  rw [binaryPow_eq_pow] at hk
  have hx : quadraticChar (ZMod P) (witnessEntry k) = -1 := by
    rw [quadraticChar_eq_pow_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; decide) hk.1,ZMod.card]
    simp only [hk.2,ite_false]
  have he : (2*g^(2*i.val)-witnessSite*g^(2*j.val))*g^14 =
      g^(2*i.val)*witnessEntry k := by
    have heq : 2*j.val+14=2*i.val+2*k.val := by dsimp [k]; omega
    simp only [witnessEntry,binaryPow_eq_pow,mul_sub,sub_mul,mul_assoc,← pow_add,heq]
    rw [pow_add]
    ring
  have hz := congrArg (quadraticChar (ZMod P)) he
  have hχ (m : ℕ) : quadraticChar (ZMod P) (g^(2*m))=1 := by
    rw [map_pow,PaleyCosetCancellation.second_generator_character,pow_mul]
    norm_num
  have h₁₄ : quadraticChar (ZMod P) (g^14)=1 := hχ 7
  simpa only [map_mul,h₁₄,hχ,hx,mul_one,one_mul] using hz

end SecondPrime

end ProximityGap.PaleyMaskedStrata

#print axioms ProximityGap.PaleyMaskedStrata.complementary_energy
#print axioms ProximityGap.PaleyMaskedStrata.residual_sq
#print axioms ProximityGap.PaleyMaskedStrata.paired_interval

#print axioms ProximityGap.PaleyMaskedStrata.lag_character
#print axioms ProximityGap.PaleyMaskedStrata.aggregate_sq
#print axioms ProximityGap.PaleyMaskedStrata.named_mask_bound

#print axioms ProximityGap.PaleyMaskedStrata.rectangle_overlap

#print axioms ProximityGap.PaleyMaskedStrata.translated_roots

#print axioms ProximityGap.PaleyMaskedStrata.masked_lag_sq

#print axioms ProximityGap.PaleyMaskedStrata.second_half_density

#print axioms ProximityGap.PaleyMaskedStrata.full_constant
#print axioms ProximityGap.PaleyMaskedStrata.uniform_periodic_cancellation
#print axioms ProximityGap.PaleyMaskedStrata.full_masked_lag_sq
