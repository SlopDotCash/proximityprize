/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyMixedTraceSaving

/-! # Complete mixed product strata on the Goldilocks field -/
namespace ProximityGap.GoldilocksMixedTrace
open Finset PaleyInversionTrace PaleyMixedTraceSaving
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

set_option maxRecDepth 8192

local instance : Fact goldilocks.Prime := ⟨goldilocks_prime⟩
local notation "K" => ZMod goldilocks
local notation "N" => (2^30:ℕ)
local notation "M" => (2^29:ℕ)
local notation "C" => ZMod (2*M)

/-- The fixed generator of order `2^30`. -/
def generator : K := 9123114210336311365

set_option maxRecDepth 8192 in
private theorem genOrder : orderOf generator = N := by
  have h : generator^(2^29:ℕ)≠1 := by rw [← binaryPow_eq_pow]; decide
  have h' : generator^(2^30:ℕ)=1 := by rw [← binaryPow_eq_pow]; decide
  exact orderOf_eq_prime_pow h h'

private theorem genChar : quadraticChar K generator=1 := by
  have hs : generator=(4614640910117430873 : K)^2 := by decide
  rw [hs,quadraticChar_sq_one' (by decide)]

private def atIndex (i : C) : K := generator^i.val

private theorem idxNonzero (i : C) : atIndex i ≠ 0 := pow_ne_zero _ (by decide)

private theorem idxAdd (i j : C) : atIndex (i+j)=atIndex i*atIndex j := by
  unfold atIndex
  rw [ZMod.val_add, ← pow_add]
  have he := pow_mod_orderOf generator (i.val+j.val)
  rw [genOrder] at he
  exact he

private theorem idxSub (i j : C) : atIndex (i-j)=atIndex i/atIndex j := by
  apply (eq_div_iff (idxNonzero j)).mpr
  rw [← idxAdd, sub_add_cancel]

private theorem idxChar (i : C) : quadraticChar K (atIndex i)=1 := by
  rw [atIndex,map_pow,genChar,one_pow]

private theorem idxInj : Function.Injective atIndex := by
  intro i j he
  apply ZMod.val_injective (2*M)
  exact pow_injOn_Iio_orderOf (x:=generator) (by rw [genOrder]; exact i.val_lt)
    (by rw [genOrder]; exact j.val_lt) he

/-- The full multiplicative subgroup and its product strata. -/
def domain : Finset K := univ.image atIndex

def stratum (s : K) : Finset K := domain.image (productTrace s)

private theorem domainCard : domain.card=N := by
  rw [domain,card_image_of_injective _ idxInj,card_univ,ZMod.card]
  decide

private theorem domainGroup : IsMulSubgroup domain where
  one_mem := mem_image.mpr ⟨0,mem_univ _, by simp [atIndex]⟩
  zero_notMem := by
    rintro h
    obtain ⟨i,_,hi⟩ := mem_image.mp h
    exact idxNonzero i hi
  mul_mem := by
    rintro _ hy _ hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hy
    obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨i+j, mem_univ _, idxAdd i j⟩
  inv_mem := by
    rintro _ hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    refine mem_image.mpr ⟨-i, mem_univ _, ?_⟩
    apply inv_eq_of_mul_eq_one_left ?_ |>.symm
    rw [← idxAdd,neg_add_cancel]
    simp [atIndex]

private def evenDomain : Finset K := (range M).image (fun j => generator^(2*j))

private theorem evenInj : Set.InjOn (fun j : ℕ => generator^(2*j)) (↑(range M)) := by
  intro i hi j hj he
  have h₁ := mem_range.mp hi
  have h₂ := mem_range.mp hj
  have hi' : 2*i ∈ Set.Iio (orderOf generator) := by change 2*i<_; rw [genOrder]; omega
  have hj' : 2*j ∈ Set.Iio (orderOf generator) := by change 2*j<_; rw [genOrder]; omega
  have heq := pow_injOn_Iio_orderOf (x:=generator) hi' hj' he
  omega

private theorem evenCard : evenDomain.card=M := by rw [evenDomain,card_image_of_injOn evenInj,card_range]

private theorem evenPower (x : K) (hx : x∈evenDomain) : x^M=1 := by
  obtain ⟨j,_,rfl⟩ := mem_image.mp hx
  rw [← pow_mul, show 2*j*M=N*j by ring, pow_mul,
    ← genOrder, pow_orderOf_eq_one, one_pow]

private theorem evenGroup : IsMulSubgroup evenDomain where
  one_mem := mem_image.mpr ⟨0,mem_range.mpr (by decide),by simp⟩
  zero_notMem := by
    rintro he
    obtain ⟨j,_,hj⟩ := mem_image.mp he
    exact pow_ne_zero _ (by decide : generator≠0) hj
  mul_mem := by
    rintro _ hi _ hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp hj
    refine mem_image.mpr ⟨(i+j)%M,mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩
    rw [← pow_add, ← Nat.mul_add, ← Nat.mul_mod_mul_left,
      show 2*M=orderOf generator by rw [genOrder]; decide, pow_mod_orderOf]
  inv_mem := by
    rintro _ hi
    have hx := evenPower _ hi
    obtain ⟨i,_,rfl⟩ := mem_image.mp hi
    refine mem_image.mpr ⟨(i*(M-1))%M,mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩
    rw [← Nat.mul_mod_mul_left, show 2*M=orderOf generator by rw [genOrder]; decide,
      pow_mod_orderOf, ← Nat.mul_assoc, pow_mul]
    apply inv_eq_of_mul_eq_one_left ?_ |>.symm
    rw [← pow_succ]
    exact hx

private theorem parityCell {R : Type*} [AddCommMonoid R] (f : C→R) (e : ℕ) (he : e<2) :
    ∑ i∈univ.filter (fun i:C => i.val%2=e), f i =
    ∑ j∈range M,f ((2*j+e:ℕ):C) := by
  apply sum_nbij' (fun i => i.val/2) (fun j => ((2*j+e:ℕ):C))
  · intro i _
    have := i.val_lt
    apply mem_range.mpr
    omega
  · intro j hj
    have h := mem_range.mp hj
    have hlt : 2*j+e<2*M := by omega
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt hlt]
    omega
  · intro i hi
    have hh := (mem_filter.mp hi).2
    apply ZMod.val_injective (2*M)
    rw [ZMod.val_natCast, show 2*(i.val/2)+e=i.val by omega, Nat.mod_eq_of_lt i.val_lt]
  · intro j hj
    have h := mem_range.mp hj
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 2*j+e<2*M)]
    omega
  · intro i hi
    have hh := (mem_filter.mp hi).2
    rw [show 2*(i.val/2)+e=i.val by omega,ZMod.natCast_zmod_val]

private theorem parity_sum {R : Type*} [AddCommMonoid R] (f : C→R) :
    ∑ i:C,f i =
      ∑ j∈range M, f ((2*j:ℕ):C) + ∑ j∈range M, f ((2*j+1:ℕ):C) := by
  classical
  have hpart := sum_filter_add_sum_filter_not (s:=univ) (fun i:C => i.val%2=0) f
  have hnot : univ.filter (fun i:C => ¬i.val%2=0)=univ.filter (fun i:C => i.val%2=1) := by
    ext i
    simp only [mem_filter,mem_univ,true_and]
    omega
  rw [hnot,parityCell f 0 (by decide),parityCell f 1 (by decide)] at hpart
  simpa using hpart.symm

private def indexAt (e j : ℕ) : C := ((2*j+e:ℕ):C)

private theorem parityAt {e j : ℕ} (he : e<2) (hj : j<M) :
    (indexAt e j).val%2=e := by
  rw [indexAt,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : 2*j+e<2*M)]
  omega

private theorem valueAt {e j : ℕ} (he : e<2) (hj : j<M) :
    atIndex (indexAt e j)=generator^e*generator^(2*j) := by
  rw [atIndex,indexAt,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : 2*j+e<2*M),
    pow_add,mul_comm]

private theorem parityBlock (q : K→K→ℤ) (e : ℕ) (he : e<2) :
    (∑ j∈range M, ∑ i:C, if (indexAt e j).val%2=i.val%2 then
      q (atIndex (indexAt e j)) (atIndex i) else 0) =
    ∑ x∈evenDomain, ∑ y∈evenDomain, q ((generator^e)*x) ((generator^e)*y) := by
  classical
  simp only [evenDomain,sum_image evenInj]
  apply sum_congr rfl
  intro j hj
  rw [parityAt he (mem_range.mp hj),valueAt he (mem_range.mp hj)]
  have hswap (i:C) : (e=i.val%2)↔(i.val%2=e) := eq_comm
  simp_rw [hswap]
  rw [← sum_filter,parityCell _ e he]
  apply sum_congr rfl
  intro k hk
  rw [← valueAt he (mem_range.mp hk)]
  rfl

private theorem sameParitySum (q : K→K→ℤ) :
    (∑ w:C×C, if w.1.val%2=w.2.val%2 then q (atIndex w.1) (atIndex w.2) else 0) =
      (∑ x∈evenDomain, ∑ y∈evenDomain,q x y) +
      ∑ x∈evenDomain, ∑ y∈evenDomain,q (generator*x) (generator*y) := by
  rw [Fintype.sum_prod_type,parity_sum]
  have h0 := parityBlock q 0 (by decide)
  have h1 := parityBlock q 1 (by decide)
  simp only [indexAt,Nat.add_zero,pow_zero,pow_one,one_mul] at h0 h1
  exact congrArg₂ (·+·) h0 h1

private def charEntry (s t x y : K) : ℤ := quadraticChar K (productTrace s x-productTrace t y)
private def bulk (s t : K) : ℤ := ∑ x∈domain, ∑ y∈domain,charEntry s t x y

private theorem bulkBound {s t : K} (hs : s≠0) (ht : t≠0) (hst : s≠t) :
    |bulk s t| ≤ 4*230497832882265705 := by
  classical
  let G (u v : K) := quadraticChar K ((u-1)*v-t*u+s)
  have hxy (i j : C) : charEntry s t (atIndex i) (atIndex j)=G (atIndex (i-j)) (atIndex (i+j)) := by
    rw [idxSub,idxAdd]
    dsimp only [charEntry,G]
    rw [← ratio_product_identity s t (idxNonzero i) (idxNonzero j),map_mul,idxChar, mul_one]
  have hsum : bulk s t = ∑ z:C×C,G (atIndex (z.1-z.2)) (atIndex (z.1+z.2)) := by
    rw [Fintype.sum_prod_type]
    simp only [bulk,domain,sum_image idxInj.injOn,hxy]
  rw [hsum,sum_difference_pushforward (fun w:C×C => G (atIndex w.1) (atIndex w.2))]
  have hd (w : C×C) : (if w.1.val%2=w.2.val%2 then
      G (atIndex w.1) (atIndex w.2)+G (atIndex w.1) (atIndex w.2) else 0)=
      2*(if w.1.val%2=w.2.val%2 then G (atIndex w.1) (atIndex w.2) else 0) := by
    split <;> simp [two_mul]
  simp_rw [hd]
  rw [← mul_sum,sameParitySum G,abs_mul]
  have he := goldilocks_parity evenDomain evenGroup evenCard evenPower hs ht (γ:=1) one_ne_zero hst
  simp only [one_mul] at he
  have ho := goldilocks_parity evenDomain evenGroup evenCard evenPower hs ht
    (γ:=generator) (by decide) hst
  have hh := abs_add_le (∑ x∈evenDomain,∑ y∈evenDomain,G x y)
    (∑ x∈evenDomain,∑ y∈evenDomain,G (generator*x) (generator*y))
  dsimp only [G] at *
  rw [abs_of_nonneg (by decide : (0:ℤ)≤2)]
  omega

private def branch (s : K) := (domain.filter fun x => x^2=s).image (productTrace s)

private theorem branch_sub (s : K) : branch s ⊆ stratum s :=
  image_subset_image (filter_subset ..)

private theorem branchCard (s : K) : (branch s).card≤2 := by
  classical
  apply card_image_le.trans
  by_cases he : (domain.filter fun x => x^2=s).Nonempty
  · obtain ⟨x,hx⟩ := he
    have hh : domain.filter (fun y => y^2=s) ⊆ {x,-x} := by
      intro y hy
      have hyx : y^2=x^2 := (mem_filter.mp hy).2.trans (mem_filter.mp hx).2.symm
      simpa only [mem_insert,mem_singleton] using sq_eq_sq_iff_eq_or_eq_neg.mp hyx
    apply (card_le_card hh).trans
    by_cases h : x= -x
    · simp [←h]
    · exact (card_pair h).le
  · rw [not_nonempty_iff_eq_empty.mp he,card_empty]; decide

private theorem branch_mem {s x : K} (hx : x∈domain) :
    productTrace s x ∈ branch s ↔ x^2=s := by
  constructor
  · intro he
    obtain ⟨y,hy,he⟩ := mem_image.mp he
    obtain ⟨hy',hey⟩ := mem_filter.mp hy
    rcases (productTrace_eq_iff (ne_zero_of_mem domainGroup hy')
      (ne_zero_of_mem domainGroup hx)).mp he with h|h
    · simpa [←h] using hey
    · have hh : x=y := mul_left_cancel₀ (ne_zero_of_mem domainGroup hy')
        (show y*x=y*y by rw [h, ← pow_two,hey])
      simpa [hh] using hey
  · intro he
    exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,he⟩,rfl⟩

private theorem traceFiber {s x : K} (hs : s∈domain) (hx : x∈domain) :
    domain.filter (fun y => productTrace s y=productTrace s x)={x,s/x} := by
  have hx₀ := ne_zero_of_mem domainGroup hx
  have hdiv : s/x ∈ domain := by
    rw [div_eq_mul_inv]
    exact domainGroup.mul_mem _ hs _ (domainGroup.inv_mem _ hx)
  ext y
  simp only [mem_filter,mem_insert,mem_singleton]
  constructor
  · rintro ⟨hy,he⟩
    rcases (productTrace_eq_iff (ne_zero_of_mem domainGroup hy) hx₀).mp he with h|h
    · exact Or.inl h
    · exact Or.inr ((eq_div_iff hx₀).mpr h)
  · rintro (rfl|rfl)
    · exact ⟨hx,rfl⟩
    · exact ⟨hdiv,(productTrace_eq_iff (ne_zero_of_mem domainGroup hdiv) hx₀).mpr
        (Or.inr (div_mul_cancel₀ _ hx₀))⟩

private theorem setSum {s : K} (hs : s∈domain) (f : K→ℤ) :
    2*(∑ z∈stratum s,f z) =
      (∑ x∈domain,f (productTrace s x)) + ∑ z∈branch s,f z := by
  classical
  have hb : (stratum s).filter (fun z=>z∈branch s)=branch s := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr (branch_sub s)]
  rw [← sum_fiberwise_of_maps_to' (s:=domain) (t:=stratum s)
    (fun _ => mem_image_of_mem (productTrace s)) f]
  rw [← hb, sum_filter, ← sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro z hz
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  rw [traceFiber hs hx]
  by_cases h : x=s/x
  · have hh : x^2=s := by rw [pow_two]; exact (eq_div_iff (ne_zero_of_mem domainGroup hx)).mp h
    simp [←h,(branch_mem hx).mpr hh,two_mul]
  · have hh : productTrace s x ∉ branch s := by
      intro he
      exact h ((eq_div_iff (ne_zero_of_mem domainGroup hx)).mpr
        (by simpa [pow_two] using (branch_mem hx).mp he))
    simp [h,hh,two_mul]

private theorem charBound (x : K) : |quadraticChar K x|≤1 := by
  by_cases hx : x=0
  · simp [hx]
  rcases quadraticChar_dichotomy hx with h|h <;> simp [h]

private theorem setError {s : K} (hs : s∈domain) (f : K→ℤ) (B : ℤ)
    (hB : 0≤B) (h : ∀ x, |f x|≤B) :
    |2*(∑ z∈stratum s,f z)-∑ x∈domain,f (productTrace s x)| ≤ 2*B := by
  rw [setSum hs,add_sub_cancel_left]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (s:=branch s) (fun x _ => h x)).trans
  rw [sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast branchCard s) hB

private theorem stratumCard {s : K} (hs : s∈domain) : (M:ℤ) ≤ (stratum s).card := by
  have h := setSum hs (fun _=>1)
  simp only [sum_const,nsmul_eq_mul,mul_one,domainCard] at h
  omega

/-- On the actual order-`2^30` Goldilocks subgroup, every two distinct full
product strata retain relative Paley discrepancy strictly below four fifths. -/
theorem full_discrepancy {s t : K} (hs : s∈domain) (ht : t∈domain) (hst : s≠t) :
    5*|∑ z∈stratum s, ∑ w∈stratum t, quadraticChar K (z-w)| <
      (4:ℤ)*(stratum s).card*(stratum t).card := by
  classical
  let R z := ∑ w∈stratum t,quadraticChar K (z-w)
  let S := ∑ z∈stratum s,R z
  let I := ∑ x∈domain,R (productTrace s x)
  have hR (z : K) : |R z|≤N := calc
    _ ≤ ∑ w∈stratum t, |quadraticChar K (z-w)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _w∈stratum t,(1:ℤ) := sum_le_sum (fun _ _ => charBound _)
    _ = (stratum t).card := by rw [sum_const,nsmul_eq_mul,mul_one]
    _ ≤ N := by exact_mod_cast ((card_image_le (s:=domain) (f:=productTrace t)).trans_eq domainCard)
  have hs₁ : |2*S-I|≤2*N := setError hs R N (by positivity) hR
  have hs₂ : |2*I-bulk s t|≤2*N := by
    change |2*(∑ x∈domain,R (productTrace s x))-∑ x∈domain,∑ y∈domain,charEntry s t x y|≤_
    rw [mul_sum,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    apply (sum_le_sum (s:=domain) (g:=fun _=>(2:ℤ)) (fun x _ =>
      setError ht (fun w => quadraticChar K (productTrace s x-w)) 1 (by decide) (fun w=>charBound _))).trans
    simp [domainCard]
  have hbulk := bulkBound (ne_zero_of_mem domainGroup hs) (ne_zero_of_mem domainGroup ht) hst
  have hsabs : 5*|S|<4*(M:ℤ)*M := by
    rcases abs_le.mp hs₁ with ⟨h₁,h₂⟩
    rcases abs_le.mp hs₂ with ⟨h₃,h₄⟩
    rcases abs_le.mp hbulk with ⟨h₅,h₆⟩
    rcases le_total 0 S with hh|hh
    · rw [abs_of_nonneg hh]; omega
    · rw [abs_of_nonpos hh]; omega
  apply hsabs.trans_le
  exact mul_le_mul (mul_le_mul_of_nonneg_left (stratumCard hs) (by decide)) (stratumCard ht) (by positivity) (by positivity)

end ProximityGap.GoldilocksMixedTrace

#print axioms ProximityGap.GoldilocksMixedTrace.full_discrepancy
