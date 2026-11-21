/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList
import ArkLib.Research.ProximityGap.Frontier.SameDomainListMca

/-!
# Scalar lists on the 237-bit large-period domain

A zero-sum triple in the actual cyclic group can be adjoined to an arbitrary
collection of disjoint antipodal pairs. Their error locators give distinct
codewords in one ball about the specified monomial center at every sponsor rate.
-/

namespace ArkLib.ProximityGap.Frontier.DyadicLocatorSumBarrier

open Polynomial Finset DyadicLogWitness237

variable {I F : Type*} [Fintype I] [Field F]

/-- Every degree-`k+1` locator with vanishing root sum gives a distinct codeword
at exactly `n-k-1` errors from the explicit monomial center. -/
theorem monomial_fiber (D : I ↪ F) {k : ℕ} (hk : 0 < k) (A : Finset (Finset I))
    (hcard : ∀ T ∈ A, T.card = k+1) (hsum : ∀ T ∈ A, ∑ i ∈ T, D i = 0) :
    (A.card : ℕ∞) ≤ (Code.closeCodewordsRel (ReedSolomon.code D k : Set (I → F))
      (fun i => (D i)^(k+1)) (((Fintype.card I-(k+1) : ℕ) : ℝ) / Fintype.card I)).encard := by
  classical
  let loc (T : Finset I) := ∏ i ∈ T, (X - C (D i))
  let pol (T : Finset I) : F[X] := X^(k+1)-loc T
  let word (T : Finset I) (i : I) := (pol T).eval (D i)
  have deg {T : Finset I} (hT : T ∈ A) : (pol T).natDegree < k := by
    have dl : (loc T).natDegree = k+1 := by simp [loc, hcard T hT]
    have ml : (loc T).Monic := monic_prod_X_sub_C _ _
    have nk : (loc T).nextCoeff = 0 := by
      rw [show (loc T).nextCoeff = _ from Monic.nextCoeff_prod T _ (fun i _ => monic_X_sub_C (D i))]
      simpa using congrArg Neg.neg (hsum T hT)
    rw [nextCoeff_of_natDegree_pos (by omega : 0 < (loc T).natDegree), dl] at nk
    have dd : (pol T).natDegree ≤ k-1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      simp only [pol, coeff_sub, sub_eq_zero]
      rcases lt_trichotomy j (k+1) with h | rfl | h
      · have : j=k := by omega
        subst j
        simpa [coeff_X_pow, Nat.succ_ne_self] using nk.symm
      · simpa [dl] using ml.coeff_natDegree.symm
      · rw [coeff_eq_zero_of_natDegree_lt (by simpa using h : (X^(k+1) : F[X]).natDegree < j),
            coeff_eq_zero_of_natDegree_lt (dl ▸ h)]
    omega
  have agree (T : Finset I) (i : I) : word T i = (D i)^(k+1) ↔ i ∈ T := by
    simp [word, pol, loc, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, D.injective.eq_iff]
  have hi : Set.InjOn word (A : Set (Finset I)) := by
    intro S _ T _ he
    ext i
    exact (agree S i).symm.trans ((congrFun he i) ▸ agree T i)
  have hm : (↑(A.image word) : Set (I → F)) ⊆ Code.closeCodewordsRel
      (ReedSolomon.code D k : Set (I → F)) (fun i => (D i)^(k+1))
      (((Fintype.card I-(k+1) : ℕ) : ℝ) / Fintype.card I) := by
    rw [←Code.closeCodewords_eq_closeCodewordsRel]
    intro u hu
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hu
    refine ⟨ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ (deg hT) (fun _ => rfl), ?_⟩
    rw [Code.mem_hammingBall_iff]
    have he : univ.filter (fun i => (D i)^(k+1) = word T i) = T := by
      ext i; simp only [mem_filter, mem_univ, true_and]; exact eq_comm.trans (agree T i)
    have hh := card_filter_add_card_filter_not (s := (univ : Finset I))
      (p := fun i => (D i)^(k+1)=word T i)
    rw [he, hcard T hT, card_univ] at hh
    change (univ.filter fun i => (D i)^(k+1) ≠ word T i).card ≤ _
    exact Nat.le_of_eq (Nat.eq_sub_of_add_eq' hh)
  have bound := Set.encard_le_encard hm
  rwa [Set.encard_coe_eq_coe_finsetCard, card_image_of_injOn hi] at bound

abbrev Sites := Bool × Fin 512

/-- An enumeration of the entire order-1024 subgroup by its 512 antipodal pairs. -/
def domain : Sites ↪ ZMod P where
  toFun x := g^((x.2 : ℕ) + if x.1 then 512 else 0)
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ he
    have hi := i.isLt
    have hj := j.isLt
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero,
      Prod.mk.injEq] at he ⊢ <;>
      have hjj := primitive.pow_inj (by omega) (by omega) he <;> simp_all [Fin.ext_iff]; omega

open scoped Classical in
private theorem image_of_powers {K A : Type*} [Field K] [Fintype K] [Fintype A]
    [DecidableEq K] (E : A ↪ K) (u : Kˣ) (j : A → ℕ)
    (he : ∀ a, E a = (u : K)^(j a))
    (hcard : (Round8CosetConcentration.sgFinset (Subgroup.zpowers u)).card ≤ Fintype.card A) :
    (univ : Finset A).image E = Round8CosetConcentration.sgFinset (Subgroup.zpowers u) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    rw [he]
    exact mem_image.mpr ⟨⟨u^(j a),Subgroup.npow_mem_zpowers _ _⟩,mem_univ _,Units.val_pow_eq_pow_val u (j a)⟩
  · rw [card_image_of_injective _ E.injective, card_univ]; exact hcard

open scoped Classical in
/-- The list/MCA evaluation sites are exactly the subgroup in the period certificate. -/
theorem domain_image : (univ : Finset Sites).image domain = Round8CosetConcentration.sgFinset H := by
  apply image_of_powers domain (Units.mk0 g (by decide))
    (fun a => (a.2 : ℕ) + if a.1 then 512 else 0) (fun _ => rfl)
  change (Round8CosetConcentration.sgFinset H).card ≤ Fintype.card Sites
  rw [card_H]; simp [Sites, Fintype.card_prod]

private def base : Finset Sites := {(false,0), (true,1), (true,17)}
private def pairs : Finset (Fin 512) := ((univ.erase 0).erase 1).erase 17
private def support (T : Finset (Fin 512)) : Finset Sites := base ∪ univ ×ˢ T

private theorem disjoint_base (T : Finset (Fin 512)) (ht : T ⊆ pairs) : Disjoint base (univ ×ˢ T) := by
  apply disjoint_left.mpr
  intro i hi ht'
  have h := ht (mem_product.mp ht').2
  simp only [base, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp [pairs] at h

/-- The explicit additive relation has three distinct antipodal pairs. -/
theorem root_triple : g+g^17=1 := by decide

/-- The same field and evaluation generator as the spectral witness admit this
many distinct scalar words about the monomial center. -/
theorem triple_list (s : ℕ) :
    ((509).choose s : ℕ∞) ≤ (Code.closeCodewordsRel
      (ReedSolomon.code domain (2*s+2) : Set (Sites → ZMod P))
      (fun x => (domain x)^(2*s+3)) (((1024-(2*s+3) : ℕ) : ℝ)/1024)).encard := by
  classical
  let A := (pairs.powersetCard s).image support
  have info {T : Finset (Fin 512)} (hT : T ∈ pairs.powersetCard s) := mem_powersetCard.mp hT
  have inj : Set.InjOn support (↑(pairs.powersetCard s) : Set (Finset (Fin 512))) := by
    intro S hS T hT he
    ext i
    by_cases hi : i ∈ pairs
    · have h0 : i ≠ 0 := by intro eq; subst i; simp [pairs] at hi
      have h := congrArg (fun W : Finset Sites => (false,i) ∈ W) he
      simpa [support, base, h0] using h
    · exact iff_of_false (fun h => hi ((info hS).1 h)) (fun h => hi ((info hT).1 h))
  have cA : A.card = (509).choose s := by
    dsimp only [A]; rw [card_image_of_injOn inj, card_powersetCard]
    have hp : pairs.card = 509 := by
      simp [pairs, card_erase_of_mem]
    rw [hp]
  have cardA (T : Finset Sites) (hT : T ∈ A) : T.card = (2*s+2)+1 := by
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
    have hb : base.card=3 := by decide
    have hc : (univ : Finset Bool).card=2 := by decide
    rw [support,card_union_of_disjoint (disjoint_base S (info hS).1),hb, card_product, hc, (info hS).2]
    omega
  have sumA (T : Finset Sites) (hT : T ∈ A) : ∑ i ∈ T, domain i=0 := by
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
    rw [support, sum_union (disjoint_base S (info hS).1)]
    have negpow : g^512 = -1 := by decide
    have hb : ∑ i ∈ base, domain i = 0 := by
      simp [base, domain, pow_add, negpow]
      linear_combination -root_triple
    rw [hb, zero_add, sum_product_right]
    apply sum_eq_zero
    intro i _
    simp [domain, pow_add, negpow]
  have h := monomial_fiber domain (by omega : 0 < 2*s+2) A cardA sumA
  simpa [cA, Sites, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using h

open scoped NNReal ENNReal

set_option maxRecDepth 10000 in
/-- Each sponsor rate has an over-budget scalar list and an over-budget canonical
MCA event at the same error count on the same 237-bit prime-field code. -/
theorem four_rates (s : ℕ) (hs : s=255 ∨ s=127 ∨ s=63 ∨ s=31) :
    let k := 2*s+2
    let t := k+1
    let C := (ReedSolomon.code domain k : Set (Sites → ZMod P))
    ((P/2^128 : ℕ) : ℕ∞) < Code.Lambda C (((1024-t : ℕ) : ℝ)/1024) ∧
      1/((2^128 : ℕ) : ℝ≥0∞) < _root_.ProximityGap.epsMCA (F:=ZMod P) C (((1024-t : ℕ) : ℝ≥0)/1024) := by
  classical
  dsimp only
  have count : P/2^128 < (509 : ℕ).choose s := by
    rcases hs with rfl|rfl|rfl|rfl <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide
  have cn : Fintype.card Sites = 1024 := by simp [Sites, Fintype.card_prod]
  have cf : Fintype.card (ZMod P) = P := ZMod.card P
  have hs' : s ≤ 255 := by rcases hs with rfl|rfl|rfl|rfl <;> decide
  have st : 2*s+3 ≤ Fintype.card Sites := by omega
  have ar : (1-(((1024-(2*s+3):ℕ):ℝ≥0)/1024))*(Fintype.card Sites:ℝ≥0) ≤ 2*s+3 := by
    rw [cn]
    norm_num only [Nat.cast_ofNat]
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num)]
    rcases hs with rfl|rfl|rfl|rfl <;> norm_num
  have hroom : (Fintype.card (ZMod P)/2^128)^2*(2*s+2-1)<Fintype.card (ZMod P)+1 := by
    rw [cf]; apply lt_of_le_of_lt (Nat.mul_le_mul_left _ (show 2*s+2-1≤511 by omega))
    decide
  have lower := (show ((P/2^128 : ℕ) : ℕ∞) < (509 : ℕ).choose s by exact_mod_cast count).trans_le
    ((triple_list s).trans (Code.encard_closeCodewordsRel_le_Lambda _ _ _))
  refine ⟨lower, lt_of_not_ge (fun hh => ?_)⟩
  have outside := _root_.ProximityGap.SameDomainListMca.closed_list_of_mca domain _
    (by omega : 0 < 2*s+2) (by omega : 2*s+2 < 2*s+3) st (by simpa using ar)
    (by decide : 0 < (2^128 : ℕ)) hroom hh
  exact lower.not_ge (by simpa only [cn, cf, Nat.cast_ofNat] using outside)

private theorem sum_square_differences {V : Type*} [Fintype V] (x : V → ℤ) :
    ∑ i, ∑ j, (x i-x j)^2 = 2*Fintype.card V*(∑ i, (x i)^2)-2*(∑ i, x i)^2 := by
  classical
  have hi (i : V) : ∑ j, (x i-x j)^2 = Fintype.card V*(x i)^2 + (∑ j, (x j)^2) -
      2*x i*(∑ j, x j) := by
    simp_rw [show ∀ j, (x i-x j)^2=(x i)^2+(x j)^2-2*x i*x j from fun j => by ring,
      sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ←mul_sum]
  simp_rw [hi, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ←mul_sum,
    ←sum_mul, ←mul_sum]
  ring

/-- Euclidean Plotkin counting for a fiber of folded integer orientation vectors. -/
theorem folded_plotkin {V J : Type*} [Fintype V] [Nonempty V] [Fintype J]
    (c : V → J → ℤ) (D w : ℤ) (hs : ∀ i j, i ≠ j → D ≤ ∑ a, (c i a-c j a)^2)
    (hw : ∀ i, ∑ a, (c i a)^2 ≤ w) :
    ((Fintype.card V : ℤ)-1)*D ≤ 2*Fintype.card V*w := by
  classical
  let M : ℤ := Fintype.card V
  have hm : 0 < M := by
    dsimp only [M]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have row (i : V) : (M-1)*D ≤ ∑ j, ∑ a, (c i a-c j a)^2 := by
    have h := sum_le_sum (s := (univ : Finset V).erase i)
      (fun j hj => hs i j (ne_of_mem_erase hj).symm)
    rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, nsmul_eq_mul,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one, sum_erase_eq_sub (mem_univ i)] at h
    simpa [M] using h
  have lo := sum_le_sum (s := (univ : Finset V)) (fun i _ => row i)
  rw [sum_const, card_univ, nsmul_eq_mul] at lo
  have heq : ∑ i, ∑ j, ∑ a, (c i a-c j a)^2 =
      2*M*(∑ i, ∑ a, (c i a)^2)-2*∑ a, (∑ i, c i a)^2 := by
    calc
      _ = ∑ a, ∑ i, ∑ j, (c i a-c j a)^2 := by
        simp_rw [sum_comm (s := (univ : Finset V)) (t := (univ : Finset J))]
      _ = _ := by simp_rw [sum_square_differences, sum_sub_distrib, ←mul_sum]
                  rw [sum_comm (s := (univ : Finset J)) (t := (univ : Finset V))]
  rw [heq] at lo
  have hu := sum_le_sum (s := (univ : Finset V)) (fun i _ => hw i)
  rw [sum_const, card_univ, nsmul_eq_mul] at hu
  apply le_of_mul_le_mul_left (a := M) _ hm
  change M*((M-1)*D) ≤ M*(2*M*w)
  change M*((M-1)*D) ≤ _ at lo
  change _ ≤ M*w at hu
  nlinarith only [lo, mul_le_mul_of_nonneg_left hu (show 0 ≤ 2*M by omega),
    sum_nonneg (s := (univ : Finset J)) (fun a _ => sq_nonneg (∑ i, c i a))]

#print axioms monomial_fiber
#print axioms triple_list
#print axioms four_rates
#print axioms domain_image
#print axioms folded_plotkin

end ArkLib.ProximityGap.Frontier.DyadicLocatorSumBarrier
