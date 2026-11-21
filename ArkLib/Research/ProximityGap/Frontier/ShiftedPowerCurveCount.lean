/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RegularTaylorPole
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # Bad scalar labels supported on the first-order curve (X+z)P' = DP

Compare the scalar multiples of (X+z)^D with the affine received polynomial
at two sites. The common multiplier disappears. The resulting nonzero
univariate polynomial has at most D+1 roots. The zero multiplier is counted
separately, using a single already witnessed support.
-/
set_option autoImplicit false
namespace ProximityGap.ShiftedPowerCurveCount
open Polynomial Finset
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]

private theorem roots_bound (U : Finset F) {p : F[X]} (h : p ≠ 0)
    (hu : ∀ z ∈ U, p.eval z = 0) : U.card ≤ p.natDegree := by
  classical
  apply card_le_degree_of_subset_roots
  intro z hz
  exact (mem_roots h).mpr (hu _ hz)

private theorem pair_polynomial {x y : F} (hxy : x ≠ y) {P Q : F[X]} {D : ℕ}
    (hD : 2 ≤ D) (hP : P ≠ 0) (hp : P.natDegree ≤ 1) (hq : Q.natDegree ≤ 1) :
    let R := P*(X+C y)^D-Q*(X+C x)^D
    R ≠ 0 ∧ R.natDegree ≤ D+1 := by
  dsimp only
  have hcop : IsCoprime (X+C x) (X+C y) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub (a := -x) (b := -y)
      (sub_ne_zero_of_ne (neg_injective.ne hxy)).isUnit
  constructor
  · intro h
    have hdvd : (X+C x)^D ∣ P*(X+C y)^D := by
      rw [sub_eq_zero.mp h]
      exact dvd_mul_left ..
    have hdeg := natDegree_le_of_dvd (hcop.pow.dvd_of_dvd_mul_right hdvd) hP
    simp at hdeg
    omega
  · apply (natDegree_sub_le ..).trans (max_le _ _)
    · exact (natDegree_mul_le.trans (Nat.add_le_add hp (by simp))).trans_eq (Nat.add_comm ..)
    · exact (natDegree_mul_le.trans (Nat.add_le_add hq (by simp))).trans_eq (Nat.add_comm ..)

/-- The nonzero multipliers can be counted without differential or Taylor
coordinates. This applies over finite and infinite fields. -/
theorem fiber_nonzero_count [DecidableEq F] (dom : I → F) (s : ℕ)
    (hcap : ∀ x : F, (univ.filter fun i => dom i = x).card ≤ s) (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1)
    (B : Finset F) (S : F → Finset I) (a : F → F) (D A : ℕ) (hD : 2 ≤ D)
    (ha : ∀ z ∈ B, a z ≠ 0) (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(dom i+z)^D) :
    B.card*((A-s)*(A-2*s)) ≤ Fintype.card I * (Fintype.card I-1) * (D+1) := by
  classical
  let good (z : F) := (S z).filter fun i => dom i+z ≠ 0
  let pairs (U : Finset I) := (U ×ˢ U).filter fun ij => dom ij.1 ≠ dom ij.2
  let R (z : F) (ij : I × I) := ij ∈ pairs (good z)
  have hgood (z : F) (hz : z ∈ B) : A-s ≤ (good z).card := by
    have hx : ((S z) \ good z).card ≤ s := by
      apply le_trans (card_le_card _) (hcap (-z))
      intro i hi
      simp [good] at hi
      exact mem_filter.mpr ⟨mem_univ _,eq_neg_of_add_eq_zero_left (hi.2 hi.1)⟩
    have he : ((S z) \ good z).card + (good z).card = (S z).card :=
      card_sdiff_add_card_eq_card (filter_subset _ (S z) : good z ⊆ S z)
    have := hsize z hz
    omega
  have hpairs (U : Finset I) : U.card*(U.card-s) ≤ (pairs U).card := by
    have row (i : I) : U.card-s ≤ (U.filter fun j => dom i ≠ dom j).card := by
      have hcut : (U.filter fun j => dom i = dom j).card ≤ s := by
        apply le_trans (card_le_card _) (hcap (dom i))
        intro j hj
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2.symm⟩
      have h : (U.filter fun j => dom i = dom j).card +
          (U.filter fun j => dom i ≠ dom j).card = U.card := card_filter_add_card_filter_not ..
      omega
    calc _ = ∑ _i ∈ U, (U.card-s) := by simp
         _ ≤ ∑ i ∈ U, (U.filter fun j => dom i ≠ dom j).card :=
           sum_le_sum fun i _ => row i
         _ = (pairs U).card := by simp [pairs,card_filter,sum_product]
  have hleft (z : F) (hz : z ∈ B) :
      (A-s)*(A-2*s) ≤ (univ.offDiag.bipartiteAbove R z).card := by
    have h := Nat.mul_le_mul (hgood z hz) (Nat.sub_le_sub_right (hgood z hz) s)
    apply le_trans (show (A-s)*(A-2*s) ≤ (good z).card*((good z).card-s) by
      simpa [Nat.sub_sub,two_mul] using h)
    apply (hpairs _).trans (card_le_card _)
    intro ij hij
    refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,?_⟩,hij⟩
    exact fun heq => (mem_filter.mp hij).2 (congrArg dom heq)
  have hright (ij : I × I) (_hij : ij ∈ (univ : Finset I).offDiag) :
      (B.bipartiteBelow R ij).card ≤ D+1 := by
    obtain he | ⟨z,hz⟩ := (B.bipartiteBelow R ij).eq_empty_or_nonempty
    · simp [he]
    have hsites : ∀ t ∈ B.bipartiteBelow R ij, t ∈ B ∧ ij.1 ∈ good t ∧ ij.2 ∈ good t := by
      intro t ht
      obtain ⟨ht,h⟩ := mem_filter.mp ht
      exact ⟨ht,(mem_product.mp (mem_filter.mp h).1).1,(mem_product.mp (mem_filter.mp h).1).2⟩
    obtain ⟨hzB,hg,_⟩ := hsites z hz
    obtain ⟨hi,hzn⟩ := mem_filter.mp hg
    have hn : w ij.1 ≠ 0 := by
      intro h
      have hr := hfit z hzB ij.1 hi
      rw [h,eval_zero] at hr
      exact (mul_ne_zero (ha z hzB) (pow_ne_zero _ hzn)) hr.symm
    have hdiff : dom ij.1 ≠ dom ij.2 := (mem_filter.mp (mem_filter.mp hz).2).2
    have ⟨hpoly,hdeg⟩ := pair_polynomial hdiff
      hD hn (hw ij.1) (hw ij.2)
    apply le_trans (roots_bound _ hpoly _) hdeg
    intro t ht
    obtain ⟨htB,h₁,h₂⟩ := hsites t ht
    simp only [eval_sub,eval_mul,eval_pow,eval_add,eval_X,eval_C,
      hfit t htB _ (mem_filter.mp h₁).1,hfit t htB _ (mem_filter.mp h₂).1]
    ring
  have h := card_mul_le_card_mul R hleft hright
  simpa only [offDiag_card,card_univ,Nat.mul_sub,Nat.mul_one] using h

/-- The nonzero multipliers can be counted without differential or Taylor
coordinates. This applies over finite and infinite fields. -/
theorem nonzero_count (dom : I ↪ F) (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1)
    (B : Finset F) (S : F → Finset I) (a : F → F) (D A : ℕ) (hD : 2 ≤ D)
    (ha : ∀ z ∈ B, a z ≠ 0) (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(dom i+z)^D) :
    B.card*((A-1)*(A-2)) ≤ Fintype.card I * (Fintype.card I-1) * (D+1) := by
  classical
  have hc (x : F) : (univ.filter fun i => dom i = x).card ≤ 1 :=
    card_le_one.mpr fun i hi j hj => dom.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  simpa using fiber_nonzero_count dom 1 hc w hw B S a D A hD ha hsize hfit

/-- A zero multiplier accounts for at most n−A+1 bad scalar labels as long
as each support includes a site with a nonzero affine received polynomial. -/
theorem zero_count (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1)
    (B : Finset F) (S : F → Finset I) (A : ℕ) (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = 0)
    (hind : ∀ z ∈ B, ∃ i ∈ S z, w i ≠ 0) :
    B.card ≤ Fintype.card I-A+1 := by
  classical
  obtain hB | ⟨z₀,h₀⟩ := B.eq_empty_or_nonempty
  · simp [hB]
  let J := (univ : Finset I) \ S z₀
  let R (z : F) (i : I) := i ∈ S z ∧ w i ≠ 0
  have hleft (z : F) (hz : z ∈ B.erase z₀) : 1 ≤ (J.bipartiteAbove R z).card := by
    obtain ⟨hne,hzB⟩ := mem_erase.mp hz
    obtain ⟨i,hi,hn⟩ := hind z hzB
    have hout : i ∉ S z₀ := by
      intro hi₀
      have htwo := roots_bound ({z,z₀} : Finset F) hn (by
        intro t ht
        rcases mem_insert.mp ht with rfl | ht
        · exact hfit _ hzB _ hi
        · obtain rfl := mem_singleton.mp ht
          exact hfit _ h₀ _ hi₀)
      rw [card_pair hne] at htwo
      have := hw i
      omega
    exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hout⟩,hi,hn⟩⟩
  have hright (i : I) (_hi : i ∈ J) : ((B.erase z₀).bipartiteBelow R i).card ≤ 1 := by
    by_cases hn : w i = 0
    · simp [bipartiteBelow,R,hn]
    · apply (roots_bound _ hn _).trans (hw i)
      intro z hz
      obtain ⟨hz,h⟩ := mem_filter.mp hz
      exact hfit z (mem_erase.mp hz).2 i h.1
  have hbound := card_mul_le_card_mul R hleft hright
  have hc := card_erase_add_one h₀
  have hsize₀ := hsize z₀ h₀
  simp only [J,card_sdiff_of_subset (subset_univ _),card_univ,Nat.mul_one] at hbound
  omega

/-- In large characteristic the bounded-degree solutions of the linear first-order
equation are exactly scalar multiples of the shifted power. -/
theorem shifted_power_of_equation {P : F[X]} {D : ℕ} {z : F}
    (hchar : ringChar F = 0 ∨ D < ringChar F) (hdeg : P.natDegree ≤ D)
    (heq : (X+C z)*P.derivative = C (D:F)*P) :
    ∃ a : F, P = C a*(X+C z)^D := by
  let Q := taylor (-z) P
  have he : X*Q.derivative = C (D:F)*Q := by
    have h := congrArg (fun f : F[X] => f.comp (X+C (-z))) heq
    simpa [Q,taylor_apply,derivative_comp,add_assoc] using h
  have hm : Q = monomial D (Q.coeff D) := by
    ext j
    by_cases hj : j = D
    · simp [hj]
    rw [coeff_monomial,ite_eq_right (Ne.symm hj)]
    by_contra hn
    have hjD : j < D := by
      have hbound := le_natDegree_of_ne_zero hn
      have hQdeg : Q.natDegree = P.natDegree := natDegree_taylor ..
      omega
    have hp : ((D-j : ℕ) : F) ≠ 0 :=
      natCast_ne_zero_of_ringChar_eq_zero_or_lt hchar (by omega) (by omega)
    rw [Nat.cast_sub hjD.le] at hp
    have hcoeff := congrArg (fun f : F[X] => f.coeff j) he
    have hfactor : ((D:F)-(j:F))*Q.coeff j = 0 := by
      cases j with
      | zero => simpa using hcoeff.symm
      | succ i =>
        simp only [coeff_X_mul,coeff_derivative,coeff_C_mul,Nat.cast_succ] at hcoeff ⊢
        linear_combination -hcoeff
    exact (mul_ne_zero hp hn) hfactor
  refine ⟨Q.coeff D,?_⟩
  have h := congrArg (taylor z) hm
  simpa [Q,taylor_taylor] using h

/-- Total count allowing both zero and nonzero multipliers. The last
hypothesis is automatic for an MCA witness with no joint fit. -/
theorem fiber_total_count [DecidableEq F] (dom : I → F) (s : ℕ)
    (hcap : ∀ x : F, (univ.filter fun i => dom i = x).card ≤ s) (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1)
    (B : Finset F) (S : F → Finset I) (a : F → F) (D A : ℕ) (hD : 2 ≤ D) (hA : 2*s < A)
    (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(dom i+z)^D)
    (hind : ∀ z ∈ B, a z = 0 → ∃ i ∈ S z, w i ≠ 0) :
    B.card ≤ Fintype.card I-A+1 +
      Fintype.card I*(Fintype.card I-1)*(D+1)/((A-s)*(A-2*s)) := by
  classical
  let Z := B.filter fun z => a z = 0
  let U := B.filter fun z => a z ≠ 0
  have hZ := zero_count w hw Z S A
    (fun z hz => hsize z (mem_filter.mp hz).1)
    (fun z hz i hi => by rw [hfit z (mem_filter.mp hz).1 i hi,(mem_filter.mp hz).2,zero_mul])
    (fun z hz => hind z (mem_filter.mp hz).1 (mem_filter.mp hz).2)
  have hU := fiber_nonzero_count dom s hcap w hw U S a D A hD (fun z hz => (mem_filter.mp hz).2)
    (fun z hz => hsize z (mem_filter.mp hz).1) (fun z hz => hfit z (mem_filter.mp hz).1)
  have hpos : 0 < (A-s)*(A-2*s) := Nat.mul_pos (by omega) (by omega)
  have hu := (Nat.le_div_iff_mul_le hpos).mpr hU
  have hZU : Z.card+U.card = B.card := card_filter_add_card_filter_not ..
  omega

/-- Total count allowing both zero and nonzero multipliers. The last
hypothesis is automatic for an MCA witness with no joint fit. -/
theorem total_count (dom : I ↪ F) (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1)
    (B : Finset F) (S : F → Finset I) (a : F → F) (D A : ℕ) (hD : 2 ≤ D) (hA : 3 ≤ A)
    (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(dom i+z)^D)
    (hind : ∀ z ∈ B, a z = 0 → ∃ i ∈ S z, w i ≠ 0) :
    B.card ≤ Fintype.card I-A+1 +
      Fintype.card I*(Fintype.card I-1)*(D+1)/((A-1)*(A-2)) := by
  classical
  have hc (x : F) : (univ.filter fun i => dom i = x).card ≤ 1 :=
    card_le_one.mpr fun i hi j hj => dom.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  simpa using fiber_total_count dom 1 hc w hw B S a D A hD hA hsize hfit hind

/-- The four numerical count bounds are each strictly below twice the
production length, in the order half, quarter, eighth and sixteenth. -/
theorem four_test_costs :
    let n : ℕ := 2^30
    let cost := fun (k A : ℕ) => n-A+1+n*(n-1)*k/((A-1)*(A-2))
    cost (2^29) (89*2^23) < 2*n ∧ cost (2^28) (61*2^23) < 2*n ∧
      cost (2^27) (42*2^23) < 2*n ∧ cost (2^26) (29*2^23) < 2*n := by decide

section MCA
open scoped NNReal
open Classical

/-- An actual witness lies on the indicated translated shifted-power
differential equation and has no joint fit on its entire local support. -/
def WitnessOnShiftedEquation {I F : Type} [Field F] [Fintype I] (dom : I ↪ F)
    (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (D A : ℕ) (z : F) : Prop :=
  ∃ (S : Finset I) (P : F[X]), P.natDegree ≤ D ∧ A ≤ S.card ∧
    (∀ i ∈ S, P.eval (dom i) = u₀ i+z*u₁ i) ∧
    ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ ∧
    (let Q := P-(q₀+C z*q₁)
     (X+C z)*Q.derivative = C (D:F)*Q)

/-- On every received pair and for any two prescribed codeword heads, at
most this many scalar labels have a bad witness on the shifted curve. -/
theorem captured_count {I F : Type} [DecidableEq I] [Fintype I] [Field F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (D A : ℕ)
    (hD : 2 ≤ D) (hA : 3 ≤ A) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hchar : ringChar F = 0 ∨ D < ringChar F) (B : Finset F)
    (captured : ∀ z ∈ B, WitnessOnShiftedEquation dom u₀ u₁ q₀ q₁ D A z) :
    B.card ≤ Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(D+1)/((A-1)*(A-2)) := by
  classical
  let v₀ := fun i => u₀ i-q₀.eval (dom i)
  let v₁ := fun i => u₁ i-q₁.eval (dom i)
  let w := fun i => C (v₀ i)+X*C (v₁ i)
  have hw (i : I) : (w i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have wit (z : F) (hz : z ∈ B) : ∃ (S : Finset I) (a : F), A ≤ S.card ∧
      (∀ i ∈ S, (w i).eval z = a*(dom i+z)^D) ∧ (∃ i ∈ S, w i ≠ 0) := by
    obtain ⟨S,P,hp,hs,hf,hind,heq⟩ := captured z hz
    let Q := P-(q₀+C z*q₁)
    have hq : Q.natDegree ≤ D := by
      apply (natDegree_sub_le ..).trans (max_le hp _)
      apply (natDegree_add_le ..).trans (max_le hq₀ _)
      exact natDegree_mul_le.trans (by simpa using hq₁)
    obtain ⟨a,hea⟩ := shifted_power_of_equation (P:=Q) hchar hq
      heq
    refine ⟨S,a,hs,?_,?_⟩
    · intro i hi
      have he := congrArg (eval (dom i)) hea
      simp only [Q,eval_sub,eval_mul,eval_add,eval_X,eval_C,eval_pow,hf i hi] at he
      simp only [w,v₀,v₁,eval_add,eval_mul,eval_C,eval_X]
      linear_combination he
    · by_contra! hz₀
      apply hind
      refine ⟨ReedSolomon.evalOnPoints dom q₀,
        ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),
        ReedSolomon.evalOnPoints dom q₁,
        ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),?_⟩
      intro i hi
      have hc₀ := congrArg (fun f : F[X] => f.coeff 0) (hz₀ i hi)
      have hc₁ := congrArg (fun f : F[X] => f.coeff 1) (hz₀ i hi)
      simp [w,v₀,v₁] at hc₀ hc₁
      exact ⟨(sub_eq_zero.mp hc₀).symm,(sub_eq_zero.mp hc₁).symm⟩
  choose! S a hs hf hind using wit
  exact total_count dom w hw B S a D A hD hA hs hf (fun z hz _ => hind z hz)

/-- Any common affine pair of codeword heads can be subtracted in the
differential equation. The count is for the original local MCA event. -/
theorem mca_count_of_shifted_equation
    {I F : Type} [DecidableEq I] [Fintype I] [Field F] [DecidableEq F] [Fintype F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (D A : ℕ) (δ : ℝ≥0)
    (hD : 2 ≤ D) (hA : 3 ≤ A) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hchar : ringChar F = 0 ∨ D < ringChar F)
    (hr : ∀ S : Finset I, (1-δ)*(Fintype.card I : ℝ≥0) ≤ S.card → A ≤ S.card)
    (hcurve : ∀ (z : F) (P : F[X]) (S : Finset I), P.natDegree ≤ D → A ≤ S.card →
      (∀ i ∈ S, P.eval (dom i) = u₀ i + z*u₁ i) →
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ →
      let Q := P-(q₀+C z*q₁)
      (X+C z)*Q.derivative = C (D:F)*Q) :
    (univ.filter (mcaEvent (F:=F) (ReedSolomon.code dom (D+1) : Set (I → F)) δ u₀ u₁)).card ≤
      Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(D+1)/((A-1)*(A-2)) := by
  classical
  let Ccode := ReedSolomon.code dom (D+1)
  let B := univ.filter (mcaEvent (F:=F) (Ccode : Set (I → F)) δ u₀ u₁)
  apply captured_count dom u₀ u₁ q₀ q₁ D A hD hA hq₀ hq₁ hchar B
  intro z hz
  obtain ⟨S,hs,⟨c,hc,hfit⟩,hind⟩ := (mem_filter.mp hz).2
  obtain ⟨P,hp,hcP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
  have hf (i : I) (hi : i ∈ S) : P.eval (dom i) = u₀ i + z*u₁ i := (hcP i).trans (hfit i hi)
  exact ⟨S,P,by omega,hr S hs,hf,hind,hcurve z P S (by omega) (hr S hs) hf hind⟩
end MCA

#print axioms fiber_nonzero_count
#print axioms fiber_total_count
#print axioms captured_count
#print axioms mca_count_of_shifted_equation
#print axioms shifted_power_of_equation
#print axioms total_count
#print axioms four_test_costs
#print axioms nonzero_count
#print axioms zero_count
end ProximityGap.ShiftedPowerCurveCount
