/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ShiftedPowerCurveCount
import Mathlib.RingTheory.Polynomial.Wronskian

/-! # Bounding the actual MCA labels on powers of a coordinate polynomial pencil

For any nonconstant degree-s polynomial G the values G(x_i) have multiplicity
at most s on an injective domain. Counting only pairs with distinct values
controls all rich witnesses on scalar multiples of (G(X)+z)^e, after subtracting
any common affine family of codewords.
-/

set_option autoImplicit false
namespace ProximityGap.PowerPencilCurveCount
open Polynomial Finset
open ProximityGap.ShiftedPowerCurveCount
variable {F : Type*} [Field F]

private theorem constant_of_derivative {h : F[X]} {D : ℕ}
    (hc : ringChar F = 0 ∨ D < ringChar F) (hd : h.natDegree ≤ D)
    (he : h.derivative = 0) : h = C (h.coeff 0) := by
  ext i
  cases i with
  | zero => simp
  | succ i =>
    simp only [coeff_C, Nat.succ_ne_zero]
    have hz := congrArg (fun p : F[X] => p.coeff i) he
    simp only [coeff_derivative,coeff_zero] at hz
    by_contra hind
    have hm := le_natDegree_of_ne_zero hind
    have hn : ((i+1 : ℕ) : F) ≠ 0 :=
      natCast_ne_zero_of_ringChar_eq_zero_or_lt hc (by omega) (by omega)
    exact (mul_ne_zero hind (by simpa using hn)) hz

/-- A zero Wronskian means proportionality for bounded-degree polynomials
over any field whose characteristic exceeds the cap, also in characteristic zero. -/
theorem scalar_of_wronskian {P Q : F[X]} {D : ℕ} (hQ : Q ≠ 0)
    (hc : ringChar F = 0 ∨ D < ringChar F) (hPdeg : P.natDegree ≤ D)
    (hQdeg : Q.natDegree ≤ D) (hw : wronskian P Q = 0) : ∃ a : F, P = C a*Q := by
  classical
  by_cases hP : P = 0
  · exact ⟨0,by simp [hP]⟩
  let g := GCDMonoid.gcd P Q
  let p := P/g
  let q := Q/g
  have hg : g ≠ 0 := gcd_ne_zero_of_right hQ
  have hp : g*p = P := EuclideanDomain.mul_div_cancel' hg (GCDMonoid.gcd_dvd_left ..)
  have hq : g*q = Q := EuclideanDomain.mul_div_cancel' hg (GCDMonoid.gcd_dvd_right ..)
  have hsmall : wronskian p q = 0 := by
    apply (mul_right_inj' (pow_ne_zero 2 hg)).mp
    rw [mul_zero]
    rw [← hp, ← hq] at hw
    unfold wronskian at hw ⊢
    simp only [derivative_mul] at hw
    linear_combination hw
  have ⟨hdp,hdq⟩ := (isCoprime_div_gcd_div_gcd hQ).wronskian_eq_zero_iff.mp hsmall
  have hpd : p ∣ P := ⟨g,(mul_comm p g).trans hp |>.symm⟩
  have hqd : q ∣ Q := ⟨g,(mul_comm q g).trans hq |>.symm⟩
  have hpC := constant_of_derivative hc ((natDegree_le_of_dvd hpd hP).trans hPdeg) hdp
  have hqC := constant_of_derivative hc ((natDegree_le_of_dvd hqd hQ).trans hQdeg) hdq
  change p = C (p.coeff 0) at hpC
  change q = C (q.coeff 0) at hqC
  have hn : q.coeff 0 ≠ 0 := by intro he; rw [he,map_zero] at hqC; rw [hqC,mul_zero] at hq; exact hQ hq.symm
  refine ⟨p.coeff 0/q.coeff 0,?_⟩
  rw [← hp,← hq]
  have hcoef := (div_mul_cancel₀ (p.coeff 0) hn)
  have ht := congrArg (C : F →+* F[X]) hcoef
  rw [map_mul] at ht
  calc g*p = g*C (p.coeff 0) := congrArg (g*·) hpC
       _ = C (p.coeff 0/q.coeff 0)*(g*C (q.coeff 0)) := by linear_combination -g*ht
       _ = _ := congrArg (fun u => C (p.coeff 0/q.coeff 0)*(g*u)) hqC.symm

/-- All degree-bounded solutions of G P' = e G' P are scalar multiples of
G^e as long as this power is nonzero and has degree below the characteristic. -/
theorem scalar_of_log_derivative {P G : F[X]} {e D : ℕ} (hG : G ≠ 0)
    (hc : ringChar F = 0 ∨ D < ringChar F) (hp : P.natDegree ≤ D)
    (hg : (G^e).natDegree ≤ D) (he : G*P.derivative = C (e:F)*G.derivative*P) :
    ∃ a : F, P = C a*G^e := by
  apply scalar_of_wronskian (pow_ne_zero e hG) hc hp hg
  cases e with
  | zero =>
    simp only [Nat.cast_zero,C_0,zero_mul,mul_eq_zero] at he
    simp [wronskian,he.resolve_left hG]
  | succ j =>
    rw [wronskian,derivative_pow_succ,pow_succ]
    push_cast at he
    linear_combination -G^j*he

/-- A positive-degree polynomial has at most s sites above every value on an
injective domain, with s its degree. -/
theorem fiber_bound {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq F]
    (dom : I ↪ F) (G : F[X]) (hG : 0 < G.natDegree) (x : F) :
    (univ.filter fun i => G.eval (dom i) = x).card ≤ G.natDegree := by
  classical
  let S := univ.filter fun i => G.eval (dom i) = x
  have hne : G-C x ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h,natDegree_C] at hG
    omega
  rw [← card_image_of_injective S dom.injective]
  apply (card_le_degree_of_subset_roots (p:=G-C x) _).trans
    ((natDegree_sub_le ..).trans (by simp))
  intro t ht
  obtain ⟨i,hi,rfl⟩ := mem_image.mp (show t ∈ S.image dom from ht)
  exact (mem_roots hne).mpr (by simpa [IsRoot] using sub_eq_zero.mpr (mem_filter.mp hi).2)

/-- Every qualifying challenge has a nonjoint fit from a scalar multiple of
(G+z)^e, translated by two fixed codewords. No condition is imposed on the
other decoders of either received word. -/
theorem power_family_count {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ G : F[X]) (D e A : ℕ)
    (hG : 0 < G.natDegree) (he : 2 ≤ e) (hA : 2*G.natDegree < A)
    (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D) (B : Finset F)
    (hwitness : ∀ z ∈ B, ∃ (S : Finset I) (a : F), A ≤ S.card ∧
      (∀ i ∈ S, u₀ i+z*u₁ i = q₀.eval (dom i)+z*q₁.eval (dom i)+
        a*(G.eval (dom i)+z)^e) ∧
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁) :
    B.card ≤ Fintype.card I-A+1 + Fintype.card I*(Fintype.card I-1)*(e+1) /
      ((A-G.natDegree)*(A-2*G.natDegree)) := by
  classical
  let w (i : I) := C (u₀ i-q₀.eval (dom i))+X*C (u₁ i-q₁.eval (dom i))
  have hw (i : I) : (w i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  choose! S a hs hfit hind using hwitness
  apply fiber_total_count (fun i => G.eval (dom i)) G.natDegree (fiber_bound dom G hG)
    w hw B S a e A he hA hs
  · intro z hz i hi
    simp [w]
    linear_combination hfit z hz i hi
  · intro z hz _
    by_contra! hnone
    apply hind z hz
    refine ⟨ReedSolomon.evalOnPoints dom q₀,ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),
      ReedSolomon.evalOnPoints dom q₁,ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),?_⟩
    intro i hi
    have hz₀ := congrArg (fun f : F[X] => f.coeff 0) (hnone i hi)
    have hz₁ := congrArg (fun f : F[X] => f.coeff 1) (hnone i hi)
    simp [w] at hz₀ hz₁
    exact ⟨(sub_eq_zero.mp hz₀).symm,(sub_eq_zero.mp hz₁).symm⟩

open Classical in
/-- The production MCA event is bounded for a received pair whenever its
local witnesses satisfy the translated logarithmic differential equation.
The zero multiplier and all coincident values of G are included. -/
theorem mca_count_of_power_pencil
    {I F : Type} [DecidableEq I] [Fintype I] [Field F] [DecidableEq F] [Fintype F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ G : F[X]) (D e A : ℕ) (δ : NNReal)
    (hG : 0 < G.natDegree) (he : 2 ≤ e) (hA : 2*G.natDegree < A)
    (hdeg : G.natDegree*e ≤ D) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hc : ringChar F = 0 ∨ D < ringChar F)
    (hr : ∀ S : Finset I, (1-δ)*(Fintype.card I : NNReal) ≤ S.card → A ≤ S.card)
    (hcurve : ∀ (z : F) (P : F[X]) (S : Finset I), P.natDegree ≤ D → A ≤ S.card →
      (∀ i ∈ S, P.eval (dom i) = u₀ i + z*u₁ i) →
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ →
      let Q := P-(q₀+C z*q₁)
      (G+C z)*Q.derivative = C (e:F)*G.derivative*Q) :
    (univ.filter (mcaEvent (F:=F) (ReedSolomon.code dom (D+1) : Set (I → F)) δ u₀ u₁)).card ≤
      Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(e+1) /
        ((A-G.natDegree)*(A-2*G.natDegree)) := by
  classical
  apply power_family_count dom u₀ u₁ q₀ q₁ G D e A hG he hA hq₀ hq₁
  intro z hz
  obtain ⟨S,hs,⟨c,hcC,hfit⟩,hind⟩ := (mem_filter.mp hz).2
  obtain ⟨P,hp,hcP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hcC
  have hf (i : I) (hi : i ∈ S) : P.eval (dom i) = u₀ i + z*u₁ i := (hcP i).trans (hfit i hi)
  let Q := P-(q₀+C z*q₁)
  have hq : Q.natDegree ≤ D := by
    apply (natDegree_sub_le ..).trans (max_le (by omega) _)
    apply (natDegree_add_le ..).trans (max_le hq₀ _)
    exact natDegree_mul_le.trans (by simpa using hq₁)
  have hn : G+C z ≠ 0 := by
    intro hz
    have hg : G = C (-z) := (eq_neg_of_add_eq_zero_left hz).trans (map_neg C z).symm
    rw [hg,natDegree_C] at hG
    omega
  have hle : ((G+C z)^e).natDegree ≤ D := by
    rw [natDegree_pow]
    have ht : (G+C z).natDegree ≤ G.natDegree := (natDegree_add_le ..).trans (by simp)
    exact (Nat.mul_le_mul_left e ht).trans (by simpa [Nat.mul_comm] using hdeg)
  obtain ⟨a,ha⟩ := scalar_of_log_derivative (P:=Q) hn hc hq hle
    (by simpa only [Q,derivative_add,derivative_C,add_zero] using hcurve z P S (by omega) (hr S hs) hf hind)
  refine ⟨S,a,hr S hs,?_,hind⟩
  intro i hi
  have hv := congrArg (eval (dom i)) ha
  simp only [Q,eval_sub,eval_mul,eval_add,eval_C,eval_pow,hf i hi] at hv
  linear_combination hv

/-- The thinner budget n suffices at each rate for coordinate-map degrees
2, 3, 4, and 6 respectively, with the largest allowed power at that degree. -/
theorem four_thin_costs :
    let n : ℕ := 2^30
    let cost := fun (k A s : ℕ) => n-A+1+n*(n-1)*((k-1)/s+1)/((A-s)*(A-2*s))
    cost (2^29) (89*2^23) 2 = 882394513 ∧
    cost (2^28) (61*2^23) 3 = 956021025 ∧
    cost (2^27) (42*2^23) 4 = 1033073255 ∧
    cost (2^26) (29*2^23) 6 = 1048369882 := by decide

#print axioms mca_count_of_power_pencil
#print axioms scalar_of_wronskian
#print axioms scalar_of_log_derivative
#print axioms fiber_bound
#print axioms power_family_count
#print axioms four_thin_costs
end ProximityGap.PowerPencilCurveCount
