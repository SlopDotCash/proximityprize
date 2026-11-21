/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DoubleInterpolationCommonFactor
import ArkLib.Research.ProximityGap.Frontier.PrimitiveReceivedInterpolation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount

/-! # A variable-degree quadratic interpolant with a double auxiliary
The primary surface has degree two in the folded value. A factor supporting
more than the resultant degree divides a second surface of scalar/value
degree at most thirty-four. Thus the discriminant and affine extraction estimates apply
even when the primary scalar degree is large.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount

open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open _root_.ProximityGap _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
  {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}


private theorem simple_capacity {s n d t : ℕ} (hs : 2 ≤ s) (hd : 2*d ≤ t)
    (surplus : (s+1)*n+(3*s-2)*d < 3*s*t) :
    n*(s+1) < Fintype.card (Monomials s 2 d t) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  have a : s+1-1=s := by omega
  have b : s+1-2=s-1 := by omega
  have c : t-d+d=t := by omega
  have e : t-2*d+2*d=t := by omega
  have h : 3*s-2+2=3*s := by omega
  have f : s-1+1=s := by omega
  nlinarith only [surplus, congrArg (·*d) h,congrArg (·*(t-d)) a,congrArg (·*(t-2*d)) b,
    congrArg (s*·) c, congrArg ((s-1)*·) e,congrArg (·*t) f,congrArg (·*d) f]

theorem double_capacity {n d t : ℕ} (surplus : 50*n+140*d<150*t) :
    n*(2*(16+1)+16)<Fintype.card (Monomials 16 4 d (2*t)) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

set_option maxRecDepth 8192 in
/-- Two successive common factors exhaust the value degree of the primitive
primary surface. Each shared component carries at most one head's population. -/
theorem primitive_cap {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) {n e t t₀ s b v : ℕ}
    (hn : Fintype.card I=n) (hsum : e+t=n) (hk : 1 ≤ k) (hmin : t₀ ≤ t)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hs : 2 ≤ s) (hd : 2*(k-1) ≤ t₀) (hsur : (s+1)*n+(3*s-2)*(k-1)<3*s*t₀)
    (bh : 0 < b) (bd : b ≤ 34) (aux : n*(b+1)<Fintype.card (Monomials b v (k-1) t₀) ∨
      n*(2*(b+1)+b)<Fintype.card (Monomials b v (k-1) (2*t₀)))
    (hbase : n+3*(k-1) ≤ 3*t₀) (enough : 512 ≤ e+1)
    (first : 2*b+v*s ≤ 2*e+2) (second : b+(v-1)*s ≤ e+1)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(t₀-1-(k-1)) → (i:F) ≠ 0) :
    fam.G.card ≤ 2*e+2 := by
  classical
  have extract : SecantExtraction fam 512 := by
    intro M hM hm U
    apply extraction_of_geometry (m:=478) (t:=t₀) fam hk (by decide) _ M hM hm U hn (hmin.trans ht.ge)
    intro c a b l v hc hinc hcover ha hb hl
    omega
  obtain ⟨c,hc,lines,_⟩ := exists_curve (s:=s) (v:=2) (d:=k-1) dom (u 0) (u 1)
    (by omega : 0<t₀) (by rw [hn];exact simple_capacity hs hd hsur)
  obtain ⟨T,c₂,hc₂,witness₂⟩ : ∃ (T : ℕ) (a : Monomials b v (k-1) T → F), a ≠ 0 ∧
      ∀ (z : F) (q : F[X]), q.natDegree ≤ k-1 → ∀ S : Finset I, t₀ ≤ S.card →
        (∀ i∈S, q.eval (dom i)=u 0 i+z*u 1 i) → specialize a z q=0 := by
    rcases aux with simple|double
    · obtain ⟨a,h,_,w⟩ := exists_curve (s:=b) (v:=v) (d:=k-1) dom (u 0) (u 1)
        (by omega : 0 < t₀) (by rw [hn];exact simple)
      exact ⟨_,a,h,w⟩
    · obtain ⟨a,h,w⟩ := exists_curve_double (s:=b) (v:=v) (d:=k-1) dom (u 0) (u 1)
        (by omega : 0 < t₀) bh (by rw [hn];exact double)
      exact ⟨_,a,h,w⟩
  let A := surface c₂
  have hA : A ≠ 0 := surface_ne_zero hc₂
  have ashape {j i a : ℕ} (h : ((A.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ v ∧ i+j ≤ b ∧ a+j*(k-1)<T := surface_support c₂ h
  have aval : A.natDegree ≤ v := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (ashape h).1
  let Q := surface c
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have shape {j i a : ℕ} (h : ((Q.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 2 ∧ i+j ≤ s ∧ a+j*(k-1) < t₀ := surface_support c h
  have val : Q.natDegree ≤ 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (shape h).1
  let φ := RingHom.id F
  let pop (f : F[X][X][X]) := fam.G.filter fun z =>
    f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  have population_eq (f : F[X][X][X])
      (d : DecidablePred fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
      @Finset.filter F _ d fam.G = pop f := by
    ext z
    simp only [pop, mem_filter]
  let P := Q.primPart
  have prim : P.IsPrimitive := isPrimitive_primPart _
  have hPQ : P ∣ Q := primPart_dvd _
  have pdeg : P.natDegree ≤ 2 := (natDegree_primPart _).le.trans val
  have roots (z : F) (hz : z ∈ fam.G) :
      P.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    apply PrimitiveReceivedInterpolation.raw_primitive_section dom (u 0) (u 1) hc
      (by omega) lines _ _ (by have := fam.degree_lt z hz; omega)
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (hmin.trans (ht ▸ fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  have rootsAux (z : F) (hz : z ∈ fam.G) :
      A.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    simp only [A, surface_eval]
    apply witness₂ _ _ (by have := fam.degree_lt z hz; omega) (fullAgreement dom (u 0) (u 1) z (fam.q z))
      (hmin.trans (ht ▸ fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  have qtri {R : F[X][X][X]} (rdiv : R ∣ Q) :=
    SecondPrimeSectionResultant.factor_triangle hQ rdiv (fun _ _ _ h => (shape h).2.1)
  have atri {R : F[X][X][X]} (rdiv : R ∣ A) :=
    SecondPrimeSectionResultant.factor_triangle hA rdiv (fun _ _ _ h => (ashape h).2.1)
  have component (f : F[X][X][X]) (hirr : Irreducible f) (hpos : 0 < f.natDegree)
      (hdivQ : f ∣ Q) (divAux : f ∣ A) : (pop f).card ≤ e+1 := by
    by_contra! hpop
    have hd := (natDegree_le_of_dvd hdivQ hQ).trans val
    have htot := factor_totalDegree_le hA divAux (fun _ _ _ h => ((ashape h).2.1).trans bd)
    have triAux := SecondPrimeSectionResultant.factor_triangle hA divAux (fun _ _ _ h => (ashape h).2.1)
    have weightQ : SecondPrimeCoordinateWeight.weight (k-1) Q ≤ t₀-1 :=
      SecondPrimeCoordinateWeight.weight_le_of_coeff _ _ (fun j i a h => by have := (shape h).2.2;omega)
    have weightf : SecondPrimeCoordinateWeight.weight (k-1) f ≤ t₀-1 := by
      obtain ⟨g,hg⟩ := hdivQ
      rw [hg] at hQ weightQ
      rw [SecondPrimeCoordinateWeight.weight_mul _ f g (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)] at weightQ
      omega
    have commonShape (j i a : ℕ) (h : ((f.coeff j).coeff i).coeff a ≠ 0) : i+j ≤ 34 ∧ a+j*(k-1) ≤ t₀-1 := by
      have hj : f.coeff j ≠ 0 := fun eq => h (by simp [eq])
      have hi : (f.coeff j).coeff i ≠ 0 := fun eq => h (by simp [eq])
      have one := triAux j hj
      have two := le_natDegree_of_ne_zero hi
      have three := (SecondPrimeCoordinateWeight.coeff_weight_le (k-1) f h).trans weightf
      omega
    have hlin : f.natDegree = 1 := by
      by_contra hnon
      have hquad : f.natDegree=2 := by omega
      have lc : f.coeff 2 ≠ 0 := hquad ▸ leadingCoeff_ne_zero.mpr hirr.ne_zero
      have lead := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr lc)
      have wt := (commonShape 2 _ _ lead).2
      have bound := SecondPrimeQuadraticFactor.quadratic_population_weighted
        (w:=t₀-1) (m:=511) fam φ f f hirr.ne_zero dvd_rfl hirr hquad commonShape (by omega) (by omega) hchar extract
      rw [population_eq f] at bound
      omega
    obtain ⟨p,hp,hcarry⟩ := linear_factor_is_head_of_extraction (m := 511) fam φ f hirr hlin
      htot extract (by rw [population_eq f]; omega)
    rw [population_eq f] at hcarry
    have linebound := TwoLargeCoreCount.line_occupancy_le fam (hn.trans hsum.symm) ht hp
    exact hpop.not_ge ((card_le_card hcarry).trans linebound)
  by_contra! tooMany
  obtain ⟨f,irrF,posF,fP,fA⟩ := DoubleInterpolationCommonFactor.exists_common prim fam.G fam.q
    (fun z hz => ⟨roots z hz,rootsAux z hz⟩) (qtri hPQ) (atri dvd_rfl) (by
      have a := Nat.mul_le_mul_right b pdeg
      have c := Nat.mul_le_mul_right s aval
      omega)
  have cntF := component f irrF posF (fP.trans hPQ) fA
  obtain ⟨R,pf⟩ := fP
  obtain ⟨A',af⟩ := fA
  have rP : R ∣ P := pf ▸ dvd_mul_left R f
  have aA : A' ∣ A := af ▸ dvd_mul_left A' f
  have pr := isPrimitive_of_dvd prim rP
  have ane : A' ≠ 0 := right_ne_zero_of_mul (af ▸ hA)
  have ry : R.natDegree ≤ 1 := by rw [pf,natDegree_mul irrF.ne_zero pr.ne_zero] at pdeg; omega
  have ay : A'.natDegree ≤ v-1 := by rw [af,natDegree_mul irrF.ne_zero ane] at aval;omega
  let H := fam.G \ pop f
  have hH : e+1 < H.card := by have := le_card_sdiff (pop f) fam.G; change _ < (fam.G \ pop f).card;omega
  have outside {z : F} (hz : z∈H) : f.eval₂ (evalRingHom (C z)) (fam.q z) ≠ 0 := by
    intro zero
    apply (mem_sdiff.mp hz).2
    exact mem_filter.mpr ⟨(mem_sdiff.mp hz).1,by simpa [φ] using zero⟩
  have rroots (z : F) (hz : z∈H) : R.eval₂ (evalRingHom (C z)) (fam.q z)=0 ∧
      A'.eval₂ (evalRingHom (C z)) (fam.q z)=0 := by
    have h₁ := roots z (mem_sdiff.mp hz).1
    have h₂ := rootsAux z (mem_sdiff.mp hz).1
    rw [pf,eval₂_mul] at h₁
    rw [af,eval₂_mul] at h₂
    exact ⟨(mul_eq_zero.mp h₁).resolve_left (outside hz),(mul_eq_zero.mp h₂).resolve_left (outside hz)⟩
  obtain ⟨g,irrG,posG,gR,gA⟩ := DoubleInterpolationCommonFactor.exists_common pr H fam.q rroots
    (qtri (rP.trans hPQ)) (atri aA) (by
      have a := Nat.mul_le_mul_right b ry
      have c := Nat.mul_le_mul_right s ay
      omega)
  have cntG := component g irrG posG (gR.trans (rP.trans hPQ)) (gA.trans aA)
  obtain ⟨J,rj⟩ := gR
  have jR : J ∣ R := rj ▸ dvd_mul_left J g
  have pj := isPrimitive_of_dvd pr jR
  have zeroJ : J.natDegree=0 := by rw [rj,natDegree_mul irrG.ne_zero pj.ne_zero] at ry;omega
  obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (H \ pop g).card by have := le_card_sdiff (pop g) H;omega)
  have hzH := (mem_sdiff.mp hz).1
  have gn : g.eval₂ (evalRingHom (C z)) (fam.q z) ≠ 0 := by
    intro zero
    apply (mem_sdiff.mp hz).2
    exact mem_filter.mpr ⟨(mem_sdiff.mp hzH).1,by simpa [φ] using zero⟩
  have hr := (rroots z hzH).1
  rw [rj,eval₂_mul] at hr
  have := DoubleInterpolationCommonFactor.positive_of_section pj z _ ((mul_eq_zero.mp hr).resolve_left gn)
  omega

set_option maxRecDepth 8192 in
/-- Variable-degree primary interpolation gives the full two-head bound
when both interpolation surpluses and the scalar and core tests hold. -/
theorem family_cap {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) {n e t t₀ s L : ℕ}
    (hn : Fintype.card I=n) (hsum : e+t=n) (hk : 1 ≤ k) (hmin : t₀ ≤ t)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hs : 2 ≤ s) (hd : 2*(k-1) ≤ t₀) (hsur : (s+1)*n+(3*s-2)*(k-1)<3*s*t₀)
    (hdouble : 50*n+140*(k-1)<150*t₀) (hbase : n+3*(k-1) ≤ 3*t₀)
    (hL : 512 ≤ L) (hresult : 4*s+32 ≤ L) (enough : s+2*L<e+2)
    (_geom : n+3*(k-1)<t+2*(t-n/L))
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(t₀-1) → (i:F) ≠ 0) :
    fam.G.card ≤ 2*e+2 := by
  exact primitive_cap fam hn hsum hk hmin ht hs hd hsur (by decide : 0 < 16)
    (by decide) (Or.inr (double_capacity hdouble)) hbase (by omega) (by omega) (by omega) (fun i hi hb => hchar i hi (by omega))

end ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount
#print axioms ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount.primitive_cap
#print axioms ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount.family_cap
