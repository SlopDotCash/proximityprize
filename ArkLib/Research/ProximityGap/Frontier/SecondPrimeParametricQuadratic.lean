/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeLinearFactor

/-! # Quadratic factors with a parameter-only discriminant square class -/

open Finset Polynomial Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ProximityGap.SecondPrimeLinearFactor
open scoped NNReal

namespace ProximityGap.SecondPrimeParametricQuadratic

variable {I F K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
private abbrev Family (dom : I ↪ F) (δ : ℝ≥0) (u : WordStack F (Fin 2) I) :=
  BadScalarRichPointFamily dom 67108864 δ u

private theorem affine_degree {R : Type*} [CommRing R] [IsDomain R] {f : Polynomial R[X]}
    {h : R[X]} (hh : h.natDegree ≤ 1) : (f.eval h).natDegree ≤ Bivariate.totalDegree f := by
  rw [eval_eq_sum, Polynomial.sum]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hp : (h^j).natDegree ≤ j*h.natDegree := natDegree_pow_le
  have hj' := Nat.mul_le_mul_left j hh
  have hc := Bivariate.coeff_totalDegree_le f hj
  exact natDegree_mul_le.trans (by omega)

open Classical in
/-- A nonlinear irreducible factor carries at most its scalar-value total degree
in labels from any given base-field secant. -/
theorem secant_population_le {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) (φ : F →+* K)
    (f : Polynomial (Polynomial K[X])) (hf : Irreducible f) (hnl : 1 < f.natDegree) (p : F[X] × F[X]) :
    ((pointsOn fam p).filter fun z =>
      f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0).card ≤ Bivariate.totalDegree f := by
  classical
  let h : Polynomial K[X] := C (p.1.map φ) + Polynomial.X*C (p.2.map φ)
  have dh : h.natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have hne : f.eval h ≠ 0 := by
    intro he
    have hd := dvd_iff_isRoot.mpr he
    have hs := (irreducible_X_sub_C h).associated_of_dvd hf hd
    have hn := natDegree_le_of_dvd hs.symm.dvd (X_sub_C_ne_zero h)
    simp at hn
    omega
  have el (z : F) : h.eval (C (φ z)) = (p.1+C z*p.2).map φ := by
    simp [h]
    exact mul_comm _ _
  let T := (pointsOn fam p).filter fun z =>
    f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  by_contra! hgt
  apply hne
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : T => C (φ z.val))
    (C_injective.comp (φ.injective.comp Subtype.val_injective))
  · intro z
    obtain ⟨hz,he⟩ := mem_filter.mp z.property
    have hp := ((mem_pointsOn_iff fam p z.val).mp hz).2
    rw [hp, ← el] at he
    exact (eval₂_at_apply (p := f) (evalRingHom (C (φ z.val))) h).symm.trans he
  · exact lt_of_le_of_lt (affine_degree dh) (by simpa only [Fintype.card_coe,T] using hgt)

private theorem quadratic_shape {f : Polynomial (Polynomial K[X])} (hd : f.natDegree = 2) :
    f = C (f.coeff 2) * Polynomial.X^2 + C (f.coeff 1) * Polynomial.X + C (f.coeff 0) := by
  have he := as_sum_range_C_mul_X_pow' f (by omega : f.natDegree < 3)
  simpa [sum_range_succ, add_comm, add_left_comm, add_assoc] using he

/-- An irreducible quadratic has no square discriminant even after clearing an
arbitrary nonzero denominator in its coefficient ring. -/
private theorem no_square_discriminant (f : Polynomial (Polynomial K[X])) (hf : Irreducible f)
    (hd : f.natDegree = 2) (hchar : (2 : K) ≠ 0) (P Q : Polynomial K[X]) (hQ : Q ≠ 0) :
    P^2 ≠ ((f.coeff 1)^2 - 4*f.coeff 2*f.coeff 0)*Q^2 := by
  classical
  intro hs
  let A := f.coeff 2
  let B := f.coeff 1
  let D := f.coeff 0
  have hA : A ≠ 0 := by
    change f.coeff 2 ≠ 0
    rw [← hd]
    exact leadingCoeff_ne_zero.mpr hf.ne_zero
  have ht : (2 : Polynomial K[X]) ≠ 0 := by
    simpa only [map_ofNat] using C_ne_zero.mpr (C_ne_zero.mpr hchar)
  let L (b : Polynomial K[X]) : Polynomial (Polynomial K[X]) := C (2*A*Q) * Polynomial.X + C b
  have hprod : L (Q*B-P) * L (Q*B+P) = C (4*A*Q^2)*f := by
    have hsc := congrArg (fun r : Polynomial K[X] => (C r : Polynomial (Polynomial K[X]))) hs
    simp only [map_pow,map_sub,map_mul,map_ofNat] at hsc
    calc
      _ = (C (2*A*Q)*Polynomial.X+C (Q*B))^2-(C P)^2 := by
        simp only [L,map_sub,map_add]
        ring
      _ = _ := by
        rw [hsc]
        conv_rhs => rhs; rw [quadratic_shape hd]
        dsimp only [A,B]
        simp only [map_mul,map_pow,map_ofNat]
        ring
  have hdiv : f ∣ L (Q*B-P) * L (Q*B+P) := by
    rw [hprod]; exact ⟨C (4*A*Q^2), mul_comm (C (4*A*Q^2)) f⟩
  have impossible (b : Polynomial K[X]) (hv : f ∣ L b) : False := by
    have hn : L b ≠ 0 := by
      intro he
      have hc := congrArg (fun p : Polynomial (Polynomial K[X]) => p.coeff 1) he
      simp [L, mul_ne_zero (mul_ne_zero ht hA) hQ] at hc
    have hg := natDegree_le_of_dvd hv hn
    have hl : (L b).natDegree ≤ 1 := by
      dsimp only [L]
      apply natDegree_add_le_of_degree_le _ (by simp)
      exact natDegree_mul_le.trans (by rw [natDegree_C,natDegree_X])
    omega
  have hprime : Prime f := hf.prime
  exact (hprime.dvd_or_dvd hdiv).elim (impossible _) (impossible _)

/-- A quadratic factor with parameter-only discriminant square class restricts
to a double root wherever an affine received value solves it identically in the
parameter. The specialized quadratic coefficient remains nonzero there. -/
private theorem double_at_identity (f : Polynomial (Polynomial K[X])) (hf : Irreducible f)
    (hd : f.natDegree = 2) (hchar : (2 : K) ≠ 0) (s : K[X]) (V : Polynomial K[X])
    (hdisc : (f.coeff 1)^2 - 4*f.coeff 2*f.coeff 0 = s.map C * V^2)
    (x : K) (L : K[X]) :
    let a := (f.coeff 2).map (evalRingHom x)
    let b := (f.coeff 1).map (evalRingHom x)
    let c := (f.coeff 0).map (evalRingHom x)
    a*L^2+b*L+c = 0 → a ≠ 0 ∧ 2*a*L+b = 0 := by
  classical
  let e := mapRingHom (evalRingHom x)
  let ι := mapRingHom (C (R := K))
  let a := e (f.coeff 2)
  let b := e (f.coeff 1)
  let c := e (f.coeff 0)
  let v := e V
  let m := 2*a*L+b
  change a*L^2+b*L+c = 0 → a ≠ 0 ∧ m = 0
  intro hroot
  have hes : e (s.map C) = s := by
    ext j
    simp [e,coeff_map]
  have hel := congrArg (fun r => e r) hdisc
  change e _ = e _ at hel
  simp only [map_sub,map_pow,map_mul,map_ofNat,hes] at hel
  change b^2-4*a*c = s*v^2 at hel
  have hm : m^2 = s*v^2 := by
    dsimp only [m]
    linear_combination 4*a*hroot + hel
  have hv : v = 0 := by
    by_contra hnv
    have hιv : ι v ≠ 0 := (Polynomial.map_ne_zero_iff C_injective).mpr hnv
    apply no_square_discriminant f hf hd hchar (ι m * V) (ι v) hιv
    have hw := congrArg (fun g => ι g) hm
    change ι _ = ι _ at hw
    simp only [map_mul,map_pow] at hw
    rw [hdisc,mul_pow,hw]
    change (s.map C * (ι v)^2)*V^2 = (s.map C * V^2)*(ι v)^2
    ring
  have hm0 : m = 0 := by simpa [hv] using hm
  refine ⟨?_,hm0⟩
  intro haz
  have hbz : b = 0 := by simpa [m,haz] using hm0
  have hcz : c = 0 := by simpa [haz,hbz] using hroot
  have div (p : Polynomial K[X]) (hp : e p = 0) : C (Polynomial.X-C x) ∣ p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro j
    apply dvd_iff_isRoot.mpr
    have hc := congrArg (fun v : K[X] => v.coeff j) hp
    simpa [IsRoot,e, coeff_map] using hc
  have hfactor : C (C (Polynomial.X-C x)) ∣ f := by
    obtain ⟨vA,hA⟩ := div _ haz
    obtain ⟨vB,hB⟩ := div _ hbz
    obtain ⟨vD,hD⟩ := div _ hcz
    refine ⟨C vA * Polynomial.X^2 + C vB * Polynomial.X + C vD,?_⟩
    rw [quadratic_shape hd,hA,hB,hD]
    simp only [map_mul]
    ring
  have hp := hf.isPrimitive (by omega : f.natDegree ≠ 0)
  exact not_isUnit_X_sub_C x (isUnit_C.mp (isPrimitive_iff_isUnit_of_C_dvd.mp hp _ hfactor))

open Classical in
/-- If a large set of sections meets the secant extraction criterion, an irreducible quadratic
with parameter-only discriminant square class supports fewer than that many sections. -/
theorem parametric_population_of_extraction {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) (φ : F →+* K)
    (f : Polynomial (Polynomial K[X])) (hf : Irreducible f) (hd : f.natDegree = 2)
    (hweight : Bivariate.totalDegree f ≤ 34) (hchar : (2 : K) ≠ 0)
    (s : K[X]) (V : Polynomial K[X])
    (hdisc : (f.coeff 1)^2 - 4*f.coeff 2*f.coeff 0 = s.map C * V^2)
    {m : ℕ} (extract : SecantExtraction fam (m+1)) :
    (fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0).card ≤ m := by
  classical
  let pop := fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  change pop.card ≤ m
  by_contra! hpop
  obtain ⟨M,hsub,hm⟩ := exists_subset_card_eq (show m + 1 ≤ pop.card by omega)
  let site (i : I) (j : ℕ) := (f.coeff j).map (evalRingHom (φ (dom i)))
  let L (i : I) : K[X] := C (φ (u 0 i)) + Polynomial.X*C (φ (u 1 i))
  let R (i : I) := site i 2*(L i)^2 + site i 1*L i + site i 0
  let U := univ.filter fun i => R i = 0
  have degSite (i : I) (j : ℕ) (hj : j ≤ 34) : (site i j).natDegree + j ≤ 34 := by
    rcases Bivariate.coeff_totalDegree_le' f j with h | h
    · have hle : (site i j).natDegree ≤ (f.coeff j).natDegree := natDegree_map_le
      omega
    · simpa [site,h] using hj
  have degR (i : I) : (R i).natDegree ≤ 34 := by
    have h2 := degSite i 2 (by decide)
    have h1 := degSite i 1 (by decide)
    have h0 := degSite i 0 (by decide)
    have hl : (L i).natDegree ≤ 1 := by
      apply natDegree_add_le_of_degree_le
      · simp
      · exact natDegree_mul_le.trans (by simp)
    have hp : ((L i)^2).natDegree ≤ 2*(L i).natDegree := natDegree_pow_le
    apply natDegree_add_le_of_degree_le _ (by omega)
    apply natDegree_add_le_of_degree_le <;> exact natDegree_mul_le.trans (by omega)
  have he (i : I) (z : F) (hz : z ∈ pop) :
      (site i 2).eval (φ z) * φ ((fam.q z).eval (dom i))^2 +
      (site i 1).eval (φ z) * φ ((fam.q z).eval (dom i)) + (site i 0).eval (φ z) = 0 := by
    have hh := (mem_filter.mp hz).2
    rw [quadratic_shape hd] at hh
    have he' := congrArg (fun w : K[X] => w.eval (φ (dom i))) hh
    simpa only [site,eval₂_add,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X,coe_evalRingHom,
      eval_add,eval_mul,eval_pow,at_site,eval_map_apply,eval_zero] using he'
  obtain ⟨p,_,h35⟩ := extract M (hsub.trans (filter_subset _ _)) hm U (by
    intro i hi
    have hne : R i ≠ 0 := fun hh => hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
    apply (root_bound φ (R i) hne ?_).trans (degR i)
    intro z hz
    obtain ⟨hzM,ha⟩ := mem_filter.mp hz
    have hy := (mem_filter.mp ha).2
    have hh := he i z (hsub hzM)
    simpa only [R,L,eval_add,eval_mul,eval_pow,eval_C,eval_X,hy,map_add,map_mul] using hh) (by
    intro i hi
    have hri : R i = 0 := (mem_filter.mp hi).2
    obtain ⟨ha,hder⟩ := double_at_identity f hf hd hchar s V hdisc (φ (dom i)) (L i) hri
    change site i 2 ≠ 0 at ha
    change 2*site i 2*L i+site i 1 = 0 at hder
    apply (root_bound φ (site i 2) ha ?_).trans (by have := degSite i 2 (by decide); omega)
    intro z hz
    obtain ⟨hzM,hmiss⟩ := mem_filter.mp hz
    have hh := he i z (hsub hzM)
    have h0 := congrArg (fun v : K[X] => v.eval (φ z)) hri
    have h1 := congrArg (fun v : K[X] => v.eval (φ z)) hder
    simp only [R,eval_add,eval_mul,eval_pow,eval_ofNat,eval_zero] at h0 h1
    let v := φ ((fam.q z).eval (dom i))
    have hz0 : (site i 2).eval (φ z) * (v-(L i).eval (φ z))^2 = 0 := by
      dsimp only [v]
      linear_combination hh - h0 - (φ ((fam.q z).eval (dom i))-(L i).eval (φ z))*h1
    apply (mul_eq_zero.mp hz0).resolve_right
    intro hpow
    have heq : v = (L i).eval (φ z) := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
    apply hmiss
    apply mem_filter.mpr
    refine ⟨mem_univ _,φ.injective ?_⟩
    simpa only [v,L,eval_add,eval_mul,eval_C,eval_X,map_add,map_mul] using heq)
  have hs : M ∩ pointsOn fam p ⊆ (pointsOn fam p).filter fun z =>
      f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    intro z hz
    obtain ⟨hzM,hzp⟩ := mem_inter.mp hz
    exact mem_filter.mpr ⟨hzp,(mem_filter.mp (hsub hzM)).2⟩
  have hcap := secant_population_le fam φ f hf (by omega) p
  exact (by omega : ¬35 ≤ 34) (h35.trans ((card_le_card hs).trans (hcap.trans hweight)))

open Classical in
/-- At the second-prime predecessor, the participating scalar square class has at most 184 labels. -/
theorem parametric_discriminant_population_le (fam : Family dom δ u) (φ : F →+* K)
    (f : Polynomial (Polynomial K[X])) (hf : Irreducible f) (hd : f.natDegree = 2)
    (hweight : Bivariate.totalDegree f ≤ 34) (hchar : (2 : K) ≠ 0)
    (s : K[X]) (V : Polynomial K[X])
    (hdisc : (f.coeff 1)^2 - 4*f.coeff 2*f.coeff 0 = s.map C * V^2)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    (fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0).card ≤ 184 := by
  apply parametric_population_of_extraction fam φ f hf hd hweight hchar s V hdisc
  intro M hM hm U
  exact many_on_secant fam M hM hm U hn ht

#print axioms secant_population_le
#print axioms parametric_discriminant_population_le

end ProximityGap.SecondPrimeParametricQuadratic
