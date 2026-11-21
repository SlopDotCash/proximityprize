/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.MCALatticeExact
import ArkLib.Research.ProximityGap.Frontier.ApolarSuccessorDefect
import ArkLib.Research.ProximityGap.Frontier.ApolarUnitChartSpecialization

/-! # The product of the error coordinates on a smooth successor fiber -/

set_option autoImplicit false
open Finset Polynomial Code ProximityGap Classical
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarDividedPolynomial
open ProximityGap.ApolarUnitChartSpecialization ProximityGap.ApolarRootTransition
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ProximityGap.ApolarMcaSyndrome
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.ApolarSmoothProduct

variable {F : Type} [Field F] [DecidableEq F]

/-- On a full smooth domain, equal powers of the two moment polynomials mean
that they differ by multiplication by a single original domain element. -/
theorem power_eq_iff (H : Finset F) {n : ℕ} (hn : 0 < n) (hH : H.card = n)
    (hroots : ∀ y ∈ H, y^n = 1) (c z : F[X]) :
    c^n = z^n ↔ ∃ y ∈ H, c = C y * z := by
  classical
  constructor
  · intro he
    by_cases hz : z = 0
    · rw [hz,zero_pow hn.ne'] at he
      have hc : c = 0 := (pow_eq_zero_iff hn.ne').mp he
      obtain ⟨y,hy⟩ := card_pos.mp (hH.symm ▸ hn)
      exact ⟨y,hy,by simp [hz,hc]⟩
    let J := FractionRing F[X]
    let ψ : F[X] →+* J := algebraMap F[X] J
    have hi : Function.Injective ψ := IsFractionRing.injective F[X] J
    let φ : F →+* J := ψ.comp C
    let into : F ↪ J := ⟨φ,φ.injective⟩
    let A := H.map into
    let R := (Polynomial.nthRoots n (1 : J)).toFinset
    have hsub : A ⊆ R := by
      intro y hy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hy
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_nthRoots hn).mpr
      change (φ a)^n = 1
      rw [← map_pow,hroots a ha,map_one]
    have heq : A = R := eq_of_subset_of_card_le hsub (by
      rw [show A.card = n by simp [A,hH]]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _))
    have hψ : ψ z ≠ 0 := (map_ne_zero_iff _ hi).mpr hz
    have hx : ψ c / ψ z ∈ R := by
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_nthRoots hn).mpr
      rw [div_pow,← map_pow,he,map_pow,div_self (pow_ne_zero _ hψ)]
    obtain ⟨a,ha,hae⟩ := Finset.mem_map.mp (heq ▸ hx : ψ c / ψ z ∈ A)
    refine ⟨a,ha,hi ?_⟩
    rw [map_mul]
    exact (div_eq_iff hψ).mp hae.symm
  · rintro ⟨a,ha,rfl⟩
    rw [mul_pow,← C_pow,hroots a ha,map_one,one_mul]

private theorem root_relation (E : Finset F) (ν : F → F) (q : F[X]) {h : ℕ} (hh : 0 < h)
    (hs : E.card = h + 1) (hroots : ∀ y ∈ E, y ^ (4*h) = 1)
    (ha : ApolarThrough (weighted E (RingHom.id F) ν) (Polynomial.X * q) (h-1)) :
    (weighted E (RingHom.id F) ν ((Polynomial.X * q) * Polynomial.X ^ h)) ^ (4*h) =
      (weighted E (RingHom.id F) ν q) ^ (4*h) := by
  let L := weighted E (RingHom.id F) ν
  let f := Polynomial.X * q
  have hp := ApolarSuccessorDefect.residue_identity E ν f (s := h-1) (by omega) ha
  have hh' : h-1+1=h := by omega
  rw [hh'] at hp
  have hval := congrArg (Polynomial.eval (0 : F)) hp
  have hrep := eval₂_representative E ν (RingHom.id F) 0 f
  rw [eval₂_id,Polynomial.map_id] at hrep
  have hdiv : divided f 0 = q := by
    simp only [divided,f,map_zero,sub_zero]
    exact mul_divByMonic_cancel_left q monic_X
  rw [hdiv] at hrep
  have h0 : f.eval 0 = 0 := by simp [f]
  simp only [eval_add,eval_mul,eval_C,hrep,h0,zero_mul] at hval
  have hen : Even (4*h) := ⟨2*h,by omega⟩
  have hz : ((Lagrange.nodal E id).eval 0)^(4*h) = 1 := by
    rw [Lagrange.eval_nodal,← Finset.prod_pow]
    exact prod_eq_one fun y hy => by simpa only [id_eq,zero_sub,hen.neg_pow] using hroots y hy
  have he : L (f * Polynomial.X^h) = -((Lagrange.nodal E id).eval 0 * L q) := by
    change _ + L (f * Polynomial.X^h) = 0 at hval
    linear_combination hval
  change (L (f * Polynomial.X^h)) ^ (4*h) = (L q) ^ (4*h)
  rw [he,hen.neg_pow,mul_pow,hz,one_mul]

/-- The affine barycentric weights for the two received rows. -/
noncomputable def weight (H : Finset F) (u v : F → F) (y : F) : F[X] :=
  C (rowWeight H u y) + Polynomial.X * C (rowWeight H v y)

omit [DecidableEq F] in
private theorem eval_weight (H : Finset F) (u v : F → F) (t y : F) :
    (weight H u v y).eval t = rowWeight H (fun x => u x + t * v x) y := by
  simp only [weight,eval_add,eval_mul,eval_X,eval_C,rowWeight,add_div,mul_div_assoc]

omit [DecidableEq F] in
private theorem moment_degree (H : Finset F) (u v : F → F) (q : F[X][X]) (m l : ℕ)
    (hq : ∀ i, (q.coeff i).natDegree ≤ l) :
    ((measure H C (weight H u v)) (q * Polynomial.X^m)).natDegree ≤ l+1 := by
  classical
  simp only [_root_.ProximityGap.ApolarRootTransition.measure,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.leval,
    LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul,eval_mul,eval_pow,eval_X]
  apply natDegree_sum_le_of_forall_le
  intro y hy
  have hw : (weight H u v y).natDegree ≤ 1 := by
    unfold weight
    apply (natDegree_add_le ..).trans
    exact max_le (by simp) ((natDegree_mul_le ..).trans (by simp))
  have hqev : (q.eval (C y)).natDegree ≤ l := by
    rw [eval_eq_sum_range]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    rw [← C_pow]
    exact (natDegree_mul_C_le ..).trans (hq j)
  rw [← C_pow]
  have hdeg := (natDegree_mul_C_le (q.eval (C y)) (y^m)).trans hqev
  exact (natDegree_mul_le ..).trans (by omega)

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Fintype F]

/-- For a locator with the two fixed projective roots zero and infinity,
the global moments constrain every actual bad scalar by a single polynomial. -/
theorem count (dom : I ↪ F) (u : WordStack F (Fin 2) I) {h l : ℕ} (hh : 2 ≤ h)
    (hn : Fintype.card I = 4*h) (hdom : ∀ i, (dom i) ^ (4*h) = 1)
    (q : F[X][X]) (hq : q.natDegree ≤ h-2) (hl : ∀ i, (q.coeff i).natDegree ≤ l) :
    let H := (univ : Finset I).map dom
    let a := coordinateRow dom (u 0)
    let b := coordinateRow dom (u 1)
    let Λ := measure H C (weight H a b)
    let c := Λ (q * Polynomial.X^(h+1))
    let z := Λ q
    ApolarThrough Λ (Polynomial.X*q) (h-1) → c^(4*h) ≠ z^(4*h) →
    (univ.filter fun t : F => mcaEvent (ReedSolomon.code dom (2*h) : Set (I → F))
       (((h+1 : ℕ) : ℝ≥0) / (4*h : ℕ)) (u 0) (u 1) t).card ≤ (4*h)*(l+1) := by
  classical
  intro H a b Λ c z ha hdiff
  let δ : ℝ≥0 := (((h+1 : ℕ) : ℝ≥0) / (4*h : ℕ))
  let fam := canonicalBadScalarRichPointFamily dom δ u (by omega : 1 ≤ 2*h)
  let P := c^(4*h)-z^(4*h)
  have hP : P ≠ 0 := sub_ne_zero.mpr hdiff
  have hz := moment_degree H a b q 0 l hl
  simp only [pow_zero,mul_one] at hz
  have hc := moment_degree H a b q (h+1) l hl
  have hd : P.natDegree ≤ (4*h)*(l+1) := (natDegree_sub_le ..).trans
    (max_le (natDegree_pow_le_of_le _ hc) (natDegree_pow_le_of_le _ hz))
  have hsub : fam.G ⊆ P.roots.toFinset := by
    intro t ht
    let p := fam.q t
    let A := fullAgreement dom (u 0) (u 1) t p
    have hag : 3*h-1 ≤ A.card := by
      have ht' := fam.threshold_le t ht
      have he := one_sub_div_mul_cast (ι:=I) (h+1) (by omega)
      rw [hn] at he
      change ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ ≤ A.card at ht'
      rw [hn, show (1-δ)*(↑(4*h : ℕ) : ℝ≥0) = ↑(4*h-(h+1) : ℕ) from he,
        Nat.ceil_natCast] at ht'
      omega
    obtain ⟨S, hSA, hS⟩ := exists_subset_card_eq hag
    let E := ((univ : Finset I) \ S).map dom
    have hE : E ⊆ H := Finset.map_subset_map.mpr sdiff_subset
    have hec : E.card = h+1 := by
      simp only [E,card_map,card_sdiff_of_subset (subset_univ _),card_univ,hn,hS]
      omega
    let v := fun y => a y + t*b y
    let ν := rowWeight H (fun y => v y - p.eval y)
    have agree (y : F) (hy : y ∈ H) (hey : y ∉ E) : v y = p.eval y := by
      obtain ⟨i,_,rfl⟩ := mem_map.mp hy
      have his : i ∈ S := by
        by_contra hi
        exact hey (mem_map.mpr ⟨i,mem_sdiff.mpr ⟨mem_univ _,hi⟩,rfl⟩)
      simpa only [v,a,b,coordinateRow_apply] using (mem_filter.mp (hSA his)).2.symm
    let qₜ := q.map (evalRingHom t)
    have hdq : qₜ.natDegree ≤ h-2 := natDegree_map_le.trans hq
    have hp : p.natDegree < 2*h := fam.degree_lt t ht
    have hH : H.card = 4*h := by simp [H,hn]
    have red (B : F[X]) (hB : B.natDegree ≤ 2*h-1) :
        weighted H (RingHom.id F) (fun y => (weight H a b y).eval t) B =
          weighted E (RingHom.id F) ν B := by
      simp_rw [eval_weight]
      exact syndrome_reduced H E v p B (RingHom.id F) hE agree (by omega)
    have hap : ApolarThrough (weighted E (RingHom.id F) ν) (Polynomial.X * qₜ) (h-1) := by
      intro B hB
      rw [← red]
      · have hsp := specialize_apolar H (weight H a b) (Polynomial.X*q) (h-1) ha t
        simpa only [Polynomial.map_mul,map_X] using hsp B hB
      · have hdf := natDegree_mul_le (p := (Polynomial.X : F[X])) (q := qₜ)
        rw [natDegree_X] at hdf
        have hh' := natDegree_mul_le (p:=Polynomial.X * qₜ) (q:=B)
        omega
    have hr := root_relation E ν qₜ (by omega : 0<h) hec (by
      intro y hy
      obtain ⟨i,_,rfl⟩ := mem_map.mp (hE hy)
      exact hdom i) hap
    have hcz : c.eval t = weighted E (RingHom.id F) ν ((Polynomial.X*qₜ)*Polynomial.X^h) := by
      rw [show c=Λ (q*Polynomial.X^(h+1)) from rfl,specialize_measure]
      simp only [Polynomial.map_mul,Polynomial.map_pow,map_X]
      rw [show qₜ*Polynomial.X^(h+1)=(Polynomial.X*qₜ)*Polynomial.X^h by
        rw [pow_succ]; ring]
      apply red
      have hdf := natDegree_mul_le (p := (Polynomial.X : F[X])) (q := qₜ)
      rw [natDegree_X] at hdf
      have hh' := natDegree_mul_le (p:=Polynomial.X*qₜ) (q:=(Polynomial.X : F[X])^h)
      rw [natDegree_X_pow] at hh'
      omega
    have hzz : z.eval t = weighted E (RingHom.id F) ν qₜ :=
      (specialize_measure H (weight H a b) t q).trans (red qₜ (by omega))
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hP).mpr
    simp only [P,IsRoot.def,eval_sub,eval_pow,hcz,hzz,hr,sub_self]
  exact ((card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_roots' P))).trans hd

set_option pp.fullNames true
#print axioms power_eq_iff
#print axioms count
end ArkLib.ProximityGap.Frontier.ApolarSmoothProduct
