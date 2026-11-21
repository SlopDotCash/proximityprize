/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarSparseSpecialization

/-! # Normalizing the two finite coordinate charts of an MCA moment pencil -/

open Polynomial Finset Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarCoordinateTransport
open ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarPrimitiveKernel
open ProximityGap.ApolarSparseSpecialization

namespace ProximityGap.ApolarChartNormalization

variable {R B : Type*} [CommRing R] [CommRing B]

/-- Homogeneous binary substitution commutes with changing the coefficient ring. -/
theorem map_substitute (ψ : R →+* B) (u v p : R[X]) {r : ℕ} (hp : p.natDegree ≤ r) :
    (substitute r u v p).map ψ = substitute r (u.map ψ) (v.map ψ) (p.map ψ) := by
  apply Polynomial.induction_with_natDegree_le (fun q => (substitute r u v q).map ψ =
    substitute r (u.map ψ) (v.map ψ) (q.map ψ)) r (by simp) _ _ p hp
  · intro j c _ hj
    simp only [substitute_term _ _ _ hj,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,
      Polynomial.map_X]
  · intro q q' _ _ h1 h2
    simp only [map_add,Polynomial.map_add,h1,h2]

variable {K : Type*} [Field K]

/-- Affine translation in the pencil parameter. Its inverse is translation by the negative. -/
noncomputable def shift (a : K) : K[X] →+* K[X] := compRingHom (X+C a)

theorem eval_shift (a t : K) (p : K[X]) : (shift a p).eval t = p.eval (t+a) := by
  simp [shift,coe_compRingHom_apply,eval_comp]

theorem shift_degree (a : K) (p : K[X]) : (shift a p).natDegree=p.natDegree := by
  simp [shift,coe_compRingHom_apply,natDegree_comp]

theorem shift_neg (a : K) (p : K[X]) : shift (-a) (shift a p) = p := by
  simp [shift,coe_compRingHom_apply,comp_assoc]

theorem shift_injective (a : K) : Function.Injective (shift a) :=
  fun p q h => by simpa only [shift_neg] using congrArg (shift (-a)) h

/-- Translate a finite set of parameters off zero without losing their original
labels. The old parameter corresponding to the new t is t+a. -/
theorem translate_parameters [Infinite K] [DecidableEq K] (S : Finset K) :
    ∃ a ∉ S, ∃ S' : Finset K, S'.card=S.card ∧ 0 ∉ S' ∧ ∀ t : K, t ∈ S' ↔ t+a ∈ S := by
  obtain ⟨a,ha⟩ := Infinite.exists_notMem_finset S
  let ψ : K ↪ K := ⟨fun t => t-a, fun s t h => sub_left_injective h⟩
  refine ⟨a,ha,S.map ψ,card_map _,?_,?_⟩
  · intro h
    obtain ⟨t,ht,h⟩ := mem_map.mp h
    change t-a=0 at h
    exact ha (sub_eq_zero.mp h ▸ ht)
  · intro t
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := mem_map.mp h
      change u-a+a ∈ S
      simpa using hu
    · intro h
      exact mem_map.mpr ⟨t+a,h,by change t+a-a=t; simp⟩

/-- Coordinate-normalized locator, with its parameter shifted first. -/
noncomputable def locator (a x z : K) (r : ℕ) (p : K[X][X]) : K[X][X] :=
  substitute r (C (C z)*X-C (C x)) (X-1) (p.map (shift a))

theorem shift_specialize (a t : K) (p : K[X][X]) :
    (p.map (shift a)).map (evalRingHom t)=p.map (evalRingHom (t+a)) := by
  have h : (evalRingHom t).comp (shift a) = evalRingHom (t+a) := RingHom.ext fun f => eval_shift a t f
  rw [Polynomial.map_map,h]

theorem locator_specialize (a x z t : K) (p : K[X][X]) {r : ℕ} (hp : p.natDegree ≤ r) :
    (locator a x z r p).map (evalRingHom t) =
      substitute r (C z*X-C x) (X-1) (p.map (evalRingHom (t+a))) := by
  rw [locator,map_substitute _ _ _ _ (natDegree_map_le.trans hp),shift_specialize]
  simp [Polynomial.map_mul,Polynomial.map_sub]

theorem locator_no_zero_fiber (a x z : K) (hxz : x ≠ z) (p : K[X][X]) {r : ℕ}
    (hp : p.natDegree ≤ r) (hf : ∀ t, p.map (evalRingHom t) ≠ 0) :
    ∀ t, (locator a x z r p).map (evalRingHom t) ≠ 0 := by
  intro t h
  rw [locator_specialize _ _ _ _ _ hp] at h
  have hh := congrArg (substitute r (X-C x) (X-C z)) h
  rw [inverse_substitute x z hxz _ (natDegree_map_le.trans hp),map_zero] at hh
  exact (smul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hxz.symm)) (hf _)) hh

/-- Specialization on the coordinate side commutes with the parameter shift. -/
theorem shift_site (a y : K) (p : K[X][X]) :
    (p.map (shift a)).eval (C y) = shift a (p.eval (C y)) := by
  have h : shift a (C y) = C y := by simp [shift,coe_compRingHom_apply]
  rw [←h,eval_map_apply,h]

/-- The normalized locator retains exact coordinate degree r and a nonzero
constant coefficient. Both command the same parameter degree as before. -/
theorem locator_endpoints (a x z : K) (p : K[X][X]) {r l : ℕ} (hl : 0<l)
    (hp : p.natDegree ≤ r) (hx : (p.eval (C x)).natDegree = l) (hz : (p.eval (C z)).natDegree = l) :
    let g := locator a x z r p
    g.natDegree=r ∧ (g.coeff 0).natDegree=l ∧ (g.coeff r).natDegree=l ∧ g.coeff 0≠0 := by
  let g := locator a x z r p
  have hg : g.natDegree ≤ r := by
    apply substitute_degree _ _ _ _ _ (natDegree_map_le.trans hp) <;> compute_degree
  have h₁ : g.coeff r=shift a (p.eval (C z)) := by
    rw [show g=locator a x z r p from rfl,locator,top_coefficient _ _ _ (natDegree_map_le.trans hp),shift_site]
  have h₀ : g.coeff 0=(-1)^r*shift a (p.eval (C x)) := by
    rw [show g=locator a x z r p from rfl,locator,bottom_coefficient _ _ _ (natDegree_map_le.trans hp),shift_site]
  have dz : (g.coeff r).natDegree=l := by rw [h₁,shift_degree,hz]
  have hn : g.coeff r ≠ 0 := fun he => by rw [he,natDegree_zero] at dz; omega
  have dx : (g.coeff 0).natDegree=l := by
    rw [h₀,show ((-1:K[X])^r)=C ((-1:K)^r) by simp,natDegree_C_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
      shift_degree,hx]
  exact ⟨le_antisymm hg (le_natDegree_of_ne_zero hn),dx,dz,fun he => by rw [he,natDegree_zero] at dx; omega⟩

/-- A primitive coefficient array remains nonzero after ordinary coefficient specialization. -/
theorem primitive_form {s : ℕ} (v : Fin (s+1) → K[X]) (hf : ∀ t, (family v).eval (C t) ≠ 0) :
    ∀ t, (form v).map (evalRingHom t) ≠ 0 := by
  intro t h
  apply hf t
  have he : (family v).eval (C t) = (form v).map (evalRingHom t) := by
    rw [form_specialize]
    ext j
    by_cases hj : j<s+1
    · exact (coeff_family v t ⟨j,hj⟩).trans (coeff_form (fun i : Fin (s+1) => (v i).eval t) ⟨j,hj⟩).symm
    · have hp : ((family v).eval (C t)).natDegree ≤ s := by
        simp only [family,eval_finsetSum,eval_mul,eval_C,eval_map,eval₂_hom]
        apply natDegree_sum_le_of_forall_le
        intro i _
        exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le i.val).trans (by have := i.isLt; omega))
      rw [coeff_eq_zero_of_natDegree_lt (by omega),coeff_eq_zero_of_natDegree_lt (by
        have hdeg := form_degree (fun i : Fin (s+1) => (v i).eval t); omega)]
  rwa [he]

/-- The exact coefficient array before and after swapping the variables agrees. -/
theorem coeff_coeff_family {s : ℕ} (v : Fin (s+1) → K[X]) (i : Fin (s+1)) (j : ℕ) :
    ((family v).coeff j).coeff i.val = (v i).coeff j := by
  classical
  simp only [family,finsetSum_coeff,coeff_mul_C,coeff_map,coeff_C_mul_X_pow]
  rw [sum_eq_single i]
  · simp
  · intro k _ h
    simp [show i.val ≠ k.val from fun he => h (Fin.ext he.symm)]
  · simp

theorem coefficient_height {s : ℕ} (v : Fin (s+1) → K[X]) (i : Fin (s+1)) :
    (v i).natDegree ≤ (family v).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [←coeff_coeff_family v i j,coeff_eq_zero_of_natDegree_lt hj,coeff_zero]

theorem map_form {s : ℕ} (v : Fin (s+1) → R) (ψ : R →+* B) :
    (form v).map ψ=form (fun i => ψ (v i)) := by
  simp [form,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow]

/-- Every normalized coordinate coefficient has parameter degree bounded by the
original height. Only constant-field binary forms enter the coordinate change. -/
theorem locator_height {s : ℕ} (v : Fin (s+1) → K[X]) (a x z : K) (j : ℕ) :
    ((locator a x z s (form v)).coeff j).natDegree ≤ (family v).natDegree := by
  classical
  rw [locator,map_form,form,map_sum,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [substitute_term _ _ _ (by have := i.isLt; omega),mul_assoc,coeff_C_mul]
  let P : K[X] := (C z*X-C x)^i.val*(X-1)^(s-i.val)
  have h : (C (C z)*X-C (C x))^i.val*(X-1)^(s-i.val)=P.map (C : K →+* K[X]) := by
    simp [P,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_pow]
  rw [h,coeff_map,mul_comm]
  exact (natDegree_C_mul_le _ _).trans (by rw [shift_degree]; exact coefficient_height v i)

/-- Polynomial matrix kernels and their kernels in smaller coordinate degrees
are unchanged by translating the scalar parameter. -/
theorem shift_kernel_iff (m : ℕ → K[X]) {d s : ℕ} (a : K) (v : Fin (s+1) → K[X]) :
    catalecticant (fun j => shift a (m j)) d s *ᵥ (fun i => shift a (v i))=0 ↔
      catalecticant m d s *ᵥ v=0 := by
  have hh (j : Fin (d-s+1)) : (catalecticant (fun k => shift a (m k)) d s *ᵥ
      (fun i => shift a (v i))) j = shift a ((catalecticant m d s *ᵥ v) j) := by
    simp [catalecticant,Matrix.mulVec,dotProduct]
  constructor
  · intro h
    funext j
    apply shift_injective a
    simpa only [←hh,map_zero,Pi.zero_apply] using congrFun h j
  · intro h
    funext j
    simp only [hh,h,Pi.zero_apply,map_zero]

noncomputable def normalizedFunctional (m : ℕ → K[X]) (a x z : K) (d : ℕ) :
    K[X][X] →ₗ[K[X]] K[X] :=
  (functional (fun j => shift a (m j))).comp (substitute d (X-C (C x)) (X-C (C z)))

/-- The normalized functional is the dual coordinate transformation of the
same polynomial locator, including its scalar translation. -/
theorem normalized_apolar (m : ℕ → K[X]) {d s : ℕ} (hs : s ≤ d) (v : Fin (s+1) → K[X])
    (hker : catalecticant m d s *ᵥ v=0) (a x z : K) (hxz : x ≠ z) :
    ApolarThrough (normalizedFunctional m a x z d) (locator a x z s (form v)) (d-s) := by
  have hpre : ApolarThrough (functional (fun j => shift a (m j))) (form (fun i => shift a (v i))) (d-s) := by
    apply (equations_iff_apolar _ _).mp
    intro j hj
    exact congrFun ((shift_kernel_iff m a v).mpr hker) ⟨j,by omega⟩
  have he := (apolar_substitute_iff (C x) (C z) (fun h => hxz (C_injective h)) _
    _ (s:=d-s) (form_degree (fun i => shift a (v i)))).mpr hpre
  simpa only [normalizedFunctional,locator,map_form,Nat.add_sub_of_le hs] using he

theorem normalized_affine (m : ℕ → K[X]) {d : ℕ} (hm : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (a x z : K) (j : ℕ) (hj : j ≤ d) :
    ((normalizedFunctional m a x z d) (X^j)).natDegree ≤ 1 :=
  functional_chart_degree _ (fun i hi => by rw [shift_degree]; exact hm i hi) x z j hj

/-- The coordinate evaluation map after normalization. -/
def site (x z y : K) := (y-x)/(y-z)

theorem site_unit (x z : K) (H : Finset K) (hx : x ∉ H) (hz : z ∉ H)
    {y : K} (hy : y ∈ H) : IsUnit (site x z y) :=
  isUnit_iff_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr fun h => hx (h ▸ hy))
    (sub_ne_zero.mpr fun h => hz (h ▸ hy)))

/-- Sparse original fibers have the same number of sites in the normalized
chart, carry transformed weights, and preserve all bounded polynomial tests. -/
theorem normalized_atoms [DecidableEq K] (m : ℕ → K[X]) (a x z t : K) (hxz : x ≠ z)
    (E : Finset K) (hz : z ∉ E) (w : K → K) {d : ℕ}
    (ha : ∀ j ≤ d, (m j).eval (t+a)=∑ y ∈ E,w y*y^j) :
    let E' := E.image (site x z)
    E'.card=E.card ∧ ∃ w' : K → K, ∀ p : K[X], p.natDegree ≤ d →
      ((normalizedFunctional m a x z d) (p.map C)).eval t = weighted E' (RingHom.id K) w' p := by
  classical
  obtain ⟨hcard,hrep⟩ := error_measure_substitute x z hxz E hz w d
  let inv (u : K) := (z*u-x)/(u-1)
  refine ⟨hcard,fun u => w (inv u)*(inv u-z)^d,?_⟩
  intro p hp
  let q := substitute d (X-C x) (X-C z) p
  have hq : q.natDegree ≤ d := substitute_degree _ _ _ (by simp) (by simp) hp
  have hh := atoms_apply (fun j => shift a (m j)) t E w (fun j hj => by rw [eval_shift]; exact ha j hj) q hq
  have hq' := map_substitute (C : K →+* K[X]) (X-C x) (X-C z) p hp
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C] at hq'
  rw [normalizedFunctional,LinearMap.comp_apply,←hq']
  exact hh.trans (hrep p hp)

/-- Preceding rectangular injectivity persists over the parameter-polynomial ring
after both coordinate changes. -/
theorem normalized_minimal (m : ℕ → K[X]) {d b : ℕ} (hb : b ≤ d) (a x z : K) (hxz : x ≠ z)
    (hi : ∀ v, catalecticant m d b *ᵥ v=0 → v=0) :
    ∀ q : K[X][X], q.natDegree ≤ b → ApolarThrough (normalizedFunctional m a x z d) q (d-b) → q=0 := by
  let m' (j : ℕ) := shift a (m j)
  have hinj (v : Fin (b+1) → K[X]) (hv : catalecticant m' d b *ᵥ v=0) : v=0 := by
    have hh := (shift_kernel_iff m' (-a) v).mpr hv
    simp only [m',shift_neg] at hh
    have hrow := hi _ hh
    funext i
    apply shift_injective (-a)
    simpa only [Pi.zero_apply,map_zero] using congrFun hrow i
  have hpre (p : K[X][X]) (hp : p.natDegree ≤ b) (h : ApolarThrough (functional m') p (d-b)) : p=0 := by
    let v (i : Fin (b+1)) := p.coeff i.val
    have hh : form v=p := form_coeff p hp
    have he := (equations_iff_apolar m' v).mpr (by simpa only [hh] using h)
    have hz' := hinj v (funext fun j => he j.val (by have := j.isLt; omega))
    rw [←hh,hz']; simp [form]
  have hh := (trivial_kernel_iff (C x) (C z) (fun h => hxz (C_injective h))
    (functional m') b (d-b)).mp hpre
  simpa only [normalizedFunctional,m',Nat.add_sub_of_le hb] using hh

/-- The reciprocal chart on a set of unit sites is sparse on the inverses of
the same sites, with weights multiplied by the binary degree power. -/
theorem inverse_atoms [DecidableEq K] (E : Finset K) (hz : 0 ∉ E) (w : K → K)
    {d : ℕ} (p : K[X]) (hp : p.natDegree ≤ d) :
    weighted E (RingHom.id K) w (reflect d p) = weighted (E.image Inv.inv) (RingHom.id K)
      (fun y => w y⁻¹*(y⁻¹)^d) p := by
  classical
  simp only [weighted_apply,RingHom.id_apply]
  rw [sum_image (inv_injective.injOn)]
  apply sum_congr rfl
  intro y hy
  have hn : y≠0 := fun h => hz (h ▸ hy)
  let _ := invertibleOfNonzero hn
  have hr := eval₂_reflect_mul_pow (RingHom.id K) y d (reflect d p)
    ((natDegree_reflect_le (N := d) (p := p)).trans (max_le le_rfl hp))
  simp only [reflect_reflect,eval₂_id,invOf_eq_inv] at hr
  simp only [inv_inv]
  rw [←hr]
  ring

#print axioms normalized_minimal
#print axioms inverse_atoms
#print axioms normalized_atoms
#print axioms normalized_apolar
#print axioms locator_height
#print axioms locator_endpoints
#print axioms locator_no_zero_fiber
#print axioms primitive_form

end ProximityGap.ApolarChartNormalization
