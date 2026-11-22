/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.GroupTheory.Perm.Cycle.Type
import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity
import ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-! # Dyadic covariance of four eighth-rate heads

The local direction count uses the actual unordered directions determined by a
four-point multiset. A common primitive scale and the degrees of the triangles
give constraints on lifts from the half-size and quarter-size quotients.
-/
set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.EighthDyadicHeadDirections

/-- Parallelism of the third side of a triangle identifies the scales on the
two incident sides, over the rational function field as well as a base field. -/
theorem triangle_scale {K : Type*} [Field K] {a b c d l m : K}
    (indep : a*d-c*b ≠ 0)
    (side : (a-c)*(l*b-m*d)-(b-d)*(l*a-m*c)=0) : l=m := by
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp _).resolve_right indep
  linear_combination side

/-- Two primitive polynomial tuples proportional over the fraction field have
a unit polynomial scale. The coefficients witness their respective unit ideals. -/
theorem primitive_scale {K I : Type*} [Field K] [Fintype I]
    (U V A B : I → K[X]) (r s : K[X]) (hr : r ≠ 0)
    (primU : ∑ i, A i * U i = 1) (primV : ∑ i, B i * V i = 1)
    (rel : ∀ i, r * V i = s * U i) :
    ∃ c : K[X], IsUnit c ∧ ∀ i, V i = c * U i := by
  let c := ∑ i, A i * V i
  let e := ∑ i, B i * U i
  have hc : r*c=s := by
    dsimp [c]
    rw [mul_sum, ← mul_one s, ← primU, mul_sum]
    apply sum_congr rfl
    intro i _
    linear_combination A i * rel i
  have he : s*e=r := by
    dsimp [e]
    rw [mul_sum, ← mul_one r, ← primV, mul_sum]
    apply sum_congr rfl
    intro i _
    linear_combination - B i * rel i
  refine ⟨c, isUnit_iff_exists_inv.mpr ⟨e, mul_left_cancel₀ hr ?_⟩, fun i => mul_left_cancel₀ hr ?_⟩
  · rw [← mul_assoc, hc, he, mul_one]
  · rw [← mul_assoc, hc, rel]

/-- A nonzero coefficient of an eigenpolynomial for input rotation has the prescribed character. -/
theorem coefficient_character {K : Type*} [Field K] (P : K[X]) (z a : K)
    (covariant : P.comp (C z * X) = C a * P) (i : ℕ) (hi : P.coeff i ≠ 0) :
    z^i=a := by
  have h := congrArg (fun Q : K[X] => Q.coeff i) covariant
  simp only [comp_C_mul_X_coeff, coeff_C_mul] at h
  exact mul_right_cancel₀ hi (by simpa [mul_comm] using h)

/-- Factoring out the two row weights leaves a triangle on the smaller cyclic quotient. -/
theorem quotient_triangle {K : Type*} [Field K] (A B C' D h : K[X]) (l j : ℕ) :
    (h * expand K l A) * (h * X^j * expand K l D) -
      (h * expand K l C') * (h * X^j * expand K l B) =
      h^2 * X^j * expand K l (A*D-C'*B) := by
  simp only [map_sub,map_mul]
  ring

/-- Projective fresh directions from a center to the distinct other values. -/
def star {V Z : Type*} [DecidableEq V] [DecidableEq Z] (P : Finset V)
    (dir : V → V → Z) (u : V) : Finset Z := (P.erase u).image (dir u)

/-- For two homothetic configurations with four heads, the union of the two
stars loses a direction whenever their centers are different. Multiplicities
one and two give the indicated combined bound for either choice of centers. -/
theorem two_stars {V Z : Type*} [DecidableEq V] [DecidableEq Z]
    (P : Finset V) (w : V → ℕ) (dir : V → V → Z) (symm : ∀ u v, dir u v = dir v u)
    (total : ∑ i ∈ P, w i = 4) (pos : ∀ i ∈ P, 1 ≤ w i)
    {u v : V} (hu : u ∈ P) (hv : v ∈ P) (wu : w u ≤ 2) (wv : w v ≤ 2) :
    2*((star P dir u) ∪ (star P dir v)).card + 3*(w u+w v) ≤ 16 := by
  have lower (S : Finset V) (hs : S ⊆ P) : S.card ≤ ∑ i ∈ S, w i := by
    simpa using sum_le_sum (s := S) (f := fun _ => 1) (g := w) (fun i hi => pos i (hs hi))
  have cap (j : V) : (star P dir j).card ≤ (P.erase j).card := card_image_le
  have sizeU := sum_erase_add P w hu
  have cardU := card_erase_add_one hu
  have one := lower (P.erase u) (erase_subset ..)
  have cu := cap u
  by_cases h : u=v
  · subst v
    rw [union_self]
    omega
  have vU : v ∈ P.erase u := mem_erase.mpr ⟨Ne.symm h,hv⟩
  have sizeUV := sum_erase_add (P.erase u) w vU
  have cardUV := card_erase_add_one vU
  have two := lower ((P.erase u).erase v) ((erase_subset ..).trans (erase_subset ..))
  have shared : dir u v ∈ star P dir u ∩ star P dir v := by
    apply mem_inter.mpr
    refine ⟨mem_image.mpr ⟨v,vU,rfl⟩,?_⟩
    exact mem_image.mpr ⟨u,mem_erase.mpr ⟨h,hu⟩,symm v u⟩
  have nonempty := card_pos.mpr ⟨_,shared⟩
  have unionCount := card_union_add_card_inter (star P dir u) (star P dir v)
  have cv := cap v
  have cardV := card_erase_add_one hv
  have pu := pos u hu
  have pv := pos v hv
  omega

/-- A family of regular antipodal pairs with at most twelve exceptional pairs
has the following total number of occupied projective directions. -/
theorem antipodal_mass {J : Type*} [Fintype J] [DecidableEq J]
    (bad : Finset J) (M W : J → ℕ) (count : Fintype.card J = 536870912)
    (rich : 1610612728 ≤ ∑ i, W i)
    (small : bad.card ≤ 12)
    (localBound : ∀ i, 2*M i+3*W i ≤ 16 + (if i ∈ bad then 24 else 0)) :
    (∑ i, M i) ≤ 1879048348 := by
  have t := sum_le_sum (s := (univ : Finset J)) (fun i _ => localBound i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, count, smul_eq_mul] at t
  have hb : (∑ i, if i ∈ bad then 24 else 0) = bad.card * 24 := by simp
  omega

/-- Uncovered sites and sites covered by three or four heads cost incidence
slack in the four triangle determinants. -/
theorem exceptional_sites {s r x₀ x₂ x₃ x₄ : ℕ}
    (slack : s ≤ 4) (locator : r ≤ s)
    (inc : x₂+2*x₃+3*x₄+s=536870908+x₀)
    (triangles : 2*x₂+5*x₃+8*x₄ ≤ 1073741816) :
    r+x₀+x₃+x₄ ≤ 12 := by omega

/-- For a nonscalar quarter turn, the two quotient row degrees leave too few
triangle roots. This includes all three nontrivial row characters. -/
theorem quarter_turn_impossible {r j a b : ℕ} (positive : 1 ≤ j) (character : j < 4)
    (ha : 4*a+r ≤ 134217727) (hb : 4*b+j+r ≤ 134217727)
    (rich : 536870904 ≤ 3*r+8*(a+b)) : False := by omega

/-- For a nonscalar antipode the common locator is constant, both quotient
row degrees are maximal, and all four units of overlap slack are used. -/
theorem antipode_forces_quotient {r a b s : ℕ} (slack : s ≤ 4)
    (ha : 2*a+r ≤ 134217727) (hb : 2*b+1+r ≤ 134217727)
    (rich : 536870908 ≤ 3*r+4*(a+b)+s) :
    r=0 ∧ a=67108863 ∧ b=67108863 ∧ s=4 := by omega

/-- Off the common locator and the origin, only the quotient triangle
contributes to the root multiplicity on the evaluation set. -/
theorem quotient_root_budget {K : Type*} [Field K] (S : Finset K)
    (h P : K[X]) (l j : ℕ) (hP : h^2*X^j*expand K l P ≠ 0)
    (regular : ∀ x ∈ S, h.eval x ≠ 0 ∧ x ≠ 0) :
    ∑ x ∈ S, (h^2*X^j*expand K l P).rootMultiplicity x ≤ l*P.natDegree := by
  have eq (x : K) (hx : x ∈ S) :
      (h^2*X^j*expand K l P).rootMultiplicity x = (expand K l P).rootMultiplicity x := by
    obtain ⟨nh,nx⟩ := regular x hx
    have nroot : ¬ (h^2*X^j).IsRoot x := by
      simpa [IsRoot] using mul_ne_zero (pow_ne_zero 2 nh) (pow_ne_zero j nx)
    rw [rootMultiplicity_mul hP, rootMultiplicity_eq_zero nroot, zero_add]
  rw [sum_congr rfl eq]
  simpa [natDegree_expand, Nat.mul_comm] using
    (Polynomial.sum_rootMultiplicity_le_natDegree (W := expand K l P) S)

open HalfPredecessorRateQuarterDeterminantMultiplicity

private def bit (b : Fin 4 → Bool) (i : Fin 4) : ℕ := if b i then 1 else 0

/-- Increasing triples of four labeled vertices. -/
def triangleIndices : Fin 4 → Fin 3 → Fin 4 :=
  ![![0,1,2],![0,1,3],![0,2,3],![1,2,3]]

private def charge (b : Fin 4 → Bool) (i : Fin 4) :=
  bit b (triangleIndices i 0)+bit b (triangleIndices i 1)+bit b (triangleIndices i 2)-1

private theorem weights : ∀ b : Fin 4 → Bool,
    2*(∑ i, bit b i) ≤ 2+∑ i, charge b i := by decide

open scoped Classical in
/-- Total incidence of actual cores when the four triangle determinants factor
through one cyclic quotient. The common locator can consume three excess core
incidences per root, independently of its multiplicities. -/
theorem quotient_core_incidence {K : Type} [Field K] [DecidableEq K]
    (S : Finset K) (zeroFree : ∀ x ∈ S, x ≠ 0) (u v : K → K)
    (L : Fin 4 → K[X] × K[X]) (h : K[X]) (P : Fin 4 → K[X])
    (l j b : ℕ) (hn : h ≠ 0) (hd : ∀ i, (P i).natDegree ≤ b)
    (factor : ∀ i, threeLineDeterminant (L (triangleIndices i 0)) (L (triangleIndices i 1)) (L (triangleIndices i 2))
      = h^2*X^j*expand K l (P i))
    (nz : ∀ i, h^2*X^j*expand K l (P i) ≠ 0) :
    (∑ x ∈ S, (univ.filter (fun i => AgreesAt (u x) (v x) x (L i))).card) ≤
      S.card+3*h.natDegree+2*(l*b) := by
  classical
  let Z := S.filter (fun x => h.eval x = 0)
  let T := S \ Z
  let B (x : K) (i : Fin 4) := decide (AgreesAt (u x) (v x) x (L i))
  let W (x : K) := (univ.filter (fun i => AgreesAt (u x) (v x) x (L i))).card
  have zsub : Z ⊆ S := filter_subset ..
  have zcard : Z.card ≤ h.natDegree := by
    apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hn (Function.injective_id.injOn)
    intro x hx
    exact (mem_filter.mp hx).2
  have reg (x : K) (hx : x ∈ T) : h.eval x ≠ 0 ∧ x ≠ 0 := by
    obtain ⟨hs,hnz⟩ := mem_sdiff.mp hx
    exact ⟨fun he => hnz (mem_filter.mpr ⟨hs,he⟩), zeroFree x hs⟩
  have wm (x : K) : (∑ i, bit (B x) i) = W x := by simp [W,B,bit]
  have bound (i : Fin 4) : ∑ x ∈ T, charge (B x) i ≤ l*b := by
    apply le_trans (sum_le_sum (g := fun x => (h^2*X^j*expand K l (P i)).rootMultiplicity x) ?_)
    · exact (quotient_root_budget _ _ _ _ _ (nz i) reg).trans (Nat.mul_le_mul_left l (hd i))
    · intro x _
      have ntr := (factor i) ▸ nz i
      have loc := coreCount_sub_one_le_rootMultiplicity (u0 := u x) (u1 := v x) (x := x) ntr
      rw [factor i] at loc
      simpa [coreCount,charge,bit,B] using loc
  have all : (∑ x ∈ T, ∑ i, charge (B x) i) ≤ 4*(l*b) := by
    rw [sum_comm]
    simpa [Nat.mul_comm] using sum_le_sum (s := univ) (fun i _ => bound i)
  have sites := sum_le_sum (s := T) (fun x _ => weights (B x))
  simp_rw [wm] at sites
  rw [← mul_sum,sum_add_distrib] at sites
  simp only [sum_const,smul_eq_mul] at sites
  have onZ : (∑ x ∈ Z, W x) ≤ Z.card*4 := by
    simpa using sum_le_sum (s := Z) (g := fun _ => 4) (fun x _ => show W x ≤ 4 from
      (card_le_univ _).trans_eq (Fintype.card_fin 4))
  have split := sum_sdiff zsub (f := W)
  have sizes := card_sdiff_add_card_eq_card zsub
  change (∑ x ∈ S, W x) ≤ _
  dsimp only [T] at sites all
  omega

/-- A nonsymmetric side can satisfy its prescribed comparison on at most twice
the head degree, even when the comparison set includes vanishing sides. -/
theorem matched_sites {K J : Type*} [Field K] (dom : J ↪ K) (S : Finset J)
    (A B U V : K[X]) (d : ℕ)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hU : U.natDegree ≤ d) (hV : V.natDegree ≤ d)
    (different : A*V-B*U ≠ 0)
    (agree : ∀ i ∈ S, A.eval (dom i)*V.eval (dom i)=B.eval (dom i)*U.eval (dom i)) :
    S.card ≤ 2*d := by
  have roots : S.card ≤ (A*V-B*U).natDegree := by
    apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero different dom.injective.injOn
    intro i hi
    simp [agree i hi]
  exact roots.trans ((natDegree_sub_le ..).trans (max_le
    (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega))))

/-- Twelve applications remove every possible fixed relabelling of four heads. -/
theorem relabelling_twelfth (p : Equiv.Perm (Fin 4)) : p^12=1 := by
  classical
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
  apply Multiset.lcm_dvd.mpr
  intro m hm
  have lo := Equiv.Perm.two_le_of_mem_cycleType hm
  have hi := (Equiv.Perm.le_card_support_of_mem_cycleType hm).trans (card_le_univ _)
  simp only [Fintype.card_fin] at hi
  interval_cases m <;> decide

#print axioms quotient_root_budget
#print axioms quotient_core_incidence
#print axioms matched_sites
#print axioms relabelling_twelfth
#print axioms triangle_scale
#print axioms primitive_scale
#print axioms coefficient_character
#print axioms quotient_triangle
#print axioms two_stars
#print axioms antipodal_mass
#print axioms exceptional_sites
#print axioms quarter_turn_impossible
#print axioms antipode_forces_quotient
end ArkLib.ProximityGap.Frontier.EighthDyadicHeadDirections
