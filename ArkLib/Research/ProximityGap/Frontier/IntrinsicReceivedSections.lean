/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.JetMultiplierGraph

/-! # Intrinsic interpolation on an actual polynomial section space

The degree in scalar and value controls all polynomial jet entries uniformly,
including after translation by the affine received lines.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Module
open scoped BigOperators Matrix
namespace ArkLib.ProximityGap.Frontier.IntrinsicReceivedSections

open JetMultiplierGraph TruncatedJetMultipliers PolynomialJetConstraintSpace

variable {R : Type*} [CommRing R] {K : Type} [Field K]

private theorem coeff_shift_monomial (a w A : R) (i l v t : ℕ) :
    (((shift (monomial i (monomial l A)) a w).coeff v).coeff t) =
      ((i.choose v : R) * ((l.choose t : R) * A * a^(l-t))) * w^(i-v) := by
  rw [shift,coeff_map]
  change ((((monomial i (monomial l A)).taylor (C w)).coeff v).taylor a).coeff t = _
  rw [taylor_coeff (C w) _ v,hasseDeriv_monomial,eval_monomial,← C_pow,← C_eq_natCast,
    C_mul_monomial,monomial_mul_C,taylor_coeff,hasseDeriv_monomial,eval_monomial]
  ring

/-- The source polynomial has total scalar-plus-value degree at most m. -/
def ScalarValueBound (F : K[X][X][X]) (m : ℕ) : Prop :=
  ∀ i l, (F.coeff i).coeff l ≠ 0 → ((F.coeff i).coeff l).natDegree + i ≤ m

private theorem degree_shift_monomial (a : K) (w A : K[X]) (i l v t : ℕ)
    (hw : w.natDegree ≤ 1) :
    (((shift (monomial i (monomial l A)) (C a) w).coeff v).coeff t).natDegree ≤
      A.natDegree+i := by
  rw [coeff_shift_monomial]
  have h0 (p : K[X]) (c : K) : (C c*p).natDegree ≤ p.natDegree :=
    natDegree_mul_le.trans (by simp)
  have hw' : (w^(i-v)).natDegree ≤ i := by
    have := (natDegree_pow_le (p := w) (n := i-v)).trans (Nat.mul_le_mul_left _ hw)
    simpa using this.trans (by simp)
  have hw2 : (((i.choose v : K[X]) * ((l.choose t : K[X]) * A * (C a)^(l-t)))).natDegree ≤
      A.natDegree := by
    rw [← C_pow,← C_eq_natCast,← C_eq_natCast]
    calc
      _ ≤ _ := h0 _ _
      _ ≤ _ := natDegree_mul_le
      _ ≤ _ := by simpa using h0 A (l.choose t)
  exact natDegree_mul_le.trans (Nat.add_le_add hw2 hw')

/-- Taylor translating in the coordinate at a constant and in value at an affine
scalar polynomial cannot increase the original scalar-plus-value degree. -/
theorem translated_height (F : K[X][X][X]) (m : ℕ) (hf : ScalarValueBound F m)
    (a : K) (w : K[X]) (hw : w.natDegree ≤ 1) (v t : ℕ) :
    (((shift F (C a) w).coeff v).coeff t).natDegree ≤ m := by
  classical
  have hdecomp : F = ∑ i ∈ F.support, ∑ l ∈ (F.coeff i).support,
      monomial i (monomial l ((F.coeff i).coeff l)) := by
    conv_lhs => rw [← sum_monomial_eq F,sum_def]
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_sum (monomial i)]
    congr 1
    exact (sum_monomial_eq (F.coeff i)).symm
  rw [hdecomp]
  simp only [shift,map_sum,Polynomial.map_sum,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro l hl
  exact (degree_shift_monomial a w ((F.coeff i).coeff l) i l v t hw).trans
      (hf i l (Polynomial.mem_support_iff.mp hl))

/-- Actual received scalar line. -/
def received (u v : K) : K[X] := C u + Polynomial.X*C v

theorem received_degree (u v : K) : (received u v).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · exact natDegree_mul_le.trans (by simp)

/-- Every actual monomial-multiplier column satisfies the same uniform scalar height. -/
theorem translated_column_height (F : K[X][X][X]) (m : ℕ) (hf : ScalarValueBound F m)
    (a u v : K) {μ ν : ℕ} (i : JetIdx μ) (c : JetIdx ν) :
    (columns μ ν (shift F (C a) (received u v)) i c).natDegree ≤ m := by
  unfold columns jet monomialMultiple
  rw [coeff_mul_X_pow']
  split
  · rw [coeff_mul_C,coeff_mul_X_pow']
    split
    · exact translated_height F m hf a _ (received_degree u v) _ _
    · simp
  · simp

/-- Canonical generic multiplicity over the scalar function field. -/
def receivedOrder (F : K[X][X][X]) (a u v : K) : ℕ :=
  CanonicalQuarticSiteOrder.siteOrder (mapPlane (algebraMap K[X] (RatFunc K)) F)
    (RatFunc.C a) (C ((algebraMap K[X] (RatFunc K)) (received u v)))

/-- The primitive generic equation determines an actual polynomial leading
coefficient for the triangular multiplier columns before specialization. -/
theorem exists_polynomial_leader (F : K[X][X][X])
    (hf : (mapPlane (algebraMap K[X] (RatFunc K)) F).IsPrimitive) (a u v : K) :
    ∃ j, Leader (shift F (C a) (received u v)) (receivedOrder F a u v) j := by
  let φ := algebraMap K[X] (RatFunc K)
  let G := mapPlane φ F
  let w := received u v
  let r := receivedOrder F a u v
  obtain ⟨j,hj⟩ := exists_leader_at_site G hf (RatFunc.C a) (C (φ w))
  have hmap : mapPlane φ (shift F (C a) w) =
      translate G (RatFunc.C a) (C (φ w)) := by
    rw [mapPlane_shift]
    rfl
  have hc (i t : ℕ) : φ (((shift F (C a) w).coeff i).coeff t) =
      (((translate G (RatFunc.C a) (C (φ w))).coeff i).coeff t) := by
    rw [← hmap]
    simp only [mapPlane,coeff_map,coe_mapRingHom]
  refine ⟨j,hj.value_le,?_,?_⟩
  · intro hz
    apply hj.nonzero
    rw [← hc]
    exact (congrArg φ hz).trans (map_zero _)
  · intro i t ht
    apply (RatFunc.algebraMap_injective K)
    rw [map_zero,hc]
    exact hj.lower i t ht

variable {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The genuine linear observation of the section at all received sites, with
the scalar degree of every observed mixed coefficient proved from support. -/
def observation {I : Type} {μ s : ℕ} (site u v : I → K)
    (surface : E →ₗ[K] K[X][X][X]) (hs : ∀ e, ScalarValueBound (surface e) s) :
    E →ₗ[K] (I → JetIdx μ → degreeLT K (s+1)) where
  toFun e x i := ⟨jet (shift (surface e) (C (site x)) (received (u x) (v x))) i,
    mem_degreeLT.mpr (degree_le_natDegree.trans_lt <| by
      exact_mod_cast Nat.lt_succ_of_le (translated_height (surface e) s (hs e) (site x) _
        (received_degree (u x) (v x)) i.2.val (i.1.val-i.2.val)))⟩
  map_add' e f := by
    funext x i
    apply Subtype.ext
    change jet (shift (surface (e+f)) _ _) i = jet (shift (surface e) _ _) i +
      jet (shift (surface f) _ _) i
    simp only [map_add,jet,shift,Polynomial.map_add,coeff_add]
  map_smul' b e := by
    funext x i
    apply Subtype.ext
    change jet (shift (surface (b • e)) _ _) i = b • jet (shift (surface e) _ _) i
    rw [map_smul,Algebra.smul_def b (surface e)]
    simp only [jet,shift,taylor_apply,mul_comp,Polynomial.map_mul,Polynomial.algebraMap_apply,
      Algebra.algebraMap_self,C_comp,map_C,coeff_C_mul]
    simp [Algebra.smul_def, taylorAlgHom_apply, taylor_apply]

/-- Intrinsic interpolation for actual received rows, arbitrary value degree,
and any forbidden linear space of sections. The same section vanishes for all
rich selected polynomials on the component simultaneously. -/
theorem exists_section_outside {μ s m : ℕ} (D : Finset K) (u v : K → K)
    (F : K[X][X][X]) (hprim : (mapPlane (algebraMap K[X] (RatFunc K)) F).IsPrimitive)
    (hf : ScalarValueBound F m) (hr : ∀ x ∈ D, receivedOrder F x (u x) (v x) ≤ μ)
    (hm : m ≤ s+1) (surface : E →ₗ[K] K[X][X][X]) (hs : ∀ e, ScalarValueBound (surface e) s)
    (U : Submodule K E)
    (hb : D.card*((μ*(μ+1)/2)*(s+1)) + finrank K U < finrank K E +
      ∑ x ∈ D, let r := receivedOrder F x (u x) (v x)
        ((μ-r)*(μ-r+1)/2)*((s+1)-m)) :
    ∃ e ∉ U, ∀ (z : K) (q : K[X]) (H : Finset K), H ⊆ D →
      (mapPlane (evalRingHom z) F).eval q = 0 →
      (∀ a ∈ H, q.eval a = u a+z*v a) →
      ((mapPlane (evalRingHom z) (surface e)).eval q).natDegree < H.card*μ →
      (mapPlane (evalRingHom z) (surface e)).eval q = 0 := by
  classical
  let I := {x // x ∈ D}
  let r (x : I) := receivedOrder F x (u x) (v x)
  let G (x : I) := shift F (C x.val) (received (u x) (v x))
  have hlead (x : I) : ∃ j, Leader (G x) (r x) j := exists_polynomial_leader F hprim _ _ _
  choose j hj using hlead
  let L := observation (μ := μ) (fun x : I => x.val) (fun x => u x) (fun x => v x) surface hs
  let cost (x : K) := ((μ-receivedOrder F x (u x) (v x))*
    (μ-receivedOrder F x (u x) (v x)+1)/2)*((s+1)-m)
  have hcost : (∑ x : I, cost x.val) = ∑ x ∈ D, cost x := D.sum_coe_sort (f := cost)
  obtain ⟨e,he,Q,hQ⟩ := exists_polynomial_multipliers r j G (fun x => hr x x.property)
    hj hm (fun x i c => translated_column_height F m hf _ _ _ i c) L U (by
      change Fintype.card I*((μ*(μ+1)/2)*(s+1)) + finrank K U < finrank K E + ∑ x : I, cost x.val
      rw [hcost]
      simpa only [I,Fintype.card_coe] using hb)
  refine ⟨e,he,fun z q H hH hF ha hd => selected_section z H u v F (surface e) q hF ha ?_ hd⟩
  intro x hx
  let i : I := ⟨x,hH hx⟩
  exact ⟨μ-r i,fun c => (Q i c).val,hQ i⟩

/-- Numeric quartic budget for the complete selected-site version. There is a
surplus of more than 55 quadrillion parameters, using every agreement. -/
theorem quartic_count {I : Type*} [Fintype I] (r : I → ℕ)
    (hn : Fintype.card I = 1073741824) (hr : ∀ x, r x ≤ 4)
    (hR : ∑ x, r x ≤ 1412316443) :
    Fintype.card I * (2080*67108865) <
      6121893077231948920 + ∑ x, ((64-r x)*(64-r x+1)/2)*67108831 := by
  have localBound (x : I) : 2080*67108831 ≤
      ((64-r x)*(64-r x+1)/2)*67108831 + (64*67108831)*r x := by
    have h := hr x
    interval_cases h' : r x <;> decide
  have hp := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun x _ => localBound x)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hn, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hp
  rw [hn]
  omega

end ArkLib.ProximityGap.Frontier.IntrinsicReceivedSections

open ArkLib.ProximityGap.Frontier.IntrinsicReceivedSections in
#print axioms exists_section_outside
open ArkLib.ProximityGap.Frontier.IntrinsicReceivedSections in
#print axioms quartic_count
