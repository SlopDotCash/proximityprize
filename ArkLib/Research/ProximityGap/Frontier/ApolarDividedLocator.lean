/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! # The divided locator and the Reed–Solomon syndrome on an affine chart

The quotient of a locator by the universal root factor represents a functional
by evaluation. At a reduced error support the domain vanisher kills this
representative in the full root algebra, including for a locator with repeated roots.
-/

open Polynomial Finset
namespace ProximityGap.ApolarDividedLocator

variable {R : Type*} [CommRing R]

/-- A locator annihilates all multiples with multiplier degree at most the stated bound. -/
def ApolarThrough (L : R[X] →ₗ[R] R) (f : R[X]) (s : ℕ) : Prop :=
  ∀ B : R[X], B.natDegree ≤ s → L (f*B) = 0

/-- The affine divided locator, computed by monic polynomial division. -/
noncomputable def divided (f : R[X]) (x : R) : R[X] := f /ₘ (X - C x)

theorem divided_identity (f : R[X]) (x : R) (hx : f.IsRoot x) :
    (X-C x)*divided f x = f := mul_divByMonic_eq_iff_isRoot.mpr hx

/-- On a locator root, the functional on the divided locator times a polynomial
equals evaluation times the value of the functional on the divided locator. -/
theorem divided_evaluate [Nontrivial R] (L : R[X] →ₗ[R] R) (f B : R[X]) (x : R)
    {s : ℕ} (hx : f.IsRoot x) (ha : ApolarThrough L f s) (hb : B.natDegree ≤ s+1) :
    L (divided f x * B) = B.eval x * L (divided f x) := by
  let Q := B /ₘ (X-C x)
  have hd : Q.natDegree ≤ s := by
    dsimp only [Q]
    rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
    omega
  have hs := B.modByMonic_add_div (X-C x)
  rw [modByMonic_X_sub_C_eq_C_eval] at hs
  have hsplit : divided f x * B = B.eval x • divided f x + f*Q := by
    rw [smul_eq_C_mul]
    dsimp only [Q]
    linear_combination (divided f x) * hs.symm + (B /ₘ (X-C x)) * divided_identity f x hx
  rw [hsplit, map_add, map_smul, ha Q hd, add_zero]
  rfl

/-- At a geometric root of a minimal positive-degree apolar polynomial the divided
functional is nonzero. The hypothesis checks the preceding catalecticant degree. -/
theorem divided_nonzero [Nontrivial R] (L : R[X] →ₗ[R] R) (f : R[X]) (x : R)
    {s r : ℕ} (hf : f.natDegree = r+1) (hx : f.IsRoot x) (ha : ApolarThrough L f s)
    (hprev : ∀ q : R[X], q.natDegree = r → q ≠ 0 → ¬ ApolarThrough L q (s+1)) :
    L (divided f x) ≠ 0 := by
  intro h
  have hq : (divided f x).natDegree = r := by
    simp [divided, natDegree_divByMonic _ (monic_X_sub_C _), hf]
  have hn : divided f x ≠ 0 := by
    intro he
    have hh := divided_identity f x hx
    rw [he, mul_zero] at hh
    rw [← hh, natDegree_zero] at hf
    omega
  apply hprev _ hq hn
  intro B hB
  rw [divided_evaluate L f B x hx ha hB, h, mul_zero]

variable {K : Type*} [Field K]

/-- A weighted sum of coordinate evaluations, allowing extension to a nonreduced algebra. -/
noncomputable def weighted (E : Finset K) (φ : K →+* R) (w : K → K) : R[X] →ₗ[R] R :=
  ∑ y ∈ E, φ (w y) • Polynomial.leval (φ y)

theorem weighted_apply (E : Finset K) (φ : K →+* R) (w : K → K) (B : R[X]) :
    weighted E φ w B = ∑ y ∈ E, φ (w y) * B.eval (φ y) := by
  simp [weighted, LinearMap.sum_apply, Polynomial.leval, smul_eq_mul]

/-- A reduced error syndrome with sufficiently few nonzero weights forces each
error site to be a root of every apolar locator. -/
theorem isRoot_of_reduced (E : Finset K) (w : K → K) (f : K[X]) {s : ℕ}
    (hc : E.card ≤ s+1) (ha : ApolarThrough (weighted E (RingHom.id K) w) f s)
    {y : K} (hy : y ∈ E) (hw : w y ≠ 0) : f.IsRoot y := by
  classical
  let B := Lagrange.nodal (E.erase y) id
  have hb : B.natDegree ≤ s := by
    rw [show B.natDegree = (E.erase y).card from Lagrange.natDegree_nodal, card_erase_of_mem hy]
    omega
  have hn : B.eval y ≠ 0 := Lagrange.eval_nodal_not_at_node (fun z hz => (mem_erase.mp hz).1.symm)
  have h := ha B hb
  rw [weighted_apply, sum_eq_single_of_mem y hy (fun z hz hzy => by
    rw [eval_mul, show B.eval ((RingHom.id K) z) = 0 from
      Lagrange.eval_nodal_at_node (mem_erase.mpr ⟨hzy,hz⟩), mul_zero, mul_zero])] at h
  simp only [RingHom.id_apply, eval_mul, mul_eq_zero] at h
  exact (h.resolve_left hw).resolve_right hn

/-- Pointwise multiplication by the domain vanisher kills the divided locator
functional over an arbitrary commutative coefficient algebra. No reducedness
assumption is needed on the ring containing the locator root. -/
theorem vanisher_mul_divided (H E : Finset K) (φ : K →+* R) (w : K → K)
    (f : K[X]) (x : R) (hx : (f.map φ).IsRoot x) (hE : E ⊆ H)
    (hr : ∀ y ∈ E, w y ≠ 0 → f.IsRoot y) :
    (Lagrange.nodal H φ).eval x * weighted E φ w (divided (f.map φ) x) = 0 := by
  classical
  rw [weighted_apply, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hw : w y = 0
  · simp [hw]
  have hzero := congrArg (Polynomial.eval (φ y)) (divided_identity (f.map φ) x hx)
  have hv : (f.map φ).eval (φ y) = 0 := by rw [eval_map, eval₂_hom, (hr y hy hw).eq_zero, map_zero]
  simp only [eval_mul, eval_sub, eval_X, eval_C, hv] at hzero
  rw [Lagrange.nodal_eq_mul_nodal_erase (v := φ) (hE hy), eval_mul, eval_sub, eval_X, eval_C]
  linear_combination -(Lagrange.nodal (H.erase y) φ).eval x * φ (w y) * hzero

/-- The vanishing identity in the actual quotient by the locator, with every
multiplicity retained. -/
theorem quotient_reduced_fiber (H E : Finset K) (w : K → K) (f : K[X]) {s : ℕ}
    (hE : E ⊆ H) (hc : E.card ≤ s+1)
    (ha : ApolarThrough (weighted E (RingHom.id K) w) f s) :
    (Lagrange.nodal H (AdjoinRoot.of f)).eval (AdjoinRoot.root f) *
      weighted E (AdjoinRoot.of f) w (divided (f.map (AdjoinRoot.of f)) (AdjoinRoot.root f)) = 0 :=
  vanisher_mul_divided H E _ w f _ (AdjoinRoot.isRoot_root f) hE
    (fun _ hy hw => isRoot_of_reduced E w f hc ha hy hw)

/-- The explicit parity-check weights on an arbitrary evaluation domain. -/
noncomputable def rowWeight (H : Finset K) (u : K → K) (x : K) : K := by
  classical
  exact u x / ∏ z ∈ H.erase x, (x-z)

/-- The Reed–Solomon moment functional on the domain, extended to the given coefficient ring. -/
noncomputable def syndrome (H : Finset K) (φ : K →+* R) (u : K → K) : R[X] →ₗ[R] R :=
  weighted H φ (rowWeight H u)

/-- The received affine fold gives the literal linear pencil of syndrome functionals. -/
theorem syndrome_pencil (H : Finset K) (u v : K → K) (t : K) (φ : K →+* R) :
    syndrome H φ (fun x => u x+t*v x) = syndrome H φ u + φ t • syndrome H φ v := by
  classical
  apply LinearMap.ext
  intro B
  simp only [syndrome, weighted_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    rowWeight, add_div, mul_div_assoc, map_add, map_mul, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_assoc]

private theorem syndrome_codeword_zero (H : Finset K) (Q B : K[X])
    (hd : Q.natDegree + B.natDegree < H.card-1) :
    syndrome H (RingHom.id K) (fun y => Q.eval y) B = 0 := by
  classical
  have hp := (natDegree_mul_le (p := Q) (q := B)).trans_lt hd
  have htt : (Q*B).natDegree < H.card := by omega
  have hh : (Q*B).degree < (H.card : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr htt)
  have hc := Lagrange.coeff_eq_sum (s := H) (v := id) Function.injective_id.injOn hh
  have hz := coeff_eq_zero_of_natDegree_lt hp
  dsimp only [syndrome]
  rw [weighted_apply]
  simp only [RingHom.id_apply, rowWeight, id_eq, eval_mul] at hc ⊢
  rw [hz] at hc
  simpa only [div_mul_eq_mul_div] using hc.symm

private theorem syndrome_reduced_base (H E : Finset K) (u : K → K) (Q B : K[X])
    (hE : E ⊆ H) (hoff : ∀ x ∈ H, x ∉ E → u x = Q.eval x)
    (hd : Q.natDegree + B.natDegree < H.card-1) :
    syndrome H (RingHom.id K) u B =
      weighted E (RingHom.id K) (rowWeight H (fun x => u x-Q.eval x)) B := by
  classical
  have h0 := syndrome_codeword_zero H Q B hd
  have hs := Finset.sum_subset (f := fun x => rowWeight H (fun y => u y-Q.eval y) x * B.eval x)
    hE (fun x hx he => by simp [rowWeight, hoff x hx he])
  simp only [syndrome, weighted_apply, RingHom.id_apply, rowWeight] at h0 ⊢
  dsimp only [rowWeight] at hs
  rw [hs]
  simp only [sub_div, sub_mul, Finset.sum_sub_distrib,h0, sub_zero]

private theorem weighted_moment (H : Finset K) (w : K → K) (φ : K →+* R) (j : ℕ) :
    weighted H φ w (X^j) = φ (weighted H (RingHom.id K) w (X^j)) := by
  simp [weighted_apply]

/-- Changing a received word by a neighboring polynomial restricts the syndrome
to its actual error support in the whole relevant degree window, after arbitrary
coefficient extension. -/
theorem syndrome_reduced (H E : Finset K) (u : K → K) (Q : K[X]) (B : R[X]) (φ : K →+* R)
    (hE : E ⊆ H) (hoff : ∀ x ∈ H, x ∉ E → u x = Q.eval x)
    (hd : Q.natDegree + B.natDegree < H.card-1) :
    syndrome H φ u B = weighted E φ (rowWeight H (fun x => u x-Q.eval x)) B := by
  classical
  have hm (j : ℕ) (hj : j ≤ B.natDegree) :
      syndrome H φ u (X^j) = weighted E φ (rowWeight H (fun x => u x-Q.eval x)) (X^j) := by
    have hj' : Q.natDegree + ((X : K[X])^j).natDegree < H.card-1 := by simp; omega
    change weighted H φ _ (X^j) = _
    rw [weighted_moment H _ φ, weighted_moment E _ φ]
    exact congrArg φ (syndrome_reduced_base H E u Q (X^j) hE hoff hj')
  calc
    _ = ∑ j ∈ range (B.natDegree+1), B.coeff j • syndrome H φ u (X^j) := by
      conv_lhs => rw [B.as_sum_range_C_mul_X_pow]
      simp only [map_sum, ← smul_eq_C_mul, map_smul]
    _ = ∑ j ∈ range (B.natDegree+1), B.coeff j •
        weighted E φ (rowWeight H (fun x => u x-Q.eval x)) (X^j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hm j (by have := mem_range.mp hj; omega)]
    _ = _ := by
      conv_rhs => rw [B.as_sum_range_C_mul_X_pow]
      simp only [map_sum, ← smul_eq_C_mul, map_smul]

/-- The divided syndrome vanishes after multiplication by the domain vanisher in
the original locator quotient. The hypotheses are a genuine neighboring received
word, a root count and the corresponding catalecticant kernel condition. -/
theorem syndrome_quotient_fiber (H E : Finset K) (u : K → K) (Q f : K[X]) {s : ℕ}
    (hE : E ⊆ H) (hoff : ∀ x ∈ H, x ∉ E → u x = Q.eval x)
    (hc : E.card ≤ s+1) (hd : Q.natDegree + f.natDegree + s < H.card-1)
    (ha : ApolarThrough (syndrome H (RingHom.id K) u) f s) :
    (Lagrange.nodal H (AdjoinRoot.of f)).eval (AdjoinRoot.root f) *
      syndrome H (AdjoinRoot.of f) u (divided (f.map (AdjoinRoot.of f)) (AdjoinRoot.root f)) = 0 := by
  classical
  nontriviality AdjoinRoot f
  have hb : Q.natDegree + (divided (f.map (AdjoinRoot.of f)) (AdjoinRoot.root f)).natDegree <
      H.card-1 := by
    rw [divided, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
    have hh := natDegree_map_le (p := f) (f := AdjoinRoot.of f)
    omega
  rw [syndrome_reduced H E u Q _ _ hE hoff hb]
  apply quotient_reduced_fiber H E _ f hE hc
  intro B hB
  have hdeg := natDegree_mul_le (p := f) (q := B)
  rw [← syndrome_reduced_base H E u Q (f*B) hE hoff (by omega)]
  exact ha B hB

#print axioms syndrome_pencil
#print axioms syndrome_quotient_fiber

#print axioms divided_nonzero
#print axioms quotient_reduced_fiber

end ProximityGap.ApolarDividedLocator
