/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import CompPoly.ToMathlib.Polynomial.Roots
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Affine heads on a minimum-distance support

Relative to a code pencil agreeing with the received pencil off a minimum
support, every decoded head with errors in that support differs by a scalar
multiple of one residual codeword. Agreement at any coordinate of the support
then cuts a single affine line in the resulting two-parameter family.
-/

open scoped BigOperators Polynomial

set_option autoImplicit false

namespace ProximityGap.MinimumSupportHeadPlane

/-- A nonzero word on a minimum support spans all codewords on that support. -/
theorem residual_on_minimum_support {F X : Type*} [Field F] [DecidableEq X]
    (C : Submodule F (X → F)) (S : Finset X) (D : ℕ) (hS : S.card = D)
    (hdist : ∀ v ∈ C, ∀ B : Finset X, B.card < D → (∀ x ∉ B, v x = 0) → v = 0)
    (v w : X → F) (hv : v ∈ C) (hw : w ∈ C) (hv0 : v ≠ 0)
    (hvS : ∀ x ∉ S, v x = 0) (hwS : ∀ x ∉ S, w x = 0) :
    (∀ x ∈ S, v x ≠ 0) ∧ ∃ a : F, w = a • v := by
  classical
  have vanishes {z : X → F} (hz : z ∈ C) (hzS : ∀ x ∉ S, z x = 0)
      {p : X} (hp : p ∈ S) (hzp : z p = 0) : z = 0 := by
    refine hdist z hz (S.erase p) ?_ ?_
    · rw [Finset.card_erase_of_mem hp, hS]
      have hc := Finset.card_pos.mpr ⟨p, hp⟩
      omega
    · intro x hx
      by_cases hxp : x = p
      · subst x
        exact hzp
      · exact hzS x (fun hxS => hx (Finset.mem_erase.mpr ⟨hxp, hxS⟩))
  have hvnz : ∀ x ∈ S, v x ≠ 0 := fun x hx h => hv0 (vanishes hv hvS hx h)
  have hSnonempty : S.Nonempty := by
    by_contra h
    apply hv0
    funext x
    exact hvS x (fun hx => h ⟨x, hx⟩)
  obtain ⟨p, hp⟩ := hSnonempty
  let a := w p / v p
  refine ⟨hvnz, a, sub_eq_zero.mp (vanishes (C.sub_mem hw (C.smul_mem a hv)) ?_ hp ?_)⟩
  · intro x hx
    simp [Pi.sub_apply, Pi.smul_apply, hvS x hx, hwS x hx]
  · change w p - a * v p = 0
    rw [show a * v p = w p from div_mul_cancel₀ _ (hvnz p hp), sub_self]

/-- All decoded heads supported relative to one code pencil have the same residual direction. -/
theorem affine_heads_on_minimum_support {F X I : Type*} [Field F] [DecidableEq X]
    (C : Submodule F (X → F)) (S : Finset X) (D : ℕ) (hS : S.card = D)
    (hdist : ∀ v ∈ C, ∀ B : Finset X, B.card < D → (∀ x ∉ B, v x = 0) → v = 0)
    (U V v : X → F) (hU : U ∈ C) (hV : V ∈ C) (hv : v ∈ C) (hv0 : v ≠ 0)
    (hvS : ∀ x ∉ S, v x = 0) (γ : I → F) (w : I → X → F) (hw : ∀ i, w i ∈ C)
    (hoff : ∀ i x, x ∉ S → w i x = U x + γ i * V x) :
    (∀ x ∈ S, v x ≠ 0) ∧ ∃ a : I → F, ∀ i, w i = U + γ i • V + a i • v := by
  classical
  have hfull := (residual_on_minimum_support C S D hS hdist v v hv hv hv0 hvS hvS).1
  refine ⟨hfull, ?_⟩
  have hfit (i : I) : ∃ a : F, w i = U + γ i • V + a • v := by
    let r := w i - (U + γ i • V)
    have hr : r ∈ C := C.sub_mem (hw i) (C.add_mem hU (C.smul_mem (γ i) hV))
    have hrS (x : X) (hx : x ∉ S) : r x = 0 := by
      change w i x - (U x + γ i * V x) = 0
      rw [hoff i x hx, sub_self]
    obtain ⟨a, ha⟩ := (residual_on_minimum_support C S D hS hdist v r hv hr hv0 hvS hrS).2
    exact ⟨a, (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)⟩
  choose a ha using hfit
  exact ⟨a, ha⟩

/-- The agreement condition on one coordinate is affine in the head parameter. -/
theorem agreement_on_residual_line {F : Type*} [Field F]
    (u₀ u₁ U V v γ a : F) (hv : v ≠ 0) :
    U + γ * V + a * v = u₀ + γ * u₁ ↔
      a = (u₀ - U) / v + γ * ((u₁ - V) / v) := by
  rw [← mul_div_assoc, ← add_div, eq_div_iff hv]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- The two cross triples force separation between the original triple supports. -/
theorem support_symmetric_difference_bound {X : Type*} [Fintype X] [DecidableEq X]
    (A B C E : Finset X) (D t : ℕ)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t) (hE : E.card ≤ t)
    (hACE : D ≤ ((A ∪ C) ∪ E).card) (hBCE : D ≤ ((B ∪ C) ∪ E).card) :
    2 * D ≤ 4 * t + (((A ∪ B) ∪ C) \ ((A ∪ B) ∪ E)).card +
      (((A ∪ B) ∪ E) \ ((A ∪ B) ∪ C)).card := by
  classical
  let S := (A ∪ B) ∪ C
  let T := (A ∪ B) ∪ E
  have charge (x : X) :
      (if x ∈ (A ∪ C) ∪ E then 1 else 0) + (if x ∈ (B ∪ C) ∪ E then 1 else 0) ≤
        (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0) +
        (if x ∈ C then 1 else 0) + (if x ∈ E then 1 else 0) +
        (if x ∈ S \ T then 1 else 0) + (if x ∈ T \ S then 1 else 0) := by
    by_cases ha : x ∈ A
    all_goals by_cases hb : x ∈ B
    all_goals by_cases hc : x ∈ C
    all_goals by_cases he : x ∈ E
    all_goals simp [S, T, Finset.mem_union, Finset.mem_sdiff, ha, hb, hc, he]
  have summed := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ ↦ charge x)
  have count (P : Finset X) : (∑ x : X, if x ∈ P then 1 else 0) = P.card := by simp
  simp only [Finset.sum_add_distrib, count] at summed
  change 2 * D ≤ 4 * t + (S \ T).card + (T \ S).card
  omega

/-- Near-minimal triple supports sharing an edge have a large one-sided difference. -/
theorem near_minimal_support_separation {X : Type*} [Fintype X] [DecidableEq X]
    (A B C E : Finset X) (D t J : ℕ)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t) (hE : E.card ≤ t)
    (hACE : D ≤ ((A ∪ C) ∪ E).card) (hBCE : D ≤ ((B ∪ C) ∪ E).card)
    (hABC : D ≤ ((A ∪ B) ∪ C).card) (hABE : ((A ∪ B) ∪ E).card ≤ D + J) :
    2 * D ≤ 4 * t + J + 2 * (((A ∪ B) ∪ C) \ ((A ∪ B) ∪ E)).card := by
  classical
  let S := (A ∪ B) ∪ C
  let T := (A ∪ B) ∪ E
  have hsep := support_symmetric_difference_bound A B C E D t hA hB hC hE hACE hBCE
  change 2 * D ≤ 4 * t + (S \ T).card + (T \ S).card at hsep
  change D ≤ S.card at hABC
  change T.card ≤ D + J at hABE
  change 2 * D ≤ 4 * t + J + 2 * (S \ T).card
  have split (P Q : Finset X) : (P \ Q).card + (P ∩ Q).card = P.card := by
    have h : P \ (P ∩ Q) = P \ Q := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [← h]
    exact Finset.card_sdiff_add_card_eq_card Finset.inter_subset_left
  have splitS := split S T
  have splitT := split T S
  rw [Finset.inter_comm T S] at splitT
  omega

/-- Tight triples sharing an edge separate by the distance margin. -/
theorem tight_support_separation {X : Type*} [Fintype X] [DecidableEq X]
    (A B C E : Finset X) (D t : ℕ)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t) (hE : E.card ≤ t)
    (hACE : D ≤ ((A ∪ C) ∪ E).card) (hBCE : D ≤ ((B ∪ C) ∪ E).card)
    (hABC : ((A ∪ B) ∪ C).card = D) (hABE : ((A ∪ B) ∪ E).card = D) :
    D ≤ 2 * t + (((A ∪ B) ∪ C) \ ((A ∪ B) ∪ E)).card := by
  have h := near_minimal_support_separation A B C E D t 0 hA hB hC hE hACE hBCE
    hABC.ge (by simpa using hABE.le)
  omega

/-- A residual with a full set of prescribed roots has a complementary locator. -/
theorem residual_mul_nodal_complement {F X : Type*} [Field F] [DecidableEq X]
    (z : X ↪ F) (G B : Finset X) (hB : B ⊆ G) (v : F[X]) (hv : v ≠ 0)
    (hdeg : v.natDegree ≤ (G \ B).card)
    (hroot : ∀ x ∈ G \ B, v.eval (z x) = 0) :
    ∃ a : F, a ≠ 0 ∧ v * Lagrange.nodal B z = Polynomial.C a * Lagrange.nodal G z := by
  classical
  obtain ⟨R, hR⟩ : Lagrange.nodal (G \ B) z ∣ v :=
    Polynomial.prod_X_sub_C_dvd (G \ B) z z.injective.injOn v hroot
  have hR0 : R ≠ 0 := by
    intro h
    apply hv
    simp [hR, h]
  have hRdeg : R.natDegree = 0 := by
    rw [hR, Polynomial.natDegree_mul Lagrange.nodal_ne_zero hR0,
      Lagrange.natDegree_nodal] at hdeg
    omega
  have hRC := Polynomial.eq_C_of_natDegree_eq_zero hRdeg
  refine ⟨R.coeff 0, ?_, ?_⟩
  · intro h
    exact hR0 (by simpa [h] using hRC)
  · have hpartition : Lagrange.nodal (G \ B) z * Lagrange.nodal B z =
        Lagrange.nodal G z := Finset.prod_sdiff hB
    have hscaled : v = Lagrange.nodal (G \ B) z * Polynomial.C (R.coeff 0) :=
      hR.trans (congrArg (fun f => Lagrange.nodal (G \ B) z * f) hRC)
    rw [hscaled, mul_right_comm, hpartition, mul_comm]

/-- Evaluation of a reciprocal locator on a coordinate explained by the received line. -/
theorem reciprocal_locator_evaluation {F : Type*} [Field F]
    (v L P a delta s : F) (ha : a ≠ 0) (hd : delta ≠ 0)
    (hfactor : v * L = a * P) (hvalue : v = s * delta) :
    s / a * L = P / delta := by
  apply (eq_div_iff hd).mpr
  calc
    (s / a * L) * delta = (1 / a) * (v * L) := by
      rw [hvalue]
      ring
    _ = P := by
      rw [hfactor]
      field_simp

/-- Exact integer margins for the reciprocal-locator incidence argument.
The first inequality caps the surviving tight completions below 6830. The
second guarantees more than 30 percent long triples after counting high-union
pairs and removing up to 7001 exceptional completions at each pair. -/
theorem first_sponsor_reciprocal_locator_margins :
    let n : ℤ := 1073741824
    let D : ℤ := 536870913
    let t : ℤ := 221512374
    let e : ℤ := 377420252
    let q : ℤ := 852229450
    let b := n + 1
    let s := e - t
    let l := D - 2 * t
    let U := (n - D) * b * (b - 1) * (b - 2) + 2 * D * b + 3 * n * b^2
    let denom := 3 * q * b * (b - 1)
    let meanNum := n * denom - (2 * U + n * q^3) + 3 * q * b * (n - t)
    24 * t * (4 * s^2) < 6830 * ((s + l)^3 - 4 * s^2 * (D - e)) ∧
    3 * (2 * t - e) * denom * (b - 2) < 10 * (meanNum - e * denom) * (b - 2 - 7001) := by
  norm_num

/-- Exact integer margins for the near-minimal-support band of 3100000 coordinates. -/
theorem first_sponsor_near_minimal_locator_margins :
    let n : ℤ := 1073741824
    let D : ℤ := 536870913
    let t : ℤ := 221762374
    let J : ℤ := 3100000
    let e : ℤ := 388694542
    let q : ℤ := 851979450
    let b := n + 1
    let s := e - t
    let l := D - 2 * t
    let g := b * (n - t)
    let triples := b * (b - 1) * (b - 2) / 6
    let U := (n - D) * b * (b - 1) * (b - 2) + 2 * D * b + 3 * n * b^2
    let denom := 3 * q * b * (b - 1)
    let meanNum := n * denom - (2 * U + n * q^3) + 3 * q * b * (n - t)
    n < 12 * (l - J / 2) ∧
    24 * t * (4 * s^2) < 7500 * ((s + l)^3 - 4 * s^2 * (D - e + 3 * J)) ∧
    1574 * (2 * t - e) * denom * (b - 2) < 10000 * (meanNum - e * denom) * (b - 2 - 7503) ∧
    6 * n^2 * ((n - D) * triples + D * (b / 3) - (157 * triples / 1000) * (J + 1)) <
      g * (g - n) * (g - 2 * n) := by
  norm_num

end ProximityGap.MinimumSupportHeadPlane

#print axioms ProximityGap.MinimumSupportHeadPlane.residual_on_minimum_support
#print axioms ProximityGap.MinimumSupportHeadPlane.agreement_on_residual_line
#print axioms ProximityGap.MinimumSupportHeadPlane.affine_heads_on_minimum_support
#print axioms ProximityGap.MinimumSupportHeadPlane.tight_support_separation
#print axioms ProximityGap.MinimumSupportHeadPlane.first_sponsor_reciprocal_locator_margins
#print axioms ProximityGap.MinimumSupportHeadPlane.residual_mul_nodal_complement
#print axioms ProximityGap.MinimumSupportHeadPlane.reciprocal_locator_evaluation
#print axioms ProximityGap.MinimumSupportHeadPlane.support_symmetric_difference_bound
#print axioms ProximityGap.MinimumSupportHeadPlane.near_minimal_support_separation
#print axioms ProximityGap.MinimumSupportHeadPlane.first_sponsor_near_minimal_locator_margins
