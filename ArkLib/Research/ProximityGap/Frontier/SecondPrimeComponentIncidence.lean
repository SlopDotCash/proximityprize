/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Norm.Basic

/-! # Rich parameters on a component of the second-prime interpolant

Restriction to the received line gives one parameter polynomial per site.
Counting its roots at the nonidentity sites forces many identity sites on
every factor carrying at least 118 parameters. Interpolation over a field
extension identifies polynomial sections agreeing generically at those sites.
-/

open Finset Polynomial
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.SecondPrimeComponentIncidence

variable {F K ι : Type*} [Field F] [Field K]

/-- Double counting the roots of the specialized received-line restrictions. -/
theorem component_incidence [DecidableEq F] (D : Finset ι) (M : Finset F)
    (R : ι → F[X]) (t h : ℕ) (hdeg : ∀ x ∈ D, (R x).natDegree ≤ h)
    (hfit : ∀ z ∈ M, t ≤ (D.filter fun x => (R x).eval z = 0).card) :
    M.card * t ≤ (D.filter fun x => R x = 0).card * M.card +
      (D.filter fun x => R x ≠ 0).card * h := by
  classical
  have hroots (x : ι) (hx : x ∈ D) (hne : R x ≠ 0) :
      (M.filter fun z => (R x).eval z = 0).card ≤ h := by
    by_contra! hcard
    apply hne
    let S := M.filter fun z => (R x).eval z = 0
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (R x) (f := fun i : S => i.val)
      Subtype.val_injective
    · exact fun i => (mem_filter.mp i.property).2
    · simpa [S] using (hdeg x hx).trans_lt hcard
  calc
    M.card * t = ∑ _z ∈ M, t := by simp
    _ ≤ ∑ z ∈ M, (D.filter fun x => (R x).eval z = 0).card :=
      sum_le_sum hfit
    _ = ∑ x ∈ D, (M.filter fun z => (R x).eval z = 0).card := by
      simp_rw [Finset.card_filter]
      rw [sum_comm]
    _ ≤ ∑ x ∈ D, if R x = 0 then M.card else h := by
      apply sum_le_sum
      intro x hx
      split_ifs with hz
      · exact card_le_card (filter_subset _ _)
      · exact hroots x hx hz
    _ = _ := by simp [Finset.sum_ite]

/-- The degree-34 certificate demands at least d+1 identity sites on every
component containing 118 or more rich distinct parameters. -/
theorem secondPrime_identity_sites [DecidableEq F] (D : Finset ι) (M : Finset F)
    (R : ι → F[X]) (hn : D.card = 1073741824) (hm : 118 ≤ M.card)
    (hdeg : ∀ x ∈ D, (R x).natDegree ≤ 34)
    (hfit : ∀ z ∈ M, 357913943 ≤ (D.filter fun x => (R x).eval z = 0).card) :
    67108864 ≤ (D.filter fun x => R x = 0).card := by
  classical
  obtain ⟨S, hSM, hS⟩ := exists_subset_card_eq hm
  have h := component_incidence D S R 357913943 34 hdeg (fun z hz => hfit z (hSM hz))
  rw [hS] at h
  have hpart := D.card_filter_add_card_filter_not (fun x => R x = 0)
  change (D.filter fun x => R x = 0).card + (D.filter fun x => R x ≠ 0).card = D.card at hpart
  rw [hn] at hpart
  omega

/-- A polynomial over an extension that agrees with the generic received line
at d+1 sites is an affine combination of two polynomials over the base field. -/
theorem generic_section_is_head (f : F →+* K) (g : K) (D : Finset ι) (x : ι ↪ F)
    (u v : ι → F) (d : ℕ) (P : K[X]) (hdeg : P.natDegree ≤ d) (hcard : d < D.card)
    (hfit : ∀ i ∈ D, P.eval (f (x i)) = f (u i) + g * f (v i)) :
    ∃ A B : F[X], A.natDegree ≤ d ∧ B.natDegree ≤ d ∧ P = A.map f + C g * B.map f := by
  classical
  obtain ⟨S, hSD, hS⟩ := exists_subset_card_eq (show d + 1 ≤ D.card by omega)
  let A := Lagrange.interpolate S x u
  let B := Lagrange.interpolate S x v
  have hb (w : ι → F) : (Lagrange.interpolate S x w).natDegree ≤ d := by
    by_cases hz : Lagrange.interpolate S x w = 0
    · simp [hz]
    · have hh := (natDegree_lt_iff_degree_lt hz).mpr
          (Lagrange.degree_interpolate_lt w x.injective.injOn)
      omega
  refine ⟨A, B, hb u, hb v, ?_⟩
  have hsum : (A.map f + C g * B.map f).natDegree ≤ d :=
    natDegree_add_le_of_degree_le (natDegree_map_le.trans (hb u))
      ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (hb v)))
  apply eq_of_degrees_lt_of_eval_index_eq S (f.injective.comp x.injective).injOn
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast (hS ▸ Nat.lt_succ_of_le hdeg :
        P.natDegree < S.card))
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show
        (A.map f + C g * B.map f).natDegree < S.card by omega))
  · intro i hi
    have hA : A.eval (x i) = u i := Lagrange.eval_interpolate_at_node _ x.injective.injOn hi
    have hB : B.eval (x i) = v i := Lagrange.eval_interpolate_at_node _ x.injective.injOn hi
    simpa only [Function.comp_apply, eval_add, eval_mul, eval_C, eval_map_apply, hA, hB] using
      hfit i (hSD hi)


/-- For a polynomial section defined over a finite extension of the parameter
field, a norm presentation of the received-line restrictions yields a sharp
alternative between a small parameter set and a genuine affine head. -/
theorem secondPrime_norm_section {L : Type*} [Field L] [Algebra L K]
    [FiniteDimensional L K] [DecidableEq F] (φ : F →+* L) (γ : L)
    (D : Finset ι) (dom : ι ↪ F) (u v : ι → F) (M : Finset F) (R : ι → F[X])
    (P : K[X]) (hP : P.natDegree ≤ 67108863) (c : L) (hc : c ≠ 0)
    (hn : D.card = 1073741824) (hdeg : ∀ i ∈ D, (R i).natDegree ≤ 34)
    (hfit : ∀ z ∈ M, 357913943 ≤ (D.filter fun i => (R i).eval z = 0).card)
    (hnorm : ∀ i ∈ D, (R i).eval₂ φ γ =
      c * Algebra.norm L (P.eval (algebraMap L K (φ (dom i))) -
        algebraMap L K (φ (u i) + γ * φ (v i)))) :
    M.card ≤ 117 ∨ ∃ A B : F[X], A.natDegree ≤ 67108863 ∧ B.natDegree ≤ 67108863 ∧
      P = A.map ((algebraMap L K).comp φ) + C (algebraMap L K γ) * B.map ((algebraMap L K).comp φ) := by
  classical
  rcases le_or_gt M.card 117 with h | h
  · exact Or.inl h
  right
  apply generic_section_is_head ((algebraMap L K).comp φ) (algebraMap L K γ)
    (D.filter fun i => R i = 0) dom u v _ P hP
  · exact secondPrime_identity_sites D M R hn h hdeg hfit
  · intro i hi
    obtain ⟨hiD, hiR⟩ := mem_filter.mp hi
    have heq := hnorm i hiD
    rw [hiR, eval₂_zero] at heq
    have hz := Algebra.norm_eq_zero_iff.mp ((mul_eq_zero.mp heq.symm).resolve_left hc)
    simpa only [RingHom.comp_apply, map_add, map_mul] using sub_eq_zero.mp hz

end ArkLib.ProximityGap.Frontier.SecondPrimeComponentIncidence

open ArkLib.ProximityGap.Frontier.SecondPrimeComponentIncidence in
#print axioms secondPrime_norm_section
