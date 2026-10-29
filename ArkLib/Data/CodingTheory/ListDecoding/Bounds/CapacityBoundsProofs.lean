import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GKL24
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.BCHKS25
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.SubstitutionMultiplicity
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GuruswamiSudanListSize
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Final Capacity Bound Proofs
This file unifies the GKL24 interpolation bounds, the BCHKS25 multiplicity bounds,
and the Phase 1 Guruswami-Sudan roots theorems into the final list decoding
capacity bound theorems for cryptographic application.
-/

namespace CodingTheory.Bounds.Capacity

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- Evaluates the substitution P(X) = Q(X, f(X)) at a point x. -/
lemma aeval_eval_eq (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) (x : F) :
    (MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q).eval x =
    MvPolynomial.eval (fun i => if i = 0 then x else f.eval x) Q := by
  rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, ← MvPolynomial.aeval_eq_eval]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext i
  fin_cases i <;> simp

set_option maxHeartbeats 1000000 in
/-- Bounding the degree of the substituted polynomial P(X) = Q(X, f(X)). -/
lemma natDegree_aeval_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
    (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X)
    (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
    (f : Polynomial F) :
    (MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q).natDegree
      ≤ deg_X + deg_Y * f.natDegree := by
  let g : Fin 2 → Polynomial F := fun i => if i = 0 then Polynomial.X else f
  have heval : MvPolynomial.aeval g Q
      = ∑ m ∈ Q.support, MvPolynomial.aeval g (MvPolynomial.monomial m (Q.coeff m)) := by
    rw [← map_sum, ← MvPolynomial.as_sum]
  rw [heval]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le ?_
  intro m hm
  simp only [Function.comp_apply]
  have h_eval_m : MvPolynomial.aeval g (MvPolynomial.monomial m (Q.coeff m)) =
      Polynomial.C (Q.coeff m) * g 0 ^ m 0 * g 1 ^ m 1 := by
    rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod_fintype,
      Fin.prod_univ_two, ← mul_assoc]
    intro i; rw [pow_zero]
  rw [h_eval_m]
  have hg0 : g 0 = Polynomial.X := rfl
  have hg1 : g 1 = f := rfl
  rw [hg0, hg1]
  have h0 : (Polynomial.X ^ m 0 : Polynomial F).natDegree ≤ m 0 := by
    have h_pow : (Polynomial.X ^ m 0 : Polynomial F).natDegree ≤ m 0 * (Polynomial.X : Polynomial F).natDegree :=
      Polynomial.natDegree_pow_le
    rw [Polynomial.natDegree_X, mul_one] at h_pow
    exact h_pow
  have h1 : (f ^ m 1).natDegree ≤ m 1 * f.natDegree := Polynomial.natDegree_pow_le
  have hX_m : m 0 ≤ deg_X := le_trans (MvPolynomial.monomial_le_degreeOf 0 hm) hX
  have hY_m : m 1 ≤ deg_Y := le_trans (MvPolynomial.monomial_le_degreeOf 1 hm) hY
  calc (Polynomial.C (Q.coeff m) * Polynomial.X ^ m 0 * f ^ m 1).natDegree
      ≤ (Polynomial.C (Q.coeff m) * Polynomial.X ^ m 0).natDegree
          + (f ^ m 1).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (Polynomial.X ^ m 0 : Polynomial F).natDegree + (f ^ m 1).natDegree := by
        gcongr; exact Polynomial.natDegree_C_mul_le _ _
    _ ≤ m 0 + m 1 * f.natDegree := by gcongr
    _ ≤ deg_X + deg_Y * f.natDegree := by gcongr


/-- The final list-decoding capacity bound combining GKL24 interpolation and BCHKS25 vanishing.
Any codeword with agreement strictly greater than the list decoding radius will correspond
to a Y-root of the interpolating polynomial Q(X,Y). -/
theorem capacity_bound_implies_y_root [DecidableEq F]
    (points : Finset F)
    (f : Polynomial F)
    (received : F → F)
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun x => (multiplicities (x, received x) + 1) * multiplicities (x, received x) / 2)) < (deg_X + 1) * (deg_Y + 1))
    (h_agree : (points.filter (fun x => f.eval x = received x)).sum (fun x => multiplicities (x, received x)) > deg_X + deg_Y * f.natDegree) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ x, MvPolynomial.eval (fun i => if i = 0 then x else f.eval x) Q = 0) := by
  classical
  have h_dim' : ((points.image (fun x => (x, received x))).sum
      (fun p => (multiplicities p + 1) * multiplicities p / 2)) < (deg_X + 1) * (deg_Y + 1) := by
    rw [Finset.sum_image (fun x _ y _ h => (Prod.ext_iff.mp h).1)]
    exact h_dim
  obtain ⟨Q, hQ_neq, hQ_degX, hQ_degY, hQ_mult⟩ :=
    GKL24.gkl24_interpolation_existence (points.image (fun x => (x, received x)))
      multiplicities deg_X deg_Y h_dim'
  refine ⟨Q, hQ_neq, ?_⟩
  set P : Polynomial F :=
    MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q with hPdef
  -- The substituted polynomial `P = Q(T, f(T))` is identically zero.
  have hP0 : P = 0 := by
    by_cases hPne : P = 0
    · exact hPne
    · refine BCHKS25.bchks25_vanishing_of_multiplicity_sum_gt_degree P
        (points.filter (fun z => f.eval z = received z))
        (fun z => multiplicities (z, received z)) ?_ ?_
      · -- multiplicity at each agreement point via substitution–multiplicity transfer
        intro z hz
        have hz_points : z ∈ points := Finset.mem_of_mem_filter z hz
        have hz_eq : f.eval z = received z := (Finset.mem_filter.mp hz).2
        have hz_points' : (z, f.eval z) ∈ points.image (fun x => (x, received x)) := by
          rw [hz_eq]; exact Finset.mem_image_of_mem _ hz_points
        have h_mult_Q := hQ_mult (z, f.eval z) hz_points'
        have hmult_eq : multiplicities (z, received z) = multiplicities (z, f.eval z) := by rw [hz_eq]
        show multiplicities (z, received z) ≤ Polynomial.rootMultiplicity z P
        rw [hmult_eq]
        exact CodingTheory.Bounds.rootMultiplicity_aeval_ge Q f z
          (multiplicities (z, f.eval z)) (hPdef ▸ hPne) h_mult_Q
      · -- degree bound exceeded by the agreement
        exact lt_of_le_of_lt (natDegree_aeval_le Q deg_X deg_Y hQ_degX hQ_degY f) h_agree
  intro x
  rw [← aeval_eval_eq Q f x]
  show Polynomial.eval x P = 0
  rw [hP0, Polynomial.eval_zero]

/-- **Guruswami–Sudan list-decoding bound.** Interpolating a single `Q` from the received word,
*every* low-degree polynomial `f` that agrees with `received` on more than
`deg_X + deg_Y · deg(f)` (multiplicity-weighted) points makes the substitution `Q(X, f(X))`
vanish, hence is a `Y`-root of `Q`. As `Q` has `Y`-degree `≤ deg_Y`, there are at most `deg_Y`
such codewords.

This is the headline classical list-decoding theorem: it composes the interpolation
(`gkl24_interpolation_existence`), the per-codeword vanishing (`rootMultiplicity_aeval_ge` +
`bchks25_vanishing…`), and the list-size bound (`gs_list_size_bound`). -/
theorem gs_list_decoding_bound [DecidableEq F]
    (points : Finset F) (received : F → F) (multiplicities : (F × F) → ℕ) (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun x => (multiplicities (x, received x) + 1)
        * multiplicities (x, received x) / 2)) < (deg_X + 1) * (deg_Y + 1))
    (S : Finset (Polynomial F))
    (hS : ∀ f ∈ S,
      (points.filter (fun z => f.eval z = received z)).sum (fun z => multiplicities (z, received z))
        > deg_X + deg_Y * f.natDegree) :
    S.card ≤ deg_Y := by
  classical
  have h_dim' : ((points.image (fun x => (x, received x))).sum
      (fun p => (multiplicities p + 1) * multiplicities p / 2)) < (deg_X + 1) * (deg_Y + 1) := by
    rw [Finset.sum_image (fun x _ y _ h => (Prod.ext_iff.mp h).1)]
    exact h_dim
  obtain ⟨Q, hQ_neq, hQ_degX, hQ_degY, hQ_mult⟩ :=
    GKL24.gkl24_interpolation_existence (points.image (fun x => (x, received x)))
      multiplicities deg_X deg_Y h_dim'
  refine CodingTheory.Bounds.gs_list_size_bound Q hQ_neq deg_Y hQ_degY S ?_
  -- every `f ∈ S` annihilates `Q`: `Q(X, f(X)) = 0`.
  intro f hf
  set P : Polynomial F :=
    MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q with hPdef
  by_cases hPne : P = 0
  · exact hPne
  · refine BCHKS25.bchks25_vanishing_of_multiplicity_sum_gt_degree P
      (points.filter (fun z => f.eval z = received z))
      (fun z => multiplicities (z, received z)) ?_ ?_
    · intro z hz
      have hz_points : z ∈ points := Finset.mem_of_mem_filter z hz
      have hz_eq : f.eval z = received z := (Finset.mem_filter.mp hz).2
      have hz_points' : (z, f.eval z) ∈ points.image (fun x => (x, received x)) := by
        rw [hz_eq]; exact Finset.mem_image_of_mem _ hz_points
      have h_mult_Q := hQ_mult (z, f.eval z) hz_points'
      have hmult_eq : multiplicities (z, received z) = multiplicities (z, f.eval z) := by rw [hz_eq]
      show multiplicities (z, received z) ≤ Polynomial.rootMultiplicity z P
      rw [hmult_eq]
      exact CodingTheory.Bounds.rootMultiplicity_aeval_ge Q f z
        (multiplicities (z, f.eval z)) (hPdef ▸ hPne) h_mult_Q
    · exact lt_of_le_of_lt (natDegree_aeval_le Q deg_X deg_Y hQ_degX hQ_degY f) (hS f hf)

/-- **Sudan list-decoding radius** (multiplicity-`1` specialisation of `gs_list_decoding_bound`).
For `n = |points|` evaluation points and any degrees `deg_X, deg_Y` with `n < (deg_X+1)(deg_Y+1)`,
the number of polynomials of degree `< k` that agree with `received` on more than
`deg_X + deg_Y·(k-1)` points is at most `deg_Y`. Optimising `deg_X, deg_Y` recovers the Sudan
radius; here the parameters are left explicit. -/
theorem sudan_list_decoding_bound [DecidableEq F]
    (points : Finset F) (received : F → F) (k deg_X deg_Y : ℕ)
    (h_dim : points.card < (deg_X + 1) * (deg_Y + 1))
    (S : Finset (Polynomial F))
    (hdeg : ∀ f ∈ S, f.natDegree ≤ k - 1)
    (hagree : ∀ f ∈ S,
      (points.filter (fun z => f.eval z = received z)).card > deg_X + deg_Y * (k - 1)) :
    S.card ≤ deg_Y := by
  classical
  refine gs_list_decoding_bound points received (fun _ => 1) deg_X deg_Y ?_ S ?_
  · simpa using h_dim
  · intro f hf
    have hcard : (points.filter (fun z => f.eval z = received z)).sum
        (fun z => (fun _ => 1) (z, received z)) =
        (points.filter (fun z => f.eval z = received z)).card := by
      simp
    rw [hcard]
    calc deg_X + deg_Y * f.natDegree
        ≤ deg_X + deg_Y * (k - 1) := by gcongr; exact hdeg f hf
      _ < (points.filter (fun z => f.eval z = received z)).card := hagree f hf

end CodingTheory.Bounds.Capacity
