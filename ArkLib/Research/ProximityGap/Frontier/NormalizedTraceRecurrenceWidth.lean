/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.NormalizedTripleEnergy
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Width of a scalar recurrence for the normalized third-energy histogram

For nonzero weights and distinct field elements, the scalar exponential trace
has no annihilating polynomial of degree below its number of occupied bins.
The sixth-moment bound forces quadratically many such bins. The implication
applies to constant-coefficient scalar recurrences and, on nonzero nodes over
a prime field, to recurrences with coefficients depending on the offset mod p.
-/

set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.NormalizedTraceRecurrenceWidth

variable {F : Type*} [Field F]

/-- The scalar trace of a finite weighted signature histogram. -/
def traceSeq (U : Finset F) (w : F → F) (j : ℕ) : F := ∑ u ∈ U, w u * u^j

/-- The coefficients of P give a recurrence valid at every offset j. -/
def Annihilates (P : F[X]) (s : ℕ → F) : Prop :=
  ∀ j, P.sum (fun i c => c * s (j+i)) = 0

private theorem shifted_trace (P : F[X]) (U : Finset F) (w : F → F) (j : ℕ) :
    P.sum (fun i c => c * traceSeq U w (j+i)) =
      ∑ u ∈ U, (w u*P.eval u)*u^j := by
  simp only [traceSeq, Polynomial.sum_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
  exact sum_congr rfl fun i _ => by rw [pow_add]; ring

/-- A polynomial annihilates the trace iff it vanishes at every weighted node. -/
theorem annihilates_iff (P : F[X]) (U : Finset F) (w : F → F)
    (hw : ∀ u ∈ U, w u ≠ 0) :
    Annihilates P (traceSeq U w) ↔ ∀ u ∈ U, P.eval u = 0 := by
  classical
  constructor
  · intro h
    let e : Fin U.card ≃ U := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
    let r (i : Fin U.card) : F := e i
    let c (i : Fin U.card) : F := w (r i)*P.eval (r i)
    have hv (j : Fin U.card) : ∑ i, c i * (r i)^j.val = 0 := by
      have hz := h j.val
      rw [shifted_trace, ← Finset.sum_coe_sort U] at hz
      exact (e.sum_comp (fun u : U => (w (u:F)*P.eval (u:F))*(u:F)^j.val)).trans hz
    have hc := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := r) (v := c) (Subtype.val_injective.comp e.injective) hv
    intro u hu
    let i := e.symm ⟨u,hu⟩
    have he : r i = u := by simp [r,i]
    have hzero : c i = 0 := congrFun hc i
    exact (mul_eq_zero.mp (by simpa only [c, he] using hzero)).resolve_left (hw u hu)
  · intro hp j
    rw [shifted_trace]
    exact sum_eq_zero fun u hu => by rw [hp u hu, mul_zero, zero_mul]

/-- The least recurrence degree equals the number of occupied bins, regardless of their ordering. -/
theorem min_degree (U : Finset F) (w : F → F) (hw : ∀ u ∈ U, w u ≠ 0) :
    (∀ P : F[X], P ≠ 0 → Annihilates P (traceSeq U w) → U.card ≤ P.natDegree) ∧
      ∃ P : F[X], P ≠ 0 ∧ Annihilates P (traceSeq U w) ∧ P.natDegree = U.card := by
  classical
  constructor
  · intro P hP ha
    by_contra! h
    exact hP (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P U ((annihilates_iff P U w hw).mp ha) h)
  · let P : F[X] := ∏ u ∈ U, (X-C u)
    refine ⟨P, (Polynomial.monic_prod_of_monic _ _ (fun u _ => monic_X_sub_C u)).ne_zero,
      (annihilates_iff _ _ _ hw).mpr ?_, ?_⟩
    · intro u hu
      simp [P, Polynomial.eval_prod, Finset.prod_eq_zero hu]
    · simp [P, Polynomial.natDegree_prod_of_monic U (fun u : F => X - C u) (fun u _ => monic_X_sub_C u)]

/-- Coefficients may vary with the offset modulo the prime. At each residue where
the shift polynomial is nonzero, its degree still covers the whole nonzero support. -/
theorem periodic_recurrence_degree {p : ℕ} [Fact p.Prime]
    (U : Finset (ZMod p)) (w : ZMod p → ZMod p)
    (hw : ∀ u ∈ U, w u ≠ 0) (hu : ∀ u ∈ U, u ≠ 0)
    (P : ZMod p → (ZMod p)[X])
    (hrec : ∀ j : ℕ, (P (j : ZMod p)).sum
      (fun i c => c * traceSeq U w (j+i)) = 0)
    (a : ℕ) (ha : P (a : ZMod p) ≠ 0) : U.card ≤ (P (a : ZMod p)).natDegree := by
  apply (min_degree U (fun u => w u*u^a)
    (fun u h => mul_ne_zero (hw u h) (pow_ne_zero _ (hu u h)))).1 _ ha
  intro k
  have hz := hrec (a+p*k)
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at hz
  rw [shifted_trace] at hz ⊢
  convert hz using 1
  apply Finset.sum_congr rfl
  intro u _
  rw [pow_add, pow_mul, ZMod.pow_card]
  ring

variable [DecidableEq F] [Fintype F]
open NormalizedTripleEnergy (profile)

/-- Occupied signatures of ordered normalized pairs. -/
def occupied (H : Finset F) (n : ℕ) : Finset F :=
  (H ×ˢ H).image (fun P => (1+P.1+P.2)^n)

/-- The literal third energy bounds the reciprocal occupancy of its pair histogram. -/
theorem occupancy_bound {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x^n=1) (hpos : 0 < H.card) :
    H.card ^ 5 ≤ (occupied H n).card *
      ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.addEnergy3 H := by
  let U := occupied H n
  let m := profile H n
  have mass : ∑ u ∈ U, m u = H.card^2 := by
    simpa [U, occupied, m, profile, pow_two] using
      (Finset.card_eq_sum_card_image (fun P : F × F => (1+P.1+P.2)^n) (H ×ˢ H)).symm
  have hcs : (H.card^2)^2 ≤ U.card * ∑ u ∈ U, (m u)^2 := by
    simpa [mass] using Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1:ℕ)) m
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u => (m u)^2)
    (Finset.subset_univ U) (fun _ _ _ => Nat.zero_le _)
  have hnorm : H.card * ∑ u ∈ U, (m u)^2 ≤
      ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.addEnergy3 H := by
    apply (Nat.mul_le_mul_left H.card hsum).trans
    rw [NormalizedTripleEnergy.addEnergy3_eq_profile hn hH,
      ← Finset.add_sum_erase (univ : Finset F) (fun u => (m u)^2) (mem_univ 0)]
    change H.card * ((m 0)^2 + _) ≤ (H.card * m 0)^2 + _
    rw [Nat.mul_add, mul_pow]
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul_right _ (by nlinarith [Nat.mul_le_mul_left H.card (show 1 ≤ H.card by omega)])
  calc
    H.card^5 = H.card * (H.card^2)^2 := by ring
    _ ≤ H.card * (U.card * ∑ u ∈ U, (m u)^2) := Nat.mul_le_mul_left _ hcs
    _ = U.card * (H.card * ∑ u ∈ U, (m u)^2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left U.card hnorm

/-- At production the unit Wick upper bound already requires at least this many bins. -/
theorem production_min_bins (d E : ℕ) (h : (2^30)^5 ≤ d*E)
    (hwick : E ≤ 15*(2^30)^3) : 76861433640456466 ≤ d := by
  have ht := h.trans (Nat.mul_le_mul_left d hwick)
  norm_num at ht
  omega

/-- On the literal size-2^30 histogram in a sufficiently large prime field, a true
unit sixth-moment bound forces quadratic recurrence degree even after reducing coefficients mod p. -/
theorem production_recurrence_degree {p : ℕ} [Fact p.Prime] (hp : 2^60 < p)
    {H : Finset (ZMod p)} (hcard : H.card = 2^30)
    (hroots : ∀ x, x ∈ H ↔ x^(2^30:ℕ)=1)
    (henergy : ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.addEnergy3 H ≤ 15*(2^30)^3)
    {P : (ZMod p)[X]} (hP : P ≠ 0)
    (hrec : Annihilates P (traceSeq (occupied H (2^30)) (fun u => (profile H (2^30) u : ZMod p)))) :
    76861433640456466 ≤ P.natDegree := by
  let n : ℕ := 2^30
  have hwidth := occupancy_bound (H := H) (n := n) (by decide) hroots (by rw [hcard]; decide)
  rw [hcard] at hwidth
  have hb := production_min_bins _ _ hwidth henergy
  apply hb.trans
  apply (min_degree (occupied H n) (fun u => (profile H n u : ZMod p)) ?_).1 _ hP hrec
  intro u hu hzero
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hu
  have hpos : 0 < profile H n u := Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, he⟩⟩
  have hmax : profile H n u ≤ 2^60 := by
    apply (Finset.card_filter_le _ _).trans
    rw [Finset.card_product, hcard]
    decide
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact (not_le_of_gt (hmax.trans_lt hp)) (Nat.le_of_dvd hpos hdiv)

#print axioms production_recurrence_degree
#print axioms annihilates_iff
#print axioms min_degree
#print axioms periodic_recurrence_degree
#print axioms occupancy_bound
#print axioms production_min_bins

end ArkLib.ProximityGap.Frontier.NormalizedTraceRecurrenceWidth
