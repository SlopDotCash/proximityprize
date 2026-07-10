/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R385CrossGeneratorCovarianceBlindSpot

/-!
# R386: first incidence is the exact blind stratum of cross-generator covariance

R385 shows that an endpoint incident to exactly one generator is invisible to the off-diagonal
factorial moment.  Here we prove the quantitative converse: after splitting the weighted first
incidence moment into the strata `Z = 1` and `2 ≤ Z`, the entire multi-root stratum is bounded by
the off-diagonal moment `Z(Z-1)`.  Thus the unique-root mass is the only part of the positive
first incidence that a cross-generator pair estimate cannot control.

We also rewrite R384's centered endpoint sum exactly in terms of the unique-root mass, multi-root
mass, and total endpoint weight.  Any future estimate may therefore combine a genuinely new
first-incidence bound with an off-diagonal algebraic-geometric bound without double counting.

This is an unconditional finite combinatorial reduction.  It supplies no bound on the unique-root
mass and hence makes no CORE, cancellation, moment-saving, or capacity claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition

open ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount
open ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage
open ArkLib.ProximityGap.Frontier.R385CrossGeneratorCovarianceBlindSpot

variable {A D : Type*} [DecidableEq A] [DecidableEq D]

/-- Weighted mass of endpoints incident to exactly one generator. -/
def firstIncidenceMass (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] : ℕ :=
  ∑ d ∈ S with endpointIncidence T rel d = 1, w d

/-- Weighted first-incidence moment restricted to endpoints incident to at least two generators. -/
def multiIncidenceMass (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] : ℕ :=
  ∑ d ∈ S with 2 ≤ endpointIncidence T rel d, w d * endpointIncidence T rel d

/-- Weighted off-diagonal second factorial moment. -/
def offDiagIncidenceMass (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] : ℕ :=
  ∑ d ∈ S, w d * offDiagEndpointIncidence T rel d

/-- The first incidence moment splits exactly into its unique-root and multi-root strata. -/
theorem weightedIncidence_eq_first_add_multi
    (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] :
    (∑ d ∈ S, w d * endpointIncidence T rel d) =
      firstIncidenceMass T S w rel + multiIncidenceMass T S w rel := by
  classical
  simp only [firstIncidenceMass, multiIncidenceMass, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hzero : endpointIncidence T rel d = 0
  · simp [hzero]
  by_cases hone : endpointIncidence T rel d = 1
  · simp [hone]
  · have htwo : 2 ≤ endpointIncidence T rel d := by omega
    simp [hone, htwo]

/-- On the multi-root stratum, the first moment is bounded by the second factorial moment. -/
theorem multiIncidenceMass_le_offDiagIncidenceMass
    (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] :
    multiIncidenceMass T S w rel ≤ offDiagIncidenceMass T S w rel := by
  classical
  simp only [multiIncidenceMass, offDiagIncidenceMass, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro d hd
  by_cases htwo : 2 ≤ endpointIncidence T rel d
  · simp only [Finset.mem_filter, hd, htwo, and_self, ↓reduceIte]
    apply Nat.mul_le_mul_left
    rw [offDiagEndpointIncidence_eq]
    let z := endpointIncidence T rel d
    change z ≤ z * z - z
    calc
      z = z * 1 := by simp
      _ ≤ z * (z - 1) := Nat.mul_le_mul_left z (by omega)
      _ = z * z - z := by rw [Nat.mul_sub_left_distrib]; simp
  · simp only [Finset.mem_filter, hd, htwo, and_false, ↓reduceIte, zero_le]

/-- R384's centered weighted endpoint sum, rewritten through the exact first/multi split. -/
theorem sum_centeredEndpointIncidence_eq_first_multi
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) =
      q * ((firstIncidenceMass T S w rel : ℕ) : ℝ) +
        q * ((multiIncidenceMass T S w rel : ℕ) : ℝ) -
          (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) := by
  classical
  have hsplit := weightedIncidence_eq_first_add_multi T S w rel
  have hsplitReal :
      (∑ d ∈ S, (w d : ℝ) * (endpointIncidence T rel d : ℝ)) =
        (firstIncidenceMass T S w rel : ℝ) +
          (multiIncidenceMass T S w rel : ℝ) := by
    exact_mod_cast hsplit
  calc
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) =
        q * (∑ d ∈ S, (w d : ℝ) * (endpointIncidence T rel d : ℝ)) -
          (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) := by
      unfold centeredEndpointIncidence
      simp_rw [mul_sub]
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro d hd <;> ring
    _ = q * ((firstIncidenceMass T S w rel : ℕ) : ℝ) +
          q * ((multiIncidenceMass T S w rel : ℕ) : ℝ) -
            (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) := by
      rw [hsplitReal]
      ring

/-- If the unique-root stratum is empty, cross-generator covariance controls the full positive
first incidence moment.  This is the precise converse to R385's blind-spot example. -/
theorem weightedIncidence_le_offDiag_of_firstIncidenceMass_eq_zero
    (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel]
    (hfirst : firstIncidenceMass T S w rel = 0) :
    (∑ d ∈ S, w d * endpointIncidence T rel d) ≤ offDiagIncidenceMass T S w rel := by
  rw [weightedIncidence_eq_first_add_multi, hfirst, zero_add]
  exact multiIncidenceMass_le_offDiagIncidenceMass T S w rel

/-- **Hybrid first-incidence/covariance bound.**  For nonnegative field scale `q`, the centered
endpoint discrepancy is bounded by the unique-root mass plus the off-diagonal factorial moment.
This is the lossless consumer for the #505 strategy: algebraic geometry may control the covariance
term, and only a genuinely new estimate on `firstIncidenceMass` remains to close the bound. -/
theorem sum_centeredEndpointIncidence_le_first_add_offDiag
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] (hq : 0 ≤ q) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤
      q * ((firstIncidenceMass T S w rel : ℕ) : ℝ) +
        q * ((offDiagIncidenceMass T S w rel : ℕ) : ℝ) -
          (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) := by
  rw [sum_centeredEndpointIncidence_eq_first_multi]
  have hmultiNat := multiIncidenceMass_le_offDiagIncidenceMass T S w rel
  have hmulti :
      (multiIncidenceMass T S w rel : ℝ) ≤ (offDiagIncidenceMass T S w rel : ℝ) := by
    exact_mod_cast hmultiNat
  have hqmulti := mul_le_mul_of_nonneg_left hmulti hq
  linarith

/-- A modular CORE consumer.  Separate bounds on unique-root incidence and covariance add directly
inside the centered discrepancy budget. -/
theorem sum_centeredEndpointIncidence_le_of_first_of_offDiag
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel] (hq : 0 ≤ q)
    (U V : ℕ)
    (hfirst : firstIncidenceMass T S w rel ≤ U)
    (hoff : offDiagIncidenceMass T S w rel ≤ V) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤
      q * ((U + V : ℕ) : ℝ) - (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) := by
  refine (sum_centeredEndpointIncidence_le_first_add_offDiag q T S w rel hq).trans ?_
  have hfirstReal : (firstIncidenceMass T S w rel : ℝ) ≤ (U : ℝ) := by exact_mod_cast hfirst
  have hoffReal : (offDiagIncidenceMass T S w rel : ℝ) ≤ (V : ℝ) := by exact_mod_cast hoff
  push_cast
  have hqfirst := mul_le_mul_of_nonneg_left hfirstReal hq
  have hqoff := mul_le_mul_of_nonneg_left hoffReal hq
  linarith

/-- If every endpoint has at most one root, cross-generator covariance vanishes globally. -/
theorem offDiagIncidenceMass_eq_zero_of_forall_le_one
    (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel]
    (hZ : ∀ d ∈ S, endpointIncidence T rel d ≤ 1) :
    offDiagIncidenceMass T S w rel = 0 := by
  classical
  unfold offDiagIncidenceMass
  apply Finset.sum_eq_zero
  intro d hd
  rw [offDiagEndpointIncidence_eq_zero_of_le_one T rel d (hZ d hd), mul_zero]

/-- Under pointwise unique-root incidence, the entire weighted first moment is exactly the
unique-root mass; there is no multi-root contribution for covariance to estimate. -/
theorem weightedIncidence_eq_first_of_forall_le_one
    (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel]
    (hZ : ∀ d ∈ S, endpointIncidence T rel d ≤ 1) :
    (∑ d ∈ S, w d * endpointIncidence T rel d) = firstIncidenceMass T S w rel := by
  rw [weightedIncidence_eq_first_add_multi]
  suffices multiIncidenceMass T S w rel = 0 by omega
  classical
  unfold multiIncidenceMass
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_filter] at hd
  have hle := hZ d hd.1
  omega

/-- **Aggregate covariance no-go.**  If all realized endpoints have `Z ≤ 1`, the centered
discrepancy is exactly the unique-root contribution minus the uniform baseline, while the
off-diagonal covariance mass is zero.  Thus no bound using only distinct-generator pairs can see
any positive incidence in this regime. -/
theorem centered_eq_first_and_offDiag_eq_zero_of_forall_le_one
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel]
    (hZ : ∀ d ∈ S, endpointIncidence T rel d ≤ 1) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) =
        q * ((firstIncidenceMass T S w rel : ℕ) : ℝ) -
          (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ))
      ∧ offDiagIncidenceMass T S w rel = 0 := by
  constructor
  · rw [sum_centeredEndpointIncidence_eq_first_multi]
    have hoff := offDiagIncidenceMass_eq_zero_of_forall_le_one T S w rel hZ
    have hmulti := multiIncidenceMass_le_offDiagIncidenceMass T S w rel
    have : multiIncidenceMass T S w rel = 0 := by omega
    rw [this, Nat.cast_zero, mul_zero, add_zero]
  · exact offDiagIncidenceMass_eq_zero_of_forall_le_one T S w rel hZ

/-- **Exact first-incidence criterion in the covariance-free regime.**  When every endpoint has at
most one root, nonpositivity of the centered discrepancy is equivalent to weighted unique-root
incidence occurring no more often than the uniform density `card(T)/q`.  This is the precise
positive theorem required after the R386 covariance no-go. -/
theorem centered_nonpos_iff_q_mul_first_le_baseline_of_forall_le_one
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel]
    (hZ : ∀ d ∈ S, endpointIncidence T rel d ≤ 1) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤ 0 ↔
      q * ((firstIncidenceMass T S w rel : ℕ) : ℝ) ≤
        (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) := by
  rw [(centered_eq_first_and_offDiag_eq_zero_of_forall_le_one q T S w rel hZ).1]
  exact sub_nonpos

/-- Budgeted form of the exact criterion: a first-incidence excess allowance `W` is equivalent to
the same allowance for the centered discrepancy. -/
theorem centered_le_iff_q_mul_first_le_baseline_add_of_forall_le_one
    (q W : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ)
    (rel : A → D → Prop) [DecidableRel rel]
    (hZ : ∀ d ∈ S, endpointIncidence T rel d ≤ 1) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤ W ↔
      q * ((firstIncidenceMass T S w rel : ℕ) : ℝ) ≤
        (T.card : ℝ) * (∑ d ∈ S, (w d : ℝ)) + W := by
  rw [(centered_eq_first_and_offDiag_eq_zero_of_forall_le_one q T S w rel hZ).1]
  constructor <;> intro h <;> linarith

end ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.weightedIncidence_eq_first_add_multi
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.multiIncidenceMass_le_offDiagIncidenceMass
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.sum_centeredEndpointIncidence_eq_first_multi
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.weightedIncidence_le_offDiag_of_firstIncidenceMass_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.sum_centeredEndpointIncidence_le_first_add_offDiag
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.sum_centeredEndpointIncidence_le_of_first_of_offDiag
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.offDiagIncidenceMass_eq_zero_of_forall_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.weightedIncidence_eq_first_of_forall_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.centered_eq_first_and_offDiag_eq_zero_of_forall_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.centered_nonpos_iff_q_mul_first_le_baseline_of_forall_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R386FirstIncidenceFactorialDecomposition.centered_le_iff_q_mul_first_le_baseline_add_of_forall_le_one
