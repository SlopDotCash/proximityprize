/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R385CrossGeneratorCovarianceBlindSpot

/-!
# G77: first-incidence Jordan decomposition of the centered relation load

G76 proves that all distinct-generator factorial moments of order at least two identify the
zero-incidence and unique-incidence strata.  This file isolates exactly the missing statistic.
For endpoint incidence `Z`, field scale `q`, and generator count `t`,

```text
q Z - t = (q-t) 1[Z>0] + q (Z-1)_+ - t 1[Z=0].
```

After weighting and summing endpoints, the centered load is therefore the difference of three
pointwise nonnegative masses (when `q >= t`): first-incidence coverage, excess multiplicity after
the first incidence, and uncovered mass.  In particular there is no signed cancellation between
distinct *covered* relation orbits.  All negative mass is supported on endpoints with no relation;
all incidence multiplicity beyond the first hit is an additional positive tax.

The resulting inequality is an iff, so replacing the centered anomaly by a first-incidence
formulation does not create quantitative slack: one must bound the weighted covered mass together
with its excess multiplicity against the uncovered mass.  This is the precise binary
coverage-discrepancy wall left open by G75/G76.

Issue #505.  No CORE closure is claimed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G77FirstIncidenceJordanDecomposition

open ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount
open ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage
open ArkLib.ProximityGap.Frontier.R385CrossGeneratorCovarianceBlindSpot

variable {A D : Type*} [DecidableEq A] [DecidableEq D]

/-- Endpoints carrying at least one incidence. -/
def coveredEndpoints (T : Finset A) (S : Finset D) (rel : A → D → Prop)
    [DecidableRel rel] : Finset D :=
  S.filter fun d => 0 < endpointIncidence T rel d

/-- Endpoints carrying no incidence. -/
def uncoveredEndpoints (T : Finset A) (S : Finset D) (rel : A → D → Prop)
    [DecidableRel rel] : Finset D :=
  S.filter fun d => endpointIncidence T rel d = 0

/-- Weighted mass of endpoints carrying at least one incidence. -/
noncomputable def coveredWeight
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] : ℝ :=
  ∑ d ∈ coveredEndpoints T S rel, (w d : ℝ)

/-- Weighted mass of endpoints carrying no incidence. -/
noncomputable def uncoveredWeight
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] : ℝ :=
  ∑ d ∈ uncoveredEndpoints T S rel, (w d : ℝ)

/-- Incidence multiplicity remaining after assigning the first hit of each covered endpoint to
the binary coverage term. -/
noncomputable def excessIncidenceWeight
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] : ℝ :=
  ∑ d ∈ S, (w d : ℝ) * (endpointIncidence T rel d - 1 : ℕ)

/-- Weighted ordered distinct-generator covariance mass. -/
noncomputable def offDiagIncidenceWeight
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] : ℝ :=
  ∑ d ∈ S, (w d : ℝ) * offDiagEndpointIncidence T rel d

/-- **Pointwise first-incidence decomposition.** -/
theorem centeredEndpointIncidence_eq_first_add_excess_sub_uncovered
    (q : ℝ) (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D) :
    centeredEndpointIncidence q T rel d =
      (q - T.card) * (if 0 < endpointIncidence T rel d then 1 else 0) +
        q * (endpointIncidence T rel d - 1 : ℕ) -
          T.card * (if endpointIncidence T rel d = 0 then 1 else 0) := by
  unfold centeredEndpointIncidence
  by_cases hzero : endpointIncidence T rel d = 0
  · simp [hzero]
  · have hpos : 0 < endpointIncidence T rel d := Nat.pos_of_ne_zero hzero
    have hone : 1 ≤ endpointIncidence T rel d := hpos
    rw [if_pos hpos, if_neg hzero]
    push_cast [Nat.cast_sub hone]
    ring

/-- Covered and uncovered endpoints partition the ambient endpoint set. -/
theorem coveredWeight_add_uncoveredWeight_eq
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] :
    coveredWeight T S w rel + uncoveredWeight T S w rel = ∑ d ∈ S, (w d : ℝ) := by
  classical
  unfold coveredWeight uncoveredWeight coveredEndpoints uncoveredEndpoints
  have hfilter :
      S.filter (fun d => endpointIncidence T rel d = 0) =
        S.filter (fun d => ¬ 0 < endpointIncidence T rel d) := by
    ext d
    simp
  rw [hfilter]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := S) (p := fun d => 0 < endpointIncidence T rel d) (f := fun d => (w d : ℝ))]

/-- **Weighted Jordan decomposition.** The exact centered endpoint load is coverage plus excess
multiplicity minus uncovered mass. -/
theorem sum_centeredEndpointIncidence_eq_jordan
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) =
      (q - T.card) * coveredWeight T S w rel +
        q * excessIncidenceWeight T S w rel -
          T.card * uncoveredWeight T S w rel := by
  classical
  have hcovered :
      (∑ d ∈ S, (w d : ℝ) * (if 0 < endpointIncidence T rel d then 1 else 0)) =
        coveredWeight T S w rel := by
    unfold coveredWeight coveredEndpoints
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : 0 < endpointIncidence T rel d <;> simp [h]
  have huncovered :
      (∑ d ∈ S, (w d : ℝ) * (if endpointIncidence T rel d = 0 then 1 else 0)) =
        uncoveredWeight T S w rel := by
    unfold uncoveredWeight uncoveredEndpoints
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : endpointIncidence T rel d = 0 <;> simp [h]
  calc
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) =
        ∑ d ∈ S,
          ((q - T.card) * ((w d : ℝ) *
              (if 0 < endpointIncidence T rel d then 1 else 0)) +
            q * ((w d : ℝ) * (endpointIncidence T rel d - 1 : ℕ)) -
            T.card * ((w d : ℝ) *
              (if endpointIncidence T rel d = 0 then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [centeredEndpointIncidence_eq_first_add_excess_sub_uncovered q T rel d]
      ring
    _ = (q - T.card) * coveredWeight T S w rel +
          q * excessIncidenceWeight T S w rel -
            T.card * uncoveredWeight T S w rel := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        hcovered, huncovered]
      rfl

/-- The first-incidence formulation is quantitatively equivalent to the original centered-load
bound.  There is no averaging or orbit-size slack to harvest. -/
theorem centeredLoad_le_iff_firstIncidenceJordan_le
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (W : ℝ) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤ W ↔
      (q - T.card) * coveredWeight T S w rel +
          q * excessIncidenceWeight T S w rel ≤
        W + T.card * uncoveredWeight T S w rel := by
  rw [sum_centeredEndpointIncidence_eq_jordan]
  constructor <;> intro h <;> linarith

/-- **Cross-generator consumer bridge.** For a uniform generator family, the exact first-hit
Jordan expression is `card(T)` times the original one-generator centered load. -/
theorem card_mul_centeredLoad_eq_firstIncidenceJordan
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (L : ℝ)
    (huniform : ∀ a ∈ T, centeredGeneratorLoad q S w rel a = L) :
    (T.card : ℝ) * L =
      (q - T.card) * coveredWeight T S w rel +
        q * excessIncidenceWeight T S w rel -
          T.card * uncoveredWeight T S w rel := by
  rw [← sum_centeredEndpointIncidence_eq_jordan]
  exact card_mul_centeredLoad_eq q T S w rel L huniform

/-- **No-slack verdict at the production abstraction.** For a nonempty uniform generator family,
bounding the positive first-hit-plus-excess mass against the uncovered mass is equivalent to
bounding the original centered load, with exactly the unavoidable `card(T)` factor. -/
theorem centeredLoad_le_iff_firstIncidenceJordan_le_of_uniform
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (L W : ℝ) (hT : T.Nonempty)
    (huniform : ∀ a ∈ T, centeredGeneratorLoad q S w rel a = L) :
    L ≤ W ↔
      (q - T.card) * coveredWeight T S w rel +
          q * excessIncidenceWeight T S w rel ≤
        (T.card : ℝ) * W + T.card * uncoveredWeight T S w rel := by
  have hEq := card_mul_centeredLoad_eq_firstIncidenceJordan q T S w rel L huniform
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Every term in the excess-multiplicity mass is nonnegative. -/
theorem excessIncidenceWeight_nonneg
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] :
    0 ≤ excessIncidenceWeight T S w rel := by
  unfold excessIncidenceWeight
  positivity

/-- The sharp pointwise comparison: after the unique-incidence stratum is removed, the second
factorial moment pays every remaining incidence with factor two.  Equality holds at incidence
two, so the constant cannot be improved in this abstraction. -/
theorem two_mul_excess_le_offDiagEndpointIncidence
    (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D) :
    (2 : ℝ) * (endpointIncidence T rel d - 1 : ℕ) ≤
      offDiagEndpointIncidence T rel d := by
  rw [offDiagEndpointIncidence_eq]
  let Z := endpointIncidence T rel d
  change (2 : ℝ) * (Z - 1 : ℕ) ≤ (Z * Z - Z : ℕ)
  by_cases hzero : Z = 0
  · simp [Z, hzero]
  by_cases hone : Z = 1
  · simp [Z, hone]
  have htwo : 2 ≤ Z := by omega
  have honele : 1 ≤ Z := by omega
  have hZmul : Z ≤ Z * Z := by
    exact Nat.le_mul_of_pos_right Z (Nat.pos_of_ne_zero hzero)
  push_cast [Nat.cast_sub honele, Nat.cast_sub hZmul]
  have htwo' : (2 : ℝ) ≤ Z := by exact_mod_cast htwo
  have honele' : (1 : ℝ) ≤ Z := by exact_mod_cast honele
  have hprod : (0 : ℝ) ≤ ((Z : ℝ) - 1) * ((Z : ℝ) - 2) :=
    mul_nonneg (sub_nonneg.mpr honele') (sub_nonneg.mpr htwo')
  nlinarith

/-- **Covariance discharges all excess multiplicity.** The weighted second factorial moment is at
least twice the full excess-incidence tax.  Thus R385/G76's blind spot is exactly binary first
coverage, not multiplicity `Z ≥ 2`. -/
theorem two_mul_excessIncidenceWeight_le_offDiagIncidenceWeight
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] :
    2 * excessIncidenceWeight T S w rel ≤ offDiagIncidenceWeight T S w rel := by
  unfold excessIncidenceWeight offDiagIncidenceWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  calc
    2 * ((w d : ℝ) * (endpointIncidence T rel d - 1 : ℕ)) =
        (w d : ℝ) * (2 * (endpointIncidence T rel d - 1 : ℕ)) := by ring
    _ ≤ (w d : ℝ) * offDiagEndpointIncidence T rel d :=
      mul_le_mul_of_nonneg_left
        (two_mul_excess_le_offDiagEndpointIncidence T rel d) (by positivity)

/-- With nonnegative field scale, covariance gives a complete upper bound for the excess term.
Only the binary covered-versus-uncovered discrepancy remains outside this bound. -/
theorem sum_centeredEndpointIncidence_le_coverage_add_half_covariance
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (hq : 0 ≤ q) :
    (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤
      (q - T.card) * coveredWeight T S w rel +
        (q / 2) * offDiagIncidenceWeight T S w rel -
          T.card * uncoveredWeight T S w rel := by
  rw [sum_centeredEndpointIncidence_eq_jordan]
  have hcov := two_mul_excessIncidenceWeight_le_offDiagIncidenceWeight T S w rel
  nlinarith

/-- At field scale at least the number of generators, every covered endpoint has nonnegative
centered coefficient.  Hence two covered relation orbits cannot cancel each other by sign. -/
theorem centeredEndpointIncidence_nonneg_of_covered
    (q : ℝ) (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D)
    (hq : (T.card : ℝ) ≤ q) (hcovered : 0 < endpointIncidence T rel d) :
    0 ≤ centeredEndpointIncidence q T rel d := by
  unfold centeredEndpointIncidence
  have hZ : (1 : ℝ) ≤ endpointIncidence T rel d := by exact_mod_cast hcovered
  nlinarith

/-- An uncovered endpoint has exactly the negative coefficient `-card(T)`. -/
theorem centeredEndpointIncidence_eq_neg_card_of_uncovered
    (q : ℝ) (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D)
    (huncovered : endpointIncidence T rel d = 0) :
    centeredEndpointIncidence q T rel d = -(T.card : ℝ) := by
  simp [centeredEndpointIncidence, huncovered]

#print axioms centeredEndpointIncidence_eq_first_add_excess_sub_uncovered
#print axioms coveredWeight_add_uncoveredWeight_eq
#print axioms sum_centeredEndpointIncidence_eq_jordan
#print axioms centeredLoad_le_iff_firstIncidenceJordan_le
#print axioms card_mul_centeredLoad_eq_firstIncidenceJordan
#print axioms centeredLoad_le_iff_firstIncidenceJordan_le_of_uniform
#print axioms excessIncidenceWeight_nonneg
#print axioms two_mul_excess_le_offDiagEndpointIncidence
#print axioms two_mul_excessIncidenceWeight_le_offDiagIncidenceWeight
#print axioms sum_centeredEndpointIncidence_le_coverage_add_half_covariance
#print axioms centeredEndpointIncidence_nonneg_of_covered
#print axioms centeredEndpointIncidence_eq_neg_card_of_uncovered

end ArkLib.ProximityGap.Frontier.G77FirstIncidenceJordanDecomposition
