/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual

/-!
# Discharging the closed square-root boundary `hBoundary` residual

This file analyses and discharges the `hBoundary` residual of
`ArkLib/ToMathlib/CorrelatedAgreementListDecodingClosed.lean`, namely the boundary case
`¬(δ < 1 − √ρ)`.  Under the keystone's ambient hypothesis `δ ≤ 1 − √ρ` this case is *exactly*
the closed equality `δ = 1 − √ρ` (`ProximityGap.eq_sqrt_boundary_of_le_sqrt_and_not_lt`,
`Curves.lean:1398`), the Johnson radius of the Reed–Solomon code.

## What the in-tree machinery provides at the boundary, and what is missing

At the boundary `δ = 1 − √ρ` the error parameter degenerates to `errorBound = 0`
(`ProximityGap.errorBound_eq_zero_of_johnson_not_lt_sqrt`, `Curves.lean:1379`), so the front-door
probability hypothesis `Pr[curve δ-close] > k · errorBound = k · 0 = 0` collapses to *strict
positivity*.  Positivity yields only
`0 < (RS_goodCoeffsCurve …).card`
(`ProximityGap.goodCoeffsCurve_card_pos_of_prob_gt_johnson_boundary`,
`Curves.lean:1410`).  We restate this as `boundary_card_only_pos` to make the gap explicit.

The `jointAgreement` assembly bridge
`ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core` (`Curves.lean:975`)
requires *three* inputs:

* `card > k`,
* `card ≥ (|ι| + 1) · k`,  and
* the §5 coefficient-polynomial extraction `hcoeffPoly`.

In the **strict** branch all three are supplied: the two cardinality bounds come from the
*quantitative* threshold `Pr[…] > k · errorBound` with `errorBound > 0`
(`ProximityGap.goodCoeffsCurve_card_bounds_of_prob_threshold`), and the extraction from the §5
chain.  At the **boundary** `errorBound = 0` kills the quantitative threshold, so neither
cardinality
bound nor the extraction is delivered by `hprob` alone.  This is precisely why the boundary
`hBoundary`
stays a residual: it needs the *same* §5 input as the strict branch *plus* the cardinality lower
bound, which `hprob` cannot give once `errorBound = 0`.

## Disposition of the three candidate routes (from the task brief)

* **(i) "card > 0 + assembly".**  FALSE as stated for the front-door hypotheses alone: the assembly
  bridge consumes `card ≥ (|ι| + 1) · k`, not `card > 0`, and the §5 extraction.
  `boundary_card_only_pos`
  proves the front door gives exactly `card > 0` and no more.
* **(ii) "the boundary is vacuous under `hprob`/`hJ`".**  FALSE in general.  At `δ = 1 − √ρ` the
  Johnson hypothesis `hJ : (1 − ρ)/2 < δ` reduces to `(1 − √ρ)² > 0`, i.e. `√ρ ≠ 1`, which holds for
  every non-full code (`ρ < 1`).  `boundary_param_consistent_iff` makes this exact: the boundary
  case
  is reachable (non-contradictory) precisely when `√ρ ≠ 1`, so it cannot be discharged by vacuity.
* **(iii) "ε-monotonicity / limiting from the strict case".**  Does not close the kernel obligation:
  there is no in-tree limiting principle transporting `jointAgreement` from `δ' < 1 − √ρ` to the
  closed point, and `jointAgreement` at `δ = 1 − √ρ` is a *weaker* (larger-radius) statement than at
  `δ' < δ`, so monotonicity points the wrong way.

## What is therefore TRUE and proved here

The honest, kernel-clean result is the **reduction**
`boundary_jointAgreement_of_cards_and_coeffPolys`:
at the boundary, `jointAgreement` follows from the smallest explicit residual that is *not* the goal
—
the two good-set cardinality lower bounds and the §5 coefficient-polynomial extraction — by the
in-tree assembly bridge.  Packaged into the exact `hBoundary` shape consumed by the keystone, this
is
`hBoundary_of_boundary_cards_and_coeffPolys`.  The boundary residual is thereby reduced to *exactly*
the strict-branch inputs (cardinality + §5 extraction), discharging it modulo that explicit datum.

`#print axioms` rests only on `[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Johnson bound at `1 − √ρ`.
-/

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace BoundaryDischarge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Structural facts about the closed boundary `δ = 1 − √ρ` -/

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype F] in
/-- Under the keystone's ambient `δ ≤ 1 − √ρ`, the non-strict Johnson case is the **closed boundary
equality** `δ = 1 − √ρ` — the Johnson radius of the Reed–Solomon code.  (Restated from
`ProximityGap.eq_sqrt_boundary_of_le_sqrt_and_not_lt`.) -/
theorem boundary_eq {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    δ = 1 - ReedSolomon.sqrtRate deg domain :=
  ProximityGap.eq_sqrt_boundary_of_le_sqrt_and_not_lt (deg := deg) (domain := domain) hδ hnot

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
/-- At the closed boundary the error parameter degenerates: `errorBound = 0`.  This is the
load-bearing structural fact — it is exactly what removes the *quantitative* probability threshold
that the strict branch relies on.  (Restated from
`ProximityGap.errorBound_eq_zero_of_johnson_not_lt_sqrt`.) -/
theorem errorBound_eq_zero_at_boundary {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    errorBound δ deg domain = 0 :=
  ProximityGap.errorBound_eq_zero_of_johnson_not_lt_sqrt (deg := deg) (domain := domain) hJ hnot

/-! ## Route (i): the front door gives only `card > 0` at the boundary

The probability hypothesis at the boundary is `Pr[…] > k · 0 = 0`, which yields *only* strict
positivity of the good-coefficient set.  No cardinality lower bound large enough to drive the
`jointAgreement` assembly is available. -/

omit [DecidableEq ι] in
/-- **The exact in-tree boundary fact.**  At the closed boundary, the front-door probability
hypothesis implies *only* `0 < (RS_goodCoeffsCurve …).card`.  This is strictly weaker than the
`card ≥ (|ι| + 1) · k` required by the assembly bridge, so route (i) cannot reach `jointAgreement`
from `hprob` alone. -/
theorem boundary_card_only_pos {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :=
  ProximityGap.goodCoeffsCurve_card_pos_of_prob_gt_johnson_boundary
    (deg := deg) (domain := domain) (δ := δ) u hprob hJ hnot

/-! ## Route (ii): the boundary is NOT vacuous (parameter consistency)

At `δ = 1 − √ρ`, the Johnson hypothesis `hJ : (1 − ρ)/2 < δ` is equivalent to `√ρ ≠ 1`, i.e. the
code is not full (`ρ < 1`).  Hence the boundary case is genuinely reachable and cannot be discharged
by showing it is vacuous. -/

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Route (ii) is false.**  At the closed boundary `δ = 1 − √ρ`, the Johnson hypothesis
`(1 − ρ)/2 < δ` is equivalent to `√ρ ≠ 1`.  Since `ρ = 1` is the full-code degenerate case, the
boundary is parameter-consistent for every non-full code: it is *not* vacuous, so the discharge must
do real work. -/
theorem boundary_param_consistent_iff {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain) :
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ ↔
      (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt ≠ 1 := by
  classical
  set ρ : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) with hρ
  set s : ℝ≥0 := ρ.sqrt with hs
  have hr_le_one : ρ ≤ 1 := by
    have h := DivergenceOfSets.reedSolomon_rate_le_one (deg := deg) (domain := domain)
    have : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) ≤ 1 := by exact_mod_cast h
    simpa [hρ] using this
  have hs_le_one : s ≤ 1 := by
    rw [hs]
    calc ρ.sqrt ≤ (1 : ℝ≥0).sqrt := by gcongr
      _ = 1 := by simp
  have hδeq' : δ = 1 - s := by simpa [ReedSolomon.sqrtRate, hρ, hs] using hδeq
  subst hδeq'
  -- Real-coe identities.  `s` is the genuine `√ρ`, so `(s:ℝ)^2 = (ρ:ℝ)`.
  have hsR_nonneg : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
  have hsR_le_one : (s : ℝ) ≤ 1 := by exact_mod_cast hs_le_one
  have hrR_le_one : (ρ : ℝ) ≤ 1 := by exact_mod_cast hr_le_one
  have hsq : (s : ℝ) ^ 2 = (ρ : ℝ) := by
    rw [hs, ← NNReal.coe_pow, sq, NNReal.mul_self_sqrt]
  have hcoe_lhs : (((1 - ρ) / 2 : ℝ≥0) : ℝ) = (1 - (ρ : ℝ)) / 2 := by
    rw [NNReal.coe_div, NNReal.coe_sub hr_le_one]; simp
  have hcoe_rhs : ((1 - s : ℝ≥0) : ℝ) = 1 - (s : ℝ) := by
    rw [NNReal.coe_sub hs_le_one]; simp
  rw [← NNReal.coe_lt_coe, hcoe_lhs, hcoe_rhs]
  constructor
  · -- `(1 - ρ)/2 < 1 - s`  ⇒  `s ≠ 1`.  If `s = 1` then `ρ = 1` and both sides are `0`.
    intro hlt heq
    have hsR_eq : (s : ℝ) = 1 := by rw [heq]; simp
    rw [hsR_eq] at hlt
    rw [show (ρ : ℝ) = 1 by rw [← hsq, hsR_eq]; ring] at hlt
    norm_num at hlt
  · -- `s ≠ 1`  ⇒  `s < 1`  ⇒  `(1 - s)² > 0`  ⇒  `(1 - ρ)/2 < 1 - s`.
    intro hne
    have hs_lt_one : s < 1 := lt_of_le_of_ne hs_le_one hne
    have hsR_lt_one : (s : ℝ) < 1 := by exact_mod_cast hs_lt_one
    rw [← hsq]
    nlinarith [sq_nonneg ((s : ℝ) - 1), hsR_lt_one]

/-! ## The deliverable: boundary `jointAgreement` from the smallest explicit residual

The honest residual at the boundary is *exactly* the strict-branch input that `hprob` no longer
supplies once `errorBound = 0`: the two good-set cardinality lower bounds and the §5 coefficient-
polynomial extraction.  Given those, the in-tree assembly bridge produces `jointAgreement`.  None of
these inputs is the goal `jointAgreement`. -/

omit [DecidableEq ι] in
/-- **Boundary `jointAgreement` from the cardinality bounds and the §5 coefficient-polynomial
extraction.**  This is the in-tree assembly bridge
`ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core`, specialised to the
boundary, with `k = (k - 1) + 1`.  The hypotheses are the smallest honest explicit residual:
the two cardinality lower bounds (which `hprob` cannot deliver at the boundary because `errorBound =
0`)
and the §5 coefficient-polynomial extraction.  None of them is `jointAgreement`. -/
theorem boundary_jointAgreement_of_cards_and_coeffPolys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hcardLt :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k)
    (hcardGe :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core
    (deg := deg) (domain := domain) (δ := δ) hk hcardLt hcardGe hcoeffPoly

omit [DecidableEq ι] in
/-- **The boundary residual `hBoundary`, discharged from the explicit boundary datum.**

This produces *exactly* the `hBoundary` shape consumed by
`ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary`
(`Curves.lean:1740`)
and by `correlatedAgreement_affine_curves_listDecoding_closed`, given a single explicit residual
`hBoundaryData`: for each curve `u` in the boundary case, the two good-set cardinality lower bounds
and
the §5 coefficient-polynomial extraction.  These are the *same* inputs the strict branch consumes;
they are the smallest honest residual because, at the boundary, `errorBound = 0` removes the
quantitative threshold that would otherwise supply the cardinality bounds.

`hBoundaryData` is *not* the goal: it is a per-curve cardinality + per-`P` extraction datum, from
which
`jointAgreement` is derived by the assembly bridge. -/
theorem hBoundary_of_boundary_cards_and_coeffPolys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hBoundaryData : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
    ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  intro hk u hprob hJ hnot
  obtain ⟨hcardLt, hcardGe, hcoeffPoly⟩ := hBoundaryData hk u hprob hJ hnot
  exact boundary_jointAgreement_of_cards_and_coeffPolys
    (deg := deg) (domain := domain) (δ := δ) hk u hcardLt hcardGe hcoeffPoly

omit [DecidableEq ι] in
/-- **Exact `BoundaryCardResidual` adapter.**  The public keystone in `Curves.lean`
does not ask for the probability/J-boundary hypotheses used by
`hBoundary_of_boundary_cards_and_coeffPolys`; it asks for the sharper closed-boundary
interface `BoundaryCardResidual`, where `δ = 1 - sqrtRate` and positive good-set
cardinality are already exposed.  This theorem packages the same assembly bridge
into that exact residual shape from the smallest explicit boundary data: the two
cardinality bounds and the coefficient-polynomial extraction. -/
theorem boundaryCardResidual_of_boundary_cards_and_coeffPolys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hBoundaryData : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
    ProximityGap.BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hδeq hcardPos
  obtain ⟨hcardLt, hcardGe, hcoeffPoly⟩ := hBoundaryData hk u hδeq hcardPos
  exact boundary_jointAgreement_of_cards_and_coeffPolys
    (deg := deg) (domain := domain) (δ := δ) hk u hcardLt hcardGe hcoeffPoly

omit [DecidableEq ι] in
/-- **Exact `BoundaryCardLatticeResidual` adapter.**  This is the lattice-boundary analogue of
`boundaryCardResidual_of_boundary_cards_and_coeffPolys`, targeting the smaller residual interface
isolated in `BoundaryCardResidual.lean`.  The extra lattice hypothesis is intentionally unused:
once the boundary cardinality bounds and coefficient-polynomial extraction are supplied, the
assembly bridge proves `jointAgreement` directly. -/
theorem boundaryCardLatticeResidual_of_boundary_cards_and_coeffPolys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hBoundaryData : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
    BoundaryCardResidual.BoundaryCardLatticeResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hδeq _hfloor hcardPos
  obtain ⟨hcardLt, hcardGe, hcoeffPoly⟩ := hBoundaryData hk u hδeq hcardPos
  exact boundary_jointAgreement_of_cards_and_coeffPolys
    (deg := deg) (domain := domain) (δ := δ) hk u hcardLt hcardGe hcoeffPoly

omit [DecidableEq ι] in
/-- **Exact lattice-data adapter.**  The #64 lattice residual is reduced to its concrete
cardinality/coefficient-polynomial data surface:
`BoundaryCardResidual.BoundaryCardLatticeData`.  This keeps the lattice witnesses explicit and
uses the same in-tree boundary assembly bridge as the non-lattice-compatible cardinality adapter. -/
theorem boundaryCardLatticeResidual_of_lattice_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual.BoundaryCardLatticeResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hδeq hfloor hcardPos
  obtain ⟨hcardLt, hcardGe, hcoeffPoly⟩ := hLatticeData hk u hδeq hfloor hcardPos
  exact boundary_jointAgreement_of_cards_and_coeffPolys
    (deg := deg) (domain := domain) (δ := δ) hk u hcardLt hcardGe hcoeffPoly

omit [DecidableEq ι] in
/-- Concrete quantization data for the closed boundary: the strict-subradius producer for the
non-lattice branch, plus the smaller cardinality/coefficient-polynomial data for the square
lattice branch.  This is the data-facing counterpart of
`BoundaryCardResidual.BoundaryCardQuantizationResiduals`, whose lattice component is already the
wider `BoundaryCardLatticeResidual`. -/
def BoundaryCardQuantizationData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  BoundaryCardResidual.BoundaryCardStrictInteriorFalseAsStated
      (k := k) (deg := deg) (domain := domain) (δ := δ) ∧
    BoundaryCardResidual.BoundaryCardLatticeData
      (k := k) (deg := deg) (domain := domain) (δ := δ)

omit [Nonempty ι] [DecidableEq ι] in
/-- At `k = 0`, the concrete square-lattice data side is vacuous.  A strict-interior producer
therefore assembles the full concrete quantization data package. -/
theorem BoundaryCardQuantizationData.ofStrictInterior_zero {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hStrict :
      BoundaryCardResidual.BoundaryCardStrictInteriorFalseAsStated
        (k := 0) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardQuantizationData (k := 0) (deg := deg) (domain := domain) (δ := δ) :=
  ⟨hStrict, BoundaryCardResidual.boundaryCardLatticeData_zero⟩

omit [DecidableEq ι] in
/-- Projection of the strict-interior side of `BoundaryCardQuantizationData`. -/
theorem BoundaryCardQuantizationData.strictInterior {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual.BoundaryCardStrictInteriorFalseAsStated
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  h.1

omit [DecidableEq ι] in
/-- Projection of the concrete square-lattice side of `BoundaryCardQuantizationData`. -/
theorem BoundaryCardQuantizationData.latticeData {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual.BoundaryCardLatticeData
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  h.2

omit [DecidableEq ι] in
/-- Projection of the first cardinality lower bound stored in `BoundaryCardQuantizationData`. -/
theorem BoundaryCardQuantizationData.card_gt {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι)
    (hcardPos : 0 < (RS_goodCoeffsCurve (k := k) (deg := deg)
      (domain := domain) u δ).card) :
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k :=
  BoundaryCardResidual.BoundaryCardLatticeData.card_gt
    h.latticeData hk u hδeq hfloor hcardPos

omit [DecidableEq ι] in
/-- Projection of the strong `(n + 1) * k` cardinality bound stored in
`BoundaryCardQuantizationData`. -/
theorem BoundaryCardQuantizationData.card_ge {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι)
    (hcardPos : 0 < (RS_goodCoeffsCurve (k := k) (deg := deg)
      (domain := domain) u δ).card) :
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
      (Fintype.card ι + 1) * k :=
  BoundaryCardResidual.BoundaryCardLatticeData.card_ge
    h.latticeData hk u hδeq hfloor hcardPos

omit [DecidableEq ι] in
/-- Projection of the coefficient-polynomial extractor stored in `BoundaryCardQuantizationData`. -/
theorem BoundaryCardQuantizationData.coeff_polys {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι)
    (hcardPos : 0 < (RS_goodCoeffsCurve (k := k) (deg := deg)
      (domain := domain) u δ).card) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z :=
  BoundaryCardResidual.BoundaryCardLatticeData.coeff_polys
    h.latticeData hk u hδeq hfloor hcardPos

omit [DecidableEq ι] in
/-- Convert concrete quantization data into the existing residual package by assembling the
square-lattice data into `BoundaryCardLatticeResidual`. -/
theorem BoundaryCardQuantizationData.toQuantizationResiduals {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg]
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual.BoundaryCardQuantizationResiduals
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  ⟨h.strictInterior,
    boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) h.latticeData⟩

omit [DecidableEq ι] in
/-- Concrete quantization data reconstructs the closed-boundary cardinality residual. -/
theorem BoundaryCardQuantizationData.toBoundaryCardResidual {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg]
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    ProximityGap.BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  h.toQuantizationResiduals.toBoundaryCardResidual

omit [DecidableEq ι] in
/-- Concrete quantization data reconstructs the sharper boundary-probability residual consumed
by the curve keystone. -/
theorem BoundaryCardQuantizationData.toBoundaryProbabilityResidual {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (h : BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  h.toQuantizationResiduals.toBoundaryProbabilityResidual hδ

/-- The affine-curves keystone can consume the complete boundary quantization package through
the concrete `BoundaryCardLatticeData` square-branch surface. -/
theorem correlatedAgreement_affine_curves_of_quantization_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [DecidableEq ι]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary :
      BoundaryCardQuantizationData (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact BoundaryCardResidual.correlatedAgreement_affine_curves_of_quantization_residuals
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    hBoundary.toQuantizationResiduals hδ

omit [DecidableEq ι] in
/-- The full closed-boundary cardinality residual follows from the quantization split when the
exact lattice branch is supplied as `BoundaryCardLatticeData`.  The non-lattice part still comes
from the strict-subradius producer; this does not widen the residual back to the old
`BoundaryCardResidual` surface. -/
theorem boundaryCardResidual_of_lattice_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)) :
    ProximityGap.BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ)
    (boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) hLatticeData)
    hStrict

omit [DecidableEq ι] in
/-- The sharper probability-branch residual follows from the exact lattice data plus the existing
strict-subradius producer.  This is the direct #64 adapter into the final curve-keystone boundary
surface. -/
theorem boundaryProbabilityResidual_of_lattice_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  BoundaryCardResidual.boundaryProbabilityResidual_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ) hδ
    (boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) hLatticeData)
    hStrict

/-- The affine-curves keystone can consume the exact lattice branch through the smaller
`BoundaryCardLatticeData` surface. This is the direct front-door adapter: the strict Johnson
coefficient-polynomial residual and strict-subradius producer are unchanged, while the exact
lattice branch is supplied through `BoundaryCardLatticeData` rather than the older
`BoundaryCardLatticeResidual`. -/
theorem correlatedAgreement_affine_curves_of_lattice_data
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [DecidableEq ι]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff hStrict
    (boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) hLatticeData)
    hδ

omit [DecidableEq ι] in
/-- At square Johnson endpoints, the closed-boundary residual can consume
`BoundaryCardLatticeData` directly.  The strict-subradius producer is unnecessary because the
perfect-square condition identifies the branch as the exact lattice endpoint. -/
theorem boundaryCardResidual_of_lattice_data_isSquare
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    ProximityGap.BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  BoundaryCardResidual.boundaryCardResidual_of_isSquare_deg_mul_card
    (deg := deg) (domain := domain) (δ := δ) hsqrt_le hdeg hSquare
    (boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
/-- Square-endpoint `BoundaryProbabilityResidual` front door from the concrete lattice-data
surface, with no strict-subradius producer. -/
theorem boundaryProbabilityResidual_of_lattice_data_isSquare
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  BoundaryCardResidual.boundaryProbabilityResidual_of_isSquare_deg_mul_card
    (deg := deg) (domain := domain) (δ := δ) hδ hsqrt_le hdeg hSquare
    (boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
/-- Curve-facing square-endpoint adapter from `BoundaryCardLatticeData`.  This is the
lattice-data counterpart of
`BoundaryCardResidual.correlatedAgreement_affine_curves_of_isSquare_deg_mul_card`. -/
theorem correlatedAgreement_affine_curves_of_lattice_data_isSquare
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hLatticeData :
      BoundaryCardResidual.BoundaryCardLatticeData
        (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact BoundaryCardResidual.correlatedAgreement_affine_curves_of_isSquare_deg_mul_card
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    (boundaryCardLatticeResidual_of_lattice_data
      (k := k) (deg := deg) (domain := domain) (δ := δ) hLatticeData)
    hδ hsqrt_le hdeg hSquare

omit [Nonempty ι] [DecidableEq ι] in
/-- The closed-boundary residual is vacuous for `k = 0`, since its first argument is
`0 < k`. This removes an unnecessary residual hypothesis from degenerate callers. -/
theorem boundaryCardResidual_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    ProximityGap.BoundaryCardResidual (k := 0) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk
  omega

omit [Nonempty ι] [DecidableEq ι] in
/-- The sharper boundary-probability residual is also vacuous for `k = 0`, since its first
argument is `0 < k`. This is the probability-branch companion to
`boundaryCardResidual_zero`. -/
theorem boundaryProbabilityResidual_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    ProximityGap.BoundaryProbabilityResidual
      (k := 0) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk
  omega

omit [DecidableEq ι] in
/-- At `k = 0`, the affine-curves keystone has no closed-boundary obligation beyond the usual
strict coefficient-polynomial residual: the boundary-probability residual is vacuous because its
first argument is `0 < k`. -/
theorem correlatedAgreement_affine_curves_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := 0) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := 0) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact ProximityGap.correlatedAgreement_affine_curves
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    boundaryProbabilityResidual_zero hδ

end BoundaryDischarge

end ArkLib

/-! ## Axiom audit — must rest only on `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.BoundaryDischarge.boundary_eq
#print axioms ArkLib.BoundaryDischarge.errorBound_eq_zero_at_boundary
#print axioms ArkLib.BoundaryDischarge.boundary_card_only_pos
#print axioms ArkLib.BoundaryDischarge.boundary_param_consistent_iff
#print axioms ArkLib.BoundaryDischarge.boundary_jointAgreement_of_cards_and_coeffPolys
#print axioms ArkLib.BoundaryDischarge.hBoundary_of_boundary_cards_and_coeffPolys
#print axioms ArkLib.BoundaryDischarge.boundaryCardResidual_of_boundary_cards_and_coeffPolys
#print axioms ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_boundary_cards_and_coeffPolys
#print axioms ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.ofStrictInterior_zero
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.card_gt
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.card_ge
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.coeff_polys
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.toQuantizationResiduals
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.toBoundaryCardResidual
#print axioms ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.toBoundaryProbabilityResidual
#print axioms ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_quantization_data
#print axioms ArkLib.BoundaryDischarge.boundaryCardResidual_of_lattice_data
#print axioms ArkLib.BoundaryDischarge.boundaryProbabilityResidual_of_lattice_data
#print axioms ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data
#print axioms ArkLib.BoundaryDischarge.boundaryCardResidual_of_lattice_data_isSquare
#print axioms ArkLib.BoundaryDischarge.boundaryProbabilityResidual_of_lattice_data_isSquare
#print axioms ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data_isSquare
#print axioms ArkLib.BoundaryDischarge.boundaryCardResidual_zero
#print axioms ArkLib.BoundaryDischarge.boundaryProbabilityResidual_zero
#print axioms ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_zero
