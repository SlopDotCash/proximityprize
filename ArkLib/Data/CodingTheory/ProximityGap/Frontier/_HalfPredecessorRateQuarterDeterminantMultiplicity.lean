/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GK16RootCounting
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry

/-!
# Rate-quarter half predecessor: determinant multiplicity for three line cores

For three decoded polynomial lines with core pairs `c_i = (a_i, r_i)`, form

```text
Delta = det(c_2 - c_1, c_3 - c_1).
```

Both components of every `c_i` have degree `< k`, so `Delta` has degree at most
`2k - 2`.  A coordinate contained in exactly two line cores is a simple root
of `Delta`; a coordinate contained in all three cores is a double root because
both determinant columns vanish there.  Consequently each coordinate contained
in `m` of the three cores contributes at least `m - 1` to the root multiplicity.

Summing over an injective evaluation domain gives the determinant-collapse
criterion

```text
|D_1| + |D_2| + |D_3| - n > 2k - 2  implies  Delta = 0.
```

The double-root argument uses divisibility by `(X - C x)^2`, rather than
ordinary derivatives, so it is valid in arbitrary characteristic.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open scoped Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity

variable {F : Type} [Field F]

/-- The determinant of the two difference columns determined by three
polynomial pairs. -/
noncomputable def threeLineDeterminant (c1 c2 c3 : F[X] × F[X]) : F[X] :=
  (c2.1 - c1.1) * (c3.2 - c1.2) -
    (c2.2 - c1.2) * (c3.1 - c1.1)

/-- A polynomial pair agrees with one received pair at `x`. -/
def AgreesAt (u0 u1 x : F) (c : F[X] × F[X]) : Prop :=
  c.1.eval x = u0 ∧ c.2.eval x = u1

/-- Number of the three cores containing one coordinate. -/
noncomputable def coreCount (u0 u1 x : F)
    (c1 c2 c3 : F[X] × F[X]) : ℕ := by
  classical
  exact
    (if AgreesAt u0 u1 x c1 then 1 else 0) +
      (if AgreesAt u0 u1 x c2 then 1 else 0) +
        (if AgreesAt u0 u1 x c3 then 1 else 0)

/-- Two core incidences force a simple root of the three-line determinant. -/
theorem one_le_rootMultiplicity_threeLineDeterminant_of_two_agree
    {u0 u1 x : F} {c1 c2 c3 : F[X] × F[X]}
    (hDelta : threeLineDeterminant c1 c2 c3 ≠ 0)
    (hcores :
      (AgreesAt u0 u1 x c1 ∧ AgreesAt u0 u1 x c2) ∨
      (AgreesAt u0 u1 x c1 ∧ AgreesAt u0 u1 x c3) ∨
      (AgreesAt u0 u1 x c2 ∧ AgreesAt u0 u1 x c3)) :
    1 ≤ (threeLineDeterminant c1 c2 c3).rootMultiplicity x := by
  rw [Nat.one_le_iff_ne_zero]
  intro hzero
  have hnotroot := (Polynomial.rootMultiplicity_pos hDelta).not.mp
    (Nat.not_lt.mpr (Nat.le_zero.mpr hzero))
  apply hnotroot
  rcases hcores with h12 | h13 | h23
  · rcases h12 with ⟨⟨h10, h11⟩, ⟨h20, h21⟩⟩
    simp only [Polynomial.IsRoot, threeLineDeterminant, eval_sub, eval_mul]
    rw [h10, h11, h20, h21]
    ring
  · rcases h13 with ⟨⟨h10, h11⟩, ⟨h30, h31⟩⟩
    simp only [Polynomial.IsRoot, threeLineDeterminant, eval_sub, eval_mul]
    rw [h10, h11, h30, h31]
    ring
  · rcases h23 with ⟨⟨h20, h21⟩, ⟨h30, h31⟩⟩
    simp only [Polynomial.IsRoot, threeLineDeterminant, eval_sub, eval_mul]
    rw [h20, h21, h30, h31]
    ring

/-- Three core incidences force a double root: both determinant columns
vanish at the coordinate. -/
theorem two_le_rootMultiplicity_threeLineDeterminant_of_three_agree
    {u0 u1 x : F} {c1 c2 c3 : F[X] × F[X]}
    (hDelta : threeLineDeterminant c1 c2 c3 ≠ 0)
    (h1 : AgreesAt u0 u1 x c1) (h2 : AgreesAt u0 u1 x c2)
    (h3 : AgreesAt u0 u1 x c3) :
    2 ≤ (threeLineDeterminant c1 c2 c3).rootMultiplicity x := by
  rw [Polynomial.le_rootMultiplicity_iff hDelta]
  have h21a : X - C x ∣ c2.1 - c1.1 := Polynomial.dvd_iff_isRoot.mpr (by
    simp only [Polynomial.IsRoot, eval_sub]
    rw [h2.1, h1.1]
    exact sub_self u0)
  have h21r : X - C x ∣ c2.2 - c1.2 := Polynomial.dvd_iff_isRoot.mpr (by
    simp only [Polynomial.IsRoot, eval_sub]
    rw [h2.2, h1.2]
    exact sub_self u1)
  have h31a : X - C x ∣ c3.1 - c1.1 := Polynomial.dvd_iff_isRoot.mpr (by
    simp only [Polynomial.IsRoot, eval_sub]
    rw [h3.1, h1.1]
    exact sub_self u0)
  have h31r : X - C x ∣ c3.2 - c1.2 := Polynomial.dvd_iff_isRoot.mpr (by
    simp only [Polynomial.IsRoot, eval_sub]
    rw [h3.2, h1.2]
    exact sub_self u1)
  rw [show (2 : ℕ) = 1 + 1 by omega, pow_add, pow_one]
  apply dvd_sub
  · exact mul_dvd_mul h21a h31r
  · exact mul_dvd_mul h21r h31a

/-- The exact local multiplicity inequality: a coordinate contained in `m`
of the three cores contributes at least `m - 1` to the determinant. -/
theorem coreCount_sub_one_le_rootMultiplicity
    {u0 u1 x : F} {c1 c2 c3 : F[X] × F[X]}
    (hDelta : threeLineDeterminant c1 c2 c3 ≠ 0) :
    coreCount u0 u1 x c1 c2 c3 - 1 ≤
      (threeLineDeterminant c1 c2 c3).rootMultiplicity x := by
  classical
  by_cases h1 : AgreesAt u0 u1 x c1 <;>
    by_cases h2 : AgreesAt u0 u1 x c2 <;>
      by_cases h3 : AgreesAt u0 u1 x c3
  · simpa [coreCount, h1, h2, h3] using
      two_le_rootMultiplicity_threeLineDeterminant_of_three_agree hDelta h1 h2 h3
  · simpa [coreCount, h1, h2, h3] using
      one_le_rootMultiplicity_threeLineDeterminant_of_two_agree hDelta (Or.inl ⟨h1, h2⟩)
  · simpa [coreCount, h1, h2, h3] using
      one_le_rootMultiplicity_threeLineDeterminant_of_two_agree hDelta
        (Or.inr (Or.inl ⟨h1, h3⟩))
  · simp [coreCount, h1, h2, h3]
  · simpa [coreCount, h1, h2, h3] using
      one_le_rootMultiplicity_threeLineDeterminant_of_two_agree hDelta
        (Or.inr (Or.inr ⟨h2, h3⟩))
  · simp [coreCount, h1, h2, h3]
  · simp [coreCount, h1, h2, h3]
  · simp [coreCount, h1, h2, h3]

/-- The determinant of three degree-`<k` polynomial pairs has degree at most
`2k - 2`. -/
theorem natDegree_threeLineDeterminant_le_two_mul_sub_two
    {k : ℕ} {c1 c2 c3 : F[X] × F[X]}
    (h1a : c1.1.natDegree < k) (h1r : c1.2.natDegree < k)
    (h2a : c2.1.natDegree < k) (h2r : c2.2.natDegree < k)
    (h3a : c3.1.natDegree < k) (h3r : c3.2.natDegree < k) :
    (threeLineDeterminant c1 c2 c3).natDegree ≤ 2 * k - 2 := by
  have hk : 1 ≤ k := by omega
  have h21a : (c2.1 - c1.1).natDegree ≤ k - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
  have h21r : (c2.2 - c1.2).natDegree ≤ k - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
  have h31a : (c3.1 - c1.1).natDegree ≤ k - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
  have h31r : (c3.2 - c1.2).natDegree ≤ k - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
  have hp : ((c2.1 - c1.1) * (c3.2 - c1.2)).natDegree ≤ 2 * (k - 1) :=
    Polynomial.natDegree_mul_le.trans (by omega)
  have hq : ((c2.2 - c1.2) * (c3.1 - c1.1)).natDegree ≤ 2 * (k - 1) :=
    Polynomial.natDegree_mul_le.trans (by omega)
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) (by omega))

variable {I : Type}

/-- Sum the exact local determinant multiplicities over any set of distinct
evaluation coordinates. -/
theorem sum_coreCount_sub_one_le_natDegree
    (dom : I ↪ F) (u0 u1 : I → F) (c1 c2 c3 : F[X] × F[X])
    (S : Finset I) (hDelta : threeLineDeterminant c1 c2 c3 ≠ 0) :
    (∑ i ∈ S, (coreCount (u0 i) (u1 i) (dom i) c1 c2 c3 - 1)) ≤
      (threeLineDeterminant c1 c2 c3).natDegree := by
  classical
  calc
    (∑ i ∈ S, (coreCount (u0 i) (u1 i) (dom i) c1 c2 c3 - 1)) ≤
        ∑ i ∈ S, (threeLineDeterminant c1 c2 c3).rootMultiplicity (dom i) :=
      Finset.sum_le_sum (s := S) fun i _ =>
        coreCount_sub_one_le_rootMultiplicity
          (u0 := u0 i) (u1 := u1 i) (x := dom i)
          (c1 := c1) (c2 := c2) (c3 := c3) hDelta
    _ = ∑ x ∈ S.image dom,
        (threeLineDeterminant c1 c2 c3).rootMultiplicity x := by
      rw [Finset.sum_image (fun i _ j _ hij => dom.injective hij)]
    _ ≤ (threeLineDeterminant c1 c2 c3).natDegree :=
      Polynomial.sum_rootMultiplicity_le_natDegree _ hDelta _

variable [Fintype I]

/-- Core coordinates of one polynomial pair relative to a received pair. -/
noncomputable def coreSet (dom : I ↪ F) (u0 u1 : I → F)
    (c : F[X] × F[X]) : Finset I := by
  classical
  exact Finset.univ.filter fun i => AgreesAt (u0 i) (u1 i) (dom i) c

/-- The determinant core set is exactly the canonical half-predecessor
`jointCore` for the same polynomial pair. -/
theorem coreSet_eq_jointCore [Fintype F] [DecidableEq F]
    (dom : I ↪ F) (u0 u1 : I → F) (c : F[X] × F[X]) :
    coreSet dom u0 u1 c = jointCore dom u0 u1 c.1 c.2 := by
  ext i
  simp [coreSet, AgreesAt, jointCore]

/-- Total core incidence is the sum of the three core cardinalities. -/
theorem sum_coreCount_eq_sum_coreSet_cards
    (dom : I ↪ F) (u0 u1 : I → F) (c1 c2 c3 : F[X] × F[X]) :
    (∑ i : I, coreCount (u0 i) (u1 i) (dom i) c1 c2 c3) =
      (coreSet dom u0 u1 c1).card + (coreSet dom u0 u1 c2).card +
        (coreSet dom u0 u1 c3).card := by
  classical
  simp only [coreCount, Finset.sum_add_distrib]
  rw [Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]
  rfl

/-- The sum of the three core sizes minus the domain size is a lower bound for
the total certified determinant-root multiplicity.  The sharper exact term
would subtract the core union; this domain-size form is the one needed by the
rate-quarter determinant-collapse criterion. -/
theorem core_card_sum_sub_domain_le_sum_coreCount_sub_one
    (dom : I ↪ F) (u0 u1 : I → F) (c1 c2 c3 : F[X] × F[X]) :
    (coreSet dom u0 u1 c1).card + (coreSet dom u0 u1 c2).card +
          (coreSet dom u0 u1 c3).card - Fintype.card I ≤
      ∑ i : I, (coreCount (u0 i) (u1 i) (dom i) c1 c2 c3 - 1) := by
  classical
  have hsum :
      (∑ i : I, coreCount (u0 i) (u1 i) (dom i) c1 c2 c3) ≤
        ∑ i : I, ((coreCount (u0 i) (u1 i) (dom i) c1 c2 c3 - 1) + 1) := by
    exact Finset.sum_le_sum fun i _ => by omega
  rw [sum_coreCount_eq_sum_coreSet_cards] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hsum
  rw [Nat.sub_le_iff_le_add]
  exact hsum

/-- **Three-line determinant collapse.**  If the excess of the three core
sizes over the domain exceeds the `2k - 2` determinant degree budget, the
three polynomial pairs are rationally collinear (`Delta = 0`). -/
theorem threeLineDeterminant_eq_zero_of_core_card_sum_sub_domain_gt
    (dom : I ↪ F) (u0 u1 : I → F) {k : ℕ}
    (c1 c2 c3 : F[X] × F[X])
    (h1a : c1.1.natDegree < k) (h1r : c1.2.natDegree < k)
    (h2a : c2.1.natDegree < k) (h2r : c2.2.natDegree < k)
    (h3a : c3.1.natDegree < k) (h3r : c3.2.natDegree < k)
    (hlarge : 2 * k - 2 <
      (coreSet dom u0 u1 c1).card + (coreSet dom u0 u1 c2).card +
        (coreSet dom u0 u1 c3).card - Fintype.card I) :
    threeLineDeterminant c1 c2 c3 = 0 := by
  by_contra hDelta
  have hlower := core_card_sum_sub_domain_le_sum_coreCount_sub_one
    dom u0 u1 c1 c2 c3
  have hroots := sum_coreCount_sub_one_le_natDegree
    dom u0 u1 c1 c2 c3 Finset.univ hDelta
  have hroots' :
      (∑ i : I, (coreCount (u0 i) (u1 i) (dom i) c1 c2 c3 - 1)) ≤
        (threeLineDeterminant c1 c2 c3).natDegree := by
    simpa using hroots
  have hdeg := natDegree_threeLineDeterminant_le_two_mul_sub_two
    h1a h1r h2a h2r h3a h3r
  omega

/-- Canonical `jointCore` form of the three-line determinant collapse, ready
for the secant-line incidence API. -/
theorem threeLineDeterminant_eq_zero_of_jointCore_card_sum_sub_domain_gt
    [Fintype F] [DecidableEq F]
    (dom : I ↪ F) (u0 u1 : I → F) {k : ℕ}
    (c1 c2 c3 : F[X] × F[X])
    (h1a : c1.1.natDegree < k) (h1r : c1.2.natDegree < k)
    (h2a : c2.1.natDegree < k) (h2r : c2.2.natDegree < k)
    (h3a : c3.1.natDegree < k) (h3r : c3.2.natDegree < k)
    (hlarge : 2 * k - 2 <
      (jointCore dom u0 u1 c1.1 c1.2).card +
        (jointCore dom u0 u1 c2.1 c2.2).card +
          (jointCore dom u0 u1 c3.1 c3.2).card - Fintype.card I) :
    threeLineDeterminant c1 c2 c3 = 0 := by
  apply threeLineDeterminant_eq_zero_of_core_card_sum_sub_domain_gt
    dom u0 u1 c1 c2 c3 h1a h1r h2a h2r h3a h3r
  simpa only [coreSet_eq_jointCore] using hlarge

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity
#print axioms coreCount_sub_one_le_rootMultiplicity
#print axioms sum_coreCount_sub_one_le_natDegree
#print axioms threeLineDeterminant_eq_zero_of_core_card_sum_sub_domain_gt
#print axioms threeLineDeterminant_eq_zero_of_jointCore_card_sum_sub_domain_gt
