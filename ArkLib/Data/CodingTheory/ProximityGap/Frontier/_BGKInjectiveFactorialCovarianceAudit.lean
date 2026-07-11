/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthSevenInjectiveVarianceEquivalence

/-!
# BGK injective covariance normalization audit

G176's polarization identity is valid for its deletion profile.  The BGK depth-seven profile has
a different normalization, however.  If `A` is the histogram of unordered distinct `r`-subsets,
then its ordered-injective profile is

`J = r! * A`,

and the ordered all-tuples profile decomposes as `R = J + D_rep`.  Thus the exact gate relevant to
the BGK injective residual is

`V(r! A) <= V(R)  <->  -2 Cov(r! A, D_rep) <= V(D_rep)`.

In particular `V(r! A) = (r!)^2 V(A)`.  At depth seven this factor is `25,401,600`, exactly the
factor already present in `_BGKDepthSevenInjectiveVarianceEquivalence`.

The correctly scaled contraction is not universal.  The smallest group-sum cell already refutes
it: for the two-element additive group and depth two, the distinct-subset profile is `A=(0,1)`,
the ordered all-pairs profile is `R=(2,2)`, and hence `J=2!A=(0,2)`, `D_rep=(2,0)`.  Their centered
masses are `V(J)=4` and `V(R)=0`; equivalently the signed gate margin is `-4`.  The profiles have
the genuine sampling totals `sum A = choose(2,2)=1` and `sum R=2^2=4`, and `D_rep` is pointwise
nonnegative.  This refutes only a universal transfer: a production-subgroup-specific signed
covariance theorem remains possible.

Consequently G176 remains a correct socket for its unscaled deletion normalization, but it cannot
by itself transfer a with-replacement/DC bound to the coefficient-`126871` BGK injective target.
The generic sampling-without-replacement comparison also remains over `141` energy bits too weak.

Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKInjectiveFactorialCovarianceAudit

/-! ## Exact scaled polarization -/

/-- Unnormalized centered square mass: `|X| * sum f^2 - (sum f)^2`. -/
def centeredMass {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ) * ∑ x, f x ^ 2 - (∑ x, f x) ^ 2

/-- The matching unnormalized centered inner product. -/
def centeredInner {X : Type*} [Fintype X] (f g : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ) * ∑ x, f x * g x - (∑ x, f x) * ∑ x, g x

/-- The ordered-injective profile associated to an unordered subset histogram. -/
def injectiveProfile {X : Type*} (r : ℕ) (A : X → ℝ) : X → ℝ :=
  fun x => (r.factorial : ℝ) * A x

/-- The genuine repeated-coordinate defect after removing all `r!` orders of each subset. -/
def repetitionDefect {X : Type*} (r : ℕ) (A R : X → ℝ) : X → ℝ :=
  fun x => R x - injectiveProfile r A x

theorem total_eq_injective_add_defect {X : Type*} (r : ℕ) (A R : X → ℝ) (x : X) :
    R x = injectiveProfile r A x + repetitionDefect r A R x := by
  unfold repetitionDefect
  ring

theorem centeredMass_eq_inner {X : Type*} [Fintype X] (f : X → ℝ) :
    centeredMass f = centeredInner f f := by
  unfold centeredMass centeredInner
  congr 1 <;> simp only [pow_two]

theorem centeredInner_add_left {X : Type*} [Fintype X] (f g h : X → ℝ) :
    centeredInner (fun x => f x + g x) h = centeredInner f h + centeredInner g h := by
  unfold centeredInner
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

theorem centeredInner_add_right {X : Type*} [Fintype X] (f g h : X → ℝ) :
    centeredInner f (fun x => g x + h x) = centeredInner f g + centeredInner f h := by
  unfold centeredInner
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

theorem centeredInner_comm {X : Type*} [Fintype X] (f g : X → ℝ) :
    centeredInner f g = centeredInner g f := by
  unfold centeredInner
  simp_rw [mul_comm]

/-- Polarization for the centered mass. -/
theorem centeredMass_add {X : Type*} [Fintype X] (f d : X → ℝ) :
    centeredMass (fun x => f x + d x) =
      centeredMass f + centeredMass d + 2 * centeredInner f d := by
  rw [centeredMass_eq_inner]
  calc
    centeredInner (fun x => f x + d x) (fun x => f x + d x) =
        centeredInner f (fun x => f x + d x) +
          centeredInner d (fun x => f x + d x) := centeredInner_add_left f d _
    _ = (centeredInner f f + centeredInner f d) +
        (centeredInner d f + centeredInner d d) := by
      rw [centeredInner_add_right f f d, centeredInner_add_right d f d]
    _ = centeredMass f + centeredMass d + 2 * centeredInner f d := by
      rw [centeredInner_comm d f, centeredMass_eq_inner, centeredMass_eq_inner]
      ring

/-- Centered mass is quadratic under scalar multiplication. -/
theorem centeredMass_smul {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    centeredMass (fun x => c * f x) = c ^ 2 * centeredMass f := by
  unfold centeredMass
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The factorial normalization costs exactly `(r!)^2` in centered mass. -/
theorem centeredMass_injectiveProfile {X : Type*} [Fintype X] (r : ℕ) (A : X → ℝ) :
    centeredMass (injectiveProfile r A) = (r.factorial : ℝ) ^ 2 * centeredMass A := by
  exact centeredMass_smul (r.factorial : ℝ) A

/-- **Correct BGK polarization.**  The covariance pairs the factorial-scaled injective profile
`J=r!A`, not the unscaled subset histogram `A`, with the genuine repetition defect. -/
theorem scaled_repetition_polarization {X : Type*} [Fintype X]
    (r : ℕ) (A R : X → ℝ) :
    centeredMass R =
      centeredMass (injectiveProfile r A) + centeredMass (repetitionDefect r A R) +
        2 * centeredInner (injectiveProfile r A) (repetitionDefect r A R) := by
  calc
    centeredMass R = centeredMass
        (fun x => injectiveProfile r A x + repetitionDefect r A R x) := by
      congr 1
      funext x
      exact total_eq_injective_add_defect r A R x
    _ = centeredMass (injectiveProfile r A) + centeredMass (repetitionDefect r A R) +
        2 * centeredInner (injectiveProfile r A) (repetitionDefect r A R) :=
      centeredMass_add (injectiveProfile r A) (repetitionDefect r A R)

/-- **Exact scaled covariance gate.**  This is an equivalence, not merely a sufficient condition. -/
theorem scaled_covariance_gate_iff {X : Type*} [Fintype X]
    (r : ℕ) (A R : X → ℝ) :
    centeredMass (injectiveProfile r A) ≤ centeredMass R ↔
      -(2 * centeredInner (injectiveProfile r A) (repetitionDefect r A R)) ≤
        centeredMass (repetitionDefect r A R) := by
  rw [scaled_repetition_polarization r A R]
  constructor <;> intro h <;> linarith

/-! ## Minimal genuine sampling counterprofile -/

/-- Distinct two-subset sum histogram for the full two-element additive group. -/
def twoPointSubsetProfile : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

/-- Ordered all-pairs sum histogram for the full two-element additive group. -/
def twoPointTupleProfile : Fin 2 → ℝ := fun _ => 2

theorem twoPoint_sampling_totals :
    (∑ i, twoPointSubsetProfile i) = 1 ∧ (∑ i, twoPointTupleProfile i) = 4 := by
  norm_num [twoPointSubsetProfile, twoPointTupleProfile, Fin.sum_univ_two]

theorem twoPoint_repetitionDefect_nonneg :
    ∀ i, 0 ≤ repetitionDefect 2 twoPointSubsetProfile twoPointTupleProfile i := by
  intro i
  fin_cases i <;>
    norm_num [repetitionDefect, injectiveProfile, twoPointSubsetProfile,
      twoPointTupleProfile, Nat.factorial]

theorem twoPoint_injective_mass :
    centeredMass (injectiveProfile 2 twoPointSubsetProfile) = 4 := by
  norm_num [centeredMass, injectiveProfile, twoPointSubsetProfile, Nat.factorial,
    Fin.sum_univ_two]

theorem twoPoint_tuple_mass : centeredMass twoPointTupleProfile = 0 := by
  norm_num [centeredMass, twoPointTupleProfile, Fin.sum_univ_two]

theorem twoPoint_defect_mass :
    centeredMass (repetitionDefect 2 twoPointSubsetProfile twoPointTupleProfile) = 4 := by
  norm_num [centeredMass, repetitionDefect, injectiveProfile, twoPointSubsetProfile,
    twoPointTupleProfile, Nat.factorial, Fin.sum_univ_two]

theorem twoPoint_injective_defect_covariance :
    centeredInner (injectiveProfile 2 twoPointSubsetProfile)
      (repetitionDefect 2 twoPointSubsetProfile twoPointTupleProfile) = -4 := by
  norm_num [centeredInner, repetitionDefect, injectiveProfile, twoPointSubsetProfile,
    twoPointTupleProfile, Nat.factorial, Fin.sum_univ_two]

/-- The correctly scaled signed gate margin is negative in the smallest group-sum cell. -/
theorem twoPoint_scaled_gate_margin :
    centeredMass (repetitionDefect 2 twoPointSubsetProfile twoPointTupleProfile) +
        2 * centeredInner (injectiveProfile 2 twoPointSubsetProfile)
          (repetitionDefect 2 twoPointSubsetProfile twoPointTupleProfile) = -4 := by
  rw [twoPoint_defect_mass, twoPoint_injective_defect_covariance]
  norm_num

/-- A universal `V(r!A) <= V(R)` sampling-without-replacement contraction is false, even with
genuine sampling totals and a pointwise nonnegative repeated-coordinate defect. -/
theorem not_twoPoint_scaled_contraction :
    ¬centeredMass (injectiveProfile 2 twoPointSubsetProfile) ≤
      centeredMass twoPointTupleProfile := by
  rw [twoPoint_injective_mass, twoPoint_tuple_mass]
  norm_num

/-! ## Depth-seven production normalization -/

theorem factorial_seven : Nat.factorial 7 = 5040 := by norm_num [Nat.factorial]

theorem factorial_seven_sq : (Nat.factorial 7) ^ 2 = 25401600 := by
  norm_num [Nat.factorial]

theorem factorial_seven_sq_real : ((Nat.factorial 7 : ℝ) ^ 2) = 25401600 := by
  norm_num [Nat.factorial]

/-- Forgetting the factorial square understates the variance multiplier by between `200` and
`201` copies of the target coefficient `126871`. -/
theorem factorial_seven_sq_vs_targetCoefficient :
    200 * 126871 < (Nat.factorial 7) ^ 2 ∧
      (Nat.factorial 7) ^ 2 < 201 * 126871 := by
  norm_num [Nat.factorial]

/-- Explicit depth-seven form of the quadratic normalization. -/
theorem centeredMass_injectiveProfile_seven {X : Type*} [Fintype X] (A : X → ℝ) :
    centeredMass (injectiveProfile 7 A) = 25401600 * centeredMass A := by
  rw [centeredMass_injectiveProfile, factorial_seven_sq_real]

/-- Standalone normalization rewrite for the right-hand side of
`_BGKDepthSevenInjectiveVarianceEquivalence.injectiveD7_target_iff_centeredVariance`.
The imported theorem need not be a dependency of this audit: its `(7!)^2` is definitionally the
explicit coefficient below. -/
theorem depthSeven_target_rhs_explicit_factorial (V q n : ℝ) :
    (Nat.factorial 7 : ℝ) ^ 2 * V ≤ 126871 * q ^ 2 * n ^ 7 ↔
      25401600 * V ≤ 126871 * q ^ 2 * n ^ 7 := by
  rw [factorial_seven_sq_real]

open ArkLib.ProximityGap.Frontier.BGKDepthSevenInjectiveVarianceEquivalence

/-- Direct consumer of the exact Fourier/subset-variance equivalence: the coefficient multiplying
the unordered seven-subset variance is `25,401,600`, not one. -/
theorem depthSeven_target_iff_explicit_factorial
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (n : ℕ) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖injectiveD7 psi G b‖ ^ 2) ≤
        126871 * (Fintype.card F : ℝ) * n ^ 7 ↔
      (25401600 : ℝ) * (sevenSubsetCenteredVariance G : ℝ) ≤
        126871 * (Fintype.card F : ℝ) ^ 2 * n ^ 7 := by
  simpa only [factorial_seven_sq_real] using
    (injectiveD7_target_iff_centeredVariance hpsi G n)

/-- Production size, duplicated locally so this narrow audit does not import another Frontier
lane merely to quote its exact arithmetic certificate. -/
def productionN : ℕ := 2 ^ 30

/-- Number of repeated ordered seven-tuples at production size. -/
def productionSamplingError : ℕ :=
  productionN ^ 7 - productionN.descFactorial 7

/-- The coefficient-`126871` pointwise energy scale. -/
def productionPointwiseEnergyBudget : ℕ := 126871 * productionN ^ 7

/-- Standalone replay of
`_BGKSamplingWithoutReplacementNoGo.samplingError_sq_exceeds_budget_by_141_bits`.
Correcting the factorial normalization does not repair the generic sampling comparison: its
repeated-coordinate error still misses the target scale by over `141` energy bits. -/
theorem generic_sampling_error_exceeds_target_by_141_bits :
    2 ^ 141 * productionPointwiseEnergyBudget < productionSamplingError ^ 2 := by
  norm_num [productionPointwiseEnergyBudget, productionSamplingError, productionN,
    Nat.descFactorial]

#print axioms centeredMass_injectiveProfile
#print axioms scaled_repetition_polarization
#print axioms scaled_covariance_gate_iff
#print axioms not_twoPoint_scaled_contraction
#print axioms factorial_seven_sq_vs_targetCoefficient
#print axioms depthSeven_target_rhs_explicit_factorial
#print axioms depthSeven_target_iff_explicit_factorial
#print axioms generic_sampling_error_exceeds_target_by_141_bits

end ArkLib.ProximityGap.Frontier.BGKInjectiveFactorialCovarianceAudit
