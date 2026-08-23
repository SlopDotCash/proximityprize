/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKRepeatedSectorNewtonAbsorption
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthSevenInjectiveVarianceEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CirculantTraceEnergy
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# Dilation-coloured Newton operator at depth seven

The univariate adjacency/Hashimoto route loses the information in

`D₇(b) = Q₇(η_b,η_{2b},...,η_{7b})`.

This file builds the operator which retains that information.  For a connection set `G`, let
`A_j` be additive convolution by the dilate `jG`.  All seven operators commute, since they are
convolutions on the same abelian group.  They have the common additive-character eigenbasis, and
the eigenvalue of `A_j` at frequency `b` is `η_{jb}`.  Substituting `A₁,...,A₇` in the exact
cycle-index/Newton polynomial therefore gives an operator whose eigenvalue is exactly the ordered
injective seven-tuple transform `7! e₇`.

This is the correct graph normal-ordering, but generic commuting-operator technology still does
not supply the live coefficient saving.  Each nonzero colour has exactly the same marginal
Schatten profile: multiplication `b ↦ jb` merely permutes the Paley spectrum.  A two-point joint
spectrum makes the loss precise.  Two commuting real diagonal seven-tuples have identical
marginal norm moments at every colour and every exponent, while their Newton energies are

`66816 < 126871 < 25401600`.

Consequently no criterion depending only on the seven marginal Schatten/Frobenius profiles can
decide the production allowance.  The missing datum is the arithmetic correlation of the seven
frequency permutations.  Moreover, the Newton scalar is sign-indefinite already on commuting
real diagonal contractions, so it is not itself a generic Schur/SOS-positive normal ordering.
Passing to `N* N` restores positivity but its trace is exactly the open injective energy from
`_BGKDepthSevenInjectiveVarianceEquivalence`.

The remaining `8264` saving must therefore enter as a mixed, subgroup-arithmetic joint spectral
inequality; commutativity and marginal unitarily-invariant norms alone are insufficient.  Issue
#466.  This is an exact socket/no-go, not a proof of the remaining estimate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKDilationColoredNewtonOperatorNoGo

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption
open ProximityGap.Frontier.CirculantTraceEnergy

/-! ## Commuting coloured Cayley operators -/

/-- Complex signals on the additive group of `F`. -/
abbrev Signal (F : Type*) := F → ℂ

/-- Additive convolution by the indicator of `S`, packaged as a complex-linear endomorphism. -/
noncomputable def adjacencyEnd {F : Type*} [Field F] (S : Finset F) :
    Module.End ℂ (Signal F) where
  toFun f := fun y => ∑ x ∈ S, f (y + x)
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] theorem adjacencyEnd_apply {F : Type*} [Field F] (S : Finset F)
    (f : Signal F) (y : F) :
    adjacencyEnd S f y = ∑ x ∈ S, f (y + x) := rfl

/-- Convolutions by any two finite connection sets commute on the additive abelian group. -/
theorem adjacencyEnd_commute {F : Type*} [Field F] (S T : Finset F) :
    adjacencyEnd S * adjacencyEnd T = adjacencyEnd T * adjacencyEnd S := by
  ext f y
  simp only [Module.End.mul_apply, adjacencyEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  abel

/-- The colour-`j` adjacency is convolution by the dilated connection set `jG`. -/
noncomputable def coloredAdjacency {F : Type*} [Field F] [DecidableEq F]
    (G : Finset F) (j : ℕ) : Module.End ℂ (Signal F) :=
  adjacencyEnd (dilate (j : F) G)

/-- Every pair of dilation colours commutes. -/
theorem coloredAdjacency_commute {F : Type*} [Field F] [DecidableEq F]
    (G : Finset F) (i j : ℕ) :
    coloredAdjacency G i * coloredAdjacency G j =
      coloredAdjacency G j * coloredAdjacency G i := by
  exact adjacencyEnd_commute _ _

/-- Additive characters diagonalize the endomorphism form of Cayley convolution. -/
theorem adjacencyEnd_chi {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (S : Finset F) (b : F) :
    adjacencyEnd S (chi ψ b) = eta ψ S b • chi ψ b := by
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  exact circulant_eigenvalue_eq_eta ψ S b y

/-- The colour-`j` eigenvalue is the dilated period `η_{jb}`. -/
theorem coloredAdjacency_chi {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (j : ℕ) (hj : (j : F) ≠ 0) (b : F) :
    coloredAdjacency G j (chi ψ b) = eta ψ G ((j : F) * b) • chi ψ b := by
  rw [coloredAdjacency, adjacencyEnd_chi, eta_dilate ψ G hj b]

/-! ## Exact multivariate Newton normal ordering -/

/-- The seventh Newton polynomial evaluated in the endomorphism algebra.  The displayed order is
canonical; `coloredAdjacency_commute` proves that all re-orderings of its monomials agree. -/
noncomputable def newtonSevenEnd {F : Type*} [Field F]
    (A1 A2 A3 A4 A5 A6 A7 : Module.End ℂ (Signal F)) : Module.End ℂ (Signal F) :=
  A1 ^ 7 - (21 : ℂ) • (A1 ^ 5 * A2) + (105 : ℂ) • (A1 ^ 3 * A2 ^ 2)
    + (70 : ℂ) • (A1 ^ 4 * A3) - (105 : ℂ) • (A1 * A2 ^ 3)
    - (420 : ℂ) • (A1 ^ 2 * A2 * A3) - (210 : ℂ) • (A1 ^ 3 * A4)
    + (210 : ℂ) • (A2 ^ 2 * A3) + (280 : ℂ) • (A1 * A3 ^ 2)
    + (630 : ℂ) • (A1 * A2 * A4) + (504 : ℂ) • (A1 ^ 2 * A5)
    - (420 : ℂ) • (A3 * A4) - (504 : ℂ) • (A2 * A5)
    - (840 : ℂ) • (A1 * A6) + (720 : ℂ) • A7

/-- A common eigenvector of seven endomorphisms is an eigenvector of their Newton polynomial,
with the scalar Newton polynomial as eigenvalue. -/
theorem newtonSevenEnd_eigen {F : Type*} [Field F]
    (A1 A2 A3 A4 A5 A6 A7 : Module.End ℂ (Signal F))
    (v : Signal F) (p1 p2 p3 p4 p5 p6 p7 : ℂ)
    (h1 : A1 v = p1 • v) (h2 : A2 v = p2 • v) (h3 : A3 v = p3 • v)
    (h4 : A4 v = p4 • v) (h5 : A5 v = p5 • v) (h6 : A6 v = p6 • v)
    (h7 : A7 v = p7 • v) :
    newtonSevenEnd A1 A2 A3 A4 A5 A6 A7 v =
      distinctSevenPolynomial p1 p2 p3 p4 p5 p6 p7 • v := by
  ext y
  simp [newtonSevenEnd, Module.End.mul_apply, pow_succ, h1, h2, h3, h4, h5, h6, h7,
    distinctSevenPolynomial]
  ring

/-- The genuine depth-seven graph normal-ordering built from `A_G,A_{2G},...,A_{7G}`. -/
noncomputable def dilationNewtonSeven {F : Type*} [Field F] [DecidableEq F]
    (G : Finset F) : Module.End ℂ (Signal F) :=
  newtonSevenEnd (coloredAdjacency G 1) (coloredAdjacency G 2)
    (coloredAdjacency G 3) (coloredAdjacency G 4) (coloredAdjacency G 5)
    (coloredAdjacency G 6) (coloredAdjacency G 7)

/-- Fourier diagonalization of the coloured normal-ordering. -/
theorem dilationNewtonSeven_chi {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0)
    (h5 : (5 : F) ≠ 0) (h6 : (6 : F) ≠ 0) (h7 : (7 : F) ≠ 0) :
    dilationNewtonSeven G (chi ψ b) =
      distinctSevenPolynomial
        (eta ψ G b) (eta ψ G ((2 : F) * b)) (eta ψ G ((3 : F) * b))
        (eta ψ G ((4 : F) * b)) (eta ψ G ((5 : F) * b))
        (eta ψ G ((6 : F) * b)) (eta ψ G ((7 : F) * b)) • chi ψ b := by
  unfold dilationNewtonSeven
  apply newtonSevenEnd_eigen
  · have h1 : ((1 : ℕ) : F) ≠ 0 := by
      rw [Nat.cast_one]
      exact one_ne_zero
    simpa only [Nat.cast_one, one_mul] using coloredAdjacency_chi ψ G 1 h1 b
  · exact coloredAdjacency_chi ψ G 2 h2 b
  · exact coloredAdjacency_chi ψ G 3 h3 b
  · exact coloredAdjacency_chi ψ G 4 h4 b
  · exact coloredAdjacency_chi ψ G 5 h5 b
  · exact coloredAdjacency_chi ψ G 6 h6 b
  · exact coloredAdjacency_chi ψ G 7 h7 b

/-- The phase family on the connection set at frequency `b`. -/
noncomputable def subgroupPhase {F : Type*} [Field F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F) : {x // x ∈ G} → ℂ :=
  fun x => ψ (b * x.1)

/-- Its `j`-th power sum is exactly the colour-`j` period. -/
theorem phasePowerSum_subgroupPhase {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F) (j : ℕ) :
    phasePowerSum (subgroupPhase ψ G b) j = eta ψ G ((j : F) * b) := by
  classical
  unfold phasePowerSum subgroupPhase eta
  rw [Finset.univ_eq_attach]
  calc
    (∑ i ∈ G.attach, ψ (b * (i : F)) ^ j) =
        ∑ x ∈ G, ψ (b * x) ^ j :=
      Finset.sum_attach G (fun x : F => ψ (b * x) ^ j)
    _ = ∑ x ∈ G, ψ ((j : F) * b * x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← AddChar.map_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul (R := F)]
      congr 1
      simp only [smul_eq_mul]
      ring

/-- **Exact injective eigenvalue.**  The coloured Newton operator, unlike a univariate
Hashimoto polynomial, recovers the ordered-injective transform pointwise. -/
theorem dilationNewtonSeven_chi_eq_injectiveTransform
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0)
    (h5 : (5 : F) ≠ 0) (h6 : (6 : F) ≠ 0) (h7 : (7 : F) ≠ 0) :
    dilationNewtonSeven G (chi ψ b) =
      injectiveSevenTransform (subgroupPhase ψ G b) • chi ψ b := by
  rw [dilationNewtonSeven_chi ψ G b h2 h3 h4 h5 h6 h7,
    injectiveSevenTransform_eq_distinctSevenPolynomial]
  simp only [phasePowerSum_subgroupPhase]
  simp

/-! ## Marginal Schatten data are permutation-blind -/

/-- The scalar marginal norm moment of colour `j`; on the common character basis this is the
`r`-th Schatten moment of `A_j`. -/
noncomputable def colorMarginalMoment {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (G : Finset F) (j : ℕ) (r : ℕ) : ℝ :=
  ∑ b : F, ‖eta ψ G ((j : F) * b)‖ ^ r

/-- Every nonzero colour has exactly the base marginal Schatten profile, in every exponent. -/
theorem colorMarginalMoment_eq_one {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (G : Finset F) (j r : ℕ) (hj : (j : F) ≠ 0) :
    colorMarginalMoment ψ G j r = colorMarginalMoment ψ G 1 r := by
  unfold colorMarginalMoment
  simp only [Nat.cast_one, one_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft₀ (j : F) hj) _ _ (fun b => rfl)

/-! ## A sharp marginal-profile no-go -/

/-- The two-point spectrum `(+1,-1)`. -/
def signSpectrum : Fin 2 → ℂ := ![1, -1]

/-- Fully aligned colours: every colour uses the same ordering of the two eigenvalues. -/
def alignedJoint : Fin 7 → Fin 2 → ℂ := fun _ b => signSpectrum b

/-- A second commuting diagonal joint spectrum.  Colours one through four retain the ordering;
colours five through seven swap it.  Every marginal multiset is still `{+1,-1}`. -/
def splitJoint : Fin 7 → Fin 2 → ℂ := fun j b =>
  if j.1 < 4 then signSpectrum b else -signSpectrum b

/-- Newton eigenvalue of a seven-colour joint spectrum at one common eigenvector. -/
def jointNewtonAt (P : Fin 7 → Fin 2 → ℂ) (b : Fin 2) : ℂ :=
  distinctSevenPolynomial (P 0 b) (P 1 b) (P 2 b) (P 3 b)
    (P 4 b) (P 5 b) (P 6 b)

/-- Hilbert--Schmidt/Frobenius energy of the Newton normal-ordering in the common eigenbasis. -/
noncomputable def jointNewtonEnergy (P : Fin 7 → Fin 2 → ℂ) : ℝ :=
  ∑ b : Fin 2, ‖jointNewtonAt P b‖ ^ 2

/-- Complete marginal norm-moment profile. -/
noncomputable def marginalNormProfile (P : Fin 7 → Fin 2 → ℂ) :
    Fin 7 → ℕ → ℝ :=
  fun j r => ∑ b : Fin 2, ‖P j b‖ ^ r

/-- The two systems have identical marginal Schatten moments at every colour and exponent. -/
theorem aligned_split_marginalNormProfile :
    marginalNormProfile alignedJoint = marginalNormProfile splitJoint := by
  funext j r
  fin_cases j <;>
    simp [marginalNormProfile, alignedJoint, splitJoint, signSpectrum, Fin.sum_univ_succ]

/-- The aligned joint arrangement has the full absolute coefficient-square energy `(7!)²`. -/
theorem alignedJoint_energy_exact : jointNewtonEnergy alignedJoint = 25401600 := by
  norm_num [jointNewtonEnergy, jointNewtonAt, alignedJoint, signSpectrum,
    distinctSevenPolynomial, Fin.sum_univ_succ]

/-- The split arrangement has energy `240²+96²=66816`. -/
theorem splitJoint_energy_exact : jointNewtonEnergy splitJoint = 66816 := by
  norm_num [jointNewtonEnergy, jointNewtonAt, splitJoint, signSpectrum,
    distinctSevenPolynomial, Fin.sum_univ_succ]

/-- The two equal-marginal systems lie on opposite sides of the production injective allowance. -/
theorem split_passes_aligned_fails_allowance :
    jointNewtonEnergy splitJoint < 126871 ∧
      126871 < jointNewtonEnergy alignedJoint := by
  rw [splitJoint_energy_exact, alignedJoint_energy_exact]
  norm_num

/-- **Marginal Schatten no-go.** No predicate of the complete seven-colour marginal norm profile
can characterize the desired Newton-energy allowance, even for commuting real diagonal systems. -/
theorem no_marginalSchatten_profile_decides_allowance :
    ¬ ∃ Φ : (Fin 7 → ℕ → ℝ) → Prop,
      ∀ P : Fin 7 → Fin 2 → ℂ,
        (Φ (marginalNormProfile P) ↔ jointNewtonEnergy P ≤ 126871) := by
  rintro ⟨Φ, hΦ⟩
  have hs : Φ (marginalNormProfile splitJoint) :=
    (hΦ splitJoint).2 (by rw [splitJoint_energy_exact]; norm_num)
  have ha : ¬ Φ (marginalNormProfile alignedJoint) := by
    intro h
    have hle := (hΦ alignedJoint).1 h
    rw [alignedJoint_energy_exact] at hle
    norm_num at hle
  apply ha
  rw [aligned_split_marginalNormProfile]
  exact hs

/-! ## The scalar normal-ordering has no generic Schur/SOS sign -/

/-- Every entry in both diagonal joint spectra is a contraction (in fact, a real unit). -/
theorem joint_examples_are_contractions (P : Fin 7 → Fin 2 → ℂ)
    (hP : P = alignedJoint ∨ P = splitJoint) :
    ∀ j b, ‖P j b‖ ≤ 1 := by
  rcases hP with rfl | rfl
  · intro j b
    fin_cases b <;> norm_num [alignedJoint, signSpectrum]
  · intro j b
    fin_cases j <;> fin_cases b <;> norm_num [splitJoint, signSpectrum]

/-- The exact Newton scalar is negative at one joint eigenvector of commuting real diagonal
contractions. -/
theorem alignedJoint_newton_negative : jointNewtonAt alignedJoint 1 = -5040 := by
  norm_num [jointNewtonAt, alignedJoint, signSpectrum, distinctSevenPolynomial]

/-- It is positive at one joint eigenvector of another such tuple. -/
theorem splitJoint_newton_positive : jointNewtonAt splitJoint 0 = 240 := by
  norm_num [jointNewtonAt, splitJoint, signSpectrum, distinctSevenPolynomial]

/-- Hence the Newton normal-ordering is not a positive polynomial on all commuting real diagonal
contractions; a Schur/SOS argument needs extra arithmetic support constraints. -/
theorem no_newton_nonnegative_on_commutingContractions :
    ¬ (∀ P : Fin 7 → Fin 2 → ℂ, (∀ j b, ‖P j b‖ ≤ 1) →
      ∀ b, 0 ≤ (jointNewtonAt P b).re) := by
  intro h
  have hn := h alignedJoint
    (joint_examples_are_contractions alignedJoint (Or.inl rfl)) 1
  rw [alignedJoint_newton_negative] at hn
  norm_num at hn

/-- Nor is it a negative polynomial on that class. -/
theorem no_newton_nonpositive_on_commutingContractions :
    ¬ (∀ P : Fin 7 → Fin 2 → ℂ, (∀ j b, ‖P j b‖ ≤ 1) →
      ∀ b, (jointNewtonAt P b).re ≤ 0) := by
  intro h
  have hp := h splitJoint
    (joint_examples_are_contractions splitJoint (Or.inr rfl)) 0
  rw [splitJoint_newton_positive] at hp
  norm_num at hp

#print axioms adjacencyEnd_commute
#print axioms coloredAdjacency_chi
#print axioms dilationNewtonSeven_chi_eq_injectiveTransform
#print axioms colorMarginalMoment_eq_one
#print axioms aligned_split_marginalNormProfile
#print axioms no_marginalSchatten_profile_decides_allowance
#print axioms no_newton_nonnegative_on_commutingContractions
#print axioms no_newton_nonpositive_on_commutingContractions

end ArkLib.ProximityGap.Frontier.BGKDilationColoredNewtonOperatorNoGo
