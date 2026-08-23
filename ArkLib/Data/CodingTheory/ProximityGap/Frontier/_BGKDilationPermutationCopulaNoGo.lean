/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKRepeatedSectorNewtonAbsorption

/-!
# A dilation-permutation copula no-go at depth seven

The abstract two-point example in `_BGKDilationColoredNewtonOperatorNoGo` permits an arbitrary
permutation at each colour.  Genuine periods have a stricter compatibility: all seven colours
come from one base profile by the dilations

`P_f(j,b) = f(jb)`.

This file tests that compatibility exactly on the prime cyclic index set `ZMod 13`.  The two
real-unit profiles below have four negative and nine positive entries, with their common value
multiset witnessed by an explicit permutation.  Every colour is a permutation pullback, so the
complete marginal norm/Schatten profiles agree.  Nevertheless their normalized seventh-Newton
energies straddle the live coefficient:

`953600 < 13 * 126871 < 64641152`.

Thus even genuine dilation-permutation compatibility does not make marginal spectral data
determine the mixed Newton energy.  The missing input is more rigid than the common permutation
action: it must use the fact that an actual period profile is the additive Fourier transform of
a multiplicative-subgroup indicator (and hence obeys its arithmetic identities).

Scope is important.  These sign profiles are an abstract copula model on the correct prime
dilation action; they are **not** asserted to be cyclotomic periods or additive-character
transforms of a subgroup.  The result is a sharp no-go for a marginal-only operator argument,
not a counterexample to the BGK estimate.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKDilationPermutationCopulaNoGo

open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption

/-! ## The genuine prime cyclic dilation action -/

/-- The prime cyclic frequency index used by the finite copula audit. -/
abbrev Frequency := ZMod 13

local instance primeThirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- Colour `j : Fin 7` represents multiplication by the nonzero residue `j+1`. -/
def colourMultiplier (j : Fin 7) : Frequency := (j.1 + 1 : ℕ)

theorem colourMultiplier_ne_zero (j : Fin 7) : colourMultiplier j ≠ 0 := by
  fin_cases j <;> decide

/-- Multiplication by every colour is literally a permutation of the prime cyclic index. -/
def colourPermutation (j : Fin 7) : Frequency ≃ Frequency :=
  Equiv.mulLeft₀ (colourMultiplier j) (colourMultiplier_ne_zero j)

/-- The joint seven-colour spectrum forced by a single base profile and the dilation action. -/
def dilationCopula (f : Frequency → ℤ) (j : Fin 7) (b : Frequency) : ℤ :=
  f (colourMultiplier j * b)

theorem dilationCopula_eq_permutationPullback (f : Frequency → ℤ) (j : Fin 7)
    (b : Frequency) :
    dilationCopula f j b = f (colourPermutation j b) := rfl

/-- Complete marginal absolute moments, the real diagonal version of the Schatten profile. -/
def marginalAbsMoment (f : Frequency → ℤ) (j : Fin 7) (r : ℕ) : ℕ :=
  ∑ b : Frequency, (dilationCopula f j b).natAbs ^ r

/-- Dilation makes every colour marginal a permutation of the base marginal. -/
theorem marginalAbsMoment_eq_base (f : Frequency → ℤ) (j : Fin 7) (r : ℕ) :
    marginalAbsMoment f j r = ∑ b : Frequency, (f b).natAbs ^ r := by
  unfold marginalAbsMoment dilationCopula
  exact Fintype.sum_equiv (Equiv.mulLeft₀ (colourMultiplier j) (colourMultiplier_ne_zero j))
    _ _ (fun _ => rfl)

/-! ## Two equimeasurable real-unit base profiles -/

/-- The low-energy negative support `{4,6,7,9}`. -/
def lowNegativeSupport : Finset Frequency := {4, 6, 7, 9}

/-- A real unit-valued base profile on `ZMod 13`. -/
def lowProfile (b : Frequency) : ℤ :=
  if b ∈ lowNegativeSupport then -1 else 1

/-- Swap `5 <-> 6` and `7 <-> 8`; this transports the low support to
`{4,5,8,9}`. -/
def copulaSwap : Frequency ≃ Frequency :=
  (Equiv.swap (5 : Frequency) 6).trans (Equiv.swap (7 : Frequency) 8)

/-- The high-energy profile is a permutation of `lowProfile`, hence has exactly the same
multiset of values. -/
def highProfile (b : Frequency) : ℤ := lowProfile (copulaSwap b)

/-- Explicit permutation witness for equality of the two value multisets.  This is stronger than
equality of all norm moments. -/
theorem low_high_equimeasurable :
    ∃ e : Frequency ≃ Frequency, ∀ b, lowProfile b = highProfile (e b) := by
  refine ⟨copulaSwap.symm, ?_⟩
  intro b
  simp [highProfile]

theorem lowProfile_real_unit (b : Frequency) : lowProfile b = -1 ∨ lowProfile b = 1 := by
  simp only [lowProfile]
  split_ifs <;> simp

theorem highProfile_real_unit (b : Frequency) : highProfile b = -1 ∨ highProfile b = 1 := by
  exact lowProfile_real_unit (copulaSwap b)

theorem lowProfile_natAbs (b : Frequency) : (lowProfile b).natAbs = 1 := by
  rcases lowProfile_real_unit b with h | h <;> simp [h]

theorem highProfile_natAbs (b : Frequency) : (highProfile b).natAbs = 1 := by
  rcases highProfile_real_unit b with h | h <;> simp [h]

/-- The two genuine dilation copulas have identical complete marginal absolute-moment profiles,
at every colour and every exponent. -/
theorem low_high_complete_marginal_profile :
    (fun j r => marginalAbsMoment lowProfile j r) =
      fun j r => marginalAbsMoment highProfile j r := by
  funext j r
  simp [marginalAbsMoment, dilationCopula, lowProfile_natAbs, highProfile_natAbs]

/-! ## Exact mixed Newton energy -/

/-- The integral seventh Newton/cycle-index polynomial. -/
def newtonSevenInt (p1 p2 p3 p4 p5 p6 p7 : ℤ) : ℤ :=
  p1 ^ 7 - 21 * p1 ^ 5 * p2 + 105 * p1 ^ 3 * p2 ^ 2
    + 70 * p1 ^ 4 * p3 - 105 * p1 * p2 ^ 3 - 420 * p1 ^ 2 * p2 * p3
    - 210 * p1 ^ 3 * p4 + 210 * p2 ^ 2 * p3 + 280 * p1 * p3 ^ 2
    + 630 * p1 * p2 * p4 + 504 * p1 ^ 2 * p5 - 420 * p3 * p4
    - 504 * p2 * p5 - 840 * p1 * p6 + 720 * p7

/-- Casting the integral polynomial gives the exact complex Newton polynomial used by the
coloured operator. -/
theorem newtonSevenInt_cast_complex (p1 p2 p3 p4 p5 p6 p7 : ℤ) :
    (newtonSevenInt p1 p2 p3 p4 p5 p6 p7 : ℂ) =
      distinctSevenPolynomial (p1 : ℂ) (p2 : ℂ) (p3 : ℂ) (p4 : ℂ)
        (p5 : ℂ) (p6 : ℂ) (p7 : ℂ) := by
  simp only [newtonSevenInt, distinctSevenPolynomial, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]

/-- The exact mixed seventh-Newton energy over all thirteen frequencies.  The zero-frequency
term vanishes for these profiles, so this is also their nonzero-frequency energy. -/
def dilationNewtonEnergy (f : Frequency → ℤ) : ℤ :=
  ∑ b : Frequency,
    newtonSevenInt (dilationCopula f 0 b) (dilationCopula f 1 b)
      (dilationCopula f 2 b) (dilationCopula f 3 b) (dilationCopula f 4 b)
      (dilationCopula f 5 b) (dilationCopula f 6 b) ^ 2

theorem lowProfile_zero_newton :
    newtonSevenInt (dilationCopula lowProfile 0 0) (dilationCopula lowProfile 1 0)
      (dilationCopula lowProfile 2 0) (dilationCopula lowProfile 3 0)
      (dilationCopula lowProfile 4 0) (dilationCopula lowProfile 5 0)
      (dilationCopula lowProfile 6 0) = 0 := by
  decide

theorem highProfile_zero_newton :
    newtonSevenInt (dilationCopula highProfile 0 0) (dilationCopula highProfile 1 0)
      (dilationCopula highProfile 2 0) (dilationCopula highProfile 3 0)
      (dilationCopula highProfile 4 0) (dilationCopula highProfile 5 0)
      (dilationCopula highProfile 6 0) = 0 := by
  decide

/-- Exact raw energy of the low copula. -/
theorem lowProfile_energy_exact : dilationNewtonEnergy lowProfile = 953600 := by
  decide

/-- Exact raw energy of the equimeasurable high copula. -/
theorem highProfile_energy_exact : dilationNewtonEnergy highProfile = 64641152 := by
  decide

/-- **Dilation-compatible copula separation.**  Cross multiplication by the full frequency-card
`13` shows that the normalized energies lie on opposite sides of `126871`. -/
theorem normalized_energy_straddles_injective_allowance :
    dilationNewtonEnergy lowProfile < 13 * 126871 ∧
      13 * 126871 < dilationNewtonEnergy highProfile := by
  rw [lowProfile_energy_exact, highProfile_energy_exact]
  norm_num

/-- The same separation stated as normalized rational trace energies. -/
theorem normalized_trace_energy_straddles :
    (dilationNewtonEnergy lowProfile : ℚ) / 13 < 126871 ∧
      (126871 : ℚ) < (dilationNewtonEnergy highProfile : ℚ) / 13 := by
  rw [lowProfile_energy_exact, highProfile_energy_exact]
  norm_num

/-- No predicate of complete marginal absolute moments can decide the normalized Newton-energy
allowance, even after requiring one common dilation action on `ZMod 13`. -/
theorem no_marginal_profile_decides_dilation_normalized_allowance :
    ¬ ∃ Phi : (Fin 7 → ℕ → ℕ) → Prop,
      ∀ f : Frequency → ℤ,
        (Phi (fun j r => marginalAbsMoment f j r) ↔
          dilationNewtonEnergy f ≤ 13 * 126871) := by
  rintro ⟨Phi, hPhi⟩
  have hlow : Phi (fun j r => marginalAbsMoment lowProfile j r) :=
    (hPhi lowProfile).2 (by rw [lowProfile_energy_exact]; norm_num)
  have hhigh : ¬ Phi (fun j r => marginalAbsMoment highProfile j r) := by
    intro h
    have hle := (hPhi highProfile).1 h
    rw [highProfile_energy_exact] at hle
    norm_num at hle
  apply hhigh
  rw [← low_high_complete_marginal_profile]
  exact hlow

#print axioms marginalAbsMoment_eq_base
#print axioms low_high_equimeasurable
#print axioms low_high_complete_marginal_profile
#print axioms newtonSevenInt_cast_complex
#print axioms normalized_energy_straddles_injective_allowance
#print axioms no_marginal_profile_decides_dilation_normalized_allowance

end ArkLib.ProximityGap.Frontier.BGKDilationPermutationCopulaNoGo
