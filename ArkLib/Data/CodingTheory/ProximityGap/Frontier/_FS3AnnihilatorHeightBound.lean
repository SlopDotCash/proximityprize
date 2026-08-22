/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS2PatternAnnihilatorResultant
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# LANE FS3 (#466, Fable session 2026-07-09): THE ANNIHILATOR HEIGHT BOUND — the pattern
  resultant has explicit dyadic height, completing the FS1 ledger's annihilator input

FS2 discharged existence (`N(g) ≠ 0`, `p ∣ N(g)` at common-root primes).  This brick adds the
HEIGHT: the Sylvester matrix of `(x^m + 1, g)` at degree parameters `(m, d)` has entries among
`{0, 1, coeffs of g}`, so Leibniz/`Matrix.det_le` gives

  `|N(g)| ≤ (m + d)! · B^(m + d)`      (`B` = coefficient bound of `g`, `B ≥ 1`),

and for the dyadic prize shape (`m = 2^k`, `d ≤ m`, `B ≤ 2^b`) the crude-but-clean form

  `|N(g)| ≤ 2^{(k + 1 + b) · 2^{k+1}}`.

`pattern_annihilator_exists_with_height` packages nonzero + divisibility + height in EXACTLY
the shape consumed by FS1's `annihilator_ledger_badPrime_cap` (`N ≤ H ≤ 2^L` with
`L = (k + 1 + b) · 2^{k+1}`).

**Remaining named input for the full FS1 almost-all-primes r=3 rung:** only the
exponent-parametrization of `addEnergy3` (pattern set of size `≤ n⁶`, coefficient bound
`B = 6 ≤ 2^3`, against the char-0 closed form).  Not claimed here.

Issue #466, lane FS3.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound

open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant

/-- The coefficients of `x^m + 1` are bounded by `1` in absolute value (for `0 < m`). -/
theorem fpoly_coeff_abs_le {m : ℕ} (hm : 0 < m) (i : ℕ) : |(fpoly m).coeff i| ≤ 1 := by
  simp only [fpoly, coeff_add, coeff_X_pow, coeff_one]
  split_ifs with h1 h2 h2 <;> simp_all

/-- **Entrywise bound on the Sylvester matrix** of `(x^m + 1, g)`: every entry is `0`, a
coefficient of `x^m + 1`, or a coefficient of `g`. -/
theorem sylvester_entry_abs_le {m d : ℕ} (hm : 0 < m) (g : ℤ[X]) {B : ℤ} (hB : 1 ≤ B)
    (hcoeff : ∀ i, |g.coeff i| ≤ B) (i j : Fin (m + d)) :
    |sylvester (fpoly m) g m d i j| ≤ B := by
  refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j <;>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  · split_ifs
    · exact hcoeff _
    · simpa using le_trans zero_le_one hB
  · split_ifs
    · exact le_trans (fpoly_coeff_abs_le hm _) hB
    · simpa using le_trans zero_le_one hB

/-- **The factorial height bound.**  `|N(g)| ≤ (m + d)! · B^(m + d)` where `d = deg g` and `B`
bounds the coefficients of `g`. -/
theorem patternResultant_abs_le {m : ℕ} (hm : 0 < m) (g : ℤ[X]) {B : ℤ} (hB : 1 ≤ B)
    (hcoeff : ∀ i, |g.coeff i| ≤ B) :
    |patternResultant m g|
      ≤ (Nat.factorial (m + g.natDegree) : ℤ) * B ^ (m + g.natDegree) := by
  have hdet := Matrix.det_le (A := sylvester (fpoly m) g m g.natDegree)
    (abv := AbsoluteValue.abs) (x := B)
    (fun i j => sylvester_entry_abs_le hm g hB hcoeff i j)
  simp only [Fintype.card_fin, nsmul_eq_mul, AbsoluteValue.abs_apply] at hdet
  have h1 : patternResultant m g = (sylvester (fpoly m) g m g.natDegree).det := by
    simp [patternResultant, resultant]
  rw [h1]
  exact hdet

/-- Crude clean dyadic form: `(m + d)! · B^(m + d) ≤ 2^{(k+1+b)·2^{k+1}}` for `m = 2^k`,
`d ≤ m`, `B ≤ 2^b`. -/
theorem factorial_height_le_two_pow {k b d : ℕ} (hd : d ≤ 2 ^ k) {B : ℤ} (hB : 0 ≤ B)
    (hBb : B ≤ 2 ^ b) :
    (Nat.factorial (2 ^ k + d) : ℤ) * B ^ (2 ^ k + d)
      ≤ 2 ^ ((k + 1 + b) * 2 ^ (k + 1)) := by
  have hDle : 2 ^ k + d ≤ 2 ^ (k + 1) := by
    have : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega
  -- factorial ≤ (2^{k+1})^(2^{k+1}) = 2^{(k+1)·2^{k+1}}
  have hfac : Nat.factorial (2 ^ k + d) ≤ 2 ^ ((k + 1) * 2 ^ (k + 1)) := by
    calc Nat.factorial (2 ^ k + d)
        ≤ Nat.factorial (2 ^ (k + 1)) := Nat.factorial_le hDle
      _ ≤ (2 ^ (k + 1)) ^ (2 ^ (k + 1)) := Nat.factorial_le_pow _
      _ = 2 ^ ((k + 1) * 2 ^ (k + 1)) := by rw [← pow_mul]
  -- B^(2^k+d) ≤ 2^{b·2^{k+1}}
  have hpow : B ^ (2 ^ k + d) ≤ (2 : ℤ) ^ (b * 2 ^ (k + 1)) := by
    calc B ^ (2 ^ k + d) ≤ ((2 : ℤ) ^ b) ^ (2 ^ k + d) :=
          pow_le_pow_left₀ hB hBb _
      _ = (2 : ℤ) ^ (b * (2 ^ k + d)) := by rw [← pow_mul]
      _ ≤ (2 : ℤ) ^ (b * 2 ^ (k + 1)) := by
          exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left b hDle)
  calc (Nat.factorial (2 ^ k + d) : ℤ) * B ^ (2 ^ k + d)
      ≤ (2 : ℤ) ^ ((k + 1) * 2 ^ (k + 1)) * (2 : ℤ) ^ (b * 2 ^ (k + 1)) := by
        refine mul_le_mul ?_ hpow (by positivity) (by positivity)
        exact_mod_cast hfac
    _ = 2 ^ ((k + 1 + b) * 2 ^ (k + 1)) := by rw [← pow_add]; ring_nf


/-- **THE COMPLETED ANNIHILATOR PACKAGE (FS1-shaped, with height).**  For `m = 2^k`, every
nonzero pattern polynomial `g` of degree `< m` with coefficients bounded by `2^b` owns an
annihilator `N` with `N ≠ 0`, `N ≤ 2^{(k+1+b)·2^{k+1}}` (the FS1 `H ≤ 2^L` input at
`L = (k+1+b)·2^{k+1}`), and `p ∣ N` at every common-root characteristic `p`. -/
theorem pattern_annihilator_exists_with_height {k b : ℕ} {g : ℤ[X]} (hg : g ≠ 0)
    (hdeg : g.natDegree < 2 ^ k) (hcoeff : ∀ i, |g.coeff i| ≤ 2 ^ b) :
    ∃ N : ℕ, N ≠ 0 ∧ N ≤ 2 ^ ((k + 1 + b) * 2 ^ (k + 1)) ∧
      ∀ (F : Type) (_ : Field F) (p : ℕ) (_ : CharP F p) (ζ : F),
        ζ ^ (2 ^ k) = -1 → aeval ζ g = 0 → p ∣ N := by
  have hm0 : 0 < 2 ^ k := by positivity
  refine ⟨(patternResultant (2 ^ k) g).natAbs, ?_, ?_, ?_⟩
  · simpa [Int.natAbs_eq_zero] using patternResultant_ne_zero hg hdeg
  · have h2b : (1 : ℤ) ≤ 2 ^ b := by exact_mod_cast Nat.one_le_two_pow (n := b)
    have habs := patternResultant_abs_le hm0 g h2b hcoeff
    have hheight := factorial_height_le_two_pow (k := k) (b := b)
      (d := g.natDegree) hdeg.le (by positivity) le_rfl
    have : |patternResultant (2 ^ k) g| ≤ 2 ^ ((k + 1 + b) * 2 ^ (k + 1)) :=
      le_trans habs hheight
    have habs_eq : (((patternResultant (2 ^ k) g).natAbs : ℤ)) =
        |patternResultant (2 ^ k) g| := Int.natCast_natAbs _
    exact_mod_cast habs_eq ▸ this
  · intro F _ p _ ζ hζ hroot
    have := charP_dvd_patternResultant_of_common_root hm0 F p ζ hζ hroot
    exact Int.ofNat_dvd.mp (by simpa [Int.dvd_natAbs] using this)

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms sylvester_entry_abs_le
#print axioms patternResultant_abs_le
#print axioms factorial_height_le_two_pow
#print axioms pattern_annihilator_exists_with_height

end ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound
