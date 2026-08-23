/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKRepeatedSectorNewtonAbsorption
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NonBacktrackingRelabelingNoGo

/-!
# Hashimoto subtraction does not isolate the primitive depth-seven packet

For a `d`-regular undirected graph, put `a=d-1`.  If `mu_+`, `mu_-` are the two
Ihara--Bass roots attached to an adjacency eigenvalue `x`, then

`mu_+^14 + mu_-^14 = H_14(a,x)`,

where

`H_14 = x^14 - 14a*x^12 + 77a^2*x^10 - 210a^3*x^8 + 294a^4*x^6
         - 196a^5*x^4 + 49a^6*x^2 - 2a^7`.

This file compares that exact polynomial with the degree-fourteen Gaussian/Wick normal-ordering
polynomial.  Their first subtraction coefficients are `14(d-1)` and `91d`, respectively.
Combinatorially this is the precise distinction: Hashimoto forbids the fourteen *cyclically
adjacent* reversals, whereas Wick/injective subtraction must address all `C(14,2)=91` possible
placements of a first paired repetition.  Thus `77d+14` first-pair placements survive the
Hashimoto transformation.  An explicit cyclically nonbacktracking, characteristic-zero closed
fourteen-step word with repeated directions proves that this mismatch is real, not just a
coefficient comparison.

There is a second, representation-theoretic obstruction.  The ordered-injective transform is the
multivariate Newton polynomial

`Q_7(eta_b, eta_(2b), ..., eta_(7b))`,

already proved in `_BGKRepeatedSectorNewtonAbsorption`.  Two seven-element unit-phase families can
have the same first power sum (the adjacency eigenvalue) but opposite injective transforms.  Hence
no univariate adjacency/Hashimoto polynomial can recover the injective packet pointwise.  A valid
graph-normal-ordering must retain the dilation-coloured operators `A_G, A_(2G), ..., A_(7G)` and,
after squaring, is genuinely degree fourteen.  The globally disjoint part then still requires the
sunflower overlap subtraction; ordinary nonbacktracking does not perform it.

Finally the production arithmetic is pinned exactly: even the ideal Wick coefficient `13!! =
135135` exceeds the injective allowance `126871` by `8264`, a saving strictly between `6.115%`
and `6.116%`.  Hashimoto positivity, Ihara zeta, and Ramanujan-style spectral preprocessing provide
no such saving without a new subgroup-arithmetic bound: the Hashimoto polynomial is negative at
the centre and its spectral radius is already the monotone relabeling formalized in
`_NonBacktrackingRelabelingNoGo`.

References:
* Bass, *The Ihara-Selberg zeta function of a tree lattice*, 1992.
* Bašić--Smajlović--Šabanac, *Discrete Space-Time Wave Kernels and Trace Identities on
  Regular Graphs*, arXiv:2606.27075.
* Bal, *Beyond Bass Collapse: New Irregular Edge-Space Invariants in Ihara Theory*,
  arXiv:2604.20578 (the regular case collapses to adjacency data).

Issue #466.  This is an exact socket/no-go, not a proof of the remaining arithmetic estimate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.BGKHashimotoWickSeparationNoGo

open BGKRepeatedSectorNewtonAbsorption

/-! ## Exact degree-fourteen Ihara--Bass polynomial -/

/-- The power sum of the two roots of `T^2-x*T+a` at exponent fourteen. -/
noncomputable def hashimotoFourteen (a : ℝ) : Polynomial ℝ :=
  monomial 14 1 - monomial 12 (14 * a) + monomial 10 (77 * a ^ 2)
    - monomial 8 (210 * a ^ 3) + monomial 6 (294 * a ^ 4)
    - monomial 4 (196 * a ^ 5) + monomial 2 (49 * a ^ 6) - monomial 0 (2 * a ^ 7)

/-- The Gaussian degree-fourteen normal-ordering polynomial at variance `d`.
Its constant coefficient is `-13!!*d^7`. -/
noncomputable def wickFourteen (d : ℝ) : Polynomial ℝ :=
  monomial 14 1 - monomial 12 (91 * d) + monomial 10 (3003 * d ^ 2)
    - monomial 8 (45045 * d ^ 3) + monomial 6 (315315 * d ^ 4)
    - monomial 4 (945945 * d ^ 5) + monomial 2 (945945 * d ^ 6)
    - monomial 0 (135135 * d ^ 7)

/-- Root-power recurrence underlying the Ihara--Bass trace polynomial. -/
noncomputable def rootPower (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 2
  | 1 => X
  | k + 2 => X * rootPower a (k + 1) - C a * rootPower a k

/-- The recurrence gives the displayed degree-fourteen polynomial exactly. -/
theorem rootPower_fourteen (a : ℝ) :
    rootPower a 14 = hashimotoFourteen a := by
  norm_num [rootPower, hashimotoFourteen]
  simp only [← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, C_1, C_ofNat]
  ring

/-- Evaluation form of the exact degree-fourteen Hashimoto polynomial. -/
theorem hashimotoFourteen_eval (a x : ℝ) :
    (hashimotoFourteen a).eval x =
      x ^ 14 - 14 * a * x ^ 12 + 77 * a ^ 2 * x ^ 10
        - 210 * a ^ 3 * x ^ 8 + 294 * a ^ 4 * x ^ 6
        - 196 * a ^ 5 * x ^ 4 + 49 * a ^ 6 * x ^ 2 - 2 * a ^ 7 := by
  simp [hashimotoFourteen]

/-- Unlike an even moment or an SOS certificate, the Hashimoto core polynomial is negative at
the centre whenever `a>0`.  Only the global graph trace (including the `±1` Bass band) is a
nonnegative walk count. -/
theorem hashimotoFourteen_eval_zero (a : ℝ) :
    (hashimotoFourteen a).eval 0 = -2 * a ^ 7 := by
  rw [hashimotoFourteen_eval]
  ring

/-! ## Hashimoto removes only cyclically adjacent first pairings -/

/-- The first Wick subtraction coefficient is the number `C(14,2)=91` of possible paired
positions. -/
theorem wickFourteen_coeff_twelve (d : ℝ) :
    (wickFourteen d).coeff 12 = -91 * d := by
  norm_num [wickFourteen, coeff_monomial]
  rw [← C_pow]
  rw [coeff_C]
  norm_num

/-- Hashimoto sees only the fourteen cyclic adjacencies. -/
theorem hashimotoFourteen_coeff_twelve (a : ℝ) :
    (hashimotoFourteen a).coeff 12 = -14 * a := by
  norm_num [hashimotoFourteen, coeff_monomial]
  rw [← C_pow]
  rw [coeff_C]
  norm_num

/-- At graph degree `d` (`a=d-1`), the exact unsubtracted first-pair coefficient is
`91d-14(d-1)=77d+14`. -/
theorem firstPairResidual_exact (d : ℝ) :
    (hashimotoFourteen (d - 1)).coeff 12 - (wickFourteen d).coeff 12 = 77 * d + 14 := by
  rw [hashimotoFourteen_coeff_twelve, wickFourteen_coeff_twelve]
  ring

/-- The production first-pair residual is enormous; this is a structural mismatch, not the
remaining small `8264` coefficient gap. -/
theorem production_firstPairResidual :
    (77 : ℕ) * 2 ^ 30 + 14 = 82678120462 := by
  norm_num

/-! ## An explicit nonbacktracking Wick word that survives -/

/-- A fourteen-step characteristic-zero closed word. -/
def survivingWickWord (i : Fin 14) : ℤ :=
  match i.1 with
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | 3 => -2
  | 4 => -3
  | 5 => 1
  | 6 => 1
  | 7 => -2
  | 8 => 1
  | 9 => 1
  | 10 => -2
  | 11 => 1
  | 12 => 1
  | _ => -2

/-- The cyclic adjacent-reversal predicate at length fourteen. -/
def CyclicallyNonbacktracking14 (w : Fin 14 → ℤ) : Prop :=
  w 1 ≠ -w 0 ∧ w 2 ≠ -w 1 ∧ w 3 ≠ -w 2 ∧ w 4 ≠ -w 3 ∧
  w 5 ≠ -w 4 ∧ w 6 ≠ -w 5 ∧ w 7 ≠ -w 6 ∧ w 8 ≠ -w 7 ∧
  w 9 ≠ -w 8 ∧ w 10 ≠ -w 9 ∧ w 11 ≠ -w 10 ∧ w 12 ≠ -w 11 ∧
  w 13 ≠ -w 12 ∧ w 0 ≠ -w 13

/-- The word is closed already over the integers, so it is a genuine Wick/tree contribution. -/
theorem survivingWickWord_closed : ∑ i, survivingWickWord i = 0 := by
  decide

/-- It nevertheless has no cyclically adjacent reversal, so Hashimoto subtraction retains it. -/
theorem survivingWickWord_nonbacktracking :
    CyclicallyNonbacktracking14 survivingWickWord := by
  norm_num [CyclicallyNonbacktracking14, survivingWickWord]

/-- The surviving word is far from globally injective: its directions repeat. -/
theorem survivingWickWord_not_injective :
    ¬ Function.Injective survivingWickWord := by
  intro h
  have heq : survivingWickWord (1 : Fin 14) = survivingWickWord (2 : Fin 14) := by
    norm_num [survivingWickWord]
  have hidx := h heq
  omega

/-! ## A univariate adjacency polynomial cannot recover the injective transform -/

/-- First unit-phase family: sum `1`, product `-1`. -/
def phaseFamilyMinus : Fin 7 → ℂ :=
  ![1, 1, 1, 1, -1, -1, -1]

/-- Second unit-phase family: the same sum `1`, product `+1`. -/
def phaseFamilyPlus : Fin 7 → ℂ :=
  ![1, 1, 1, -1, -1, Complex.I, -Complex.I]

theorem phaseFamilies_firstPowerSum_eq :
    phasePowerSum phaseFamilyMinus 1 = phasePowerSum phaseFamilyPlus 1 := by
  norm_num [phasePowerSum, phaseFamilyMinus, phaseFamilyPlus, Fin.sum_univ_succ]

theorem phaseFamilyMinus_injectiveTransform :
    injectiveSevenTransform phaseFamilyMinus = -5040 := by
  rw [injectiveSevenTransform_eq_distinctSevenPolynomial]
  norm_num [distinctSevenPolynomial, phasePowerSum, phaseFamilyMinus, Fin.sum_univ_succ]

theorem phaseFamilyPlus_injectiveTransform :
    injectiveSevenTransform phaseFamilyPlus = 5040 := by
  rw [injectiveSevenTransform_eq_distinctSevenPolynomial]
  norm_num [distinctSevenPolynomial, phasePowerSum, phaseFamilyPlus, Fin.sum_univ_succ,
    pow_succ, Complex.I_mul_I]

/-- **Pointwise univariate no-go.**  No function of the ordinary adjacency eigenvalue
`p1=sum_i w_i` can equal the ordered-injective depth-seven transform for every unit-phase family.
In particular no univariate Hashimoto/Chebyshev polynomial isolates the packet. -/
theorem no_univariate_injective_recovery (P : ℂ → ℂ) :
    ¬ (∀ w : Fin 7 → ℂ, (∀ i, ‖w i‖ = 1) →
      P (phasePowerSum w 1) = injectiveSevenTransform w) := by
  intro h
  have hm : ∀ i, ‖phaseFamilyMinus i‖ = 1 := by
    intro i
    fin_cases i <;> norm_num [phaseFamilyMinus]
  have hp : ∀ i, ‖phaseFamilyPlus i‖ = 1 := by
    intro i
    fin_cases i <;> norm_num [phaseFamilyPlus]
  have hminus := h phaseFamilyMinus hm
  have hplus := h phaseFamilyPlus hp
  rw [phaseFamilies_firstPowerSum_eq, phaseFamilyMinus_injectiveTransform] at hminus
  rw [phaseFamilyPlus_injectiveTransform] at hplus
  rw [hplus] at hminus
  norm_num at hminus

/-! ## What a genuine Ramanujan input would buy -/

/-- A pointwise Ramanujan cap `eta^2 <= 4d`, together with Parseval, gives coefficient `4^6=4096`
at the fourteenth moment.  Thus a *new proof* of the Ramanujan cap would overshoot the required
coefficient comfortably.  Ihara--Bass does not prove that cap: on a regular graph it only relabels
the same adjacency spectrum, as `_NonBacktrackingRelabelingNoGo` proves. -/
theorem fourteenthMoment_of_ramanujanCap {ι : Type*} (s : Finset ι) (eta : ι → ℝ)
    (d q : ℝ) (hd : 0 ≤ d)
    (hcap : ∀ i ∈ s, eta i ^ 2 ≤ 4 * d)
    (hparseval : ∑ i ∈ s, eta i ^ 2 ≤ q * d) :
    ∑ i ∈ s, eta i ^ 14 ≤ 4096 * q * d ^ 7 := by
  calc
    ∑ i ∈ s, eta i ^ 14 ≤ ∑ i ∈ s, 4096 * d ^ 6 * eta i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hsq : 0 ≤ eta i ^ 2 := sq_nonneg _
      have hp : (eta i ^ 2) ^ 6 ≤ (4 * d) ^ 6 :=
        pow_le_pow_left₀ hsq (hcap i hi) 6
      calc
        eta i ^ 14 = (eta i ^ 2) ^ 6 * eta i ^ 2 := by ring
        _ ≤ (4 * d) ^ 6 * eta i ^ 2 := mul_le_mul_of_nonneg_right hp hsq
        _ = 4096 * d ^ 6 * eta i ^ 2 := by ring
    _ = 4096 * d ^ 6 * (∑ i ∈ s, eta i ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4096 * d ^ 6 * (q * d) := by
      exact mul_le_mul_of_nonneg_left hparseval (by positivity)
    _ = 4096 * q * d ^ 7 := by ring

/-- The conditional Ramanujan coefficient is far below the live injective allowance. -/
theorem ramanujanCoefficient_lt_injectiveAllowance : (4096 : ℕ) < 126871 := by
  norm_num

/-! ## Exact production saving still required after ideal Wick scale -/

def wickCoefficient : ℕ := 135135
def injectiveAllowance : ℕ := 126871
def primitiveSavingGap : ℕ := wickCoefficient - injectiveAllowance

theorem primitiveSavingGap_exact : primitiveSavingGap = 8264 := by
  norm_num [primitiveSavingGap, wickCoefficient, injectiveAllowance]

/-- The saving is strictly larger than `6.115%`. -/
theorem primitiveSavingGap_gt_6115_per_100000 :
    6115 * wickCoefficient < 100000 * primitiveSavingGap := by
  norm_num [wickCoefficient, primitiveSavingGap, injectiveAllowance]

/-- The saving is strictly smaller than `6.116%`. -/
theorem primitiveSavingGap_lt_6116_per_100000 :
    100000 * primitiveSavingGap < 6116 * wickCoefficient := by
  norm_num [wickCoefficient, primitiveSavingGap, injectiveAllowance]

#print axioms rootPower_fourteen
#print axioms firstPairResidual_exact
#print axioms survivingWickWord_closed
#print axioms survivingWickWord_nonbacktracking
#print axioms no_univariate_injective_recovery
#print axioms fourteenthMoment_of_ramanujanCap
#print axioms primitiveSavingGap_exact

end ArkLib.ProximityGap.Frontier.BGKHashimotoWickSeparationNoGo
