/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKRepeatedSectorNewtonAbsorption
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RepeatedPartitionHolderBudgetPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKShiftedEtaPaddedHolder

/-!
# Full sparse Newton enumeration for the repeated depth-seven sector

This file removes the last finite-combinatorics trust gap in the repeated-sector lane.  It gives
all 88 nonzero monomials of

`p₁¹⁴ - distinctSevenPolynomial(p₁,...,p₇)²`,

records each monomial by its integer coefficient and seven-component exponent vector, and checks
the entire table by `ring`.  It then computes, in the kernel, the absolute coefficient mass in
each block-count fibre.  The result is exactly the previously advertised ledger

`B₂,...,B₁₃ = 518400,2540160,...,791,42`.

The analytic half is no longer schematic either.  Every exponent vector is canonically expanded
to a list of shifts in `{1,...,7}`.  The triangle envelope for the repeated transform is expressed
using precisely these lists, and every resulting frequency-summed monomial is discharged by
`production_small_shift_holder_canonical`.

The final fixed-target step is also discharged here.  Padding at the exact integer `79880` gives
`79880^14 ≤ 2^18*(2^30)^7`, while the twelve grouped masses give a normalized coefficient
`137.86485... < 138`; both facts are checked as exact rational inequalities.  This closes the
repeated contribution at the target value used by the noncircular barrier.  Issue #466.
-/

set_option autoImplicit false

open scoped BigOperators NNReal
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption
open ArkLib.ProximityGap.Frontier.BGKShiftedEtaPaddedHolder

namespace ArkLib.ProximityGap.Frontier.BGKRepeatedNewtonFullEnumeration

/-! ## Sparse polynomial data -/

/-- One sparse monomial: an integer coefficient and exponents of `p₁,...,p₇`. -/
structure SparseTerm where
  coeff : ℤ
  exponent : Fin 7 → ℕ
  deriving DecidableEq, Repr

/-- Constructor used to keep the checked table readable. -/
def mkTerm (c : ℤ) (e : Fin 7 → ℕ) : SparseTerm := ⟨c, e⟩

/-- Expand an exponent vector into its canonical factor list.  Index `j` represents the shift
`j+1`; repetition represents a power. -/
def SparseTerm.factorList (t : SparseTerm) : List (Fin 7) :=
  (List.finRange 7).flatMap fun j => List.replicate (t.exponent j) j

/-- Number of free blocks/factors in a monomial. -/
def SparseTerm.blockCount (t : SparseTerm) : ℕ := t.factorList.length

/-- Fast reduction rule for block counts in the explicit table. -/
@[simp] theorem blockCount_mkTerm (c : ℤ) (a b d e f g h : ℕ) :
    (mkTerm c ![a, b, d, e, f, g, h]).blockCount = a + b + d + e + f + g + h := by
  simp [SparseTerm.blockCount, SparseTerm.factorList, mkTerm, List.finRange_succ]
  omega

/-- Evaluate a sparse monomial over the complex numbers. -/
def SparseTerm.eval (t : SparseTerm) (p : Fin 7 → ℂ) : ℂ :=
  (t.coeff : ℂ) * p 0 ^ t.exponent 0 * p 1 ^ t.exponent 1 *
    p 2 ^ t.exponent 2 * p 3 ^ t.exponent 3 * p 4 ^ t.exponent 4 *
    p 5 ^ t.exponent 5 * p 6 ^ t.exponent 6

/-- Fast reduction rule for the explicit table. -/
@[simp] theorem eval_mkTerm (c : ℤ) (a b d e f g h : ℕ) (p : Fin 7 → ℂ) :
    (mkTerm c ![a, b, d, e, f, g, h]).eval p =
      (c : ℂ) * p 0 ^ a * p 1 ^ b * p 2 ^ d * p 3 ^ e *
        p 4 ^ f * p 5 ^ g * p 6 ^ h := by
  rfl

/-- The factor-list evaluation is exactly the usual exponent-vector evaluation. -/
theorem SparseTerm.factorList_map_prod (t : SparseTerm) (p : Fin 7 → ℂ) :
    (t.factorList.map p).prod = ∏ j, p j ^ t.exponent j := by
  have h : ∀ l : List (Fin 7),
      (l.flatMap fun j => List.replicate (t.exponent j) (p j)).prod =
        (l.map fun j => p j ^ t.exponent j).prod := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih => simp [ih, List.prod_append]
  rw [SparseTerm.factorList, List.map_flatMap]
  simp only [List.map_replicate]
  rw [h]
  exact (Fin.prod_univ_def _).symm

/-- The compact factor-list spelling and the seven-coordinate spelling of evaluation agree. -/
theorem SparseTerm.eval_eq_factorList (t : SparseTerm) (p : Fin 7 → ℂ) :
    t.eval p = (t.coeff : ℂ) * (t.factorList.map p).prod := by
  unfold SparseTerm.eval SparseTerm.factorList
  norm_num [List.finRange_succ, List.map_flatMap, List.prod_append,
    List.prod_replicate, Fin.succ]
  have h2 : (⟨2, by omega⟩ : Fin 7) = 2 := by rfl
  have h3 : (⟨3, by omega⟩ : Fin 7) = 3 := by rfl
  have h4 : (⟨4, by omega⟩ : Fin 7) = 4 := by rfl
  have h5 : (⟨5, by omega⟩ : Fin 7) = 5 := by rfl
  have h6 : (⟨6, by omega⟩ : Fin 7) = 6 := by rfl
  rw [h2, h3, h4, h5, h6]
  ring

/-- Complete normalized expansion of `p₁¹⁴-D₇²`.  Terms are ordered by decreasing block count.
The data were generated independently, but the theorem `repeatedTerms_eval` below checks every
entry and sign by `ring`; no computation oracle enters the trusted result. -/
def repeatedTerms : List SparseTerm := [
  mkTerm (42) ![12, 1, 0, 0, 0, 0, 0],
  mkTerm (-140) ![11, 0, 1, 0, 0, 0, 0],
  mkTerm (-651) ![10, 2, 0, 0, 0, 0, 0],
  mkTerm (420) ![10, 0, 0, 1, 0, 0, 0],
  mkTerm (3780) ![9, 1, 1, 0, 0, 0, 0],
  mkTerm (4620) ![8, 3, 0, 0, 0, 0, 0],
  mkTerm (-1008) ![9, 0, 0, 0, 1, 0, 0],
  mkTerm (-10080) ![8, 1, 0, 1, 0, 0, 0],
  mkTerm (-5460) ![8, 0, 2, 0, 0, 0, 0],
  mkTerm (-32760) ![7, 2, 1, 0, 0, 0, 0],
  mkTerm (-15435) ![6, 4, 0, 0, 0, 0, 0],
  mkTerm (1680) ![8, 0, 0, 0, 0, 1, 0],
  mkTerm (22176) ![7, 1, 0, 0, 1, 0, 0],
  mkTerm (30240) ![7, 0, 1, 1, 0, 0, 0],
  mkTerm (70560) ![6, 2, 0, 1, 0, 0, 0],
  mkTerm (70560) ![6, 1, 2, 0, 0, 0, 0],
  mkTerm (111720) ![5, 3, 1, 0, 0, 0, 0],
  mkTerm (22050) ![4, 5, 0, 0, 0, 0, 0],
  mkTerm (-1440) ![7, 0, 0, 0, 0, 0, 1],
  mkTerm (-35280) ![6, 1, 0, 0, 0, 1, 0],
  mkTerm (-70560) ![6, 0, 1, 0, 1, 0, 0],
  mkTerm (-44100) ![6, 0, 0, 2, 0, 0, 0],
  mkTerm (-127008) ![5, 2, 0, 0, 1, 0, 0],
  mkTerm (-282240) ![5, 1, 1, 1, 0, 0, 0],
  mkTerm (-39200) ![5, 0, 3, 0, 0, 0, 0],
  mkTerm (-176400) ![4, 3, 0, 1, 0, 0, 0],
  mkTerm (-264600) ![4, 2, 2, 0, 0, 0, 0],
  mkTerm (-132300) ![3, 4, 1, 0, 0, 0, 0],
  mkTerm (-11025) ![2, 6, 0, 0, 0, 0, 0],
  mkTerm (30240) ![5, 1, 0, 0, 0, 0, 1],
  mkTerm (117600) ![5, 0, 1, 0, 0, 1, 0],
  mkTerm (211680) ![5, 0, 0, 1, 1, 0, 0],
  mkTerm (176400) ![4, 2, 0, 0, 0, 1, 0],
  mkTerm (493920) ![4, 1, 1, 0, 1, 0, 0],
  mkTerm (264600) ![4, 1, 0, 2, 0, 0, 0],
  mkTerm (176400) ![4, 0, 2, 1, 0, 0, 0],
  mkTerm (211680) ![3, 3, 0, 0, 1, 0, 0],
  mkTerm (705600) ![3, 2, 1, 1, 0, 0, 0],
  mkTerm (235200) ![3, 1, 3, 0, 0, 0, 0],
  mkTerm (132300) ![2, 4, 0, 1, 0, 0, 0],
  mkTerm (235200) ![2, 3, 2, 0, 0, 0, 0],
  mkTerm (44100) ![1, 5, 1, 0, 0, 0, 0],
  mkTerm (-100800) ![4, 0, 1, 0, 0, 0, 1],
  mkTerm (-352800) ![4, 0, 0, 1, 0, 1, 0],
  mkTerm (-254016) ![4, 0, 0, 0, 2, 0, 0],
  mkTerm (-151200) ![3, 2, 0, 0, 0, 0, 1],
  mkTerm (-705600) ![3, 1, 1, 0, 0, 1, 0],
  mkTerm (-846720) ![3, 1, 0, 1, 1, 0, 0],
  mkTerm (-282240) ![3, 0, 2, 0, 1, 0, 0],
  mkTerm (-176400) ![3, 0, 1, 2, 0, 0, 0],
  mkTerm (-176400) ![2, 3, 0, 0, 0, 1, 0],
  mkTerm (-635040) ![2, 2, 1, 0, 1, 0, 0],
  mkTerm (-396900) ![2, 2, 0, 2, 0, 0, 0],
  mkTerm (-705600) ![2, 1, 2, 1, 0, 0, 0],
  mkTerm (-78400) ![2, 0, 4, 0, 0, 0, 0],
  mkTerm (-105840) ![1, 4, 0, 0, 1, 0, 0],
  mkTerm (-352800) ![1, 3, 1, 1, 0, 0, 0],
  mkTerm (-117600) ![1, 2, 3, 0, 0, 0, 0],
  mkTerm (-44100) ![0, 4, 2, 0, 0, 0, 0],
  mkTerm (302400) ![3, 0, 0, 1, 0, 0, 1],
  mkTerm (846720) ![3, 0, 0, 0, 1, 1, 0],
  mkTerm (604800) ![2, 1, 1, 0, 0, 0, 1],
  mkTerm (1058400) ![2, 1, 0, 1, 0, 1, 0],
  mkTerm (508032) ![2, 1, 0, 0, 2, 0, 0],
  mkTerm (470400) ![2, 0, 2, 0, 0, 1, 0],
  mkTerm (423360) ![2, 0, 1, 1, 1, 0, 0],
  mkTerm (151200) ![1, 3, 0, 0, 0, 0, 1],
  mkTerm (352800) ![1, 2, 1, 0, 0, 1, 0],
  mkTerm (635040) ![1, 2, 0, 1, 1, 0, 0],
  mkTerm (282240) ![1, 1, 2, 0, 1, 0, 0],
  mkTerm (529200) ![1, 1, 1, 2, 0, 0, 0],
  mkTerm (235200) ![1, 0, 3, 1, 0, 0, 0],
  mkTerm (211680) ![0, 3, 1, 0, 1, 0, 0],
  mkTerm (176400) ![0, 2, 2, 1, 0, 0, 0],
  mkTerm (-725760) ![2, 0, 0, 0, 1, 0, 1],
  mkTerm (-705600) ![2, 0, 0, 0, 0, 2, 0],
  mkTerm (-907200) ![1, 1, 0, 1, 0, 0, 1],
  mkTerm (-846720) ![1, 1, 0, 0, 1, 1, 0],
  mkTerm (-403200) ![1, 0, 2, 0, 0, 0, 1],
  mkTerm (-705600) ![1, 0, 1, 1, 0, 1, 0],
  mkTerm (-302400) ![0, 2, 1, 0, 0, 0, 1],
  mkTerm (-254016) ![0, 2, 0, 0, 2, 0, 0],
  mkTerm (-423360) ![0, 1, 1, 1, 1, 0, 0],
  mkTerm (-176400) ![0, 0, 2, 2, 0, 0, 0],
  mkTerm (1209600) ![1, 0, 0, 0, 0, 1, 1],
  mkTerm (725760) ![0, 1, 0, 0, 1, 0, 1],
  mkTerm (604800) ![0, 0, 1, 1, 0, 0, 1],
  mkTerm (-518400) ![0, 0, 0, 0, 0, 0, 2]
]

/-- There are exactly 88 nonzero normalized monomials. -/
theorem repeatedTerms_length : repeatedTerms.length = 88 := by
  norm_num [repeatedTerms]

/-- Evaluation of the sparse table. -/
def repeatedTermsEval (p : Fin 7 → ℂ) : ℂ :=
  (repeatedTerms.map fun t => t.eval p).sum

/-- **Kernel certificate for the complete generated table.**  Unfolding the table leaves a
polynomial identity over `ℂ`, closed by normalization in the commutative ring. -/
theorem repeatedTerms_eval (p : Fin 7 → ℂ) :
    repeatedTermsEval p =
      repeatedSevenTransform (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) := by
  simp only [repeatedTermsEval, repeatedTerms, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_mkTerm]
  unfold repeatedSevenTransform distinctSevenPolynomial
  ring

/-! ## Exact grouped coefficient mass -/

/-- Absolute coefficient mass in the fibre with exactly `k` free blocks. -/
def coefficientMass (k : ℕ) : ℕ :=
  ((repeatedTerms.filter fun t => t.blockCount = k).map fun t => t.coeff.natAbs).sum

/-- **Complete block-count ledger.**  This computation uses ordinary kernel reduction (`decide`),
not `native_decide`; it is independently tied to the polynomial by `repeatedTerms_eval`. -/
theorem coefficientMass_table :
    coefficientMass 2 = 518400 ∧
    coefficientMass 3 = 2540160 ∧
    coefficientMass 4 = 5450256 ∧
    coefficientMass 5 = 6787872 ∧
    coefficientMass 6 = 5482456 ∧
    coefficientMass 7 = 3034920 ∧
    coefficientMass 8 = 1184153 ∧
    coefficientMass 9 = 328986 ∧
    coefficientMass 10 = 64743 ∧
    coefficientMass 11 = 8820 ∧
    coefficientMass 12 = 791 ∧
    coefficientMass 13 = 42 := by
  decide

/-- Every table term has between two and thirteen factors. -/
theorem repeatedTerms_block_range (t : SparseTerm) (ht : t ∈ repeatedTerms) :
    2 ≤ t.blockCount ∧ t.blockCount ≤ 13 := by
  revert t
  decide

/-- The mass table is literally the earlier `repeatedMobiusMass` table. -/
theorem coefficientMass_eq_repeatedMobiusMass (k : ℕ) :
    coefficientMass k =
      ArkLib.ProximityGap.Frontier.RepeatedPartitionHolderBudgetPin.repeatedMobiusMass k := by
  by_cases hk : k < 2
  · interval_cases k <;> decide
  by_cases hk' : k ≤ 13
  · interval_cases k <;> decide
  · have hk14 : 14 ≤ k := by omega
    have hfilter : repeatedTerms.filter (fun t => t.blockCount = k) = [] := by
      rw [List.filter_eq_nil_iff]
      intro t ht
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      have hrange := repeatedTerms_block_range t ht
      omega
    rw [coefficientMass, hfilter]
    simp only [List.map_nil, List.sum_nil]
    simp only [ArkLib.ProximityGap.Frontier.RepeatedPartitionHolderBudgetPin.repeatedMobiusMass]
    split <;> omega

/-- Total mass, now derived from the fully checked polynomial table. -/
theorem coefficientMass_total :
    ∑ k ∈ Finset.Icc 2 13, coefficientMass k = 25401599 := by
  rw [Finset.sum_congr rfl fun k hk => coefficientMass_eq_repeatedMobiusMass k]
  exact ArkLib.ProximityGap.Frontier.RepeatedPartitionHolderBudgetPin.repeatedMobiusMass_total

/-! ## Triangle envelope and the exact Holder consumer -/

/-- Canonical enumeration of the factors in a sparse term. -/
def SparseTerm.which (t : SparseTerm) : Fin t.blockCount → Fin 7 :=
  fun i => t.factorList[i]

/-- A product over `which` is exactly the factor-list product. -/
theorem SparseTerm.prod_which (t : SparseTerm) {M : Type*} [CommMonoid M]
    (z : Fin 7 → M) :
    (∏ i, z (t.which i)) = (t.factorList.map z).prod := by
  exact Fin.prod_univ_fun_getElem t.factorList z

/-- Complex integer coefficients have NNReal norm equal to their natural absolute value. -/
theorem nnnorm_intCast_complex (c : ℤ) : ‖(c : ℂ)‖₊ = (c.natAbs : NNReal) := by
  ext
  change ‖(c : ℂ)‖ = (c.natAbs : ℝ)
  rw [Complex.norm_intCast, ← Int.cast_abs, Nat.cast_natAbs]

/-- Norm commutes with a finite list product. -/
theorem nnnorm_list_prod (l : List ℂ) :
    ‖l.prod‖₊ = (l.map fun z => ‖z‖₊).prod := by
  induction l with
  | nil => simp
  | cons z l ih => simp [ih]

/-- Triangle inequality for a finite list sum. -/
theorem nnnorm_list_sum_le (l : List ℂ) :
    ‖l.sum‖₊ ≤ (l.map fun z => ‖z‖₊).sum := by
  induction l with
  | nil => simp
  | cons z l ih =>
      calc
        ‖z + l.sum‖₊ ≤ ‖z‖₊ + ‖l.sum‖₊ := nnnorm_add_le _ _
        _ ≤ ‖z‖₊ + (l.map fun w => ‖w‖₊).sum := add_le_add le_rfl ih
        _ = ((z :: l).map fun w => ‖w‖₊).sum := rfl

/-- Exact positive monomial attached to a sparse term. -/
noncomputable def termNormEnvelope (t : SparseTerm) (p : Fin 7 → ℂ) : NNReal :=
  (t.coeff.natAbs : NNReal) * ∏ i, ‖p (t.which i)‖₊

/-- Norm of one signed sparse term is exactly its positive envelope. -/
theorem SparseTerm.nnnorm_eval (t : SparseTerm) (p : Fin 7 → ℂ) :
    ‖t.eval p‖₊ = termNormEnvelope t p := by
  rw [SparseTerm.eval_eq_factorList, nnnorm_mul, nnnorm_intCast_complex,
    nnnorm_list_prod]
  simp only [List.map_map, termNormEnvelope]
  change (t.coeff.natAbs : NNReal) *
      (t.factorList.map fun j => ‖p j‖₊).prod =
    (t.coeff.natAbs : NNReal) * ∏ i, ‖p (t.which i)‖₊
  rw [← SparseTerm.prod_which t (fun j => ‖p j‖₊)]

/-- Full pointwise positive envelope for the repeated Newton transform. -/
noncomputable def repeatedNormEnvelope (p : Fin 7 → ℂ) : NNReal :=
  (repeatedTerms.map fun t => termNormEnvelope t p).sum

/-- **Pointwise 88-term triangle envelope.** -/
theorem repeatedSevenTransform_nnnorm_le_envelope (p : Fin 7 → ℂ) :
    ‖repeatedSevenTransform (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6)‖₊ ≤
      repeatedNormEnvelope p := by
  rw [← repeatedTerms_eval]
  unfold repeatedTermsEval repeatedNormEnvelope
  have h := nnnorm_list_sum_le (repeatedTerms.map fun t => t.eval p)
  simpa only [List.map_map, Function.comp_def, SparseTerm.nnnorm_eval] using h

/-- Exchange a finite Fintype sum with a finite list sum. -/
theorem sum_list_sum_exchange {B A : Type*} [Fintype B]
    (l : List A) (f : B → A → NNReal) :
    (∑ b, (l.map fun a => f b a).sum) =
      (l.map fun a => ∑ b, f b a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- Distribute multiplication over a finite list sum. -/
theorem list_sum_mul (l : List NNReal) (x : NNReal) :
    (l.map fun a => a * x).sum = l.sum * x := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_mul]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Frequency sum of the positive monomial belonging to one sparse term. -/
noncomputable def etaTermSum
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F) (t : SparseTerm) : NNReal :=
  ∑ b : Fˣ, ∏ i,
    ‖eta psi G (((smallCoefficientUnit hchar (t.which i)) * b : Fˣ) : F)‖₊

/-- The complete 88-term Holder envelope after summing over nonzero frequency. -/
noncomputable def repeatedEtaEnvelope
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F) : NNReal :=
  (repeatedTerms.map fun t =>
    (t.coeff.natAbs : NNReal) * etaTermSum psi G hchar t).sum

/-- **Summed repeated-sector triangle inequality.**  This is the exact bridge from the Newton
polynomial to the 88 positive shifted eta monomials. -/
theorem sum_repeatedSevenTransform_nnnorm_le_etaEnvelope
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F) :
    (∑ b : Fˣ,
        ‖repeatedSevenTransform
          (eta psi G (((smallCoefficientUnit hchar 0) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 1) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 2) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 3) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 4) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 5) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 6) * b : Fˣ) : F))‖₊) ≤
      repeatedEtaEnvelope psi G hchar := by
  let p : Fˣ → Fin 7 → ℂ := fun b j =>
    eta psi G (((smallCoefficientUnit hchar j) * b : Fˣ) : F)
  calc
    (∑ b : Fˣ,
        ‖repeatedSevenTransform (p b 0) (p b 1) (p b 2) (p b 3)
          (p b 4) (p b 5) (p b 6)‖₊) ≤
        ∑ b : Fˣ, repeatedNormEnvelope (p b) := by
      exact Finset.sum_le_sum fun b _ => repeatedSevenTransform_nnnorm_le_envelope (p b)
    _ = repeatedEtaEnvelope psi G hchar := by
      unfold repeatedNormEnvelope repeatedEtaEnvelope termNormEnvelope etaTermSum
      rw [sum_list_sum_exchange]
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [Finset.mul_sum]

/-- **Every one of the 88 checked monomials is consumed by the canonical shifted-eta Holder
theorem.**  There is no residual eta/dilation adapter. -/
theorem etaTermSum_canonical_holder
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F)
    (t : SparseTerm) (ht : t ∈ repeatedTerms) :
    canonicalPaddingScale psi G ^ (14 - t.blockCount) * etaTermSum psi G hchar t ≤
      nonzeroFourteenthMoment psi G := by
  have hk : t.blockCount ≤ 13 := (repeatedTerms_block_range t ht).2
  simpa only [etaTermSum] using
    production_small_shift_holder_canonical psi G hchar t.blockCount hk t.which

/-- Fixed-budget variant of the shifted eta Holder adapter.  Unlike the canonical-root form,
this lets the bootstrap evaluate the repeated envelope at a proposed target `T`: every eta factor
uses `M14 ≤ T`, while the constant padding only needs `#Fˣ * R^14 ≤ T`. -/
theorem production_small_shift_fixed_budget_holder
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F)
    (k : ℕ) (hk : k ≤ 13) (which : Fin k → Fin 7) (R T : NNReal)
    (hmoment : nonzeroFourteenthMoment psi G ≤ T)
    (hpadding : (Fintype.card Fˣ : NNReal) * R ^ 14 ≤ T) :
    R ^ (14 - k) *
        (∑ b : Fˣ, ∏ j,
          ‖eta psi G (((smallCoefficientUnit hchar (which j)) * b : Fˣ) : F)‖₊) ≤ T := by
  apply finite_family_padded_holder k (by omega) R T
      (fun j b => ‖eta psi G (((smallCoefficientUnit hchar (which j)) * b : Fˣ) : F)‖₊)
  · intro j
    exact (sum_eta_nnnorm_pow_fourteen_mul_unit psi G
      (smallCoefficientUnit hchar (which j))).le.trans hmoment
  · exact hpadding

/-- Every checked Newton term is consumed at an arbitrary fixed budget. -/
theorem etaTermSum_fixed_budget_holder
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F)
    (t : SparseTerm) (ht : t ∈ repeatedTerms) (R T : NNReal)
    (hmoment : nonzeroFourteenthMoment psi G ≤ T)
    (hpadding : (Fintype.card Fˣ : NNReal) * R ^ 14 ≤ T) :
    R ^ (14 - t.blockCount) * etaTermSum psi G hchar t ≤ T := by
  have hk : t.blockCount ≤ 13 := (repeatedTerms_block_range t ht).2
  simpa only [etaTermSum] using
    production_small_shift_fixed_budget_holder psi G hchar t.blockCount hk t.which R T
      hmoment hpadding

/-! ## Scalar aggregation and the exact remaining numerical adapter -/

/-- Scalar coefficient left after dividing each `k`-factor Holder inequality by its canonical
padding power.  The grouped masses of this function are exactly `coefficientMass 2,...,13`. -/
noncomputable def canonicalScalarEnvelope (R : NNReal) : NNReal :=
  (repeatedTerms.map fun t =>
    (t.coeff.natAbs : NNReal) / R ^ (14 - t.blockCount)).sum

/-- The scalar envelope grouped by block count, with the exact certified masses. -/
noncomputable def groupedScalarEnvelope (R : NNReal) : NNReal :=
  518400 / R ^ 12 + 2540160 / R ^ 11 + 5450256 / R ^ 10 +
    6787872 / R ^ 9 + 5482456 / R ^ 8 + 3034920 / R ^ 7 +
    1184153 / R ^ 6 + 328986 / R ^ 5 + 64743 / R ^ 4 +
    8820 / R ^ 3 + 791 / R ^ 2 + 42 / R

/-- The 88-term scalar is exactly its twelve-fibre grouped form. -/
theorem canonicalScalarEnvelope_eq_grouped (R : NNReal) :
    canonicalScalarEnvelope R = groupedScalarEnvelope R := by
  simp only [canonicalScalarEnvelope, groupedScalarEnvelope, repeatedTerms, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, blockCount_mkTerm]
  norm_num [mkTerm]
  ring

/-- Aggregate the 88 termwise Holder inequalities.  This is the promised norm-level consumer;
only the one-variable scalar `canonicalScalarEnvelope R` remains. -/
theorem repeatedEtaEnvelope_le_scalar_mul_moment
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F)
    (hR : canonicalPaddingScale psi G ≠ 0) :
    repeatedEtaEnvelope psi G hchar ≤
      canonicalScalarEnvelope (canonicalPaddingScale psi G) *
        nonzeroFourteenthMoment psi G := by
  let R := canonicalPaddingScale psi G
  let M := nonzeroFourteenthMoment psi G
  unfold repeatedEtaEnvelope canonicalScalarEnvelope
  calc
    (repeatedTerms.map fun t =>
        (t.coeff.natAbs : NNReal) * etaTermSum psi G hchar t).sum ≤
      (repeatedTerms.map fun t =>
        (t.coeff.natAbs : NNReal) * (M / R ^ (14 - t.blockCount))).sum := by
        apply List.sum_le_sum
        intro t ht
        apply mul_le_mul_right
        apply (le_div_iff₀ (pow_pos (pos_iff_ne_zero.mpr hR) _)).2
        simpa [mul_comm] using etaTermSum_canonical_holder psi G hchar t ht
    _ = (repeatedTerms.map fun t =>
          (t.coeff.natAbs : NNReal) / R ^ (14 - t.blockCount)).sum * M := by
      simp only [div_eq_mul_inv]
      rw [← list_sum_mul]
      simp only [List.map_map, Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      ac_rfl

/-- Aggregate all 88 fixed-budget inequalities.  This is the exact `F(T)` evaluator used by the
sublinear bootstrap. -/
theorem repeatedEtaEnvelope_le_fixed_scalar_mul_budget
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F) (R T : NNReal)
    (hR : R ≠ 0) (hmoment : nonzeroFourteenthMoment psi G ≤ T)
    (hpadding : (Fintype.card Fˣ : NNReal) * R ^ 14 ≤ T) :
    repeatedEtaEnvelope psi G hchar ≤ canonicalScalarEnvelope R * T := by
  unfold repeatedEtaEnvelope canonicalScalarEnvelope
  calc
    (repeatedTerms.map fun t =>
        (t.coeff.natAbs : NNReal) * etaTermSum psi G hchar t).sum ≤
      (repeatedTerms.map fun t =>
        (t.coeff.natAbs : NNReal) * (T / R ^ (14 - t.blockCount))).sum := by
        apply List.sum_le_sum
        intro t ht
        apply mul_le_mul_right
        apply (le_div_iff₀ (pow_pos (pos_iff_ne_zero.mpr hR) _)).2
        simpa [mul_comm] using
          etaTermSum_fixed_budget_holder psi G hchar t ht R T hmoment hpadding
    _ = (repeatedTerms.map fun t =>
          (t.coeff.natAbs : NNReal) / R ^ (14 - t.blockCount)).sum * T := by
      simp only [div_eq_mul_inv]
      rw [← list_sum_mul]
      simp only [List.map_map, Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      ac_rfl

/-! ## Production fixed target: an entirely rational `<138` closure -/

/-- Fixed integer padding just below the exact target fourteenth root (`≈ 79889.28`).  Choosing
an integer keeps both the padding and coefficient certificates in exact rational arithmetic. -/
def productionFixedPaddingScale : NNReal := 79880

/-- Per-frequency production target without the field-size factor:
`2^18 * (2^30)^7`. -/
def productionMomentBase : NNReal := (2 ^ 18) * (2 ^ 30) ^ 7

/-- The fixed integer padding fits under the production target root. -/
theorem productionFixedPaddingScale_pow_fourteen_le :
    productionFixedPaddingScale ^ 14 ≤ productionMomentBase := by
  norm_num [productionFixedPaddingScale, productionMomentBase]

/-- Field-size-scaled production moment target. -/
def productionMomentTarget (F : Type*) [Fintype F] : NNReal :=
  (Fintype.card F : NNReal) * productionMomentBase

/-- Natural scale `q*n^7` used by the public repeated allowance. -/
def productionRepeatedScale (F : Type*) [Fintype F] : NNReal :=
  (Fintype.card F : NNReal) * (2 ^ 30) ^ 7

/-- The nonzero-frequency padding budget is valid over every finite field. -/
theorem production_fixed_padding_budget
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    (Fintype.card Fˣ : NNReal) * productionFixedPaddingScale ^ 14 ≤
      productionMomentTarget F := by
  have hcard : Fintype.card Fˣ ≤ Fintype.card F := by
    rw [Fintype.card_units]
    omega
  calc
    (Fintype.card Fˣ : NNReal) * productionFixedPaddingScale ^ 14 ≤
        (Fintype.card F : NNReal) * productionMomentBase := by
      apply mul_le_mul
      · exact_mod_cast hcard
      · exact productionFixedPaddingScale_pow_fourteen_le
      · exact zero_le _
      · exact zero_le _
    _ = productionMomentTarget F := rfl

/-- **Exact rational replacement for the irrational production coefficient audit.**  Grouping the
88 terms by the certified masses and padding at `79880` still gives a normalized coefficient
strictly below `138`. -/
theorem production_fixed_scalar_lt_138 :
    canonicalScalarEnvelope productionFixedPaddingScale * (2 ^ 18 : NNReal) < 138 := by
  rw [canonicalScalarEnvelope_eq_grouped]
  norm_num [groupedScalarEnvelope, productionFixedPaddingScale]

/-- **Production `<138` fixed-target closure.**  Under the target moment budget—the input used
when evaluating `F(T)` in the noncircular barrier—the entire 88-term repeated Newton sector fits
inside `138*q*n^7`.  There is no remaining eta, dilation, enumeration, or irrational-root seam. -/
theorem production_repeatedEtaEnvelope_lt_138
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F)
    (hmoment : nonzeroFourteenthMoment psi G ≤ productionMomentTarget F) :
    repeatedEtaEnvelope psi G hchar ≤ 138 * productionRepeatedScale F := by
  have hR : productionFixedPaddingScale ≠ 0 := by
    norm_num [productionFixedPaddingScale]
  have henv := repeatedEtaEnvelope_le_fixed_scalar_mul_budget psi G hchar
    productionFixedPaddingScale (productionMomentTarget F) hR hmoment
    (production_fixed_padding_budget F)
  have hscalar :
      canonicalScalarEnvelope productionFixedPaddingScale * (2 ^ 18 : NNReal) ≤ 138 :=
    production_fixed_scalar_lt_138.le
  calc
    repeatedEtaEnvelope psi G hchar ≤
        canonicalScalarEnvelope productionFixedPaddingScale * productionMomentTarget F := henv
    _ = (canonicalScalarEnvelope productionFixedPaddingScale * (2 ^ 18 : NNReal)) *
          productionRepeatedScale F := by
      unfold productionMomentTarget productionMomentBase productionRepeatedScale
      ring
    _ ≤ 138 * productionRepeatedScale F := mul_le_mul_left hscalar _

/-- The same production closure stated directly for the signed repeated Newton transform before
the positive envelope is introduced. -/
theorem production_sum_repeatedSevenTransform_nnnorm_le_138
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F)
    (hmoment : nonzeroFourteenthMoment psi G ≤ productionMomentTarget F) :
    (∑ b : Fˣ,
        ‖repeatedSevenTransform
          (eta psi G (((smallCoefficientUnit hchar 0) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 1) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 2) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 3) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 4) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 5) * b : Fˣ) : F))
          (eta psi G (((smallCoefficientUnit hchar 6) * b : Fˣ) : F))‖₊) ≤
      138 * productionRepeatedScale F := by
  exact (sum_repeatedSevenTransform_nnnorm_le_etaEnvelope psi G hchar).trans
    (production_repeatedEtaEnvelope_lt_138 psi G hchar hmoment)

/-- General canonical-root interface to the public repeated allowance.  The production-specialized
fixed-padding theorem above discharges its scalar arithmetic without an extra hypothesis. -/
theorem repeatedEtaEnvelope_le_138_mul_scale
    (psi : AddChar F ℂ) (G : Finset F) (hchar : 7 < ringChar F) (scale : NNReal)
    (hR : canonicalPaddingScale psi G ≠ 0)
    (hmoment : nonzeroFourteenthMoment psi G ≤ (2 ^ 18 : NNReal) * scale)
    (hscalar : canonicalScalarEnvelope (canonicalPaddingScale psi G) * (2 ^ 18 : NNReal) ≤ 138) :
    repeatedEtaEnvelope psi G hchar ≤ 138 * scale := by
  calc
    repeatedEtaEnvelope psi G hchar ≤
        canonicalScalarEnvelope (canonicalPaddingScale psi G) *
          nonzeroFourteenthMoment psi G :=
      repeatedEtaEnvelope_le_scalar_mul_moment psi G hchar hR
    _ ≤ canonicalScalarEnvelope (canonicalPaddingScale psi G) *
          ((2 ^ 18 : NNReal) * scale) := mul_le_mul_right hmoment _
    _ = (canonicalScalarEnvelope (canonicalPaddingScale psi G) * (2 ^ 18 : NNReal)) *
          scale := by ac_rfl
    _ ≤ 138 * scale := mul_le_mul_left hscalar _

#print axioms repeatedTerms_eval
#print axioms coefficientMass_table
#print axioms coefficientMass_total
#print axioms repeatedSevenTransform_nnnorm_le_envelope
#print axioms sum_repeatedSevenTransform_nnnorm_le_etaEnvelope
#print axioms etaTermSum_canonical_holder
#print axioms production_small_shift_fixed_budget_holder
#print axioms etaTermSum_fixed_budget_holder
#print axioms repeatedEtaEnvelope_le_scalar_mul_moment
#print axioms repeatedEtaEnvelope_le_fixed_scalar_mul_budget
#print axioms canonicalScalarEnvelope_eq_grouped
#print axioms production_fixed_scalar_lt_138
#print axioms production_repeatedEtaEnvelope_lt_138
#print axioms production_sum_repeatedSevenTransform_nnnorm_le_138
#print axioms repeatedEtaEnvelope_le_138_mul_scale

end ArkLib.ProximityGap.Frontier.BGKRepeatedNewtonFullEnumeration
