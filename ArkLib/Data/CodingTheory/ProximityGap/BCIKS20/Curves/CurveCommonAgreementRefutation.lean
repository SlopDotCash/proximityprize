/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionResidual
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Counterexample to the geometric strict-Johnson coefficient-polynomial residual

`CurveCommonAgreementResidual` is the geometric half of the BCIKS20 §5/§6 strict Johnson
extraction: at every good curve parameter, the decoded family `P` must share a `≥ deg`-size
agreement set with `k + 1` sampled decodings of the curve. It is used to derive the algebraic
strict coefficient-polynomial residual by Lagrange interpolation. This file shows that the
geometric statement is false as stated, at a finite parameter set in the strict Johnson
interior.

## Witness

* `F = GaloisField 2 64`, `ι = Fin 7`, `deg = 2`, `k = 1`, `δ = 3/7`;
* `domain7` is the first seven elements of an enumeration of `F`;
* `linPoly = X - C (domain7 0)` and `wLin = linPoly.eval ∘ domain7`;
* `eWord` keeps `wLin` on the coordinates `{1, 2, 3}` and is zero elsewhere, so it is at
  relative distance exactly `3/7` from both `0` and `wLin`;
* `curveStack = ![eWord, 0]`, so every curve word is `eWord` and the good-coefficient set is all
  of `F`;
* the adversarial decoder is `blockFamily 0`: `linPoly` at the single parameter `0`, and the zero
  polynomial at every other parameter. Every member is decoded on all of `F`.

The probability hypothesis is `1 > k · errorBound`, which holds because the error bound is
strictly below one for `ρ = 2/7` and `|F| = 2^64`.

## Why the residual fails

The conclusion demands two distinct sample parameters `s 0, s 1 ∈ F` and, at the good parameter
`z = 0`, an agreement set `S` with `deg ≤ |S| = 2`. At `z = 0` the first agreement clause forces
`linPoly` to agree with `eWord` on `S`. At most one of `s 0` and `s 1` can equal `0`; for the
other sample `s i ≠ 0` the decoder is the zero polynomial, so the second clause forces `eWord` to
vanish on `S`. Together, `linPoly` vanishes on `S`, and `linPoly` has the single root
`domain7 0`, hence `S ⊆ {0}` has cardinality at most one. This contradicts `2 ≤ S.card`.

## Scope

This refutes the geometric residual statement, and therefore any unconditional derivation of the
strict coefficient-polynomial residual from it. It does not refute the BCIKS20 list-decoding
theorem, the existence half of the extraction, the production parameters, or the `δ*`
conjecture. The counterexample uses an adversarial decoder, exactly as the residual's universal
quantifier over `P` permits: a repaired geometric statement must fix the decoder canonically or
restrict to a regime where decoding is unique. Axiom-clean:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace ProximityGap

noncomputable section

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

namespace CurveCommonAgreementRefutation

/-- The concrete field `GF(2⁶⁴)`, with `2⁶⁴` elements. -/
abbrev GF64 : Type := GaloisField 2 64

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fintype GF64 := Fintype.ofFinite _
local instance : DecidableEq GF64 := fun a b => Classical.propDecidable (a = b)

theorem card_GF64 : Fintype.card GF64 = 2 ^ 64 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card (p := 2) (n := 64) (by norm_num)]

/-- A seven-point evaluation domain: the first seven elements of an enumeration of `GF(2⁶⁴)`. -/
def domain7 : Fin 7 ↪ GF64 :=
  ⟨fun i => (Fintype.equivFin GF64).symm ⟨(i : ℕ), by
      rw [card_GF64]; exact lt_trans i.isLt (by norm_num)⟩,
   fun i j h => Fin.ext (by
      simpa using congrArg Fin.val ((Fintype.equivFin GF64).symm.injective h))⟩

/-- A monic linear polynomial vanishing at the first domain point. -/
def linPoly : GF64[X] := (Polynomial.X : GF64[X]) - Polynomial.C (domain7 0)

lemma linPoly_natDegree : linPoly.natDegree = 1 := by
  rw [linPoly, natDegree_X_sub_C]

/-- The evaluation word of `linPoly`: a codeword that is zero at exactly one coordinate. -/
def wLin : Fin 7 → GF64 := fun i => linPoly.eval (domain7 i)

lemma wLin_mem : wLin ∈ ReedSolomon.code domain7 2 := by
  refine ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval linPoly ?_ ?_
  · rw [linPoly_natDegree]; norm_num
  · intro i; rfl

lemma wLin_eq_zero_iff (i : Fin 7) : wLin i = 0 ↔ i = 0 := by
  rw [wLin, linPoly, eval_sub, eval_X, eval_C, sub_eq_zero]
  exact domain7.injective.eq_iff

lemma zero_eq_wLin_iff (i : Fin 7) : (0 : GF64) = wLin i ↔ i = 0 :=
  (eq_comm (a := (0 : GF64)) (b := wLin i)).trans (wLin_eq_zero_iff i)

/-- The test word: three of the six nonzero coordinates of `wLin`, zero on the rest. -/
def eWord : Fin 7 → GF64 := fun i => if i = 1 ∨ i = 2 ∨ i = 3 then wLin i else 0

lemma disagreement_e_zero :
    disagreementCols eWord (0 : Fin 7 → GF64) = ({1, 2, 3} : Finset (Fin 7)) := by
  ext i
  simp only [mem_disagreementCols, Pi.zero_apply, eWord]
  fin_cases i <;> simp [wLin_eq_zero_iff]

lemma disagreement_e_wLin :
    disagreementCols eWord wLin = ({4, 5, 6} : Finset (Fin 7)) := by
  ext i
  simp only [mem_disagreementCols, eWord]
  fin_cases i <;> simp [zero_eq_wLin_iff]

lemma hamming_e_zero : hammingDist eWord (0 : Fin 7 → GF64) = 3 := by
  rw [hammingDist_eq_disagreementCols_card, disagreement_e_zero]
  decide

lemma hamming_e_wLin : hammingDist eWord wLin = 3 := by
  rw [hammingDist_eq_disagreementCols_card, disagreement_e_wLin]
  decide

lemma relDist_e_zero : δᵣ(eWord, (0 : Fin 7 → GF64)) = (3 / 7 : ℚ≥0) := by
  rw [relHammingDist, hamming_e_zero, Fintype.card_fin]
  norm_num

lemma relDist_e_wLin : δᵣ(eWord, wLin) = (3 / 7 : ℚ≥0) := by
  rw [relHammingDist, hamming_e_wLin, Fintype.card_fin]
  norm_num

/-- The rational `3/7` has the same value under the two nonnegative coercions in play. -/
lemma coe_three_sevenths_nn : ((3 / 7 : ℚ≥0) : ℝ≥0) = (3 / 7 : ℝ≥0) := by
  apply NNReal.coe_injective
  push_cast
  norm_num

lemma coe_three_sevenths_ennreal :
    ((3 / 7 : ℚ≥0) : ENNReal) = ((3 / 7 : ℝ≥0) : ENNReal) := by
  rw [ENNReal.coe_NNRat_coe_NNReal, coe_three_sevenths_nn]

lemma relDistFromCode_e :
    δᵣ(eWord, ReedSolomon.code domain7 2) ≤ ((3 / 7 : ℝ≥0) : ENNReal) := by
  calc δᵣ(eWord, ReedSolomon.code domain7 2) ≤ δᵣ(eWord, wLin) :=
        relDistFromCode_le_relDist_to_mem eWord wLin wLin_mem
    _ = ((3 / 7 : ℚ≥0) : ENNReal) := by rw [relDist_e_wLin]
    _ = ((3 / 7 : ℝ≥0) : ENNReal) := coe_three_sevenths_ennreal

/-- The constant curve through `eWord`. -/
def curveStack : WordStack GF64 (Fin 2) (Fin 7) := fun t => if t = 0 then eWord else 0

lemma line_curveStack (z : GF64) :
    (∑ t : Fin 2, (z ^ (t : ℕ)) • curveStack t) = eWord := by
  simp [curveStack]

/-- Pointwise form of `line_curveStack`, matching the summands in the residual. -/
lemma curveStack_apply (z : GF64) (x : Fin 7) :
    (∑ t : Fin 2, (z ^ (t : ℕ)) * curveStack t x) = eWord x := by
  simpa using congrFun (line_curveStack z) x

lemma mem_goodCoeffsCurve (z : GF64) :
    z ∈ RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain7) curveStack (3 / 7) := by
  simp only [RS_goodCoeffsCurve, mem_filter, mem_univ, true_and]
  change δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • curveStack t, ReedSolomon.code domain7 2) ≤
    (3 / 7 : ℝ≥0)
  rw [line_curveStack]
  exact relDistFromCode_e

lemma goodCoeffsCurve_eq_univ :
    RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain7) curveStack (3 / 7) = univ :=
  eq_univ_of_forall mem_goodCoeffsCurve

/-! ## The error bound is strictly below one -/

theorem rate_eq : (LinearCode.rate (ReedSolomon.code domain7 2) : ℝ≥0) = 2 / 7 := by
  rw [ReedSolomon.rateOfLinearCode_eq_div' (F := GF64) (α := domain7) (n := 2) (by decide)]
  rw [Fintype.card_fin]
  push_cast
  norm_num

theorem sqrt_two_sevenths_ge : (53 / 100 : ℝ) ≤ Real.sqrt (2 / 7) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

theorem sqrt_two_sevenths_le : Real.sqrt (2 / 7) ≤ (54 / 100 : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

theorem sqrt_two_sevenths_le_one : (2 / 7 : ℝ≥0).sqrt ≤ 1 :=
  calc (2 / 7 : ℝ≥0).sqrt ≤ (1 : ℝ≥0).sqrt :=
        (NNReal.sqrt_le_sqrt).2 (by rw [← NNReal.coe_le_coe]; norm_num)
    _ = 1 := NNReal.sqrt_one

theorem sqrtRate_le_one : ReedSolomon.sqrtRate 2 domain7 ≤ 1 := by
  rw [ReedSolomon.sqrtRate, rate_eq]
  exact sqrt_two_sevenths_le_one

theorem johnson_side_lt :
    (1 - (LinearCode.rate (ReedSolomon.code domain7 2) : ℝ≥0)) / 2 < (3 / 7 : ℝ≥0) := by
  have h27 : (2 / 7 : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  rw [rate_eq, ← NNReal.coe_lt_coe]
  simp only [NNReal.coe_div, NNReal.coe_sub h27, NNReal.coe_ofNat]
  norm_num

theorem sqrtRate_lt : (3 / 7 : ℝ≥0) < 1 - ReedSolomon.sqrtRate 2 domain7 := by
  rw [ReedSolomon.sqrtRate, rate_eq, ← NNReal.coe_lt_coe]
  rw [NNReal.coe_sub sqrt_two_sevenths_le_one]
  simp only [Real.coe_sqrt, NNReal.coe_one, NNReal.coe_div, NNReal.coe_ofNat]
  linarith [sqrt_two_sevenths_le]

/-- In the strict Johnson interior the BCIKS20 error bound is strictly smaller than one, so the
probability hypothesis `Pr > k · errorBound` is satisfiable with `Pr = 1`. -/
theorem errorBound_lt_one : errorBound (3 / 7 : ℝ≥0) 2 domain7 < 1 := by
  classical
  set r : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain7 2) : ℝ≥0) with hr
  have hUD : ¬ (3 / 7 : ℝ≥0) ≤ (1 - r) / 2 := by
    rw [hr]
    exact not_le.mpr johnson_side_lt
  have hδ' : (3 / 7 : ℝ≥0) < 1 - r.sqrt := by
    rw [hr]
    exact sqrtRate_lt
  have hmem2 : (1 - r) / 2 < (3 / 7 : ℝ≥0) ∧ (3 / 7 : ℝ≥0) < 1 - r.sqrt :=
    ⟨lt_of_not_ge hUD, hδ'⟩
  simp only [errorBound, ← hr, Set.mem_Icc, zero_le, hUD, and_false,
    ↓reduceIte, Set.mem_Ioo, hmem2, and_self, coe_pow, NNReal.coe_natCast,
    coe_min, NNReal.coe_div, Real.coe_sqrt, NNReal.coe_ofNat]
  change (↑2 ^ 2 : ℝ) /
      ((2 * min (↑(1 - r.sqrt - (3 / 7 : ℝ≥0)) : ℝ) (Real.sqrt (r : ℝ) / 20)) ^ 7 *
        (Fintype.card GF64 : ℝ)) < 1
  set m : ℝ := min (↑(1 - r.sqrt - (3 / 7 : ℝ≥0)) : ℝ) (Real.sqrt (r : ℝ) / 20) with hm
  have hcoer : ((1 - r.sqrt - (3 / 7 : ℝ≥0) : ℝ≥0) : ℝ) = 1 - Real.sqrt (r : ℝ) - 3 / 7 := by
    have hsr : r.sqrt ≤ 1 := by
      rw [hr]; exact sqrtRate_le_one
    have hd : (3 / 7 : ℝ≥0) ≤ 1 - r.sqrt := by
      rw [le_tsub_iff_right hsr, ← NNReal.coe_le_coe]
      push_cast
      have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
        rw [hr, rate_eq]
        push_cast
        norm_num
      rw [h27]
      linarith [sqrt_two_sevenths_le]
    rw [NNReal.coe_sub hd, NNReal.coe_sub hsr, Real.coe_sqrt]
    have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
      rw [hr, rate_eq]
      push_cast
      norm_num
    rw [h27]
    norm_num
  have hs_le : Real.sqrt (r : ℝ) ≤ (54 / 100 : ℝ) := by
    have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
      rw [hr, rate_eq]
      push_cast
      norm_num
    rw [h27]
    exact sqrt_two_sevenths_le
  have hs_ge : (53 / 100 : ℝ) ≤ Real.sqrt (r : ℝ) := by
    have h27 : ((r : ℝ≥0) : ℝ) = 2 / 7 := by
      rw [hr, rate_eq]
      push_cast
      norm_num
    rw [h27]
    exact sqrt_two_sevenths_ge
  have harg1 : (53 / 2000 : ℝ) ≤ (↑(1 - r.sqrt - (3 / 7 : ℝ≥0)) : ℝ) := by
    rw [hcoer]
    linarith
  have harg2 : (53 / 2000 : ℝ) ≤ Real.sqrt (r : ℝ) / 20 := by linarith
  have hm_ge : (53 / 2000 : ℝ) ≤ m := by
    rw [hm]
    exact le_min harg1 harg2
  have h2m_ge : (53 / 1000 : ℝ) ≤ 2 * m := by linarith
  have hpow_ge : (53 / 1000 : ℝ) ^ 7 ≤ (2 * m) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) h2m_ge 7
  have hq : (Fintype.card GF64 : ℝ) = 2 ^ 64 := by
    rw [card_GF64]
    norm_num
  have hden_ge : (53 / 1000 : ℝ) ^ 7 * 2 ^ 64 ≤ (2 * m) ^ 7 * (Fintype.card GF64 : ℝ) := by
    rw [hq]
    exact mul_le_mul hpow_ge le_rfl (by positivity) (by positivity)
  have hden_pos : 0 < (2 * m) ^ 7 * (Fintype.card GF64 : ℝ) :=
    lt_of_lt_of_le (by norm_num) hden_ge
  rw [div_lt_one hden_pos]
  have h4 : (4 : ℝ) < (53 / 1000 : ℝ) ^ 7 * 2 ^ 64 := by norm_num
  linarith

/-! ## The probability hypothesis -/

/-- The good-coefficient set is the whole field, so a random line is close to the code with
probability `1`, which dominates `k · errorBound`. -/
theorem prob_gt_k_errorBound :
    Pr_{let z ← $ᵖ GF64}[
      δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
        ReedSolomon.code domain7 2) ≤ (3 / 7 : ℝ≥0)] >
      (((1 : ℕ) : ENNReal) * (errorBound (3 / 7 : ℝ≥0) 2 domain7 : ENNReal)) := by
  rw [prob_close_curve_eq_card_goodCoeffsCurve_div_card (k := 1) (deg := 2)
    (domain := domain7) (δ := (3 / 7 : ℝ≥0)) curveStack]
  rw [goodCoeffsCurve_eq_univ, Finset.card_univ]
  simp only [Nat.cast_one, one_mul]
  rw [ENNReal.div_self (by simp) (by simp), ← ENNReal.coe_one]
  change ((errorBound (3 / 7 : ℝ≥0) 2 domain7 : ℝ≥0) : ENNReal) <
    ((1 : ℝ≥0) : ENNReal)
  rw [ENNReal.coe_lt_coe]
  exact errorBound_lt_one

/-! ## The geometric refutation -/

/-- The adversarial decoder attached to a single parameter `z₀`: `linPoly` at `z₀`, the zero
polynomial elsewhere. Every member is decoded at every parameter. -/
def blockFamily (z₀ : GF64) : GF64 → GF64[X] := fun z => if z = z₀ then linPoly else 0

/-- Every member of the adversarial family is decoded on the good-coefficient set. -/
lemma blockFamily_decoded (z₀ z : GF64) :
    (blockFamily z₀ z).natDegree < 2 ∧
      δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • curveStack t,
        (blockFamily z₀ z).eval ∘ domain7) ≤ (3 / 7 : ℝ≥0) := by
  by_cases hz : z = z₀
  · rw [show blockFamily z₀ z = linPoly from by simp [blockFamily, hz]]
    exact ⟨by rw [linPoly_natDegree]; norm_num, by
      rw [line_curveStack, show (linPoly.eval ∘ domain7) = wLin from rfl, relDist_e_wLin,
        coe_three_sevenths_nn]⟩
  · rw [show blockFamily z₀ z = (0 : GF64[X]) from by simp [blockFamily, hz]]
    constructor
    · rw [natDegree_zero]
      norm_num
    · rw [line_curveStack]
      have hz0 : ((0 : GF64[X]).eval ∘ domain7) = (0 : Fin 7 → GF64) := by
        funext i
        simp
      rw [hz0, relDist_e_zero, coe_three_sevenths_nn]

/-- **The geometric strict-Johnson coefficient-polynomial residual is false as stated.** The
adversarial decoder is decoded everywhere, but at the good parameter `z = 0` any two distinct
sample parameters force the agreement set into the single root of `linPoly`. -/
theorem not_curveCommonAgreementResidual :
    ¬ CurveCommonAgreementResidual (k := 1) (deg := 2) (domain := domain7)
      (δ := (3 / 7 : ℝ≥0)) := by
  classical
  intro h
  obtain ⟨s, hsinj, _hsG, hCommon⟩ :=
    h (by norm_num) curveStack prob_gt_k_errorBound johnson_side_lt sqrtRate_lt
      (blockFamily 0) (fun z _ => blockFamily_decoded 0 z)
  obtain ⟨S, hScard, hPz, hPs⟩ := hCommon 0 (mem_goodCoeffsCurve 0)
  have hex : ∃ i : Fin 2, s i ≠ (0 : GF64) := by
    have hne : s 0 ≠ s 1 := by
      intro hEq
      exact absurd (hsinj hEq) (by decide)
    by_cases h0 : s 0 = 0
    · exact ⟨1, fun h1 => hne (h0.trans h1.symm)⟩
    · exact ⟨0, h0⟩
  obtain ⟨i, hi⟩ := hex
  have hsub : S ⊆ ({0} : Finset (Fin 7)) := by
    intro x hx
    have hPz_x : linPoly.eval (domain7 x) = eWord x := by
      have h' := hPz x hx
      rw [show blockFamily (0 : GF64) 0 = linPoly from by simp [blockFamily]] at h'
      rwa [curveStack_apply] at h'
    have hPs_x : eWord x = 0 := by
      have h' := hPs i x hx
      rw [show blockFamily (0 : GF64) (s i) = (0 : GF64[X]) from by simp [blockFamily, hi],
        Polynomial.eval_zero] at h'
      rw [curveStack_apply] at h'
      exact h'.symm
    have hzero : wLin x = 0 := by
      change linPoly.eval (domain7 x) = 0
      rw [hPz_x, hPs_x]
    have hx0 : x = 0 := (wLin_eq_zero_iff x).mp hzero
    simp [hx0]
  have hcard : S.card ≤ 1 := by
    calc S.card ≤ ({0} : Finset (Fin 7)).card := Finset.card_le_card hsub
      _ = 1 := by simp
  omega

end CurveCommonAgreementRefutation

end

end ProximityGap

/-! ## Axiom audit -/

open ProximityGap.CurveCommonAgreementRefutation

#print axioms not_curveCommonAgreementResidual
#print axioms errorBound_lt_one
