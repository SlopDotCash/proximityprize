/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.ToyProblem.Metrics
import ArkLib.ToMathlib.KoalaBearCode

/-!
# Koala IRS lower-bound accounting: the coding-theory distance conjunct (issue #107)

The leaderboard's 64-bit Koala anchor `arklib_lowerBound_irs_t128` is conditional on
`arklib_lowerBound_irs_t128_residual`, a conjunction of three obligations:

1. `winningSetSoundness_le_toySoundnessError_mcaSafe_residual` — the ABF26 Lemma 6.10
   `ε_mca` step (DISPROVEN up-to-capacity / NEEDS_CLASSICAL Johnson-radius; **not** touched here);
2. `koalaIRS.δ < minRelHammingDistCode koalaIRS.C` — the **proximity-below-min-distance**
   condition; and
3. `koalaIRS.toySoundnessError ≤ 2^(-64)` — the §6.3 numeric cap.

This file discharges conjunct **(2)** unconditionally and disproof-independently. The genuine
rate-`1/2` KoalaBear-sextic Reed–Solomon code `KoalaBear.rsCodeSet` evaluates affine polynomials
`m₀ + m₁·X` (degree `< 2`) at the four distinct points `0, 1, 2, 3 ∈ F_{p^6}`. Two distinct
codewords are evaluations of two distinct affine polynomials; their difference is a nonzero
polynomial of degree `≤ 1`, hence has at most one root, so the two codewords agree on at most one
of the four positions and therefore differ in at least three. The minimum relative Hamming
distance of the code is thus `≥ 3/4`, comfortably above the prize radius `δ = 3/10`.

## Main results

* `KoalaBear.rsPoint_injective` — the four evaluation points are pairwise distinct.
* `KoalaBear.rsEncoder_injective` — the rate-`1/2` RS encoder is injective.
* `KoalaBear.hammingDist_rsEncoder_ge_three` — distinct codewords differ in `≥ 3` of `4` positions.
* `KoalaBear.le_minRelHammingDistCode_rsCodeSet` — `3/4 ≤ δ_min(rsCodeSet)`.
* `ToyProblem.koalaIRS_delta_lt_minRelHammingDist` — `koalaIRS.δ < δ_min(koalaIRS.C)`, the second
  conjunct of `arklib_lowerBound_irs_t128_residual`.

## References

* Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated Agreement*
  (eprint 2026/680), §6.3 (Tables 2–5).
-/

set_option maxHeartbeats 1600000

open scoped NNReal

namespace KoalaBear

open Code

/-- The KoalaBear-sextic field has characteristic the KoalaBear prime `fieldSize`
(`= 2^31 - 2^24 + 1`). Inherited from `GaloisField`'s derived `CharP _ p` instance. -/
instance : CharP Sextic fieldSize := by
  unfold Sextic
  infer_instance

/-- `4 < fieldSize`: the KoalaBear prime exceeds the number of evaluation points, so the casts of
`0, 1, 2, 3` into the field are distinct. -/
theorem four_lt_fieldSize : 4 < fieldSize := by
  rw [fieldSize_eq]; norm_num

/-- The four evaluation points `rsPoint j = (j.val : Sextic)` are pairwise distinct: each `j.val`
is `< 4 < fieldSize = ringChar`, so `CharP.natCast_injOn_Iio` applies. -/
theorem rsPoint_injective : Function.Injective rsPoint := by
  intro i j hij
  unfold rsPoint at hij
  have hi : (i.val) ∈ Set.Iio fieldSize := by
    simp only [Set.mem_Iio]; exact lt_trans i.isLt four_lt_fieldSize
  have hj : (j.val) ∈ Set.Iio fieldSize := by
    simp only [Set.mem_Iio]; exact lt_trans j.isLt four_lt_fieldSize
  have := CharP.natCast_injOn_Iio Sextic fieldSize hi hj hij
  exact Fin.ext this

/-- Evaluating the RS encoder at point `j`. -/
@[simp] theorem rsEncoder_apply (m : Fin 2 → Sextic) (j : Fin 4) :
    rsEncoder m j = m 0 + m 1 * rsPoint j := rfl

/-- **Two distinct messages agree on at most one of the four evaluation points.** If the two
affine polynomials `m₀ + m₁·X` and `m₀' + m₁'·X` (the messages `m`, `m'`) agree at two distinct
points `i ≠ j`, then they agree everywhere (same coefficients): subtracting the two evaluation
equations and using `rsPoint i ≠ rsPoint j` forces `m 1 = m' 1`, then `m 0 = m' 0`. -/
theorem rsEncoder_agree_two_points_imp_eq {m m' : Fin 2 → Sextic} {i j : Fin 4}
    (hij : i ≠ j)
    (hi : rsEncoder m i = rsEncoder m' i)
    (hj : rsEncoder m j = rsEncoder m' j) :
    m 0 = m' 0 ∧ m 1 = m' 1 := by
  simp only [rsEncoder_apply] at hi hj
  -- Subtracting: (m 1 - m' 1) * rsPoint i = (m 1 - m' 1) * rsPoint j.
  have hsub : (m 1 - m' 1) * rsPoint i = (m 1 - m' 1) * rsPoint j := by
    have e1 : m 0 - m' 0 = -(m 1 - m' 1) * rsPoint i := by ring_nf; linear_combination hi
    have e2 : m 0 - m' 0 = -(m 1 - m' 1) * rsPoint j := by ring_nf; linear_combination hj
    have hneg := e1.symm.trans e2
    calc
      (m 1 - m' 1) * rsPoint i = - (-(m 1 - m' 1) * rsPoint i) := by ring
      _ = - (-(m 1 - m' 1) * rsPoint j) := by rw [hneg]
      _ = (m 1 - m' 1) * rsPoint j := by ring
  -- `rsPoint i ≠ rsPoint j` since the points are distinct.
  have hpt : rsPoint i ≠ rsPoint j := fun h => hij (rsPoint_injective h)
  -- Hence `m 1 = m' 1`.
  have h1 : m 1 = m' 1 := by
    by_contra hne
    have hdiff : m 1 - m' 1 ≠ 0 := sub_ne_zero.mpr hne
    have := mul_left_cancel₀ hdiff hsub
    exact hpt this
  -- Then `m 0 = m' 0` from `hi`.
  refine ⟨?_, h1⟩
  rw [h1] at hi
  have : m 0 = m' 0 := by linear_combination hi
  exact this

/-- **Distinct codewords differ in at least three of the four positions.** Contrapositive of
`rsEncoder_agree_two_points_imp_eq`: if `rsEncoder m ≠ rsEncoder m'`, the agreement set has at most
one element, so the disagreement (Hamming) distance is at least `4 - 1 = 3`. -/
theorem hammingDist_rsEncoder_ge_three {m m' : Fin 2 → Sextic}
    (hne : rsEncoder m ≠ rsEncoder m') :
    3 ≤ hammingDist (rsEncoder m) (rsEncoder m') := by
  classical
  -- Agreement set `A = {j | rsEncoder m j = rsEncoder m' j}`.
  set A : Finset (Fin 4) := Finset.univ.filter (fun j => rsEncoder m j = rsEncoder m' j) with hA
  -- `A` has at most one element: any two distinct agreeing points force `m = m'`, contradiction.
  have hAle : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    have hi' : rsEncoder m i = rsEncoder m' i := by
      simpa [hA] using hi
    have hj' : rsEncoder m j = rsEncoder m' j := by
      simpa [hA] using hj
    obtain ⟨h0, h1⟩ := rsEncoder_agree_two_points_imp_eq hij hi' hj'
    apply hne
    funext k
    simp only [rsEncoder_apply, h0, h1]
  -- The disagreement set is the complement of `A`.
  have hcompl : (Finset.univ.filter (fun j => rsEncoder m j ≠ rsEncoder m' j)) = Aᶜ := by
    ext j; simp [hA]
  -- `hammingDist = |disagreement set| = |Aᶜ| = 4 - |A| ≥ 3`.
  have hcard : hammingDist (rsEncoder m) (rsEncoder m') = Aᶜ.card := by
    unfold hammingDist
    rw [← hcompl]
  rw [hcard, Finset.card_compl, Fintype.card_fin]
  omega

/-- The RS encoder is injective (distinct messages ⇒ distinct codewords). Immediate from
`hammingDist_rsEncoder_ge_three`, or directly: agreement at all four points forces equal
coefficients. -/
theorem rsEncoder_injective : Function.Injective rsEncoder := by
  intro m m' h
  have h0 : rsEncoder m 0 = rsEncoder m' 0 := by rw [h]
  have h1 : rsEncoder m 1 = rsEncoder m' 1 := by rw [h]
  obtain ⟨e0, e1⟩ := rsEncoder_agree_two_points_imp_eq (by decide : (0 : Fin 4) ≠ 1) h0 h1
  funext k; fin_cases k <;> assumption

theorem le_minRelHammingDistCode_rsCodeSet : (3/4 : ℚ≥0) ≤ minRelHammingDistCode rsCodeSet := by
  have hmin : 3 ≤ Code.minDist rsCodeSet := by
    unfold Code.minDist
    refine le_csInf ?_ ?_
    · let m0 : Fin 2 → Sextic := 0
      let m1 : Fin 2 → Sextic := fun _ => 1
      refine ⟨hammingDist (rsEncoder m0) (rsEncoder m1), ?_⟩
      refine ⟨rsEncoder m0, Set.mem_range_self m0, rsEncoder m1, Set.mem_range_self m1, ?_, rfl⟩
      intro h
      have hm := rsEncoder_injective h
      have h01 := congrFun hm 0
      exact zero_ne_one h01
    · rintro d ⟨u, hu, v, hv, huv, rfl⟩
      rcases hu with ⟨m, rfl⟩
      rcases hv with ⟨m', rfl⟩
      exact hammingDist_rsEncoder_ge_three huv
  rw [← NNRat.coe_le_coe]
  rw [← minDist_div_card_eq_minRelHammingDistCode (C := rsCodeSet)]
  have hq : (3 : ℚ) ≤ (Code.minDist rsCodeSet : ℚ) := by
    exact_mod_cast hmin
  norm_num [Fintype.card_fin]
  linarith

end KoalaBear

namespace ToyProblem

open Code

/-- **The proximity-below-min-distance conjunct of `arklib_lowerBound_irs_t128_residual`.**
At the genuine KoalaBear-sextic anchor `koalaIRS`, the prize radius `δ = 3/10` lies strictly below
the code's minimum relative Hamming distance (`≥ 3/4`, via `KoalaBear.le_minRelHammingDistCode_rsCodeSet`).
This is the second of the three conjuncts of `arklib_lowerBound_irs_t128_residual`, discharged
unconditionally and independently of the DISPROVEN/NEEDS_CLASSICAL `ε_mca` conjunct. -/
theorem koalaIRS_delta_lt_minRelHammingDist :
    koalaIRS.δ < (minRelHammingDistCode koalaIRS.C : ℝ≥0) := by
  -- `koalaIRS.δ = 3/10`, `koalaIRS.C = rsCodeSet` definitionally.
  show (3 / 10 : ℝ≥0) < (minRelHammingDistCode KoalaBear.rsCodeSet : ℝ≥0)
  have h_le_R : (3 / 4 : ℝ≥0) ≤ (minRelHammingDistCode KoalaBear.rsCodeSet : ℝ≥0) := by
    have h_le_q := KoalaBear.le_minRelHammingDistCode_rsCodeSet
    have h_le_real :
        ((3 / 4 : ℚ≥0) : ℝ) ≤
          ((minRelHammingDistCode KoalaBear.rsCodeSet : ℚ≥0) : ℝ) := by
      exact_mod_cast h_le_q
    exact NNReal.coe_le_coe.mp (by simpa using h_le_real)
  have h_lt : (3 / 10 : ℝ≥0) < (3 / 4 : ℝ≥0) := by norm_num
  exact lt_of_lt_of_le h_lt h_le_R

end ToyProblem

-- Focused axiom checks for issue #107: the discharged distance conjunct must be
-- axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
#print axioms KoalaBear.rsPoint_injective
#print axioms KoalaBear.rsEncoder_injective
#print axioms KoalaBear.hammingDist_rsEncoder_ge_three
#print axioms KoalaBear.le_minRelHammingDistCode_rsCodeSet
#print axioms ToyProblem.koalaIRS_delta_lt_minRelHammingDist
