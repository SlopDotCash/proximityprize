/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourSyndromeChordBound
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Rate-quarter `k = 4`: weight-two points on an MDS syndrome pencil

The regular-outsider residual on the eight coordinates outside a size-eight
source core has Hamming weight exactly two after subtracting its cubic
Reed--Solomon codeword.  Its quotient class is therefore a nonzero point on
the chord spanned by the two corresponding quotient coordinate columns.

This file connects that code-level statement to the syndrome-chord graph
bound.  If the quotient row classes are independent, their affine points are
projectively injective.  Hence distinct scalar parameters cannot reuse one
missed edge, and a column-avoiding quotient pencil contains at most one
regular scalar per chord and at most `n` such scalars in total.

On exactly eight coordinates, chord-incidence transitivity rules out equality
in that first handshake bound.  The resulting ceiling is seven, which is the
strict inequality needed by the unique-eight-core residual.

The final theorem proves the needed four-wise independence of the quotient
coordinate frame from the absence of nonzero codewords of weight at most
four.  This applies in particular to an `[8,4]` Reed--Solomon code, whose
minimum distance is five.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Module Submodule
open ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeChordBound

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome

attribute [local instance] Classical.propDecidable

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype I] [DecidableEq I]

/-- The quotient syndrome column of one coordinate. -/
noncomputable def quotientColumn
    (C : Submodule F (I -> F)) (i : I) : (I -> F) ⧸ C :=
  C.mkQ (Pi.single i 1)

/-- Independence of the two received-row classes in the code quotient,
written in the coefficient form used by the projective injection proof. -/
def QuotientRowsIndependent
    (C : Submodule F (I -> F)) (u0 u1 : I -> F) : Prop :=
  ∀ a b : F,
    a • C.mkQ u0 + b • C.mkQ u1 = 0 -> a = 0 ∧ b = 0

/-- The affine quotient point at scalar `gamma`. -/
noncomputable def quotientAffinePoint
    (C : Submodule F (I -> F)) (u0 u1 : I -> F) (gamma : F) :
    (I -> F) ⧸ C :=
  C.mkQ u0 + gamma • C.mkQ u1

theorem quotientAffinePoint_ne_zero
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hrows : QuotientRowsIndependent C u0 u1) (gamma : F) :
    quotientAffinePoint C u0 u1 gamma ≠ 0 := by
  intro hzero
  have hcoeff := hrows 1 gamma (by simpa only [one_smul] using hzero)
  exact one_ne_zero hcoeff.1

/-- Independent quotient rows give a projectively honest affine chart. -/
theorem quotientAffinePoint_projectively_injective
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hrows : QuotientRowsIndependent C u0 u1)
    {gamma beta c : F}
    (hprop : c • quotientAffinePoint C u0 u1 gamma =
      quotientAffinePoint C u0 u1 beta) :
    gamma = beta := by
  have hzero :
      (c - 1) • C.mkQ u0 + (c * gamma - beta) • C.mkQ u1 = 0 := by
    dsimp only [quotientAffinePoint] at hprop
    rw [smul_add, smul_smul] at hprop
    rw [sub_smul, one_smul, sub_smul]
    calc
      (c • C.mkQ u0 - C.mkQ u0) +
          ((c * gamma) • C.mkQ u1 - beta • C.mkQ u1) =
        (c • C.mkQ u0 + (c * gamma) • C.mkQ u1) -
          (C.mkQ u0 + beta • C.mkQ u1) := by abel
      _ = 0 := sub_eq_zero.mpr hprop
  have hcoeff := hrows (c - 1) (c * gamma - beta) hzero
  have hc : c = 1 := by
    exact sub_eq_zero.mp hcoeff.1
  rw [hc] at hcoeff
  simpa only [one_mul, sub_eq_zero] using hcoeff.2

/-- Every affine quotient point belongs to the quotient row plane. -/
theorem quotientAffinePoint_mem_rowPlane
    (C : Submodule F (I -> F)) (u0 u1 : I -> F) (gamma : F) :
    quotientAffinePoint C u0 u1 gamma ∈
      span F ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C)) := by
  exact add_mem
    (subset_span (by simp))
    (smul_mem _ gamma (subset_span (by simp)))

/-- The quotient row plane has dimension at most two. -/
theorem rowPlane_finrank_le_two
    (C : Submodule F (I -> F)) (u0 u1 : I -> F) :
    finrank F (span F
      ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C))) ≤ 2 := by
  classical
  have hspan :
      finrank F (span F
        ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C))) ≤
        ({C.mkQ u0, C.mkQ u1} : Finset ((I -> F) ⧸ C)).card := by
    simpa using finrank_span_finset_le_card (R := F)
      ({C.mkQ u0, C.mkQ u1} : Finset ((I -> F) ⧸ C))
  rcases Finset.card_pair_eq_one_or_two
      (a := C.mkQ u0) (b := C.mkQ u1) with hcard | hcard
  · omega
  · omega

/-- **Weight-two syndrome-pencil bound.**

Each selected scalar is represented by one nonzero two-column syndrome.
Four-wise independence supplies the MDS chord graph, row independence makes
the affine chart projectively injective, and avoidance of coordinate columns
excludes the sparse chord degeneracy. -/
theorem weightTwoSyndromeLine_card_le
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hrows : QuotientRowsIndependent C u0 u1)
    (hMDS4 : IndependentUpTo (F := F) (quotientColumn C) 4)
    (hnoColumn : ∀ i, quotientColumn C i ∉
      span F ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C)))
    (G : Finset F) (left right : F -> I) (a b : F -> F)
    (hendpoints : ∀ gamma ∈ G, left gamma ≠ right gamma)
    (hsyndrome : ∀ gamma ∈ G,
      quotientAffinePoint C u0 u1 gamma =
        a gamma • quotientColumn C (left gamma) +
          b gamma • quotientColumn C (right gamma)) :
    G.card ≤ Fintype.card I := by
  let P : Submodule F ((I -> F) ⧸ C) :=
    span F ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C))
  apply card_le_columns_of_projectively_injective_chord_assignment
    P (quotientColumn C) (rowPlane_finrank_le_two C u0 u1)
      hMDS4 hnoColumn G left right
      (quotientAffinePoint C u0 u1)
  · exact hendpoints
  · intro gamma _hgamma
    exact quotientAffinePoint_ne_zero C u0 u1 hrows gamma
  · intro gamma _hgamma
    exact quotientAffinePoint_mem_rowPlane C u0 u1 gamma
  · intro gamma hgamma
    rw [Submodule.mem_span_pair]
    exact ⟨a gamma, b gamma, (hsyndrome gamma hgamma).symm⟩
  · intro gamma hgamma beta hbeta hprop
    obtain ⟨c, hc⟩ := hprop
    exact quotientAffinePoint_projectively_injective C u0 u1 hrows hc

/-- **Strict eight-coordinate weight-two syndrome-pencil bound.**

For an eight-column MDS quotient frame, the transitive chord graph has at most
seven edges, so a projectively injective affine pencil contains at most seven
selected weight-two syndromes. -/
theorem weightTwoSyndromeLine_card_le_seven
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hI : Fintype.card I = 8)
    (hrows : QuotientRowsIndependent C u0 u1)
    (hMDS4 : IndependentUpTo (F := F) (quotientColumn C) 4)
    (hnoColumn : ∀ i, quotientColumn C i ∉
      span F ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C)))
    (G : Finset F) (left right : F -> I) (a b : F -> F)
    (hendpoints : ∀ gamma ∈ G, left gamma ≠ right gamma)
    (hsyndrome : ∀ gamma ∈ G,
      quotientAffinePoint C u0 u1 gamma =
        a gamma • quotientColumn C (left gamma) +
          b gamma • quotientColumn C (right gamma)) :
    G.card ≤ 7 := by
  let P : Submodule F ((I -> F) ⧸ C) :=
    span F ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C))
  apply card_le_seven_of_projectively_injective_chord_assignment
    P (quotientColumn C) hI (rowPlane_finrank_le_two C u0 u1)
      hMDS4 hnoColumn G left right
      (quotientAffinePoint C u0 u1)
  · exact hendpoints
  · intro gamma _hgamma
    exact quotientAffinePoint_ne_zero C u0 u1 hrows gamma
  · intro gamma _hgamma
    exact quotientAffinePoint_mem_rowPlane C u0 u1 gamma
  · intro gamma hgamma
    rw [Submodule.mem_span_pair]
    exact ⟨a gamma, b gamma, (hsyndrome gamma hgamma).symm⟩
  · intro gamma hgamma beta hbeta hprop
    obtain ⟨c, hc⟩ := hprop
    exact quotientAffinePoint_projectively_injective C u0 u1 hrows hc

/-! ## The quotient coordinate frame of a distance-five code -/

/-- Coordinate combination supported on a selected finite set. -/
noncomputable def coordinateCombination
    (J : Finset I) (g : J -> F) : I -> F :=
  ∑ j : J, g j • Pi.single j.1 1

theorem coordinateCombination_apply
    (J : Finset I) (g : J -> F) (j : J) :
    coordinateCombination J g j.1 = g j := by
  classical
  rw [coordinateCombination]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro x hx
    have hval : x.1 ≠ j.1 := by
      intro hcoe
      exact hx (Subtype.ext hcoe)
    simp [hval]

theorem coordinateCombination_eq_zero_outside
    (J : Finset I) (g : J -> F) {i : I} (hi : i ∉ J) :
    coordinateCombination J g i = 0 := by
  classical
  rw [coordinateCombination]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hval : x.1 ≠ i := by
    intro hcoe
    apply hi
    rw [← hcoe]
    exact x.2
  simp [hval]

theorem coordinateCombination_weight_le_card
    (J : Finset I) (g : J -> F) :
    Code.wt (coordinateCombination J g) ≤ J.card := by
  classical
  unfold Code.wt
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra hiJ
  exact hi (coordinateCombination_eq_zero_outside J g hiJ)

/-- If the code has no nonzero word of weight at most `d`, then every `d`
quotient coordinate columns are independent. -/
theorem quotientColumns_independentUpTo_of_noSparseCodeword
    (C : Submodule F (I -> F)) (d : Nat)
    (hnoSparse : ∀ e ∈ C, Code.wt e ≤ d -> e = 0) :
    IndependentUpTo (F := F) (quotientColumn C) d := by
  classical
  intro J hJcard
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  let e : I -> F := coordinateCombination J g
  have hmk : C.mkQ e = 0 := by
    dsimp only [e, coordinateCombination]
    rw [map_sum]
    simp only [map_smul]
    exact hsum
  have heC : e ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hmk
  have heWeight : Code.wt e ≤ d :=
    (coordinateCombination_weight_le_card J g).trans hJcard
  have heZero : e = 0 := hnoSparse e heC heWeight
  intro j
  have hj := congrFun heZero j.1
  simpa only [e, coordinateCombination_apply, Pi.zero_apply] using hj

/-- An `[8,4]` Reed--Solomon code has no nonzero word of weight at most four. -/
theorem reedSolomon_eight_four_noSparseCodeword
    (dom : I ↪ F) (hI : Fintype.card I = 8)
    (e : I -> F) (he : e ∈ ReedSolomon.code dom 4)
    (heWeight : Code.wt e ≤ 4) : e = 0 := by
  by_contra heNe
  have hmin :
      Code.minDist ((ReedSolomon.code dom 4 : Submodule F (I -> F)) :
        Set (I -> F)) ≤ hammingDist e 0 := by
    unfold Code.minDist
    apply Nat.sInf_le
    exact ⟨e, he, 0, Submodule.zero_mem _, heNe, rfl⟩
  have hdist : hammingDist e 0 = Code.wt e := by
    rfl
  rw [ReedSolomon.minDist_eq' (n := 4) (by omega), hI, hdist] at hmin
  omega

/-- The quotient coordinate columns of an `[8,4]` Reed--Solomon code are
four-wise independent. -/
theorem reedSolomon_eight_four_quotientColumns_independentUpTo_four
    (dom : I ↪ F) (hI : Fintype.card I = 8) :
    IndependentUpTo (F := F)
      (quotientColumn (ReedSolomon.code dom 4)) 4 := by
  apply quotientColumns_independentUpTo_of_noSparseCodeword
  intro e he hweight
  exact reedSolomon_eight_four_noSparseCodeword dom hI e he hweight

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome
#print axioms quotientAffinePoint_projectively_injective
#print axioms weightTwoSyndromeLine_card_le
#print axioms weightTwoSyndromeLine_card_le_seven
#print axioms quotientColumns_independentUpTo_of_noSparseCodeword
#print axioms reedSolomon_eight_four_noSparseCodeword
#print axioms reedSolomon_eight_four_quotientColumns_independentUpTo_four
