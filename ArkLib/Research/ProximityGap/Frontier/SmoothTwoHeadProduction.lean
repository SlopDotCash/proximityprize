/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DoubleQuadraticThreshold
import ArkLib.Research.ProximityGap.Frontier.SmoothQuarterTwoHeadWindow

/-! # Three exact MCA budget regimes over smooth production fields -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.SmoothTwoHeadProduction
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger ProximityPrize
open scoped NNReal ENNReal

abbrev n : ℕ := 1073741824

/-- The first failure in the spike regime, the plateau and the two-head regime. -/
def first (a B : ℕ) : ℕ := min B (max a (B/2))

variable {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I] [Nonempty I]

/-- The field size implied by this budget window forces sufficiently large characteristic
on every smooth production domain. Thus the finite-field two-interpolant estimate applies
also to extension fields, for any even dimension below one third of the length. -/
theorem curve (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    {k a B : ℕ} (hk : 2 ≤ k) (shape : k+2*a = n) (low : n < 3*a)
    (hB : Fintype.card F / 2^128 = B)
    (cap : DoubleQuadraticThreshold.agreements n k ≤ n - B/2 + 1)
    (bound : B/2 < n) (m : ℕ) [NeZero m] :
    let C := ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m))
    let r := ((first a B : ℕ) : ℝ≥0)/n
    mcaDeltaStar (F := F) C (1/(2 : ℝ≥0∞)^128) = r ∧
      ∀ δ, epsMCA (F := F) C δ ≤ 1/(2 : ℝ≥0∞)^128 ↔ δ < r := by
  classical
  dsimp only
  by_cases small : B ≤ 2*a+1
  · have h := ApolarAllFieldPlateau.classification D hk (shape.trans hn.symm) (hn ▸ low)
        (Q := 2^128) (by decide) hB small m
    simpa only [first, max_eq_left (by omega : B/2 ≤ a), hn, Nat.cast_pow, Nat.cast_ofNat] using h
  · have hqBound : Fintype.card F < 2^256 := by
      have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2^128)).mp (hB.trans_lt (Nat.lt_succ_self B))
      dsimp [n] at bound
      omega
    have hp := SmoothCubicCharacteristic.characteristic D hn hqBound
    have tmin : k+2 ≤ DoubleQuadraticThreshold.agreements n k := by
      unfold DoubleQuadraticThreshold.agreements DoubleQuadraticThreshold.margin
      split_ifs <;> dsimp [n] <;> omega
    have fit : k+B/2+1 ≤ n := by omega
    let e := (Fintype.equivFinOfCardEq hn).symm
    let E := e.toEmbedding.trans D
    have h := DoubleQuadraticThreshold.classification (n := n) (k := k) (j := B/2) E
      (Q := 2^128) (by decide) (by rw [hB]) hk (by omega) (by decide)
      (by omega) fit cap (by
        intro i hi hi' hz
        have dv := Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff F (ringChar F) i).mp hz)
        dsimp [n] at *
        omega) m
    dsimp only at h
    rw [mcaDeltaStar_interleaved_eq] at h ⊢
    simp_rw [epsMCA_interleaved_eq] at h ⊢
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq e E D (fun _ => rfl)]
    simp_rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e E D (fun _ => rfl)]
    simpa only [first, max_eq_right (by omega : a ≤ B/2), min_eq_right (by omega : B/2 ≤ B),
      Nat.cast_pow, Nat.cast_ofNat] using h

/-- The support-rank evaluator has this closed integer cutoff throughout the full window. -/
theorem rank_answer (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    {k a B : ℕ} (hk : 2 ≤ k) (shape : k+2*a = n) (low : n < 3*a)
    (hB : Fintype.card F / 2^128 = B)
    (cap : DoubleQuadraticThreshold.agreements n k ≤ n-B/2+1) (bound : B/2 < n) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val = some (first a B) := by
  classical
  have hs := (curve D hn hk shape low hB cap bound 1).1
  rw [mcaDeltaStar_interleaved_eq] at hs
  have ins : first a B < Fintype.card I := by
    unfold first
    omega
  let ix : Fin (Fintype.card I + 1) := ⟨first a B, by omega⟩
  have hv : ix.val = first a B := rfl
  have h := SecondPrimeRankReview.rankAnswer_of_interior_supremum D (prizeThreshold : ℝ≥0) k ix
    ins (by rw [hv, hn]; simpa [prizeThreshold] using hs)
  exact congrArg (Option.map Fin.val) h

#print axioms curve
#print axioms rank_answer
end ArkLib.ProximityGap.Frontier.SmoothTwoHeadProduction
