import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OperationalLatticeExactBridge
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar

/-!
# R350: the base-consistent entropy candidate misses the production Hamming lattice

At rate `1/2` and idealized list budget `B = n = 2^25`, the continuous entropy
candidate is

`1 - 1/2 - H(1/2)/log_2(2^25) = 1/2 - 1/25 = 23/50`.

Every operational MCA threshold on a nonempty good set is a Hamming lattice
point `j/2^25`.  Since `50` has an odd factor `25`, `23/50` is not such a
point.  Thus the continuous formula cannot be an exact finite-code answer at
this production-scale row; a rounded adjacent-cell statement is mandatory.

The historical `prizeDeltaStar` definition mixes natural-log entropy with a
base-two denominator, so it instead evaluates to `1/2 - log 2 / 25`; this file
records that distinction explicitly.  The lattice refutation applies to the
base-consistent `23/50` candidate and does not refute a rounded prize conjecture.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.PrizeEntropy ProximityGap.GrandChallengesLattice
open ProximityGap.MCAListBracketInterpolation

namespace ProximityGap.PrizeEntropy

/-- Binary entropy at rate one half is `log 2`. -/
theorem binEntropy_one_half_exact :
    Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
  rw [Real.binEntropy]
  norm_num [Real.log_inv]
  ring

/-- The historical mixed-base candidate at rate one half and `B = 2^25`. -/
theorem prizeDeltaStar_half_two_pow_twenty_five :
    prizeDeltaStar (1 / 2 : ℝ) (2 ^ 25 : ℝ) =
      1 / 2 - Real.log 2 / 25 := by
  rw [prizeDeltaStar, binEntropy_one_half_exact]
  rw [Real.logb]
  change 1 - 1 / 2 - Real.log 2 /
      (Real.log ((2 : ℝ) ^ 25) / Real.log 2) =
        1 / 2 - Real.log 2 / 25
  rw [Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog]
  ring

/-- In particular, the historical mixed-base candidate is not the
base-consistent value `23/50`. -/
theorem prizeDeltaStar_half_two_pow_twenty_five_ne_base_consistent :
    prizeDeltaStar (1 / 2 : ℝ) (2 ^ 25 : ℝ) ≠ 23 / 50 := by
  rw [prizeDeltaStar_half_two_pow_twenty_five]
  have hlog_lt : Real.log (2 : ℝ) < 1 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num) using 1 <;>
      norm_num
  intro h
  nlinarith

/-- No point of the `2^25` Hamming lattice equals `23/50`. -/
theorem rateHalf_candidate_not_lattice
    (j : Fin (2 ^ 25 + 1)) :
    ((mcaLatticePoint (2 ^ 25) j : ℝ≥0) : ℝ) ≠ 23 / 50 := by
  intro h
  unfold mcaLatticePoint at h
  norm_num at h
  have hj : (50 : ℕ) * j.val = 23 * 2 ^ 25 := by
    exact_mod_cast (show (50 : ℝ) * j.val = 23 * 2 ^ 25 by nlinarith)
  have h25 : 25 ∣ 23 * 2 ^ 25 := by
    use 2 * j.val
    omega
  norm_num at h25

/-- **Production-scale lattice refutation.** For every length-`2^25` code whose
good lattice set is nonempty, the operational MCA threshold differs from the
base-consistent rate-half entropy candidate `23/50`. -/
theorem operational_deltaStar_ne_base_consistent_entropy_half_two_pow_twenty_five
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (hn : Fintype.card ι = 2 ^ 25)
    (C : Set (ι → F)) (εstar : ℝ≥0)
    (hne : mcaThresholdExists C εstar) :
    (mcaDeltaStar (F := F) (A := F) C (εstar : ENNReal) : ℝ) ≠ 23 / 50 := by
  obtain ⟨j, hj⟩ := exists_latticePoint_eq_mcaDeltaStar C εstar hne
  intro h
  let j' : Fin (2 ^ 25 + 1) :=
    ⟨j.val, by rw [← hn]; exact j.isLt⟩
  have hjpoint :
      mcaLatticePoint (Fintype.card ι) j = mcaLatticePoint (2 ^ 25) j' := by
    unfold mcaLatticePoint
    simp only [j', hn]
  have hjR := congrArg (fun x : ℝ≥0 => (x : ℝ)) hj
  have hlattice :
      ((mcaLatticePoint (2 ^ 25) j' : ℝ≥0) : ℝ) = 23 / 50 := by
    rw [← hjpoint]
    exact hjR.symm.trans h
  exact rateHalf_candidate_not_lattice j' hlattice

end ProximityGap.PrizeEntropy

#print axioms ProximityGap.PrizeEntropy.binEntropy_one_half_exact
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_half_two_pow_twenty_five
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_half_two_pow_twenty_five_ne_base_consistent
#print axioms ProximityGap.PrizeEntropy.rateHalf_candidate_not_lattice
#print axioms
  ProximityGap.PrizeEntropy.operational_deltaStar_ne_base_consistent_entropy_half_two_pow_twenty_five
