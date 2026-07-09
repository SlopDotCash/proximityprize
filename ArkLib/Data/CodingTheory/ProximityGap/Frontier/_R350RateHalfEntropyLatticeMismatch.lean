import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OperationalLatticeExactBridge
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar

/-!
# R350: the unrounded entropy candidate misses the production Hamming lattice

At rate `1/2` and idealized list budget `B = n = 2^25`, the continuous entropy
candidate is

`1 - 1/2 - H(1/2)/log_2(2^25) = 1/2 - 1/25 = 23/50`.

Every operational MCA threshold on a nonempty good set is a Hamming lattice
point `j/2^25`.  Since `50` has an odd factor `25`, `23/50` is not such a
point.  Thus the continuous formula cannot be an exact finite-code answer at
this production-scale row; a rounded adjacent-cell statement is mandatory.

This refutes only the unrounded equality, not the rounded prize conjecture.
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

/-- The rate-half entropy candidate with `B = 2^25` is exactly `23/50`. -/
theorem prizeDeltaStar_half_two_pow_twenty_five :
    prizeDeltaStar (1 / 2 : ℝ) (2 ^ 25 : ℝ) = 23 / 50 := by
  rw [prizeDeltaStar, binEntropy_one_half_exact]
  rw [Real.logb, Real.log_pow]
  norm_num
  field_simp
  ring

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
unrounded rate-half entropy candidate at idealized budget `B=2^25`. -/
theorem operational_deltaStar_ne_unrounded_entropy_half_two_pow_twenty_five
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (hn : Fintype.card ι = 2 ^ 25)
    (C : Set (ι → F)) (εstar : ℝ≥0)
    (hne : mcaThresholdExists C εstar) :
    (mcaDeltaStar (F := F) (A := F) C (εstar : ENNReal) : ℝ) ≠
      prizeDeltaStar (1 / 2 : ℝ) (2 ^ 25 : ℝ) := by
  obtain ⟨j, hj⟩ := exists_latticePoint_eq_mcaDeltaStar C εstar hne
  rw [prizeDeltaStar_half_two_pow_twenty_five]
  intro h
  have hlattice :
      ((mcaLatticePoint (2 ^ 25) j : ℝ≥0) : ℝ) = 23 / 50 := by
    rw [← hn]
    exact_mod_cast hj.symm.trans (by exact_mod_cast h)
  exact rateHalf_candidate_not_lattice
    ⟨j.val, by simpa [hn] using j.isLt⟩ hlattice

end ProximityGap.PrizeEntropy

#print axioms ProximityGap.PrizeEntropy.binEntropy_one_half_exact
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_half_two_pow_twenty_five
#print axioms ProximityGap.PrizeEntropy.rateHalf_candidate_not_lattice
#print axioms
  ProximityGap.PrizeEntropy.operational_deltaStar_ne_unrounded_entropy_half_two_pow_twenty_five
