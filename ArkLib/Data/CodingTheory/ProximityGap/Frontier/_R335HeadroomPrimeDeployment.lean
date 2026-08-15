import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R334GoodPrimeExistenceDepth3

/-!
# R335: explicit headroom-prime deployment

Specializes the FS6 finite extraction threshold to
`T = 45 n² − 40 n + 1`, the exact headroom boundary in the good-prime Wick
weld.  The output is the arithmetic inequality consumed by that weld.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R335HeadroomPrimeDeployment

open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.R334GoodPrimeExistenceDepth3

open Classical in
theorem exists_prime_with_depth3_headroom
    {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (hcap_lt :
      (2 ^ (k + 1)) ^ 6 * (((k + 1 + 3) * 2 ^ (k + 1)) / s) /
        (45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1) < P.card) :
    ∃ p ∈ P,
      p ∉ P.filter (fun p =>
        45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1 ≤
          excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p) := by
  apply exists_good_prime_of_badPrime_cap_lt hs
    (T := 45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1) (by omega) P hP
  simpa using hcap_lt

end ArkLib.ProximityGap.Frontier.R335HeadroomPrimeDeployment

#print axioms ArkLib.ProximityGap.Frontier.R335HeadroomPrimeDeployment.exists_prime_with_depth3_headroom
