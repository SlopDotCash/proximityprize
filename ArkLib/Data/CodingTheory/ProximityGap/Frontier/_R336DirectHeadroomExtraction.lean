import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R335HeadroomPrimeDeployment

/-!
# R336: direct strict headroom extraction

The good-prime filter is defined using `T ≤ excessCount`; its complement is
exactly the strict inequality `excessCount < T`.  This small logical adapter
is the form required by arithmetic consumers.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R336DirectHeadroomExtraction

open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.Frontier.R335HeadroomPrimeDeployment

theorem exists_prime_with_strict_depth3_headroom
    {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (hcap_lt :
      (2 ^ (k + 1)) ^ 6 * (((k + 1 + 3) * 2 ^ (k + 1)) / s) /
        (45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1) < P.card) :
    ∃ p ∈ P,
      excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p <
        45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1 := by
  obtain ⟨p, hpP, hpGood⟩ := exists_prime_with_depth3_headroom hs P hP hcap_lt
  refine ⟨p, hpP, ?_⟩
  by_contra hnot
  have hge : 45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1 ≤
      excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p := by omega
  exact hpGood (Finset.mem_filter.mpr ⟨hpP, hge⟩)

end ArkLib.ProximityGap.Frontier.R336DirectHeadroomExtraction

#print axioms
  ArkLib.ProximityGap.Frontier.R336DirectHeadroomExtraction
    .exists_prime_with_strict_depth3_headroom
