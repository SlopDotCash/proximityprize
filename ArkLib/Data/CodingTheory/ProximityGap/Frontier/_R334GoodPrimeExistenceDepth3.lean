import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS6AlmostAllPrimesWickRung

/-!
# R334: extracting a good prime from the FS6 cap

The FS6 ledger bounds the exceptional-prime filter.  This file supplies the
finite-set extraction step: if that bound is strictly smaller than the chosen
prime family, a member outside the bad filter exists.  The result is useful
for deploying the depth-3 Wick weld to an explicit supplied family.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R334GoodPrimeExistenceDepth3

open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open scoped Classical

theorem exists_good_prime_of_badPrime_cap_lt
    {k s T : ℕ} (hs : 0 < s) (hT : 0 < T)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (hcap_lt :
      (2 ^ (k + 1)) ^ 6 * (((k + 1 + 3) * 2 ^ (k + 1)) / s) / T < P.card) :
    ∃ p ∈ P,
      p ∉ P.filter (fun p => T ≤ excessCount
        (tupleSet (2 ^ (k + 1))) (BadPat k) p) := by
  have hcard_cap := badPrime_cap (k := k) hs hT P hP
  by_contra hnone
  push_neg at hnone
  have hsub : P ⊆ P.filter (fun p => T ≤ excessCount
      (tupleSet (2 ^ (k + 1))) (BadPat k) p) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hp, (Finset.mem_filter.mp (hnone p hp)).2⟩
  have hcard_le := Finset.card_le_card hsub
  have hbad_lt :
      (P.filter (fun p => T ≤ excessCount
        (tupleSet (2 ^ (k + 1))) (BadPat k) p)).card < P.card :=
    lt_of_le_of_lt hcard_cap hcap_lt
  exact (not_lt_of_ge hcard_le) hbad_lt

end ArkLib.ProximityGap.Frontier.R334GoodPrimeExistenceDepth3

#print axioms
  ArkLib.ProximityGap.Frontier.R334GoodPrimeExistenceDepth3.exists_good_prime_of_badPrime_cap_lt
