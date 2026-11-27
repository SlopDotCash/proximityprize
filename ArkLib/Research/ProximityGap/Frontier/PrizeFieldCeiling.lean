/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrizeCeilingFermat
import ArkLib.Research.ProximityGap.Frontier.PrizeCeilingPrimes
import ArkLib.Research.ProximityGap.Frontier.PrizeCeilingProperPowers
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent

/-! # Largest admissible field at each dimension-one prize length

For n = 2, 4, 8 and 16, the largest finite field below 2²⁵⁶ admitting a
multiplicative subgroup of order n has cardinality 2²⁵⁶ minus 189, 435,
2063 and 2063, respectively. Each maximum is attained by a prime field. -/

namespace ProximityGap.PrizeFieldCeiling

/-- Each of the three maxima is prime, as certified by its Lucas factorization tree. -/
theorem prime (n : ℕ) : (maxCard n).Prime := by
  unfold maxCard
  split
  · exact PrizeCeilingPrimes.prime_189
  · split
    · exact PrizeCeilingPrimes.prime_435
    · exact PrizeCeilingPrimes.prime_2063

/-- All three maxima lie strictly below the sponsor's ceiling. -/
theorem below (n : ℕ) : maxCard n < 2 ^ 256 := by
  unfold maxCard
  split
  · decide
  · split <;> decide

/-- The primitive subgroup order divides the multiplicative group of the indicated prime field. -/
theorem dvd_sub_one {n : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) : n ∣ maxCard n - 1 := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide

/-- Every prime power with the required subgroup divisibility obeys the explicit bound. -/
theorem upper_order {q n : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16)
    (power : IsPrimePow q) (div : n ∣ q - 1) (high : q < 2 ^ 256) : q ≤ maxCard n := by
  by_cases near : 2 ^ 256 - 2063 ≤ q
  · exact prime_le hn (PrizeCeilingProperPowers.prime_of_isPrimePow power near high) high div
  · have least : 2 ^ 256 - 2063 ≤ maxCard n := by
      unfold maxCard
      split
      · decide
      · split <;> decide
    omega

/-- Every eligible finite field, including a nonprime field, lies below or at this maximum. -/
theorem upper (F : Type*) [Field F] [Fintype F] {n : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16)
    (high : Fintype.card F < 2 ^ 256) (div : n ∣ Fintype.card F - 1) :
    Fintype.card F ≤ maxCard n :=
  upper_order hn (FiniteField.isPrimePow_card F) div high

/-- The upper cardinality is attained, with an actual smooth domain of the required length. -/
theorem attained {n : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) :
    let _ : Fact (maxCard n).Prime := ⟨prime n⟩
    ∃ D : Fin n ↪ ZMod (maxCard n), Nonempty (ReedSolomon.Smooth D) := by
  let : Fact (maxCard n).Prime := ⟨prime n⟩
  dsimp only
  apply SmoothPowerMcaDescent.exists_prime_domain (dvd_sub_one hn)
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

end ProximityGap.PrizeFieldCeiling
