/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SevenSiteTransfer
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenProjectivities

/-! # Seven-site rigidity on smooth dyadic prime-field orbits -/
namespace ProximityGap.DyadicSevenPrime
open DyadicSevenDescent

/-- On a dyadic orbit of length n in a prime field of characteristic above
2^n, seven distinct matches force either a scaling or a reciprocal scaling. -/
theorem rigid {p m : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z (2^m))
    (large : 2^(2^m)<p) : Rigid z := by
  by_cases small : 2^m<7
  · exact DyadicSevenField.small hz (by positivity) small
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by intro eq; simp [eq] at small)
  let n := 2^(j+1)
  have hn : 2<n := by dsimp [n]; omega
  have np : n<p := lt_trans Nat.lt_two_pow_self large
  let : NeZero (n : ZMod p) := ⟨fun h => (Nat.not_dvd_of_pos_of_lt (by omega) np)
    ((ZMod.natCast_eq_zero_iff n p).mp h)⟩
  have h := Complex.isPrimitiveRoot_exp n (show n≠0 by omega)
  apply SevenSiteTransfer.transfer (n:=n) hn hz h _ (DyadicSevenProjectivities.all_orders h)
  apply lt_of_eq_of_lt _ (Nat.pow_lt_pow_left large (by decide : 2≠0))
  dsimp only [n]
  rw [Nat.totient_prime_pow_succ Nat.prime_two,show 2-1=1 by decide,mul_one,
    show 16=2^4 by decide,←pow_mul,←pow_mul,pow_succ 2 j]
  congr 1
  omega

end ProximityGap.DyadicSevenPrime
#print axioms ProximityGap.DyadicSevenPrime.rigid
