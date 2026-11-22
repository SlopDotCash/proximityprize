/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.JointPairThreshold
import ArkLib.Research.ProximityGap.Frontier.DyadicList256Realizations
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup

/-! # Joint determinant transposition bounds at length 512 over four named primes -/

set_option maxRecDepth 20000

namespace ProximityGap.JointPair512
open Code ReflectionListSampling
open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)


/-- Each named field admits a 512-site smooth domain, and the integral joint
test gives row caps 55, 16, 16, and 15, respectively. -/
theorem arithmetic {p T : ℕ} (named : (p=P ∧ T=55) ∨
    (p=Pallas.baseFieldSize ∧ T=16) ∨ (p=Vesta.baseFieldSize ∧ T=16) ∨
    (p=BlsScalarSubgroup.P ∧ T=15)) :
    512∣p-1 ∧ 3≤T ∧ (12*(T+1)^3)^256<((T+1)*T*(T-2))^256*p^4 := by
  rcases named with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

/-- The four caps hold on every ordering of every 512-site smooth coset. -/
theorem caps {p T : ℕ} [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I]
    (named : (p=P ∧ T=55) ∨ (p=Pallas.baseFieldSize ∧ T=16) ∨
      (p=Vesta.baseFieldSize ∧ T=16) ∨ (p=BlsScalarSubgroup.P ∧ T=15))
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=512) : PairCap D T := by
  obtain ⟨_,size,test⟩ := arithmetic named
  exact JointPairThreshold.cap (m:=9) D hn size (by rwa [show Nat.totient (2^9)=256 by decide])

end ProximityGap.JointPair512
#print axioms ProximityGap.JointPair512.caps
