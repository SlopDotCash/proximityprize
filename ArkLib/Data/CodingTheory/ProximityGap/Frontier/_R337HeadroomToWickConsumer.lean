/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS6AlmostAllPrimesWickRung

/-!
# R337: direct headroom-to-Wick consumer

Packages the final arithmetic adapter in the FS6 route: a strict excess-count
bound directly implies the good-prime Wick estimate.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R337HeadroomToWickConsumer

open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger (excessCount)
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition (tupleSet)
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm (Gset)
open ArkLib.ProximityGap.GaussPeriodMomentBound (GaussianEnergyBound)
open scoped Classical

theorem gaussianEnergyBound_three_of_strict_headroom
    {k s p : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (hp : p ∈ P)
    (hcount : excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p <
      45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    GaussianEnergyBound (Gset ζ (2 ^ k)) 3 := by
  apply gaussianEnergyBound_three_of_good_prime hs P hP p hp
  · intro hmem
    have hge := (Finset.mem_filter.mp hmem).2
    omega
  · exact hprim
  · exact hψ

end ArkLib.ProximityGap.Frontier.R337HeadroomToWickConsumer

#print axioms ArkLib.ProximityGap.Frontier.R337HeadroomToWickConsumer.gaussianEnergyBound_three_of_strict_headroom
