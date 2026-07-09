/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R303GeneralROrbitChebyshev

/-!
# R304: orbit Chebyshev consumers for the DC-energy wall

R303 proves the depth-uniform orbit-level Chebyshev inequality in terms of the
raw DC-subtracted `r`-energy.  R240 names the analytic wall as
`DCEnergyBoundWithConstant`.  This file composes the two interfaces.

No new analytic estimate is proved here.  The point is to expose the exact
large-orbit count consequence of a future constant-`K` DC-energy wall at any
depth, at bounded depth, or at the ceiling depth.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R304OrbitChebyshevDCEnergyConsumer

open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "devR" => ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev.deviationR

/-- A constant-`K` DC-energy bound at depth `r` gives a quantitative bound on
the number of `G`-orbits with depth-`r` deviation at least `T`. -/
theorem orbit_count_chebyshev_of_dcEnergyBoundWithConstant
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (r : ℕ) (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T K : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |devR G r b|)
    (hdc : DCEnergyBoundWithConstant G r K) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  have hcheb :=
    orbit_count_chebyshev_energy G hmul hinv h0 r R hR0 hdisj hT hbig
  unfold DCEnergyBoundWithConstant at hdc
  have hq0 : 0 ≤ (Fintype.card F : ℝ) := by positivity
  calc
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
        ≤ (Fintype.card F : ℝ)
            * ((Fintype.card F : ℝ)
              * (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ)
              - (G.card : ℝ) ^ (2 * r)) := hcheb
    _ ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ)
            * (K ^ r
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :=
        mul_le_mul_of_nonneg_left hdc hq0
    _ = (Fintype.card F : ℝ) ^ 2
          * (K ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
        ring

/-- Wall form: an all-depth constant-`K` DC-energy wall gives the orbit-count
bound at every requested depth. -/
theorem orbit_count_chebyshev_of_dcEnergyWallWithConstant
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (K : ℝ) (hwall : DCEnergyWallWithConstant G K)
    (r : ℕ) (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |devR G r b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :=
  orbit_count_chebyshev_of_dcEnergyBoundWithConstant G hmul hinv h0 r R hR0 hdisj
    hT hbig (hwall r)

/-- Bounded-depth wall form: if the constant-`K` DC-energy wall is known up to
`Rmax`, the orbit-count bound is available for every `r ≤ Rmax`. -/
theorem orbit_count_chebyshev_of_dcEnergyWallWithConstantUpTo
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (K : ℝ) {Rmax : ℕ} (hwall : DCEnergyWallWithConstantUpTo G K Rmax)
    (r : ℕ) (hr : r ≤ Rmax) (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |devR G r b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :=
  orbit_count_chebyshev_of_dcEnergyBoundWithConstant G hmul hinv h0 r R hR0 hdisj
    hT hbig (hwall r hr)

/-- Ceiling-depth endpoint: a constant-`K` DC-energy ceiling wall gives the
orbit-count bound at the moment-optimal ceiling depth. -/
theorem orbit_count_chebyshev_of_dcEnergyCeilWallWithConstant
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (K : ℝ) (hwall : DCEnergyCeilWallWithConstant G K)
    (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R,
      T ≤ |devR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) :=
  orbit_count_chebyshev_of_dcEnergyBoundWithConstant G hmul hinv h0
    ⌈Real.log (Fintype.card F : ℝ)⌉₊ R hR0 hdisj hT hbig hwall

end ArkLib.ProximityGap.Frontier.R304OrbitChebyshevDCEnergyConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R304OrbitChebyshevDCEnergyConsumer.orbit_count_chebyshev_of_dcEnergyBoundWithConstant
#print axioms
  ArkLib.ProximityGap.Frontier.R304OrbitChebyshevDCEnergyConsumer.orbit_count_chebyshev_of_dcEnergyWallWithConstant
#print axioms
  ArkLib.ProximityGap.Frontier.R304OrbitChebyshevDCEnergyConsumer.orbit_count_chebyshev_of_dcEnergyWallWithConstantUpTo
#print axioms
  ArkLib.ProximityGap.Frontier.R304OrbitChebyshevDCEnergyConsumer.orbit_count_chebyshev_of_dcEnergyCeilWallWithConstant
