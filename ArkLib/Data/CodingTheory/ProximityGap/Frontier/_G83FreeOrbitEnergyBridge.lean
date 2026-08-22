/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G82DepthTwoEnergySaddleBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfA05_galois_orbit_count

/-!
# G83: free primitive orbits inject into additive energy

G82 isolated the depth-two orbit hypothesis `n * J ≤ E`.  It is not an additional analytic
conjecture.  Whenever the primitive cores form a finite type with a free action of the size-`n`
subgroup and inject into the additive-energy solution type, the free-action class equation gives
it automatically: every primitive orbit contributes exactly `n` distinct energy solutions.

The first theorem proves this abstractly with `J` defined canonically as the cardinality of the
orbit quotient. **G84 red-team correction:** this does not make `J` the cardinality of a decoder's
actual core type. Reconstructing an actual core from its orbit representative also requires the
scale in the subgroup, restoring the factor `n`. The later consumers in this file are therefore
conditional diagnostics whose `hW` quotient-envelope hypothesis is not supplied by the actual raw
ordered collision sector. Only the class equation and its ambient cardinal consequences are
unconditional. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge

open MulAction
open G82DepthTwoEnergySaddleBridge
open G81FactorialPaddingWickAbsorption

/-- A freely acted-on primitive-core type contributes one full group orbit per quotient class to
any ambient type into which it injects.  This is exactly `|H| * J ≤ E` when `X` is the primitive
depth-two core type and `Y` is the additive-energy solution type. -/
theorem card_group_mul_orbitQuotient_le_ambient
    {H X Y : Type*} [Group H] [Finite H] [MulAction H X] [Finite X] [Finite Y]
    (hfree : ∀ (g : H) (x : X), g • x = x → g = 1)
    (embed : X → Y) (hinj : Function.Injective embed) :
    Nat.card H * Nat.card (Quotient (orbitRel H X)) ≤ Nat.card Y := by
  have hclass := WFA05.spurExcess_eq_orbitCount_mul_phi hfree
  have hXY : Nat.card X ≤ Nat.card Y := Nat.card_le_card_of_injective embed hinj
  calc
    Nat.card H * Nat.card (Quotient (orbitRel H X)) = Nat.card X := by
      rw [Nat.mul_comm, ← hclass]
    _ ≤ Nat.card Y := hXY

/-- The elementary equal-sum bound `|Y| ≤ n^7` at depth four becomes the sharper orbit bound
`J ≤ n^6` after quotienting the free subgroup scaling. -/
theorem orbitQuotient_le_pow_six_of_ambient_le_pow_seven
    {H X Y : Type*} [Group H] [Finite H] [MulAction H X] [Finite X] [Finite Y]
    (hfree : ∀ (g : H) (x : X), g • x = x → g = 1)
    (embed : X → Y) (hinj : Function.Injective embed)
    (hY : Nat.card Y ≤ (Nat.card H) ^ 7) :
    Nat.card (Quotient (orbitRel H X)) ≤ (Nat.card H) ^ 6 := by
  have hmul : Nat.card H * Nat.card (Quotient (orbitRel H X)) ≤
      Nat.card H * (Nat.card H) ^ 6 := by
    calc
      Nat.card H * Nat.card (Quotient (orbitRel H X)) ≤ Nat.card Y :=
        card_group_mul_orbitQuotient_le_ambient hfree embed hinj
      _ ≤ (Nat.card H) ^ 7 := hY
      _ = Nat.card H * (Nat.card H) ^ 6 := by ring
  exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos

/-- **Conditional orbit-accounting weld.** G82's sharp corrected depth-two saddle consumer
with `n * J ≤ E` supplied by a free primitive-core action and an injection into the ambient energy
solutions. The `hW` hypothesis uses the orbit quotient as its core code; G84 proves that no such
decoder can cover actual cores when the action has nontrivial free orbits unless a scale coordinate
is restored. Hence this theorem is valid arithmetic plumbing, not an actual sector bound. -/
theorem free_orbit_energy_absorbed
    {H X Y : Type*} [Group H] [Finite H] [MulAction H X] [Finite X] [Finite Y]
    {r W C : ℕ}
    (hfree : ∀ (g : H) (x : X), g • x = x → g = 1)
    (embed : X → Y) (hinj : Function.Injective embed)
    (hr : 2 ≤ r)
    (hW : W ≤ correctedPadEnvelope
      (Nat.card H) r (Nat.card (Quotient (orbitRel H X))) 2)
    (hE : (Nat.card Y) ^ 2 ≤ C ^ 2 * (Nat.card H) ^ 5)
    (hsmall : C ^ 2 * (r.descFactorial 2) ^ 4 ≤
      (G79PrimitivePaddingSaddleLocalization.oddWickTail r 2) ^ 2 * Nat.card H) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * (Nat.card H) ^ r := by
  apply correctedPaddedDepthTwo_le_fullWick_of_exact_sq_orbit_bound hr hW
  · apply sq_orbit_bound_of_energy
    · exact Nat.card_pos
    · exact card_group_mul_orbitQuotient_le_ambient hfree embed hinj
    · exact hE
  · exact hsmall

/-- After the free-orbit saving, the entire elementary depth-four core universe fits at the
production point.  This is the exact arithmetic statement which repairs G82's `n^7` cutoff. -/
theorem production_depth_four_orbit_universe_le_fullWick :
    (2 ^ 30) ^ 6 * correctedPadEnvelope (2 ^ 30) 110 1 4 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- **Conditional depth-four quotient calculation.** If the primitive depth-four cores carry the free subgroup
scaling, inject into an ambient equal-sum universe of size at most `n^7`, and satisfy the corrected
padding envelope *with the orbit quotient as core type*, then the stated mass fits. G84's decoder
no-go shows the displayed `hW` is unavailable for the actual raw core sector without restoring the
scale factor. -/
theorem production_depth_four_free_orbits_absorbed
    {H X Y : Type*} [Group H] [Finite H] [MulAction H X] [Finite X] [Finite Y]
    {W : ℕ}
    (hcard : Nat.card H = 2 ^ 30)
    (hfree : ∀ (g : H) (x : X), g • x = x → g = 1)
    (embed : X → Y) (hinj : Function.Injective embed)
    (hY : Nat.card Y ≤ (Nat.card H) ^ 7)
    (hW : W ≤ correctedPadEnvelope
      (Nat.card H) 110 (Nat.card (Quotient (orbitRel H X))) 4) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  have hJ := orbitQuotient_le_pow_six_of_ambient_le_pow_seven hfree embed hinj hY
  calc
    W ≤ correctedPadEnvelope
        (Nat.card H) 110 (Nat.card (Quotient (orbitRel H X))) 4 := hW
    _ ≤ correctedPadEnvelope (Nat.card H) 110 ((Nat.card H) ^ 6) 4 := by
      unfold correctedPadEnvelope
      gcongr
    _ = (2 ^ 30) ^ 6 * correctedPadEnvelope (2 ^ 30) 110 1 4 := by
      rw [hcard]
      unfold correctedPadEnvelope
      ring
    _ ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 :=
      production_depth_four_orbit_universe_le_fullWick

/-- **Diagnostic cutoff for the unavailable quotient envelope.** Applying the same equal-sum (`n^9`) and free-orbit (`/n`) argument at
depth five leaves `n^8` orbit classes, whose corrected padding overcount exceeds the production
Wick budget. Since the quotient envelope itself cannot decode raw cores, this is only arithmetic
calibration and does not locate the honest sector cutoff. -/
theorem production_depth_five_orbit_overcount_exceeds_fullWick :
    Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 <
      (2 ^ 30) ^ 8 * correctedPadEnvelope (2 ^ 30) 110 1 5 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge

/-! ## Axiom audit -/
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge.card_group_mul_orbitQuotient_le_ambient
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge.orbitQuotient_le_pow_six_of_ambient_le_pow_seven
#print axioms
  ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge.free_orbit_energy_absorbed
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge.production_depth_four_orbit_universe_le_fullWick
#print axioms
  ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge.production_depth_four_free_orbits_absorbed
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G83FreeOrbitEnergyBridge.production_depth_five_orbit_overcount_exceeds_fullWick
