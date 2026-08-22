/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry

/-!
# P1 four-centre routing: one endpoint cannot determine the original secant

The four-centre interaction theorem routes one endpoint of each outside matched pair to one
endpoint of a centre.  Its canonical cross-secant is a genuine `K`-core line.  However, that
cross-secant sees no data from the outside pair's unselected endpoint.

This file records the exact algebraic blindness.  Fix scalar `0` with decoded polynomial `0`.
Against any fixed centre endpoint, its cross-secant is unchanged.  Pairing the same selected
endpoint with scalar `1` decoded respectively by `0` or `1` produces two different original
secants, `(0,0)` and `(0,1)`.  Therefore one-endpoint centre routing cannot by itself cluster the
original matched secants.  A successful successor must route both endpoints, force a second
independent cross-equation, or use a global compatibility invariant coupling the unseen partner.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.P1OneEndpointCentrePropagationRefuted

open HalfPredecessorLineCoreGeometry

/-- Family-free canonical secant parameter. -/
noncomputable def rawSecant
    {F : Type} [Field F] (gamma beta : F) (qGamma qBeta : F[X]) : F[X] × F[X] :=
  let r := slopePolynomial gamma beta qGamma qBeta
  (qGamma - C gamma * r, r)

@[simp]
theorem rawSecant_zero_zero
    {F : Type} [Field F] :
    rawSecant (0 : F) 1 (0 : F[X]) 0 = (0, 0) := by
  simp [rawSecant, slopePolynomial]

@[simp]
theorem rawSecant_zero_one
    {F : Type} [Field F] :
    rawSecant (0 : F) 1 (0 : F[X]) 1 = (0, 1) := by
  simp [rawSecant, slopePolynomial]

theorem zero_and_unit_secants_ne
    {F : Type} [Field F] :
    rawSecant (0 : F) 1 (0 : F[X]) 0 ≠
      rawSecant (0 : F) 1 (0 : F[X]) 1 := by
  simp

/-- **One-endpoint propagation is refuted.**  The routed cross-secant from the selected endpoint
is identical in two configurations, while their original matched-pair secants differ. -/
theorem one_endpoint_crossSecant_blind
    {F : Type} [Field F] (delta : F) (qCentre : F[X]) :
    rawSecant (0 : F) delta (0 : F[X]) qCentre =
        rawSecant (0 : F) delta (0 : F[X]) qCentre ∧
      rawSecant (0 : F) 1 (0 : F[X]) 0 ≠
        rawSecant (0 : F) 1 (0 : F[X]) 1 := by
  exact ⟨rfl, zero_and_unit_secants_ne⟩

end ArkLib.ProximityGap.Frontier.P1OneEndpointCentrePropagationRefuted

open ArkLib.ProximityGap.Frontier.P1OneEndpointCentrePropagationRefuted

#print axioms rawSecant_zero_zero
#print axioms rawSecant_zero_one
#print axioms zero_and_unit_secants_ne
#print axioms one_endpoint_crossSecant_blind
