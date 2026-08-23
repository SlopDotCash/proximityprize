/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry

/-!
# P1 eight-centre routing: two cross-secants reconstruct the original secant

One routed endpoint is blind to the other endpoint of a matched pair.  The two-sided eight-centre
theorem repairs that exact algebraic defect.  A canonical cross-secant remembers its outside
endpoint polynomial: evaluate the line at the outside scalar.  Consequently two cross-secants,
one through each endpoint (their centre endpoints may be completely unrelated), recover both
lifted endpoints and hence recover the original canonical secant.

This file proves the factorization and its injectivity without any degree or cardinality
hypothesis.  Thus the remaining P1 obstruction is no longer reconstruction.  It is a counting
problem: boundedly many centre *endpoints* do not yet bound the number of large-core cross-secants
incident to them.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.P1TwoEndpointCentreReconstruction

open HalfPredecessorLineCoreGeometry

/-- Family-free canonical secant parameter. -/
noncomputable def rawSecant
    {F : Type} [Field F] (gamma beta : F) (qGamma qBeta : F[X]) : F[X] × F[X] :=
  let r := slopePolynomial gamma beta qGamma qBeta
  (qGamma - C gamma * r, r)

/-- Evaluate a polynomial line `(a,r)` at its scalar parameter. -/
noncomputable def pointOnLine {F : Type} [Field F]
    (gamma : F) (line : F[X] × F[X]) : F[X] :=
  line.1 + C gamma * line.2

/-- A canonical secant always recovers its first lifted endpoint, even if the two scalar labels
coincide. -/
@[simp]
theorem pointOnLine_rawSecant_first
    {F : Type} [Field F] (gamma beta : F) (qGamma qBeta : F[X]) :
    pointOnLine gamma (rawSecant gamma beta qGamma qBeta) = qGamma := by
  simp [pointOnLine, rawSecant]

/-- At distinct labels, the same canonical secant recovers its second lifted endpoint. -/
@[simp]
theorem pointOnLine_rawSecant_second
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {gamma beta : F} (hne : gamma ≠ beta)
    (qGamma qBeta : F[X]) :
    pointOnLine beta (rawSecant gamma beta qGamma qBeta) = qBeta := by
  simpa only [pointOnLine, rawSecant] using
    (second_point_on_secant_line hne qGamma qBeta).symm

/-- The two cross-secants through arbitrary centre endpoints recover the two outside endpoint
polynomials and therefore factor the original matched secant exactly. -/
theorem originalSecant_eq_of_two_crossSecants
    {F : Type} [Field F]
    (gamma beta delta theta : F)
    (qGamma qBeta qDelta qTheta : F[X]) :
    rawSecant gamma beta qGamma qBeta =
      rawSecant gamma beta
        (pointOnLine gamma (rawSecant gamma delta qGamma qDelta))
        (pointOnLine beta (rawSecant beta theta qBeta qTheta)) := by
  simp

/-- In particular, with the scalar labels and centre data fixed, the ordered pair of routed
cross-secants is injective in the two outside decoded polynomials. -/
theorem two_crossSecants_injective
    {F : Type} [Field F]
    (gamma beta delta theta : F) (qDelta qTheta : F[X]) :
    Function.Injective (fun q : F[X] × F[X] =>
      (rawSecant gamma delta q.1 qDelta, rawSecant beta theta q.2 qTheta)) := by
  intro q p h
  have hfirst := congrArg (fun lines => pointOnLine gamma lines.1) h
  have hsecond := congrArg (fun lines => pointOnLine beta lines.2) h
  simp only [pointOnLine_rawSecant_first] at hfirst hsecond
  exact Prod.ext hfirst hsecond

/-- Equality of both routed cross-secants forces equality of the original matched secants. -/
theorem originalSecant_eq_of_crossSecants_eq
    {F : Type} [Field F]
    (gamma beta delta theta : F)
    {qGamma qBeta pGamma pBeta qDelta qTheta : F[X]}
    (hgamma : rawSecant gamma delta qGamma qDelta =
      rawSecant gamma delta pGamma qDelta)
    (hbeta : rawSecant beta theta qBeta qTheta =
      rawSecant beta theta pBeta qTheta) :
    rawSecant gamma beta qGamma qBeta = rawSecant gamma beta pGamma pBeta := by
  have hpairs : (qGamma, qBeta) = (pGamma, pBeta) :=
    two_crossSecants_injective gamma beta delta theta qDelta qTheta
      (Prod.ext hgamma hbeta)
  cases hpairs
  rfl

/-! ## Exact centre-pencil audit -/

/-- The polynomial line of slope `r` through the fixed lifted centre `(delta,qDelta)`. -/
noncomputable def centrePencilLine
    {F : Type} [Field F] (delta : F) (qDelta r : F[X]) : F[X] × F[X] :=
  (qDelta - C delta * r, r)

@[simp]
theorem centrePencilLine_at_centre
    {F : Type} [Field F] (delta : F) (qDelta r : F[X]) :
    pointOnLine delta (centrePencilLine delta qDelta r) = qDelta := by
  simp [pointOnLine, centrePencilLine]

/-- **Every polynomial slope occurs through one fixed centre endpoint.**  Choose the outside
decoded polynomial to be the value of the desired line at `gamma`; its canonical cross-secant
with the centre is literally that line. -/
theorem rawSecant_pointOn_centrePencil
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {gamma delta : F} (hne : gamma ≠ delta) (qDelta r : F[X]) :
    rawSecant gamma delta
      (pointOnLine gamma (centrePencilLine delta qDelta r)) qDelta =
        centrePencilLine delta qDelta r := by
  apply Prod.ext
  · simp only [rawSecant, centrePencilLine, pointOnLine]
    have hslope : slopePolynomial gamma delta
        (qDelta - C delta * r + C gamma * r) qDelta = r := by
      simp only [slopePolynomial, sub_sub]
      rw [show qDelta - C delta * r + C gamma * r - qDelta =
          C (gamma - delta) * r by rw [C_sub]; ring]
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]
    rw [hslope]
    ring
  · simp only [rawSecant, centrePencilLine, pointOnLine]
    simp only [slopePolynomial, sub_sub]
    rw [show qDelta - C delta * r + C gamma * r - qDelta =
        C (gamma - delta) * r by rw [C_sub]; ring]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]

/-- Distinct slopes give distinct lines in a fixed centre pencil. -/
theorem centrePencilLine_injective
    {F : Type} [Field F] (delta : F) (qDelta : F[X]) :
    Function.Injective (centrePencilLine delta qDelta) := by
  intro r s h
  exact congrArg Prod.snd h

/-- Hence a single fixed centre endpoint supports an injective copy of the entire polynomial
space as canonical cross-secants.  Boundedly many centres alone give no algebraic multiplicity
bound; any successful bound must use the large-core incidence condition. -/
theorem fixedCentre_crossSecants_injective
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {gamma delta : F} (hne : gamma ≠ delta) (qDelta : F[X]) :
    Function.Injective (fun r : F[X] => rawSecant gamma delta
      (pointOnLine gamma (centrePencilLine delta qDelta r)) qDelta) := by
  intro r s h
  dsimp only at h
  rw [rawSecant_pointOn_centrePencil hne,
    rawSecant_pointOn_centrePencil hne] at h
  exact centrePencilLine_injective delta qDelta h

end ArkLib.ProximityGap.Frontier.P1TwoEndpointCentreReconstruction

open ArkLib.ProximityGap.Frontier.P1TwoEndpointCentreReconstruction

#print axioms pointOnLine_rawSecant_first
#print axioms pointOnLine_rawSecant_second
#print axioms originalSecant_eq_of_two_crossSecants
#print axioms two_crossSecants_injective
#print axioms originalSecant_eq_of_crossSecants_eq
#print axioms centrePencilLine_at_centre
#print axioms rawSecant_pointOn_centrePencil
#print axioms centrePencilLine_injective
#print axioms fixedCentre_crossSecants_injective
