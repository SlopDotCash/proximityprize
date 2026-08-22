/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24SuperellipticS2
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25D8Descent

/-!
# LANE B2 (#466 round 147): public d = 8 superelliptic fiber consumer

R25 proves the octic norm-fold endpoint `dBlockIndependence_eight`.  R24's
superelliptic S2 machine consumes a `DBlockIndependence` input at arbitrary `d` and returns
per-fiber Stepanov counts.

This file exposes the missing public `d = 8` analogue of the existing `d = 2` and `d = 4`
fiber consumers in R24.  It does not close the prize core; it removes one interface gap in
the r = 2 superelliptic-face pipeline.
-/

namespace ArkLib.ProximityGap.Frontier.R147OcticSuperellipticS2Consumer

open Polynomial Finset
open ArkLib.ProximityGap.Frontier.R24SuperellipticS2
open ArkLib.ProximityGap.Frontier.R25D8Descent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Octic descent corollary.**  For `d = 8` and squarefree `g`, the direct R25 octic
descent theorem supplies the independence input needed by R24's general superelliptic S2
machine, so the order-8 fiber bound is exposed without the older fraction-field algebraic
instance hypotheses. -/
theorem squarefree_eight_block_fiber_bound
    (g : F[X]) (hg : g.Monic)
    (hsf : Squarefree g) (hdg : 0 < g.natDegree)
    (h8 : 8 ∣ (Fintype.card F - 1))
    {m e J D : ℕ} (hJ : 0 < J)
    (he : e = (Fintype.card F - 1) / 8)
    (hmq : m < Fintype.card F)
    (hD : 8 * D + 7 * g.natDegree < Fintype.card F)
    (hcount : m * (D + (g.natDegree - 1) * m + J) < 8 * (J * (D + 1)))
    (ζ : F) :
    m * (Finset.univ.filter fun s : F => (g.eval s) ^ e = ζ).card
      ≤ g.natDegree * (m + (8 - 1) * e) + D + Fintype.card F * (J - 1) :=
  superelliptic_stepanov_fiber_bound g hg hdg hJ
    (dBlockIndependence_eight g hsf hdg h8 hD) he hmq hcount ζ

/-- Family form of `squarefree_eight_block_fiber_bound`, for callers whose class values are
indexed by a finite support set.  The membership hypothesis is intentionally unused by the
proof; it packages the single-fiber estimate in the shape consumed by the octic model
adapters. -/
theorem squarefree_eight_block_fiber_bound_family
    {ι : Type*} (T : Finset ι) (ζOf : ι → F)
    (g : F[X]) (hg : g.Monic)
    (hsf : Squarefree g) (hdg : 0 < g.natDegree)
    (h8 : 8 ∣ (Fintype.card F - 1))
    {m e J D : ℕ} (hJ : 0 < J)
    (he : e = (Fintype.card F - 1) / 8)
    (hmq : m < Fintype.card F)
    (hD : 8 * D + 7 * g.natDegree < Fintype.card F)
    (hcount : m * (D + (g.natDegree - 1) * m + J) < 8 * (J * (D + 1))) :
    ∀ c ∈ T,
      m * (Finset.univ.filter fun s : F => (g.eval s) ^ e = ζOf c).card
        ≤ g.natDegree * (m + (8 - 1) * e) + D + Fintype.card F * (J - 1) := by
  intro c _
  exact squarefree_eight_block_fiber_bound g hg hsf hdg h8 hJ he hmq hD hcount
    (ζOf c)

end ArkLib.ProximityGap.Frontier.R147OcticSuperellipticS2Consumer

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R147OcticSuperellipticS2Consumer in
#print axioms squarefree_eight_block_fiber_bound
open ArkLib.ProximityGap.Frontier.R147OcticSuperellipticS2Consumer in
#print axioms squarefree_eight_block_fiber_bound_family
