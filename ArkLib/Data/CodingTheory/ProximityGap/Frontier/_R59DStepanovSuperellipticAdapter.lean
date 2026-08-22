/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24FullRungAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24SuperellipticS2

/-!
# LANE FULLRUNG (#466 round 59): adapt superelliptic fibers to `DStepanovOutput`

Round 24 proves the order-`d` Stepanov S2 theorem for arbitrary superelliptic power
fibers `{s : g(s)^e = ζ}`.  The full-rung assembly consumes the abstract
`DStepanovOutput` interface, stated over class fibers
`{s : tripleVal χ u v w s = c}`.

This file records the small but important interface adapter: if, for each tuple and class
value, the triple-linear class fiber is contained in one superelliptic power fiber, then
the S2 theorem supplies `DStepanovOutput`.  The remaining concrete algebra is now isolated
to proving that map for the triple kernel polynomial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter

open Polynomial
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R24SuperellipticS2
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A class-to-fiber map: for every triple-linear tuple and every class value `c`, choose
a superelliptic polynomial `g` and power-fiber target `ζ` such that the class fiber
`tripleVal = c` is contained in `{s : g(s)^e = ζ}`. -/
def ClassFiberPowerModel (χ : MulChar F ℂ) (T : Finset ℂ) (e : ℕ)
    (gOf : F → F → F → ℂ → F[X]) (ζOf : F → F → F → ℂ → F) : Prop :=
  ∀ u v w : F, ∀ c ∈ T, ∀ s : F,
    tripleVal χ u v w s = c → ((gOf u v w c).eval s) ^ e = ζOf u v w c

/-- The structural hypotheses needed to run the superelliptic S2 engine uniformly over
the tuple/class-indexed polynomials supplied by `ClassFiberPowerModel`. -/
def SuperellipticModelHypotheses (T : Finset ℂ) (gOf : F → F → F → ℂ → F[X])
    (d q D : ℕ) : Prop :=
  ∀ u v w : F, ∀ c ∈ T,
    (gOf u v w c).Monic ∧
      Squarefree (gOf u v w c) ∧
      0 < (gOf u v w c).natDegree ∧
      DBlockIndependence F d q D (gOf u v w c)

/-- Conditional adapter from tuple/class-indexed superelliptic S2 certificates to the
abstract `DStepanovOutput` consumed by the full-rung pipeline.  The concrete future task is
to instantiate `gOf`, `ζOf`, and `ClassFiberPowerModel` for the triple-linear kernel. -/
theorem dStepanovOutput_of_superelliptic_power_model
    (χ : MulChar F ℂ) (T : Finset ℂ)
    {d m e J D Dtot : ℕ}
    (gOf : F → F → F → ℂ → F[X]) (ζOf : F → F → F → ℂ → F)
    (hJ : 0 < J)
    (hmodel : ClassFiberPowerModel χ T e gOf ζOf)
    (hpoly : SuperellipticModelHypotheses (F := F) T gOf d (Fintype.card F) D)
    (he : e = (Fintype.card F - 1) / d)
    (hmq : m < Fintype.card F)
    (hcount : ∀ u v w : F, ∀ c ∈ T,
      m * (D + ((gOf u v w c).natDegree - 1) * m + J) < d * (J * (D + 1)))
    (hDtot : ∀ u v w : F, ∀ c ∈ T,
      (gOf u v w c).natDegree * (m + (d - 1) * e) + D
          + Fintype.card F * (J - 1) ≤ Dtot) :
    DStepanovOutput χ T m Dtot := by
  intro u v w c hc
  obtain ⟨hg, _hsf, hdg, hind⟩ := hpoly u v w c hc
  obtain ⟨P, hP0, hPdeg, hPvan⟩ :=
    superelliptic_stepanov_S2 (gOf u v w c) hg hdg hJ hind he hmq
      (hcount u v w c hc) (ζOf u v w c)
  refine ⟨P, hP0, ?_, le_trans hPdeg (hDtot u v w c hc)⟩
  intro a ha k hk
  rw [NClassT, Finset.mem_filter] at ha
  exact hPvan a (hmodel u v w c hc a ha.2) k hk

/-- Short audit alias for the superelliptic-to-`DStepanovOutput` adapter. -/
theorem dStepanovOutput_adapter
    (χ : MulChar F ℂ) (T : Finset ℂ)
    {d m e J D Dtot : ℕ}
    (gOf : F → F → F → ℂ → F[X]) (ζOf : F → F → F → ℂ → F)
    (hJ : 0 < J)
    (hmodel : ClassFiberPowerModel χ T e gOf ζOf)
    (hpoly : SuperellipticModelHypotheses (F := F) T gOf d (Fintype.card F) D)
    (he : e = (Fintype.card F - 1) / d)
    (hmq : m < Fintype.card F)
    (hcount : ∀ u v w : F, ∀ c ∈ T,
      m * (D + ((gOf u v w c).natDegree - 1) * m + J) < d * (J * (D + 1)))
    (hDtot : ∀ u v w : F, ∀ c ∈ T,
      (gOf u v w c).natDegree * (m + (d - 1) * e) + D
          + Fintype.card F * (J - 1) ≤ Dtot) :
    DStepanovOutput χ T m Dtot :=
  dStepanovOutput_of_superelliptic_power_model
    χ T gOf ζOf hJ hmodel hpoly he hmq hcount hDtot

end ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter.dStepanovOutput_adapter
