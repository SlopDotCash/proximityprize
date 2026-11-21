/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
import ArkLib.Research.ProximityGap.Frontier.HorizontalJetObstruction

/-! # Hidden-derivative and ordinary interpolation on the same domain

At length 128, dimension 32, and agreement 62, a primitive first-order symbolic
certificate exists for every received pair. Some pairs have trivial ordinary jet
kernels at all cutoffs, whereas others have both kinds of interpolants.
-/
set_option autoImplicit false
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.HiddenDerivativeSurfaceSeparation
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
open ReedSolomon.HiddenDerivative
variable {F : Type} [Field F]

abbrev certificate (dom : Fin 128 ↪ F) (u v : Fin 128 → F) :=
  FirstOrderSymbolicCertificate.{0,0} (F:=F) 31 62 8 3 16 32 11264 dom u v
    (firstOrderColumns (D:=31) (A:=62) (m:=8) (M:=3) (μ:=16))

/-- Strictly beyond Johnson, the derivative columns outnumber the certified
constraint rank by twenty. This gives a symbolic certificate for every pair. -/
theorem first_order (dom : Fin 128 ↪ F) (u v : Fin 128 → F) : Nonempty (certificate dom u v) := by
  have hc := card_firstOrderExponents (A:=62) (m:=8) (M:=3) (μ:=16) (by decide : 0<31)
  have hn : firstOrderDimensionCount 31 62 8 3 16=14100 := by decide
  have hr : firstOrderRankCount 8 3=110 := by decide
  apply exists_firstOrder_symbolicCertificate_of_rank_and_height (by decide)
  · rw [hc,hn,hr] <;> decide
  · rw [hc,hn,hr] <;> decide

/-- A positive hidden-derivative certificate on the same received pair that
annihilates every ordinary jet kernel. -/
theorem separated (dom : Fin 128 ↪ F) :
    ∃ u : Fin 128 → F, Nonempty (certificate dom u (fun _ => 0)) ∧
      ∀ r s v : ℕ, ∀ c : Monomials s v 31 (r*62) → F,
        (jetMatrix dom u (fun _ => 0) s v 31 62 r).mulVec c=0 → c=0 := by
  obtain ⟨u,hu⟩ := HorizontalJetObstruction.exists_trivial_kernels dom 31 62 2
    (by decide) (by decide) (by simp) (by decide)
  exact ⟨u,first_order ..,hu⟩

/-- On the zero received pair, the ordinary polynomial `Y` and the hidden-derivative
certificate both exist at these identical beyond-Johnson parameters. -/
theorem coexist (dom : Fin 128 ↪ F) : Nonempty (certificate dom 0 0) ∧
    ∃ c : Monomials 1 1 31 (1*62) → F, c ≠ 0 ∧ (jetMatrix dom 0 0 1 1 31 62 1).mulVec c=0 := by
  classical
  let m : Monomials 1 1 31 (1*62) := ⟨⟨1,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩⟩
  refine ⟨first_order ..,Pi.single m 1,?_,?_⟩
  · intro h
    have := congrFun h m
    simpa using this
  · funext z
    rw [Matrix.mulVec,dotProduct_single]
    have hj : z.2.1.val=0 := by have := z.2.1.isLt; omega
    simp [jetMatrix,jetTerm,m,hj,Nat.sub_eq_zero_of_le]

#print axioms first_order
#print axioms separated
#print axioms coexist
end ArkLib.ProximityGap.Frontier.HiddenDerivativeSurfaceSeparation
