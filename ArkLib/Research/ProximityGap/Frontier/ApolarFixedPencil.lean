/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarFixedSupport
import ArkLib.Research.ProximityGap.Frontier.ApolarMomentCoordinates

/-! # Closing the constant-coordinate branch of the generic pencil

When removing fixed sites leaves a coordinate-constant quotient, its nonzero
parameter factor cancels from the moment equations. A constant-field locator
can then be used directly against the observed Reed–Solomon bad scalar family.
-/

set_option autoImplicit false
open Polynomial Finset Code
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarMomentCoordinates
open ProximityGap.ApolarMcaSyndrome ProximityGap.ApolarHankelMinors
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.ApolarFixedSupport
open scoped BigOperators NNReal

namespace ArkLib.ProximityGap.Frontier.ApolarFixedPencil

/-- Cancel a nonzero constant-in-coordinate polynomial factor from all apolar
equations over the integral parameter polynomial ring. -/
theorem cancel_coordinate_constant {K : Type*} [Field K]
    (L : K[X][X] →ₗ[K[X]] K[X]) (g : K[X]) (q : K[X][X]) (h : q.natDegree = 0)
    (hn : q ≠ 0) (b : ℕ) (ha : ApolarThrough L (g.map C*q) b) :
    ApolarThrough L (g.map C) b := by
  have hq := eq_C_of_natDegree_eq_zero h
  have hc : q.coeff 0 ≠ 0 := fun hh => hn (by rw [hq,hh,map_zero])
  intro B hB
  have hz := ha B hB
  rw [hq,mul_comm (g.map C),mul_assoc,←smul_eq_C_mul,map_smul,smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hc

/-- A constant-field apolar locator for the polynomial moment pencil implies
the actual fixed-locator recurrence at every scalar, over a coefficient extension. -/
theorem equations_at_scalars {F L : Type*} [Field F] [Field L] (φ : F →+* L)
    (m : ℕ → F[X]) (g : L[X]) (b : ℕ)
    (ha : ApolarThrough (functional (fun j => (m j).map φ)) (g.map C) b) :
    ∀ t : F, ∀ j ≤ b, ∑ i ∈ range (g.natDegree+1), g.coeff i*φ ((m (i+j)).eval t) = 0 := by
  classical
  let v (i : Fin (g.natDegree+1)) := (g.map (C : L →+* L[X])).coeff i.val
  have hv : form v = g.map C := form_coeff _ natDegree_map_le
  have he := (equations_iff_apolar (fun j => (m j).map φ) v).mpr (by rwa [hv])
  intro t j hj
  have hh := congrArg (Polynomial.eval (φ t)) (he j hj)
  rw [Polynomial.eval_finsetSum,eval_zero] at hh
  rw [← Fin.sum_univ_eq_sum_range]
  convert hh using 1
  apply sum_congr rfl
  intro i _
  simp only [v,coeff_map,eval_mul,eval_C,Polynomial.eval_map_apply]
  rw [mul_comm,Nat.add_comm]

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- The fixed part of the generic polynomial pencil itself suffices when its
remaining factor has coordinate degree zero. -/
theorem count_le_of_constant_quotient {L : Type*} [Field L] [DecidableEq L] (φ : F →+* L)
    (fam : BadScalarRichPointFamily dom k δ u) (G : Finset F) (hG : G ⊆ fam.G)
    (hpair : 1 < G.card) (g : L[X]) (hg : g ≠ 0) (q : L[X][X]) (hq : q ≠ 0)
    (hdeg : q.natDegree = 0) (b e : ℕ) (hk : 1 ≤ k)
    (hroom : k + g.natDegree + b < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) (hb : e ≤ b+1)
    (hapo : let H := (univ : Finset ι).map dom
      let m := moment H (coordinateRow dom (u 0)) (coordinateRow dom (u 1))
      ApolarThrough (functional (fun j => (m j).map φ)) (g.map C*q) b) :
    G.card ≤ g.natDegree := by
  apply count_le_of_fixed_moment_equations φ fam G hG hpair g hg b e hk hroom he hb
  dsimp only
  intro t _ j hj
  apply equations_at_scalars φ _ g b _ t j hj
  exact cancel_coordinate_constant _ _ q hdeg hq b hapo

end ArkLib.ProximityGap.Frontier.ApolarFixedPencil

#print axioms ArkLib.ProximityGap.Frontier.ApolarFixedPencil.count_le_of_constant_quotient
