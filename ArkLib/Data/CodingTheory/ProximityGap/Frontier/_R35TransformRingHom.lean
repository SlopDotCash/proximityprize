/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R34QuadWeilBound

/-!
# LANE B2 (#466 round 35): the transform is a ring homomorphism — the COMPLETE correlation
  calculus

The capstone of the rounds 30–34 calculus: for the multiplicative convolution on `F`
(`(f ⊛ g)(v) = ∑_{z≠0} f(z)·g(z⁻¹·v)`),

  **`lamTransform_mul`** :  `c_f(i) · c_g(i) = c_{f⊛g}(i)`.

Consequences: products of λ-transforms are transforms; every product of shifted Jacobi
coefficients is a single transform of an explicit iterated-`⊛` weight; hence EVERY balanced
correlation of every such product collapses through `weighted_lag_correlation'` (round 33)
to an exact `G`-fibered complete character sum, and is bounded by the named Weil/Deligne
ladder (rounds 17/31/34) at the corresponding variety dimension.  The sextic (r = 3) class
is the transform of `W ⊛ W`-type weights against a threefold conjugate — its named input is
the three-dimensional member of the same classical family.  The correlation calculus of the
tower is COMPLETE; all remaining openness is the named top input and its A-side twin.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 35, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R35TransformRingHom

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- The multiplicative convolution of weights: `(f ⊛ g)(v) = ∑_{z≠0} f(z)·g(z⁻¹·v)`. -/
noncomputable def mulConv (f g : F → ℂ) (v : F) : ℂ :=
  ∑ z ∈ (Finset.univ : Finset F).erase 0, f z * g (z⁻¹ * v)

/-- **THE TRANSFORM IS MULTIPLICATIVE (round-35 main theorem)**:
`c_f(i)·c_g(i) = c_{f⊛g}(i)` — provided `f 0 = 0` (the transform is blind to it anyway). -/
theorem lamTransform_mul (hfam : SubgroupDualFamily G m lam)
    (f g : F → ℂ) (hf0 : f 0 = 0) (i : ZMod m) :
    lamTransform lam f i * lamTransform lam g i
      = lamTransform lam (mulConv f g) i := by
  classical
  -- LHS = Σ_z Σ_w f z g w λ_i(z)λ_i(w) = Σ_z Σ_w f z g w λ_i(z·w)
  rw [lamTransform, lamTransform, Finset.sum_mul_sum]
  have hpt : ∀ z : F, ∀ w : F,
      (f z * lam i z) * (g w * lam i w) = f z * g w * lam i (z * w) := by
    intro z w
    rw [hfam.map_mul i z w]
    ring
  rw [Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => hpt z w))]
  -- drop z = 0 (f 0 = 0), then reindex w = z⁻¹·v per z ≠ 0
  rw [← Finset.sum_erase (s := (Finset.univ : Finset F)) (a := (0:F))
    (f := fun z => ∑ w : F, f z * g w * lam i (z * w))
    (by
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [hf0]
      ring)]
  -- RHS: expand mulConv and swap
  symm
  calc lamTransform lam (mulConv f g) i
      = ∑ v : F, (∑ z ∈ (Finset.univ : Finset F).erase 0, f z * g (z⁻¹ * v)) * lam i v := by
        rw [lamTransform]
        exact Finset.sum_congr rfl (fun v _ => by rw [mulConv])
    _ = ∑ v : F, ∑ z ∈ (Finset.univ : Finset F).erase 0,
          f z * g (z⁻¹ * v) * lam i v := by
        exact Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_mul])
    _ = ∑ z ∈ (Finset.univ : Finset F).erase 0, ∑ v : F,
          f z * g (z⁻¹ * v) * lam i v := Finset.sum_comm
    _ = ∑ z ∈ (Finset.univ : Finset F).erase 0, ∑ w : F,
          f z * g w * lam i (z * w) := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
        refine (Fintype.sum_bijective (fun w => z * w) (mulLeft_bijective₀ z hz0)
          (fun w => f z * g w * lam i (z * w))
          (fun v => f z * g (z⁻¹ * v) * lam i v) (fun w => ?_)).symm
        dsimp only
        rw [← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

end ArkLib.ProximityGap.Frontier.R35TransformRingHom

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R35TransformRingHom.lamTransform_mul
