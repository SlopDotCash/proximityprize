/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R44EtaTower

/-!
# LANES A+B (#466 round 45): the GAUSS-RATIO WELD — the two towers' coefficient sequences
  exactly entangled

The classical identity `J(λ,χ)·g(λχ) = g(λ)·g(χ)`, in the campaign's function calculus:

  **`gauss_ratio`** :  `J_j · 𝔤^{λχ}_j = 𝔤_j · g(χ)`,

where `𝔤^{λχ}_j = ∑_x λ_j(x)·χ(x)·ψ(x)` is the χ-twisted Gauss coefficient and
`g(χ) = ∑_x χ(x)·ψ(x)`.  (Hypothesis: `λ_j·χ` nontrivial, i.e. `∑_x λ_j(x)χ(x) = 0` —
automatic whenever `χ` is outside the `λ`-family.)  Proof: the standard convolution reindex
`(x,y) ↦ (x, s=x+y)`, with the inner sum collapsing by the round-19/30 mechanism.

With rounds 43–44 this completes the unification: the B-side sequence `J` is the exact
multiplicative twist `𝔤·g(χ)/𝔤^{λχ}` of the A-side sequence `𝔤` — all of unit `√q` modulus —
so the ONE remaining family-torus input of the prize concerns one sequence up to explicit
unit twists.  Any cancellation statement proven for either sequence transfers to the other
through this identity and the modulus laws.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 45, LANES A+B.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R45GaussRatio

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R43GaussUnification

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The χ-twisted Gauss coefficient `𝔤^{λχ}_j = ∑_x λ_j(x)·χ(x)·ψ(x)`. -/
noncomputable def twistedGaussCoeff (lam : ZMod m → F → ℂ) (χ : F → ℂ)
    (ψ : AddChar F ℂ) (j : ZMod m) : ℂ :=
  ∑ x : F, lam j x * χ x * ψ x

/-- **THE GAUSS-RATIO WELD (round-45 main theorem)**:
`jacobiCoeff_j · 𝔤^{λχ}_j = 𝔤_j · g(χ)` — the exact entanglement of the A- and B-side
coefficient sequences. -/
theorem gauss_ratio (hfam : SubgroupDualFamily G m lam) (hχ : IsMulCharC χ)
    {ψ : AddChar F ℂ} (_hψ : ψ.IsPrimitive) (j : ZMod m)
    (hnt : ∑ x : F, lam j x * χ x = 0) :
    jacobiCoeff χ lam j * twistedGaussCoeff lam χ ψ j
      = gaussCoeff lam ψ j * (∑ x : F, χ x * ψ x) := by
  classical
  -- RHS = Σ_{x,y} λ_j(x)χ(y)ψ(x)ψ(y) = Σ_{x,y} λ_j(x)χ(y)ψ(x+y)
  have hR : gaussCoeff lam ψ j * (∑ x : F, χ x * ψ x)
      = ∑ x : F, ∑ y : F, lam j x * χ y * ψ (x + y) := by
    rw [gaussCoeff, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [AddChar.map_add_eq_mul]
    ring
  -- reindex y = s − x per x, then swap
  have hR2 : ∑ x : F, ∑ y : F, lam j x * χ y * ψ (x + y)
      = ∑ s : F, (∑ x : F, lam j x * χ (s - x)) * ψ s := by
    have hx : ∀ x : F, ∑ y : F, lam j x * χ y * ψ (x + y)
        = ∑ s : F, lam j x * χ (s - x) * ψ s := by
      intro x
      refine Fintype.sum_bijective (fun y => x + y)
        ⟨fun y₁ y₂ h => by
            exact add_left_cancel h,
          fun s => ⟨s - x, by ring⟩⟩ _ _ (fun y => ?_)
      dsimp only
      rw [show x + y - x = y from by ring]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_mul]
  -- inner sum: U_j(s) = λ_j(s)χ(s)·J_j for s ≠ 0; = 0 at s = 0 (via hnt)
  have hU : ∀ s : F, (∑ x : F, lam j x * χ (s - x))
      = (if s = 0 then 0 else lam j s * χ s * jacobiCoeff χ lam j) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [if_pos rfl]
      have hpt : ∀ x : F, lam j x * χ (0 - x) = χ (-1) * (lam j x * χ x) := by
        intro x
        rw [show (0:F) - x = -1 * x from by ring, hχ.map_mul]
        ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x), ← Finset.mul_sum, hnt, mul_zero]
    · rw [if_neg hs]
      -- reindex x = s·t
      have hre : ∑ x : F, lam j x * χ (s - x)
          = ∑ t : F, lam j (s * t) * χ (s - s * t) := by
        exact (Fintype.sum_bijective (fun t => s * t) (mulLeft_bijective₀ s hs)
          _ _ (fun t => rfl)).symm
      rw [hre]
      have hpt : ∀ t : F, lam j (s * t) * χ (s - s * t)
          = (lam j s * χ s) * (lam j t * χ (1 - t)) := by
        intro t
        rw [hfam.map_mul j s t, show s - s * t = s * (1 - t) from by ring,
          hχ.map_mul s (1 - t)]
        ring
      rw [Finset.sum_congr rfl (fun t _ => hpt t), ← Finset.mul_sum, jacobiCoeff]
  rw [hR, hR2, Finset.sum_congr rfl (fun s _ => by rw [hU s])]
  -- assemble: Σ_s ite·ψ(s) = J_j·Σ_s λ_j(s)χ(s)ψ(s) = J_j·𝔤^{λχ}_j
  have hasm : ∑ s : F, (if s = 0 then (0:ℂ) else lam j s * χ s * jacobiCoeff χ lam j) * ψ s
      = jacobiCoeff χ lam j * twistedGaussCoeff lam χ ψ j := by
    rw [twistedGaussCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : s = 0
    · subst hs
      rw [if_pos rfl]
      rw [show lam j (0:F) * χ 0 * ψ 0 = 0 from by rw [hχ.map_zero]; ring]
      ring
    · rw [if_neg hs]
      ring
  rw [hasm]

end ArkLib.ProximityGap.Frontier.R45GaussRatio

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R45GaussRatio.gauss_ratio
