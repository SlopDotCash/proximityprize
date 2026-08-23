/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AffineBlockKernels

/-!
# The proportionality trap (issue #334, A3 design-space impossibility, verified)

The structural obstruction that closes the "per-block, single-line" design space for the A3
MCA-level sharpness instance, as a machine-checked theorem over abstract row families.

**Setting.** A block's rows all carve the same projective line `λ₁ + c·λ₂ = 0`: formalized as
each row being an *affine `(1,c)`-pattern* `j ↦ γᵣ • (j, c·j) + vᵣ` (slope vector proportional
to `(1, c)`, arbitrary constant offset `vᵣ`). This is exactly the row class whose λ-constancy
kernel is the `c`-line (`affineBlockCombo_constant_iff`); the kernel leg of any single-line
instance forces home-block rows into it.

**The trap** (`combination_dichotomy`): *any* coefficient combination of such rows is again an
affine `(1,c)`-pattern with slope `γ = ∑ aᵣ·γᵣ`, and exactly one of:
* `γ = 0` — the combination is **constant** on the block (hence explainable by any code
  containing constants: no witness-forcing); or
* `γ ≠ 0` — the combination's first component is **injective** in the position (hence
  non-constant on every 2-point subset, and — for the repetition code — non-explainable on
  *every* 2-point witness set: the seed has no witnesses at all and is not bad).

Either way the badness/forcing pair required of a sharpness instance fails — no per-block
single-line stack over a constants-containing code can defeat `UniformObstruction`. The
escape routes (cross-block kernel intersections, per-block multi-line geometry) are exactly
the designs this theorem does not cover; the analysis is recorded on issue #334.
-/

namespace ProximityGap

variable {F : Type} [Field F]

/-- An affine `(1,c)`-pattern: slope vector proportional to `(1, c)`, constant offset. -/
def affinePattern (c γ : F) (v : Fin 2 → F) : F → Fin 2 → F :=
  fun j k => γ * (if k = 0 then j else c * j) + v k

/-- Combinations of affine `(1,c)`-patterns are affine `(1,c)`-patterns, with the combined
slope `∑ aᵣ·γᵣ` and combined offset. -/
theorem combination_affinePattern {ι : Type} [Fintype ι]
    (c : F) (γ : ι → F) (v : ι → Fin 2 → F) (a : ι → F) :
    (fun j k => ∑ r, a r * affinePattern c (γ r) (v r) j k)
      = affinePattern c (∑ r, a r * γ r) (fun k => ∑ r, a r * v r k) := by
  funext j k
  unfold affinePattern
  rw [Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The proportionality trap.** Any combination of same-line affine rows is either constant
in the position (slope `0`) or has an injective first component (slope `≠ 0`) — the dichotomy
that kills witness-forcing and badness respectively for any per-block single-line design. -/
theorem combination_dichotomy {ι : Type} [Fintype ι]
    (c : F) (γ : ι → F) (v : ι → Fin 2 → F) (a : ι → F) :
    -- slope zero: the combination is constant in the position
    ((∑ r, a r * γ r) = 0 →
      ∀ j j' : F, ∀ k, (∑ r, a r * affinePattern c (γ r) (v r) j k)
        = (∑ r, a r * affinePattern c (γ r) (v r) j' k)) ∧
    -- slope nonzero: the first component is injective in the position
    ((∑ r, a r * γ r) ≠ 0 →
      Function.Injective (fun j => ∑ r, a r * affinePattern c (γ r) (v r) j 0)) := by
  have hcomb := combination_affinePattern c γ v a
  constructor
  · intro hzero j j' k
    have hj := congrFun (congrFun hcomb j) k
    have hj' := congrFun (congrFun hcomb j') k
    rw [hj, hj']
    unfold affinePattern
    rw [hzero]
    ring
  · intro hne j j' hjj'
    have hj := congrFun (congrFun hcomb j) 0
    have hj' := congrFun (congrFun hcomb j') 0
    have hjj2 : (∑ r, a r * affinePattern c (γ r) (v r) j 0)
        = (∑ r, a r * affinePattern c (γ r) (v r) j' 0) := hjj'
    rw [hj, hj'] at hjj2
    unfold affinePattern at hjj2
    simp only [if_pos rfl, if_true] at hjj2
    have : (∑ r, a r * γ r) * j = (∑ r, a r * γ r) * j' := by linear_combination hjj2
    exact mul_left_cancel₀ hne this

/-- **The non-explainability half, concretely**: at nonzero slope, the combination disagrees
with every constant function on every two distinct positions — for the repetition code (and
any code whose sections are constant on the block) there is no explaining codeword on any
2-point witness set. -/
theorem no_constant_explanation {ι : Type} [Fintype ι]
    (c : F) (γ : ι → F) (v : ι → Fin 2 → F) (a : ι → F)
    (hne : (∑ r, a r * γ r) ≠ 0) (w : F) {j j' : F} (hjj' : j ≠ j') :
    ¬ ((∑ r, a r * affinePattern c (γ r) (v r) j 0) = w ∧
       (∑ r, a r * affinePattern c (γ r) (v r) j' 0) = w) := by
  rintro ⟨h0, h1⟩
  exact hjj' ((combination_dichotomy c γ v a).2 hne (h0.trans h1.symm))

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.combination_affinePattern
#print axioms ProximityGap.combination_dichotomy
#print axioms ProximityGap.no_constant_explanation
