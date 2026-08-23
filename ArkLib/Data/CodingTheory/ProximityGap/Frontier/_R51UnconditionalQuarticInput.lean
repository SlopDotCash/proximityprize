/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17Deg2WeilRung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23Milestone

/-!
# LANE B2 (#466 round 51): the WELD — the r17 quartic-pairs input holds UNCONDITIONALLY
  at constant 26 via the elementary Stepanov milestone

Round 17 named the classical input `WeilQuarticPairs` (constant 3, quantified over all of
`F × F`) and consumed it only on pairs from `G`.  The Stepanov lane subsequently landed
`quarticWeilInputC_unconditional`: the SAME class of complete quartic character sums is
bounded by `26·√q` at every odd finite field — machine-checked, elementary, zero named
hypotheses (`_R23Milestone.lean`).

This brick welds the two lanes:

1. `realQuadChar F` — the concrete real-valued quadratic character, with
   `isRealQuadChar_realQuadChar`: it satisfies the r17 axioms (`ringChar F ≠ 2`).
2. `WeilQuarticPairsOn G χ C` — the `G`-restricted, generic-constant form of the r17 input
   (exactly what the r17 proofs consume; `C = 3`, `G = univ` recovers the original).
3. **`weilQuarticPairsOn_unconditional`** — `WeilQuarticPairsOn G (realQuadChar F) 26`
   holds at EVERY odd finite field.  No named hypotheses.  The r17 named input is
   DISCHARGED (at constant 26 in place of 3); the r=2 rung of the unified tower needs only
   the generic-constant replay of the r17 moment arithmetic (round 51b).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 51, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R51UnconditionalQuarticInput

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R20QuadFaceBridge
open ArkLib.ProximityGap.Frontier.R22StepanovAssembly
open ArkLib.ProximityGap.Frontier.R23Milestone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The concrete real-valued quadratic character. -/
noncomputable def realQuadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    F → ℝ :=
  fun a => ((quadraticChar F a : ℤ) : ℝ)

/-- `realQuadChar` satisfies the r17 real-quadratic-character axioms. -/
theorem isRealQuadChar_realQuadChar (hF : ringChar F ≠ 2) :
    IsRealQuadChar (realQuadChar F) := by
  constructor
  · simp [realQuadChar]
  · intro a b
    simp [realQuadChar, map_mul]
  · intro a ha
    unfold realQuadChar
    exact_mod_cast quadraticChar_sq_one (F := F) ha
  · have h := quadraticChar_sum_zero (F := F) hF
    unfold realQuadChar
    exact_mod_cast h

/-- **The `G`-restricted generic-constant quartic-pairs input** — the exact form the r17
moment chain consumes (`sum_Rker_sq_bound` and downstream only ever invoke the input on
pairs from `G ×ˢ G`). -/
def WeilQuarticPairsOn (G : Finset F) (χ : F → ℝ) (C : ℝ) : Prop :=
  ∀ p ∈ G ×ˢ G, ∀ p' ∈ G ×ˢ G, p.1 ≠ p.2 → p'.1 ≠ p'.2 → p' ≠ p → p' ≠ Prod.swap p →
    ∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2))
      ≤ C * Real.sqrt (Fintype.card F)

/-- The real quartic product collapses to the integer quartic sum of the quadruple. -/
theorem sum_realQuadChar_eq_intQuartic (p p' : F × F) :
    ∑ s : F, realQuadChar F (s - p.1) * realQuadChar F (s - p.2)
        * (realQuadChar F (s - p'.1) * realQuadChar F (s - p'.2))
      = ((intQuartic (F := F) (p, p') : ℤ) : ℝ) := by
  unfold intQuartic
  push_cast
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [realQuadChar, map_mul]
  push_cast
  ring

/-- **THE WELD (round-51 main theorem).**  The r17 quartic-pairs input holds
UNCONDITIONALLY at constant `26` for the concrete quadratic character, at every odd finite
field — discharged by the elementary Stepanov milestone.  Zero named hypotheses. -/
theorem weilQuarticPairsOn_unconditional (hF : ringChar F ≠ 2) (G : Finset F) :
    WeilQuarticPairsOn G (realQuadChar F) 26 := by
  intro p hp p' hp' hpd hp'd hne hnsw
  have hz : ((p, p') : (F × F) × (F × F)) ∈ (G ×ˢ G) ×ˢ (G ×ˢ G) :=
    Finset.mem_product.mpr ⟨hp, hp'⟩
  have hdeg : ¬ IsDegenerate ((p, p') : (F × F) × (F × F)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩)
    · exact hne (Prod.ext h1.symm h2.symm)
    · exact hnsw (Prod.ext h2.symm h1.symm)
    · exact hpd h1
  have hbound := quarticWeilInputC_unconditional hF G ((p, p')) hz hdeg
  have hcast : ‖quadTerm (quadCharC F) ((p, p') : (F × F) × (F × F))‖
      = |((intQuartic (F := F) (p, p') : ℤ) : ℝ)| := by
    rw [quadTerm_quadCharC_eq]
    exact_mod_cast Complex.norm_intCast _
  rw [sum_realQuadChar_eq_intQuartic]
  calc ((intQuartic (F := F) (p, p') : ℤ) : ℝ)
      ≤ |((intQuartic (F := F) (p, p') : ℤ) : ℝ)| := le_abs_self _
    _ = ‖quadTerm (quadCharC F) ((p, p') : (F × F) × (F × F))‖ := hcast.symm
    _ ≤ 26 * Real.sqrt (Fintype.card F) := hbound

end ArkLib.ProximityGap.Frontier.R51UnconditionalQuarticInput

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R51UnconditionalQuarticInput.isRealQuadChar_realQuadChar
#print axioms
  ArkLib.ProximityGap.Frontier.R51UnconditionalQuarticInput.weilQuarticPairsOn_unconditional
