/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandTwoCollapse

/-!
# Round 3 (#357): the cored collapse — sunflower puncture families die at band 3

First Lean brick of the band-3 collapse programme (the `HalfDistanceStaircaseConjecture`
at `b = 3`). The band-3 case analysis splits by the overlap pattern of the puncture pairs;
this file kills the **sunflower-core** branch: three bad scalars whose witnesses all miss a
*common* point `x` (plus one private puncture each). The proof is the band-2 `c*`-mechanism
re-run with every support enlarged by the core:

* `c* = (γ₁−γ₃)•(w₁−w₂) − (γ₁−γ₂)•(w₁−w₃) ∈ C` is supported on `{x, p₁, p₂, p₃}` —
  **four** points, so distance `≥ 5` (`NoWeightLE4`) already kills it;
* evaluating `c* = 0` at the private punctures `p₂, p₃` extends `w₂, w₃` across them: both
  agree with their lines **off `{x}` alone**;
* two off-core-agreeing scalars are jointly explained on any witness avoiding the core
  (the landed `pairJoint_of_shared_witness`, applied off `x`), contradicting badness.

Two structural corollaries for the staircase programme:

1. the sunflower branch needs only `d ≥ 5` — strictly less than the conjectured collapse
   boundary `d ≥ 2b = 6`. So at the boundary `d = 5 = 2b−1`, where the staircase explodes
   to `~n/|F|`, the exploding families are necessarily **core-free** (the `t`-spike type:
   `(b−1)`-subsets of a common `b`-set) — matching the probe maximizers exactly;
2. with the directed-search refutation of disjoint families at `d = 6` (10 syndrome
   equations on 8 puncture unknowns, no admissible kernel — issue record 2026-06-11), the
   remaining open branch of the `b = 3` collapse is the **mixed-overlap rank lemma**.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; round 3 — the staircase programme), `MCABandTwoCollapse`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandThreeCoredCollapse

open ProximityGap.MCABandTwoCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Distance-`≥ 5` hypothesis, support form: no nonzero codeword on `≤ 4` points. -/
def NoWeightLE4 (C : Submodule F (ι → A)) : Prop :=
  ∀ w ∈ C, (∃ T : Finset ι, T.card ≤ 4 ∧ ∀ i ∉ T, w i = 0) → w = 0

/-- **The cored collapse.** Three distinct scalars with codeword agreements off a common
core `{x}` plus pairwise-distinct private punctures `p₁, p₂, p₃` cannot all be bad: the
cored `c*` dies on four points, the agreements of `w₂, w₃` extend across their own
punctures, and the resulting off-core pair explains `(u₀, u₁)` on any witness avoiding
`x` — in particular on γ₂'s. -/
theorem cored_collapse (C : Submodule F (ι → A)) (hC : NoWeightLE4 C)
    {x p₁ p₂ p₃ : ι} (hp12 : p₁ ≠ p₂) (hp13 : p₁ ≠ p₃) (hp23 : p₂ ≠ p₃)
    (hx1 : p₁ ≠ x) (hx2 : p₂ ≠ x) (hx3 : p₃ ≠ x)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃) (h23 : γ₂ ≠ γ₃)
    {u₀ u₁ : ι → A} {w₁ w₂ w₃ : ι → A}
    (hw₁ : w₁ ∈ C) (hw₂ : w₂ ∈ C) (hw₃ : w₃ ∈ C)
    (hag₁ : ∀ j : ι, j ≠ x → j ≠ p₁ → w₁ j = u₀ j + γ₁ • u₁ j)
    (hag₂ : ∀ j : ι, j ≠ x → j ≠ p₂ → w₂ j = u₀ j + γ₂ • u₁ j)
    (hag₃ : ∀ j : ι, j ≠ x → j ≠ p₃ → w₃ j = u₀ j + γ₃ • u₁ j)
    {S₂ : Finset ι} (hS₂x : ∀ j ∈ S₂, j ≠ x)
    (hno₂ : ¬ pairJointAgreesOn (C : Set (ι → A)) S₂ u₀ u₁) :
    False := by
  -- the cored combination
  set cstar : ι → A := (γ₁ - γ₃) • (w₁ - w₂) - (γ₁ - γ₂) • (w₁ - w₃) with hcstar
  have hcmem : cstar ∈ C :=
    C.sub_mem (C.smul_mem _ (C.sub_mem hw₁ hw₂)) (C.smul_mem _ (C.sub_mem hw₁ hw₃))
  -- supported on the core plus the three private punctures
  have hsupp : ∀ j ∉ ({x, p₁, p₂, p₃} : Finset ι), cstar j = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    push Not at hj
    obtain ⟨hjx, hj1, hj2, hj3⟩ := hj
    show (γ₁ - γ₃) • (w₁ j - w₂ j) - (γ₁ - γ₂) • (w₁ j - w₃ j) = 0
    rw [hag₁ j hjx hj1, hag₂ j hjx hj2, hag₃ j hjx hj3]
    module
  -- four points: distance ≥ 5 kills it
  have hcard4 : ({x, p₁, p₂, p₃} : Finset ι).card ≤ 4 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h3 : ({p₁, p₂, p₃} : Finset ι).card ≤ 3 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h2 : ({p₂, p₃} : Finset ι).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
      omega
    omega
  have hczero : cstar = 0 := hC cstar hcmem ⟨{x, p₁, p₂, p₃}, hcard4, hsupp⟩
  -- extension of w₂ across its own puncture p₂ (w₁, w₃ still agree there)
  have hext₂ : w₂ p₂ = u₀ p₂ + γ₂ • u₁ p₂ := by
    have hz : (γ₁ - γ₃) • (w₁ p₂ - w₂ p₂) - (γ₁ - γ₂) • (w₁ p₂ - w₃ p₂) = 0 :=
      congrFun hczero p₂
    rw [hag₁ p₂ hx2 (Ne.symm hp12), hag₃ p₂ hx2 hp23] at hz
    have hac0 : γ₁ - γ₃ ≠ 0 := sub_ne_zero.mpr h13
    have hXY : (γ₁ - γ₃) • ((u₀ p₂ + γ₁ • u₁ p₂) - w₂ p₂)
        = (γ₁ - γ₃) • ((γ₁ - γ₂) • u₁ p₂) := by
      have hY : (γ₁ - γ₂) • ((u₀ p₂ + γ₁ • u₁ p₂) - (u₀ p₂ + γ₃ • u₁ p₂))
          = (γ₁ - γ₃) • ((γ₁ - γ₂) • u₁ p₂) := by module
      have hXeq := sub_eq_zero.mp hz
      rw [hY] at hXeq
      exact hXeq
    have hcanc := congrArg (fun v => (γ₁ - γ₃)⁻¹ • v) hXY
    simp only [inv_smul_smul₀ hac0] at hcanc
    have hwb_eq : w₂ p₂ = (u₀ p₂ + γ₁ • u₁ p₂) - (γ₁ - γ₂) • u₁ p₂ := by
      rw [← hcanc]
      abel
    rw [hwb_eq]
    module
  -- hence w₂ agrees with its line off the core alone
  have hoffx₂ : ∀ j : ι, j ≠ x → w₂ j = u₀ j + γ₂ • u₁ j := by
    intro j hjx
    by_cases hj2 : j = p₂
    · rw [hj2]; exact hext₂
    · exact hag₂ j hjx hj2
  -- symmetric extension of w₃ across p₃ (swap the roles of 2 and 3)
  have hext₃ : w₃ p₃ = u₀ p₃ + γ₃ • u₁ p₃ := by
    have hz : (γ₁ - γ₂) • (w₁ p₃ - w₃ p₃) - (γ₁ - γ₃) • (w₁ p₃ - w₂ p₃) = 0 := by
      have h := congrFun hczero p₃
      have hflip : (γ₁ - γ₂) • (w₁ p₃ - w₃ p₃) - (γ₁ - γ₃) • (w₁ p₃ - w₂ p₃)
          = -((γ₁ - γ₃) • (w₁ p₃ - w₂ p₃) - (γ₁ - γ₂) • (w₁ p₃ - w₃ p₃)) := by abel
      rw [hflip]
      show -(cstar p₃) = 0
      rw [congrFun hczero p₃]
      exact neg_zero
    rw [hag₁ p₃ hx3 (Ne.symm hp13), hag₂ p₃ hx3 (Ne.symm hp23)] at hz
    have hac0 : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr h12
    have hXY : (γ₁ - γ₂) • ((u₀ p₃ + γ₁ • u₁ p₃) - w₃ p₃)
        = (γ₁ - γ₂) • ((γ₁ - γ₃) • u₁ p₃) := by
      have hY : (γ₁ - γ₃) • ((u₀ p₃ + γ₁ • u₁ p₃) - (u₀ p₃ + γ₂ • u₁ p₃))
          = (γ₁ - γ₂) • ((γ₁ - γ₃) • u₁ p₃) := by module
      have hXeq := sub_eq_zero.mp hz
      rw [hY] at hXeq
      exact hXeq
    have hcanc := congrArg (fun v => (γ₁ - γ₂)⁻¹ • v) hXY
    simp only [inv_smul_smul₀ hac0] at hcanc
    have hwb_eq : w₃ p₃ = (u₀ p₃ + γ₁ • u₁ p₃) - (γ₁ - γ₃) • u₁ p₃ := by
      rw [← hcanc]
      abel
    rw [hwb_eq]
    module
  have hoffx₃ : ∀ j : ι, j ≠ x → w₃ j = u₀ j + γ₃ • u₁ j := by
    intro j hjx
    by_cases hj3 : j = p₃
    · rw [hj3]; exact hext₃
    · exact hag₃ j hjx hj3
  -- two off-core scalars explain the pair on γ₂'s witness (which avoids the core)
  exact hno₂ (pairJoint_of_shared_witness C h23 hw₂ hw₃
    (fun j hj => hoffx₂ j (hS₂x j hj))
    (fun j hj => hoffx₃ j (hS₂x j hj)))

/-! ## Source audit -/

#print axioms cored_collapse

end ProximityGap.MCABandThreeCoredCollapse
