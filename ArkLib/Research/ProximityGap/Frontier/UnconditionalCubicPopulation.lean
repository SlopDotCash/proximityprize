/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicExact

/-! # An absolute label bound for every cubic of terminal weight

The cubic carrying one label above the target cap already has enough
simple sections to pay for the unrestricted interpolation argument.
-/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.UnconditionalCubicPopulation
open SecondPrimeActualPopulations SecondPrimeCoordinateWeight IntrinsicCubicPopulation
open SecondPrimeCubicExact
variable {F k I : Type} [Field F] [DecidableEq F] [Field k] [Infinite k] [Fintype I]
    {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- At terminal agreement every supported, weight-bounded irreducible cubic
has at most 1,200,005,270 original rich scalar labels. -/
theorem cap (fam : Family dom δ u) (φ : F →+* k) (p : ℕ) [CharP k p]
    (hp : 1744830589 < p) (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (Q f : k[X][X][X]) (hQ : Q ≠ 0) (hi : Irreducible f) (hd : f ∣ Q) (hy : f.natDegree=3)
    (hs : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34)
    (hw : weight 67108863 f ≤ 290805098) :
    (population fam φ f).card ≤ 1200005270 := by
  apply Nat.le_of_lt_succ
  apply actual_cubic_population_at φ (p:=p) (by omega) dom δ u hn ht fam Q f hQ hi hd hy
    hs hw 1200005271 (by decide)
  intro hproper hlarge
  have ht₀ := SecondPrimeSectionResultant.factor_triangle hQ hd hs
  have h := received_budget_of_defect fam φ p hp f hi hy hw ht₀ hproper 225 (by
    intro g H
    have hl : 1200005110 ≤ (population fam φ f).card-161 := by omega
    have h' := (Nat.mul_le_mul_right _ hl).trans H
    omega)
  rw [hn] at h
  have h' : (3:ℤ)*totalOrder φ dom u f+35*67108863 ≤
      2*1073741824+16*(weight 67108863 f:ℤ)+2*225 := by exact_mod_cast h
  change (3:ℤ)*totalOrder φ dom u f ≤ 2*1073741824+16*(weight 67108863 f:ℤ)-35*67108863+532
  omega

#print axioms cap
end ArkLib.ProximityGap.Frontier.UnconditionalCubicPopulation
