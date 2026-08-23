/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusDominationFullDomainNecessary

/-!
# Product-cap necessity for the census sub-obligations (#444)

`CensusDominationSufficiency` reduces the census Prop to two per-band sub-obligations:
a uniform distinct-`γ` cap `P` and a uniform per-scalar multiplicity cap `M`, with budget `P*M`.
`CensusDominationFullDomainNecessary` proves any actual census budget must dominate the full-domain
binomial floor under global alignment.  This file composes them:

* `census_product_cap_ge_choose_of_global_alignment`: any proposed uniform caps `P` and `M` that
  discharge `CensusDomination` must satisfy
  `choose (n-(k+1)) (a-(k+1)) ≤ P*M` at every globally aligned non-degenerate band.
* `census_product_cap_pos_of_global_alignment`: in the guarded band the product cap is nonzero.

This is a necessary constraint on the C71/census factorization, not a CORE closure.  It does not
prove the upper cap, does not assert capacity, and does not touch the cliff-at-`n/2` guard.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Product-cap necessity.**  If uniform caps `P` and `M` would discharge the census Prop from
band `a₀`, then a globally aligned non-degenerate stack at any band `a ≥ a₀` forces the exact
full-domain binomial floor below the product `P*M`. -/
theorem census_product_cap_ge_choose_of_global_alignment (dom : Fin n ↪ ZMod p) {k a₀ a P M : ℕ}
    (hP : ∀ u₀ u₁ : Fin n → ZMod p, ∀ b : ℕ, a₀ ≤ b →
      (pinnedScalars dom k b u₀ u₁).card ≤ P)
    (hM : ∀ u₀ u₁ : Fin n → ZMod p, ∀ b : ℕ, a₀ ≤ b →
      ∀ γ ∈ pinnedScalars dom k b u₀ u₁,
        (alignedSetsForScalar dom k b u₀ u₁ γ).card ≤ M)
    (ha₀ : a₀ ≤ a) (han : a ≤ n) (hka : k + 1 ≤ a)
    (u₀ u₁ : Fin n → ZMod p) {γ : ZMod p}
    (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    (n - (k + 1)).choose (a - (k + 1)) ≤ P * M := by
  classical
  have hCD : CensusDomination dom k a₀ (P * M) :=
    censusDomination_of_caps_exact dom k a₀ hP hM
  exact censusDomination_ge_choose_univ_of_global_alignment (dom := dom)
    (k := k) (a₀ := a₀) (a := a) (K := P * M) hCD ha₀ han hka u₀ u₁
    (γ := γ) halign htinj hnd

open Classical in
/-- **Non-vacuity for product caps.**  Under the same globally aligned non-degenerate witness in
`k+1 ≤ a ≤ n`, the product of any successful distinct-scalar and multiplicity caps is positive. -/
theorem census_product_cap_pos_of_global_alignment (dom : Fin n ↪ ZMod p) {k a₀ a P M : ℕ}
    (hP : ∀ u₀ u₁ : Fin n → ZMod p, ∀ b : ℕ, a₀ ≤ b →
      (pinnedScalars dom k b u₀ u₁).card ≤ P)
    (hM : ∀ u₀ u₁ : Fin n → ZMod p, ∀ b : ℕ, a₀ ≤ b →
      ∀ γ ∈ pinnedScalars dom k b u₀ u₁,
        (alignedSetsForScalar dom k b u₀ u₁ γ).card ≤ M)
    (ha₀ : a₀ ≤ a) (han : a ≤ n) (hka : k + 1 ≤ a)
    (u₀ u₁ : Fin n → ZMod p) {γ : ZMod p}
    (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    0 < P * M := by
  classical
  have hfloor := census_product_cap_ge_choose_of_global_alignment (dom := dom)
    (k := k) (a₀ := a₀) (a := a) (P := P) (M := M) hP hM ha₀ han hka u₀ u₁
    (γ := γ) halign htinj hnd
  have hchoose : 0 < (n - (k + 1)).choose (a - (k + 1)) := by
    exact Nat.choose_pos (by omega)
  exact lt_of_lt_of_le hchoose hfloor

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.census_product_cap_ge_choose_of_global_alignment
#print axioms ProximityGap.Ownership.census_product_cap_pos_of_global_alignment
