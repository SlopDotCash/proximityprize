/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusCapFullDomainForcedBelow
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusDominationSufficiency

/-!
# Full-domain necessity for the deployed `CensusDomination` Prop (#444)

`CensusCapFullDomainForcedBelow` proves the explicit full-domain binomial floor from a per-stack
cap hypothesis `(alignableSets ...).card ≤ K`.  The deployed `$1M` census normal form, however,
uses the named Prop `CensusDomination dom k a₀ K`.  This file welds those two faces in the
necessity direction:

* `censusDomination_ge_choose_univ_of_global_alignment`: if `CensusDomination dom k a₀ K` holds,
  then at every band `a ≥ a₀`, a globally aligned non-degenerate stack forces
  `choose (n-(k+1)) (a-(k+1)) ≤ K`.
* `censusDomination_cap_pos_of_global_alignment`: in the guarded band `k+1 ≤ a ≤ n`, the same
  hypotheses force `0 < K`.

This is not a CORE closure.  It is a C71/census reduction brick: it proves a necessary lower bound
on any actual `CensusDomination` budget.  The hard upper-bound/cancellation content remains open.
No capacity / beyond-Johnson / growth-law claim is made; the cliff-at-`n/2` guard is untouched.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Necessity floor for the actual census Prop.**  If the deployed `CensusDomination`
budget `K` holds from band `a₀` onward, then any globally aligned non-degenerate stack at a
band `a ≥ a₀` forces the explicit full-domain binomial lower bound on `K`. -/
theorem censusDomination_ge_choose_univ_of_global_alignment (dom : Fin n ↪ ZMod p) {k a₀ a K : ℕ}
    (hCD : CensusDomination dom k a₀ K) (ha₀ : a₀ ≤ a) (han : a ≤ n) (hka : k + 1 ≤ a)
    (u₀ u₁ : Fin n → ZMod p) {γ : ZMod p}
    (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    (n - (k + 1)).choose (a - (k + 1)) ≤ K := by
  classical
  have hcap : (alignableSets dom k a u₀ u₁).card ≤ K :=
    (censusDomination_iff_alignableSets dom k a₀ K).mp hCD u₀ u₁ a ha₀
  exact censusDomination_cap_ge_choose_univ (dom := dom) (u₀ := u₀) (u₁ := u₁)
    (γ := γ) (K := K) han hka halign htinj hnd hcap

open Classical in
/-- **Non-vacuity for actual census budgets.**  In the non-vacuous full-domain band, an actual
`CensusDomination` budget supporting a globally aligned non-degenerate stack cannot be zero. -/
theorem censusDomination_cap_pos_of_global_alignment (dom : Fin n ↪ ZMod p) {k a₀ a K : ℕ}
    (hCD : CensusDomination dom k a₀ K) (ha₀ : a₀ ≤ a) (han : a ≤ n) (hka : k + 1 ≤ a)
    (u₀ u₁ : Fin n → ZMod p) {γ : ZMod p}
    (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    0 < K := by
  classical
  have hfloor := censusDomination_ge_choose_univ_of_global_alignment (dom := dom)
    (k := k) (a₀ := a₀) (a := a) (K := K) hCD ha₀ han hka u₀ u₁
    (γ := γ) halign htinj hnd
  have hchoose : 0 < (n - (k + 1)).choose (a - (k + 1)) := by
    exact Nat.choose_pos (by omega)
  exact lt_of_lt_of_le hchoose hfloor

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.censusDomination_ge_choose_univ_of_global_alignment
#print axioms ProximityGap.Ownership.censusDomination_cap_pos_of_global_alignment
