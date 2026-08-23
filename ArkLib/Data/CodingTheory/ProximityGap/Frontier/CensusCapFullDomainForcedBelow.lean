/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusCapForcedBelow

/-!
# Full-domain specialization of the census-cap necessity floor (#444)

`CensusCapForcedBelow` proves the general necessity direction for the census/Conjecture-7.1 face:
one large aligned set `A` forces any census cap `K` to dominate
`choose (|A|-(k+1)) (a-(k+1))`.  The prize stack frequently discusses the full-domain/global
alignment case.  This file packages the exact specialization `A = univ`:

* `censusDomination_cap_ge_choose_univ`: a globally aligned stack with a non-degenerate
  `(k+1)`-tuple forces `choose (n-(k+1)) (a-(k+1)) ≤ K`.
* `censusDomination_cap_pos_of_univ_alignment`: in the non-vacuous band `k+1 ≤ a ≤ n`, the same
  hypotheses force `0 < K`.

This is a small but useful C71/census reduction brick: it removes the ambient-set bookkeeping and
names the exact full-domain binomial obstruction the cap must beat.  It is not a CORE closure and
makes no capacity / beyond-Johnson / growth-law claim; the cliff-at-`n/2` guard is untouched.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [NeZero n] in
/-- **Full-domain census floor.**  In the globally aligned case `A = univ`, the general
necessity theorem `censusDomination_cap_ge_choose` becomes the explicit obstruction
`choose (n-(k+1)) (a-(k+1)) ≤ K`. -/
theorem censusDomination_cap_ge_choose_univ (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {γ : F} {K : ℕ}
    (han : a ≤ n) (hka : k + 1 ≤ a)
    (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K) :
    (n - (k + 1)).choose (a - (k + 1)) ≤ K := by
  classical
  have hAa : a ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using han
  have htmem : ∀ b, t b ∈ (Finset.univ : Finset (Fin n)) := by
    intro b
    simp
  have h := censusDomination_cap_ge_choose (dom := dom) (u₀ := u₀) (u₁ := u₁)
    (γ := γ) (A := (Finset.univ : Finset (Fin n))) (K := K)
    hAa hka halign htinj htmem hnd hcap
  simpa using h

open Classical in
omit [NeZero n] in
/-- **Non-vacuity corollary.**  In the full-domain, non-vacuous band `k+1 ≤ a ≤ n`, a
census cap witnessing a globally aligned non-degenerate stack cannot be zero. -/
theorem censusDomination_cap_pos_of_univ_alignment (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {γ : F} {K : ℕ}
    (han : a ≤ n) (hka : k + 1 ≤ a)
    (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K) :
    0 < K := by
  classical
  have hfloor := censusDomination_cap_ge_choose_univ (dom := dom) (u₀ := u₀) (u₁ := u₁)
    (γ := γ) (K := K) han hka halign htinj hnd hcap
  have hchoose : 0 < (n - (k + 1)).choose (a - (k + 1)) := by
    exact Nat.choose_pos (by omega)
  exact lt_of_lt_of_le hchoose hfloor

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.censusDomination_cap_ge_choose_univ
#print axioms ProximityGap.Ownership.censusDomination_cap_pos_of_univ_alignment
