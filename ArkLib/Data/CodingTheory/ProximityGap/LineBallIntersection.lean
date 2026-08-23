/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Line–ball intersection: the `1/q` mechanism for the MCA grand challenge

This is a foundational, self-contained combinatorial lemma toward the ABF26 §4.5 MCA conjecture
(`ProximityGap.mcaConjecture`): a *fixed* codeword `w` is `δ`-close to a **non-degenerate** affine
line `γ ↦ u₀ + γ•u₁` for only very few `γ`.

  `#{γ : Δ₀(u₀+γ•u₁, w) ≤ R} · (|supp u₁| − R) ≤ |supp u₁|`.

This is the source of the conjecture's `1/q` factor: averaging over `γ ← $ᵖ F`, the per-codeword
closeness probability is `≤ |supp u₁| / (q·(|supp u₁| − R))`.  Coordinate-wise, on `T = supp(u₁)`
each `i` forces line-agreement with `w` at a *unique* `γ_i = (w i − u₀ i)/u₁ i`, so the agreement
sets `{i ∈ T : (u₀+γ•u₁) i = w i}` are pairwise disjoint across `γ`; a `γ` within radius `R` has
agreement `≥ |T| − R`, and disjoint sets that large number at most `|T| / (|T| − R)`.

## Strategy (MCA grand challenge)

`ε_mca(C,δ) = sup_u Pr_γ[mcaEvent]`, and the bad event implies *some* `w ∈ C` is `δ`-close to the
line `u₀+γ•u₁`.  A union bound over codewords plus this lemma gives

  `ε_mca(C,δ) ≤ (1/q) · N_line · M`,   `M = |supp u₁|/(|supp u₁| − R)`,

where `N_line = #{w ∈ C : w is δ-close to some point of the line}`.  Since `M = O(1/ρ)` below
capacity, the conjecture **reduces to** the list-decoding count `N_line ≤ poly(n)` — Johnson gives it
up to `1 − √ρ`, and capacity `1 − ρ` is the open core.

## Main result

* `card_close_gamma_le` — the line–ball intersection bound (multiplicative, lossless form).
* `card_close_gamma_le_div` — its `Nat`-division form `#{close γ} ≤ |supp u₁| / (|supp u₁| − R)`.
-/

set_option linter.style.longLine false


open scoped BigOperators
open Finset

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Line–ball intersection bound (the `1/q` mechanism).** A non-degenerate affine line
`γ ↦ u₀ + γ•u₁` is within Hamming radius `R` of a *fixed* word `w` for very few `γ`:
`#{γ : Δ₀(u₀+γ•u₁, w) ≤ R} · (|supp u₁| − R) ≤ |supp u₁|`. -/
theorem card_close_gamma_le (u₀ u₁ w : ι → F) (R : ℕ) :
    (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card
        * ((univ.filter (fun i => u₁ i ≠ 0)).card - R)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set T : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hT
  set G : Finset F := univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R) with hG
  -- (1) every `γ ∈ G` agrees with `w` on `≥ |T| − R` coordinates of `T`
  have hAge : ∀ γ ∈ G, (T.card - R)
      ≤ (T.filter (fun i => (u₀ + γ • u₁) i = w i)).card := by
    intro γ hγ
    rw [hG, Finset.mem_filter] at hγ
    have key := Finset.card_filter_add_card_filter_not (s := T)
      (fun i => (u₀ + γ • u₁) i = w i)
    have hcard : ({a ∈ T | ¬ ((u₀ + γ • u₁) a = w a)}).card ≤ R := by
      refine le_trans (Finset.card_le_card (fun i hi =>
        Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hi).2⟩)) ?_
      exact hγ.2
    omega
  -- (2) the per-`γ` agreement sets are pairwise disjoint (each `i ∈ T` forces a unique `γ`)
  have hdisj : (G : Set F).PairwiseDisjoint
      (fun γ => T.filter (fun i => (u₀ + γ • u₁) i = w i)) := by
    intro γ _ γ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter] at hi hi'
    have hu1 : u₁ i ≠ 0 := by rw [hT, Finset.mem_filter] at hi; exact hi.1.2
    apply hne
    have heq : γ • u₁ i = γ' • u₁ i := by
      have := hi.2.trans hi'.2.symm
      simpa [Pi.add_apply, Pi.smul_apply] using this
    simp only [smul_eq_mul] at heq
    exact mul_right_cancel₀ hu1 heq
  -- (3) so the agreement sets sum (disjointly) to at most `|T|`
  have hsum : ∑ γ ∈ G, (T.filter (fun i => (u₀ + γ • u₁) i = w i)).card ≤ T.card := by
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card (fun i hi => ?_)
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hiγ⟩ := hi
    exact (Finset.filter_subset _ _) hiγ
  -- (4) combine: `|G| · (|T| − R) ≤ ∑ agreement ≤ |T|`
  calc G.card * (T.card - R)
      = ∑ _γ ∈ G, (T.card - R) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (T.filter (fun i => (u₀ + γ • u₁) i = w i)).card := Finset.sum_le_sum hAge
    _ ≤ T.card := hsum

/-- `Nat`-division form: when the line is non-degenerate (`R < |supp u₁|`), at most
`|supp u₁| / (|supp u₁| − R)` values of `γ` are within radius `R` of a fixed `w`. -/
theorem card_close_gamma_le_div (u₀ u₁ w : ι → F) (R : ℕ)
    (hR : R < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card
          / ((univ.filter (fun i => u₁ i ≠ 0)).card - R) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact card_close_gamma_le u₀ u₁ w R

end ProximityGap
