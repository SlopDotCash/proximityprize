/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrelation

/-!
# The multiplicative-autocorrelation double-count: `∑_ρ |S ∩ ρ·S| = |S|²` (#407/#444)

The pencil / Cauchy–Schwarz / Fisher chain (`PencilCauchySchwarzAutocorr`, `PencilPairwiseBonferroni`)
controls the agreement-polynomial root count `r = |S|` over the order-`n` subgroup `μ_n` through the
**maximum** multiplicative autocorrelation `M = max_{ρ≠1} |S ∩ ρ·S|`, giving `r ≤ 1 + √((M+1)·n)`.
Its honest scope note flags the Johnson collapse: at the prize worst case `S = coset(n/2) ∪ {straggler}`
the autocorrelation spikes to `M ≍ n/2` at one bad shift (`PencilAutocorrelation.autocorr_ge_coset_core`),
so the max-`M` bound degrades to `r ≲ n` (Johnson).

This file supplies the **exact reason** that spike is *forced* — the global double-count identity that
the max-`M` route only ever takes the maximum of:

> `autocorr_sum_eq_sq` :  `∑_{ρ ∈ G} |S ∩ dilate ρ S| = |S|²`,
> `autocorr_sum_nontrivial_eq` :  `∑_{ρ ≠ 1} |S ∩ dilate ρ S| = |S|·(|S|−1)`.

**Mechanism.** Each summand counts pairs `(a,b) ∈ S×S` with `a = ρ·b` (`a ∈ S`, `ρ⁻¹a = b ∈ S`).
Every ordered pair `(a,b) ∈ S×S` is realized by a *unique* shift `ρ = a·b⁻¹`, so summing over all `ρ`
counts `S×S` exactly once: `∑_ρ |S ∩ ρ·S| = |S|²`. The trivial shift `ρ = 1` contributes the diagonal
`|S ∩ S| = |S|`; subtracting it gives `|S|·(|S|−1)` spread over the `|G|−1` nontrivial shifts.

**Consequence for the Johnson collapse (`autocorr_pigeonhole_lower`).** Over a finite group `G` of order
`N = |G|`, the nontrivial total `|S|(|S|−1)` is distributed over `N−1` shifts, so the *maximum* is at
least the average: `(N−1)·(max_{ρ≠1}|S∩ρS|) ≥ |S|·(|S|−1)`. For `|S| = r ≍ n` this forces some shift
to carry `≳ r²/N` overlap; at the prize core (`S ⊆ μ_n`, the coset worst case) the bad shift saturates
`M ≍ n/2`. The max-`M` pencil route therefore **cannot** beat Johnson by this identity alone — the
beyond-Johnson `√(log)` cancellation must come from the *signed phase* of the agreement sum (the
BGK / agreement-sharing contribution), not the unsigned overlap count, which this identity pins exactly.

This is field- and thickness-universal, sign-free additive combinatorics on a finite group (no moment
ladder, no `|·|^{2r}` energy). Probe `scripts/probes/probe_autocorr_sum_double_count.py` confirms the
identity exactly on proper thin subgroups `μ_n ⊆ F_p*` (never `n = q−1`), multiple primes incl.
`p > n³` and Fermat `257`.

NOT a CORE bound: `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**. Honest scope (rules 1,3,4,6 + asymptotic
guard): this is the exact constraint lemma *behind* the pencil-route Johnson collapse, not a new
beyond-Johnson saving. No capacity / beyond-Johnson / cliff-at-`n/2` claim.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilAutocorrSumDoubleCount

open ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **The autocorrelation double-count.** Summing the multiplicative autocorrelation
`|S ∩ ρ·S|` over *all* shifts `ρ ∈ G` recovers `|S|²` exactly:

  `∑_{ρ ∈ G} |S ∩ dilate ρ S| = |S|²`.

Each summand counts the pairs `(a,b) ∈ S×S` with `a = ρ·b`; every ordered pair is realized by a unique
shift `ρ = a·b⁻¹`, so the double sum visits `S×S` exactly once. -/
theorem autocorr_sum_eq_sq (S : Finset G) :
    ∑ ρ : G, (S ∩ dilate ρ S).card = S.card ^ 2 := by
  classical
  -- Rewrite each autocorrelation card as a sum of indicators over S, counting b ∈ S with ρ⁻¹? no:
  -- |S ∩ dilate ρ S| = #{a ∈ S : ρ⁻¹ a ∈ S}.
  have hcard : ∀ ρ : G, (S ∩ dilate ρ S).card
      = (S.filter (fun a => ρ⁻¹ * a ∈ S)).card := by
    intro ρ
    congr 1
    ext a
    rw [Finset.mem_inter, mem_dilate, Finset.mem_filter]
  simp_rw [hcard]
  -- ∑_ρ #{a ∈ S : ρ⁻¹ a ∈ S} = #(Σ ρ, {a ∈ S : ρ⁻¹ a ∈ S}), and that sigma bijects to S ×ˢ S
  rw [← Finset.card_sigma]
  -- bijection (ρ, a) ↦ (a, ρ⁻¹ a) : Σ ρ, filter ↔ S ×ˢ S, inverse (a, b) ↦ (a·b⁻¹, a)
  rw [show S.card ^ 2 = (S ×ˢ S).card by rw [Finset.card_product]; ring]
  apply Finset.card_bij (fun (p : Σ _ : G, G) _ => (p.2, p.1⁻¹ * p.2))
  · -- well-defined: lands in S ×ˢ S
    rintro ⟨ρ, a⟩ hp
    rw [Finset.mem_sigma, Finset.mem_filter] at hp
    rw [Finset.mem_product]
    exact ⟨hp.2.1, hp.2.2⟩
  · -- injective
    rintro ⟨ρ₁, a₁⟩ h1 ⟨ρ₂, a₂⟩ h2 heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨ha, hb⟩ := heq
    subst ha
    -- from ρ₁⁻¹ a₁ = ρ₂⁻¹ a₁ we get ρ₁⁻¹ = ρ₂⁻¹, hence ρ₁ = ρ₂
    have hinv : ρ₁⁻¹ = ρ₂⁻¹ := mul_right_cancel hb
    have hρ : ρ₁ = ρ₂ := inv_injective hinv
    subst hρ; rfl
  · -- surjective: (a, b) ↦ (a·b⁻¹, a)
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_product] at hab
    refine ⟨⟨a * b⁻¹, a⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hab.1, ?_⟩
      have : (a * b⁻¹)⁻¹ * a = b := by group
      rw [this]; exact hab.2
    · -- the image (a, (a b⁻¹)⁻¹ a) = (a, b)
      have : (a * b⁻¹)⁻¹ * a = b := by group
      rw [Prod.mk.injEq]
      exact ⟨rfl, this⟩

/-- **The nontrivial-shift double-count.** Stripping the trivial shift `ρ = 1` (which contributes the
diagonal `|S ∩ S| = |S|`), the autocorrelation over the `|G|−1` nontrivial shifts totals exactly
`|S|·(|S|−1)`:

  `∑_{ρ ∈ G, ρ ≠ 1} |S ∩ dilate ρ S| = |S|·(|S|−1)`. -/
theorem autocorr_sum_nontrivial_eq (S : Finset G) :
    ∑ ρ ∈ (Finset.univ.erase (1 : G)), (S ∩ dilate ρ S).card
      = S.card * (S.card - 1) := by
  classical
  have htriv : (S ∩ dilate (1 : G) S).card = S.card := by
    have : dilate (1 : G) S = S := by
      unfold dilate; simp
    rw [this, Finset.inter_self]
  have hsplit : ∑ ρ : G, (S ∩ dilate ρ S).card
      = (S ∩ dilate (1 : G) S).card
        + ∑ ρ ∈ (Finset.univ.erase (1 : G)), (S ∩ dilate ρ S).card := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
    ring
  have hfull := autocorr_sum_eq_sq S
  rw [hsplit, htriv] at hfull
  -- |S|^2 = |S| + (nontrivial sum)  ⇒  nontrivial sum = |S|^2 - |S| = |S|(|S|-1)
  have hsq : S.card ^ 2 = S.card * S.card := by ring
  have hms : S.card * (S.card - 1) = S.card * S.card - S.card := by
    rw [Nat.mul_sub_one, Nat.mul_comm]
  omega

/-- **The pigeonhole lower bound on the worst autocorrelation (the Johnson-collapse mechanism).** The
nontrivial total `|S|·(|S|−1)` is spread over the `|G|−1` nontrivial shifts, so the maximum overlap
bound `M` (with `∀ ρ ≠ 1, |S ∩ ρ·S| ≤ M`) must satisfy

  `|S|·(|S|−1) ≤ (|G|−1)·M`.

This is the exact constraint forcing `M ≥ |S|(|S|−1)/(|G|−1)`: the pencil max-`M` route cannot have a
uniformly small autocorrelation, and at `|S| ≈ n` over `μ_n` the worst shift saturates `M ≈ n/2`
(Johnson). -/
theorem autocorr_max_pigeonhole {S : Finset G} {M : ℕ}
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ M) :
    S.card * (S.card - 1) ≤ (Fintype.card G - 1) * M := by
  classical
  have hbound : ∑ ρ ∈ (Finset.univ.erase (1 : G)), (S ∩ dilate ρ S).card
      ≤ ∑ _ρ ∈ (Finset.univ.erase (1 : G)), M := by
    apply Finset.sum_le_sum
    intro ρ hρ
    exact hM ρ (Finset.ne_of_mem_erase hρ)
  rw [autocorr_sum_nontrivial_eq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, smul_eq_mul] at hbound
  exact hbound

end ProximityGap.Frontier.PencilAutocorrSumDoubleCount

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
open ProximityGap.Frontier.PencilAutocorrSumDoubleCount in
#print axioms autocorr_sum_eq_sq
open ProximityGap.Frontier.PencilAutocorrSumDoubleCount in
#print axioms autocorr_sum_nontrivial_eq
open ProximityGap.Frontier.PencilAutocorrSumDoubleCount in
#print axioms autocorr_max_pigeonhole
