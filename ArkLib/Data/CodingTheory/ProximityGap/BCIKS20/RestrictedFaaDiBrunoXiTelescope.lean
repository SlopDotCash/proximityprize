/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — the STEP-8 `ξ`-telescope for monic `H` (issue #139, obstruction 2)

For monic `H` the `W`-power weighting of the STEP-8 recursion side already collapses
(`restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one`). The remaining unit-side
content is the **separability-discriminant unit `ξ = ClaimA2.ξ`** (`ξ ≠ 0`,
`embeddingOf𝒪Into𝕃_ξ_ne_zero`). This file determines exactly how the `ξ`-powers behave and lands
every genuine `ξ`-power-bookkeeping lemma.

## The exponent geometry

* On the **recursion (RHS) side** `restrictedMatchRecursionPartitionForm`, each `(i₁, λ)` summand
  carries `ξ^{2·i₁ + σλ − 2}` (`σλ = sigmaLambda λ = λ.parts.card`), over a *global* denominator
  `ξ^{2(t+1)−1}` (the `W`-side of the denominator is `1` for monic `H`).
* On the **Faà-di-Bruno (LHS) side** `restrictedFaaDiBrunoPartitionForm`, the `ξ`-powers enter only
  through the assembled-series coefficients `coeff l (βHenselAssembled) =
  embed(βHensel l) / (W^{l+1}·ξ^{2l−1})`. Since `coeff 0` is `ξ`-free (`2·0−1 = 0` in `ℕ`) and each
  part `l ≥ 1`, a partition `λ ⊢ (t+1−i₁)` contributes the `ξ`-denominator exponent
  `∑_{l∈λ}(2l−1) = 2·(λ.parts.sum) − σλ = 2(t+1−i₁) − σλ`.

## Result: the `ξ`-powers TELESCOPE jointly, not as a pure-RHS factorization

The pure-`ℕ` identity `xiExp_recNum_add_lhsDen` proves the central fact

  `(2·i₁ + σλ − 2) + (2·(t+1−i₁) − σλ) = 2·(t+1) − 2`,

i.e. **the per-term RHS `ξ`-numerator exponent and the per-term LHS `ξ`-denominator exponent sum to
a single `(i₁,λ)`-independent constant `2(t+1)−2`.**  No `ℕ`-truncation interferes (the single-part
partition `[t+1]` of the `i₁ = 0` block is excluded by the `(t+1) ∉ λ.parts` filter, so every
surviving term has `2·i₁ + σλ ≥ 2`; `card ≤ sum` keeps the LHS exponent honest).

Consequently (`restrictedMatchRecursionPartitionForm_eq_ξfree_of_leadingCoeff_one`) the monic
recursion side factors as a **single global unit `ζ · ξ⁻¹`** times a sum whose per-term `ξ`-content
is *exactly* the LHS-shaped denominator `1/ξ^{2(t+1−i₁)−σλ}`:

  `restrictedMatchRecursionPartitionForm … t`
    `= (ζ / ξ) · ∑_{i₁,λ} (⟦B_coeff⟧ · ⟦partitionProd λ βHensel⟧) / ξ^{2(t+1−i₁)−σλ}`.

So the answer to "do the `ξ`-powers factor out cleanly?" is precise: the *global* `ξ`-power
collapses to a single `ξ⁻¹` (one global unit per order), but a genuine per-term `ξ`-denominator
`1/ξ^{2(t+1−i₁)−σλ}` **remains** — and it is exactly the `ξ`-denominator that the LHS
`βHenselAssembled` coefficients supply. The `ξ`-telescope is therefore a *joint* LHS↔RHS
cancellation, not a one-sided `(global-ξ-power)·(ξ-free core)` split. After this `ξ`-bookkeeping the
monic STEP-8 residual reduces to the `W`-free, `ξ`-matched combinatorial Faà-di-Bruno identity
(`B_coeff`/binomial/`countPerms`/`partitionProd`), which is the unformalized BCIKS20 A.4 content.

See issue #139.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## 1. The pure-`ℕ` exponent telescope -/

/-- **`σλ ≤ m` for a partition `λ ⊢ m` (axiom-clean).** The number of parts is at most the sum,
because every part is `≥ 1`. This is the no-truncation guard for the LHS `ξ`-denominator exponent
`2·m − σλ`. -/
theorem sigmaLambda_le {m : ℕ} (lam : Nat.Partition m) : sigmaLambda lam ≤ m := by
  have hc : lam.parts.card ≤ lam.parts.sum := by
    calc lam.parts.card = (lam.parts.map (fun _ => 1)).sum := by
              simp [Multiset.map_const', Multiset.sum_replicate]
      _ ≤ (lam.parts.map (fun l => l)).sum := by
              apply Multiset.sum_map_le_sum_map
              intro l hl
              exact lam.parts_pos hl
      _ = lam.parts.sum := by rw [Multiset.map_id']
  rw [lam.parts_sum] at hc
  rw [sigmaLambda]
  exact hc

/-- **The LHS `ξ`-denominator exponent of a partition (axiom-clean).** The assembled-series
coefficient `coeff l (βHenselAssembled) = embed(βHensel l) / (W^{l+1}·ξ^{2l−1})` contributes the
`ξ`-exponent `2·l − 1` for each part `l` of `λ`. Summing over the multiset of parts (the genuine
`partitionProd`-shape product), and using that every part is `≥ 1` so each `2·l − 1` is untruncated,
gives `∑_{l∈λ}(2l−1) = 2·m − σλ`. -/
theorem sum_map_two_mul_sub_one {m : ℕ} (lam : Nat.Partition m) :
    (lam.parts.map (fun l => 2 * l - 1)).sum = 2 * m - sigmaLambda lam := by
  have hmap : (lam.parts.map (fun l => 2 * l - 1))
      = lam.parts.map (fun l => 2 * (l - 1) + 1) := by
    apply Multiset.map_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := lam.parts_pos hl
    omega
  rw [hmap, Multiset.sum_map_add]
  simp only [Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]
  have hsub : (lam.parts.map (fun l => l - 1)).sum = m - lam.parts.card := by
    have heq : (lam.parts.map (fun l => (l - 1) + 1)).sum = (lam.parts.map (fun l => l)).sum := by
      apply congrArg
      apply Multiset.map_congr rfl
      intro l hl
      have hl1 : 1 ≤ l := lam.parts_pos hl
      omega
    rw [Multiset.sum_map_add] at heq
    simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one,
      Multiset.map_id'] at heq
    rw [lam.parts_sum] at heq
    omega
  rw [hsub, sigmaLambda]
  have hle := sigmaLambda_le lam
  rw [sigmaLambda] at hle
  omega

/-- **The STEP-8 `ξ`-exponent telescope (PURE `ℕ`, axiom-clean).** For a partition `λ ⊢ (t+1−i₁)`
with `i₁ ≤ t+1` and `2 ≤ 2·i₁ + σλ` (the surviving-filter guard), the per-term recursion-side
`ξ`-numerator exponent `2·i₁ + σλ − 2` and the LHS-side `ξ`-denominator exponent
`2·(t+1−i₁) − σλ` sum to the single `(i₁,λ)`-independent constant `2·(t+1) − 2`:

  `(2·i₁ + σλ − 2) + (2·(t+1−i₁) − σλ) = 2·(t+1) − 2`.

This is the algebraic heart of the `ξ`-telescope: it shows the per-term variation in the recursion
exponent is *exactly* compensated by the per-term variation in the LHS assembled-coefficient
`ξ`-denominator. -/
theorem xiExp_recNum_add_lhsDen (t i1 : ℕ) {m : ℕ} (lam : Nat.Partition m)
    (hm : m = t + 1 - i1) (hi1 : i1 ≤ t + 1) (hguard : 2 ≤ 2 * i1 + sigmaLambda lam) :
    (2 * i1 + sigmaLambda lam - 2) + (2 * m - sigmaLambda lam) = 2 * (t + 1) - 2 := by
  have hsl : sigmaLambda lam ≤ m := sigmaLambda_le lam
  subst hm
  omega

/-- **The surviving recursion terms have untruncated `ξ`-numerator exponent (axiom-clean).** Every
`(i₁, λ)` summand that survives the `(t+1) ∉ λ.parts` filter on `λ ⊢ (t+1−i₁)` satisfies
`2 ≤ 2·i₁ + σλ`, so the recursion `ξ`-exponent `2·i₁ + σλ − 2` is genuine (no `ℕ`-truncation). For
`i₁ ≥ 1` this is immediate (`2·i₁ ≥ 2`); for `i₁ = 0` the only partition of `t+1` with `σλ = 1` is
the single part `[t+1]`, which the filter excludes — forcing `σλ ≥ 2`. -/
theorem two_le_two_mul_i1_add_sigmaLambda {t i1 : ℕ}
    (lam : Nat.Partition (t + 1 - i1)) (hfilter : (t + 1) ∉ lam.parts) :
    2 ≤ 2 * i1 + sigmaLambda lam := by
  rcases Nat.eq_zero_or_pos i1 with hi0 | hi0
  · -- i1 = 0: partition of `t+1`; must have at least two parts, else it is `[t+1]` (filtered out).
    subst hi0
    simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_add] at *
    -- here `t + 1 - 0 = t + 1`
    by_contra hlt
    -- `sigmaLambda lam < 2`, i.e. `lam.parts.card ≤ 1`.
    have hcard : lam.parts.card ≤ 1 := by
      have := Nat.lt_of_not_le hlt
      rw [sigmaLambda] at this; omega
    -- card 0 is impossible (sum would be 0 ≠ t+1); card 1 forces the part to be `t+1`.
    have hsum : lam.parts.sum = t + 1 := lam.parts_sum
    interval_cases h : lam.parts.card
    · rw [Multiset.card_eq_zero] at h
      rw [h] at hsum; simp at hsum
    · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
      rw [ha] at hsum hfilter
      simp only [Multiset.sum_singleton] at hsum
      exact hfilter (by rw [hsum]; exact Multiset.mem_singleton_self _)
  · omega

/-! ## 2. The `ξ`-power factorization in the function field `𝕃 H` -/

/-- **Per-term `ξ`-power factorization (axiom-clean).** Using `ξ ≠ 0` and the pure-`ℕ` telescope
`xiExp_recNum_add_lhsDen`, the recursion-side per-term `ξ`-power splits as the global constant
`ξ^{2(t+1)−2}` over the LHS-shaped per-term denominator `ξ^{2(t+1−i₁)−σλ}`:

  `ξ^{2·i₁ + σλ − 2} = ξ^{2·(t+1) − 2} / ξ^{2·(t+1−i₁) − σλ}`.

This is the `𝕃`-level realization of the exponent telescope: the per-`(i₁,λ)` `ξ`-power is *not*
constant, but it becomes a single global power once the LHS assembled-coefficient `ξ`-denominator is
brought to the same side. -/
theorem xi_pow_recNum_eq_global_div_lhsDen (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i1 : ℕ)
    (lam : Nat.Partition (t + 1 - i1)) (hi1 : i1 ≤ t + 1)
    (hfilter : (t + 1) ∉ lam.parts) :
    embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
      = embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * (t + 1) - 2)
          / embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * (t + 1 - i1) - sigmaLambda lam) := by
  have hξ : embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ≠ 0 :=
    embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp
  have hguard : 2 ≤ 2 * i1 + sigmaLambda lam :=
    two_le_two_mul_i1_add_sigmaLambda lam hfilter
  have htel : (2 * i1 + sigmaLambda lam - 2) + (2 * (t + 1 - i1) - sigmaLambda lam)
      = 2 * (t + 1) - 2 := xiExp_recNum_add_lhsDen t i1 lam rfl hi1 hguard
  rw [eq_div_iff (pow_ne_zero _ hξ), ← pow_add, htel]

/-! ## 3. The monic recursion side, `ξ`-telescoped -/

/-- **Monic-`H` recursion side, fully `ξ`-telescoped (axiom-clean).** Starting from the `W`-free
monic recursion form (`restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one`), the
per-term `ξ`-powers telescope: every `ξ^{2·i₁+σλ−2}` combines with the global `1/ξ^{2(t+1)−1}` to
yield a **single global unit `ζ · ξ⁻¹`** times a sum whose only remaining `ξ`-content is the
per-term LHS-shaped denominator `1/ξ^{2(t+1−i₁)−σλ}`:

  `restrictedMatchRecursionPartitionForm … t`
    `= ζ · ξ⁻¹ · ∑_{i₁,λ} (⟦B_coeff⟧ · ⟦partitionProd λ βHensel⟧) / ξ^{2(t+1−i₁)−σλ}`.

The global `ξ`-power genuinely collapses to a single `ξ⁻¹`; the surviving per-term denominator
`ξ^{2(t+1−i₁)−σλ} = ξ^{∑_{l∈λ}(2l−1)}` (`sum_map_two_mul_sub_one`) is *precisely* the `ξ`-denominator
supplied by the LHS assembled-series coefficients `coeff l (βHenselAssembled)`. Hence the `ξ`-telescope
is a joint LHS↔RHS cancellation, after which the monic STEP-8 residual carries only the `W`-free,
`ξ`-matched combinatorial Faà-di-Bruno data (`B_coeff`/`partitionProd`/binomial/`countPerms`). -/
theorem restrictedMatchRecursionPartitionForm_eq_ξfree_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp t
      = ClaimA2.ζ R x₀ H
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))⁻¹
          * (∑ i1 ∈ Finset.range (t + 2),
                ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                          (fun lam => (t + 1) ∉ lam.parts),
                  embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
                    * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
                    / embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)
                        ^ (2 * (t + 1 - i1) - sigmaLambda lam)) := by
  have hξ : embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ≠ 0 :=
    embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp
  set ξ := embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) with hξdef
  -- The global numerator/denominator `ξ`-powers collapse to a single `ξ⁻¹`.
  have hglob : ξ ^ (2 * (t + 1) - 2) / ξ ^ (2 * (t + 1) - 1) = ξ⁻¹ := by
    rw [div_eq_iff (pow_ne_zero _ hξ), inv_mul_eq_div, eq_div_iff hξ, ← pow_succ]
    congr 1
  rw [restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one H x₀ R hHyp t hlc,
    mul_assoc]
  -- Reduce to the inner double-sum identity `recSum / ξ^G = ξ⁻¹ · S`.
  rw [Finset.sum_div]
  refine congrArg (fun z : 𝕃 H => ClaimA2.ζ R x₀ H * z) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i1 hi1mem => ?_)
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun lam hlam => ?_)
  have hi1 : i1 ≤ t + 1 := by
    have := Finset.mem_range.mp hi1mem; omega
  have hfilter : (t + 1) ∉ lam.parts := (Finset.mem_filter.mp hlam).2
  rw [xi_pow_recNum_eq_global_div_lhsDen H x₀ R hHyp t i1 lam hi1 hfilter]
  -- Per-term identity, with `B`, `P` the (`ξ`-free) combinatorial core and
  -- `dl := 2(t+1-i1) - σλ` the LHS-shaped per-term denominator exponent.
  set B := embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam) with hBdef
  set P := embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)) with hPdef
  set dl := 2 * (t + 1 - i1) - sigmaLambda lam with hdldef
  -- LHS term: `(ξ^g / ξ^dl) * B * P / ξ^G`; RHS term: `ξ⁻¹ * (B * P / ξ^dl)`,
  -- where `g = 2(t+1)-2`, `G = 2(t+1)-1`, and `ξ^g/ξ^G = ξ⁻¹` by `hglob`.
  rw [← hξdef]
  calc
    ξ ^ (2 * (t + 1) - 2) / ξ ^ dl * B * P / ξ ^ (2 * (t + 1) - 1)
        = (ξ ^ (2 * (t + 1) - 2) / ξ ^ (2 * (t + 1) - 1)) * (B * P / ξ ^ dl) := by
            field_simp [hξ]
    _ = ξ⁻¹ * (B * P / ξ ^ dl) := by
            rw [hglob]

end BCIKS20.HenselNumerator

-- Axiom audit: every landed `ξ`-bookkeeping lemma is axiom-clean
-- (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
#print axioms BCIKS20.HenselNumerator.sigmaLambda_le
#print axioms BCIKS20.HenselNumerator.sum_map_two_mul_sub_one
#print axioms BCIKS20.HenselNumerator.xiExp_recNum_add_lhsDen
#print axioms BCIKS20.HenselNumerator.two_le_two_mul_i1_add_sigmaLambda
#print axioms BCIKS20.HenselNumerator.xi_pow_recNum_eq_global_div_lhsDen
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionForm_eq_ξfree_of_leadingCoeff_one
