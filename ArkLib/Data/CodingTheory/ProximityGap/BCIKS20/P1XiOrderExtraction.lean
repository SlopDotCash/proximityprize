/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# BCIKS20 Appendix A.4 (P1) — constructive `ξ`-order extraction for the Hensel numerator (#138)

This file lands the **first genuinely-provable brick of the divisibility half** of the BCIKS20
Appendix-A weight-1 regularity core (#138): the *base* `ξ`-order of the Hensel numerator
`βHensel (k+1)` is `2k`, **unconditionally and constructively** (pure ring algebra over `𝒪 H`,
NO Faà-di-Bruno cancellation used), once the lower-order `ξ`-divisibility is supplied.

The arithmetic is exact: in the BCIKS20 `(A.1)` recursion (`βHensel_succ`) every surviving summand
contributes a `ξ`-power
`(2·i1 + Σλ − 2) + (2·(k+1−i1) − Σλ) = 2k`,
the first term from the explicit `ξ^{2i1+Σλ−2}` prefactor and the second from the partition
product `∏_l β_l^{λ_l}` once each `β_l = a_l · ξ^{2l−1}` is substituted (parts are positive, so
`∑_{l} (2l−1) = 2·(k+1−i1) − Σλ`). Hence `ξ^{2k}` factors out of the whole double sum, with the
`W𝒪`-power, `B_coeff`, and the cleared partition product absorbed into the quotient.

**This pins the genuine open #138 core to exactly the *one extra* `ξ`-factor** (the Newton
order-gain `2k → 2k+1`), which is the cancellation of the leading `ξ^{2k}` coefficient — the
BCIKS20 Faà-di-Bruno match, *not* available from sub-additive bounds — together with the weight-`≤1`
bound on the quotient. The base order proved here needs neither: it is honest ring algebra.

No `axiom`, no `sorry`; `#print axioms` at the bottom reports only
`[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The product of `x ^ g l` over a multiset is `x` raised to the sum of `g`. -/
theorem prod_map_pow_eq_pow_sum {M : Type*} [CommMonoid M] (x : M) (g : ℕ → ℕ)
    (s : Multiset ℕ) :
    (s.map (fun l => x ^ g l)).prod = x ^ ((s.map g).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, ih,
        ← pow_add]

/-- `∑_{l ∈ s} (2l − 1) = 2·(∑ s) − card s` for a multiset of positive parts (the `ξ`-order
contributed by a partition product `∏_l β_l^{λ_l}` when `β_l` carries `ξ`-order `2l − 1`). -/
theorem sum_map_two_mul_pred (s : Multiset ℕ) (hpos : ∀ l ∈ s, 1 ≤ l) :
    (s.map (fun l => 2 * l - 1)).sum = 2 * s.sum - Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 1 ≤ a := hpos a (Multiset.mem_cons_self a s)
      have hpos' : ∀ l ∈ s, 1 ≤ l := fun l hl => hpos l (Multiset.mem_cons_of_mem hl)
      have hsc : Multiset.card s ≤ s.sum := by
        calc Multiset.card s = (s.map (fun _ => 1)).sum := by simp
          _ ≤ (s.map id).sum := Multiset.sum_map_le_sum_map _ _ (fun l hl => hpos' l hl)
          _ = s.sum := by simp
      rw [Multiset.map_cons, Multiset.sum_cons, ih hpos', Multiset.sum_cons, Multiset.card_cons]
      omega

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **`ξ`-order extraction from a partition product.**  If `b l = a l · ξ^(2l−1)` on every part of
`lam : Nat.Partition m`, then `partitionProd lam b = partitionProd lam a · ξ^(2m − Σλ)`. -/
theorem partitionProd_xi_factor {m : ℕ} (lam : Nat.Partition m) (a : ℕ → 𝒪 H) (ξ : 𝒪 H)
    (b : ℕ → 𝒪 H) (hb : ∀ l ∈ lam.parts, b l = a l * ξ ^ (2 * l - 1)) :
    partitionProd lam b = partitionProd lam a * ξ ^ (2 * m - sigmaLambda lam) := by
  have h1 : partitionProd lam b = partitionProd lam (fun l => a l * ξ ^ (2 * l - 1)) := by
    rw [partitionProd, partitionProd]
    exact congrArg Multiset.prod (Multiset.map_congr rfl hb)
  rw [h1, partitionProd_mul]
  congr 1
  rw [partitionProd, prod_map_pow_eq_pow_sum]
  congr 1
  rw [sum_map_two_mul_pred lam.parts (fun l hl => lam.parts_pos hl), lam.parts_sum, sigmaLambda]

/-- **Constructive `ξ^{2k}` order-extraction for the Hensel numerator (#138, divisibility half).**
For ANY irreducible `H`, assuming the lower-order `ξ`-divisibility `βHensel l = a l · ξ^(2l−1)`
for all `l ≤ k`, the BCIKS20 `(A.1)` recursion gives `βHensel (k+1) = c · ξ^{2k}` constructively —
pure ring algebra, **no cancellation used**: every surviving summand of `βHensel_succ` carries
`ξ`-order exactly `(2·i1 + Σλ − 2) + (2·(k+1−i1) − Σλ) = 2k`, so `ξ^{2k}` factors out of the whole
double sum, the `W𝒪`-power, `B_coeff`, and cleared partition product collapsing into `c`.

This pins the remaining open BCIKS20 core to exactly the **one extra `ξ`** (the Newton order-gain
`2k → 2k+1`, i.e. the vanishing of the leading `ξ^{2k}` coefficient — the Faà-di-Bruno cancellation)
plus the weight-`≤ 1` bound on the quotient; neither follows from the sub-additive weight calculus.
The base `ξ`-order proved here is unconditional. -/
theorem betaHensel_succ_xi_pow_extraction
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (a : ℕ → 𝒪 H)
    (hlower : ∀ l, l ≤ k →
      βHensel H x₀ R hHyp l = a l * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * l - 1)) :
    ∃ c : 𝒪 H,
      βHensel H x₀ R hHyp (k + 1) = c * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * k) := by
  classical
  refine ⟨- ∑ i1 ∈ Finset.range (k + 2),
      ∑ lam ∈ (Finset.univ.filter
          (fun lam : Nat.Partition (k + 1 - i1) => (k + 1) ∉ lam.parts)),
        W𝒪 H ^ (i1 + deltaSave i1 - 1) * B_coeff H x₀ R i1 lam * partitionProd lam a, ?_⟩
  rw [βHensel_succ]
  set ξ := ClaimA2.ξ x₀ R H hHyp with hξ
  rw [neg_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i1 hi1 => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun lam hlam_mem => ?_)
  have hlam : (k + 1) ∉ lam.parts := (Finset.mem_filter.mp hlam_mem).2
  have hi1le : i1 ≤ k + 1 := by have := Finset.mem_range.mp hi1; omega
  have hσm : sigmaLambda lam ≤ k + 1 - i1 := by
    have hsc : Multiset.card lam.parts ≤ lam.parts.sum := by
      calc Multiset.card lam.parts = (lam.parts.map (fun _ => 1)).sum := by simp
        _ ≤ (lam.parts.map id).sum :=
          Multiset.sum_map_le_sum_map _ _ (fun l hl => lam.parts_pos hl)
        _ = lam.parts.sum := by simp
    rw [lam.parts_sum] at hsc
    rw [sigmaLambda]
    exact hsc
  have hσ0 : i1 = 0 → 2 ≤ sigmaLambda lam := by
    intro hi0
    rw [sigmaLambda]
    have hsum : lam.parts.sum = k + 1 := by rw [lam.parts_sum, hi0, Nat.sub_zero]
    by_contra hlt
    have hcases : Multiset.card lam.parts = 0 ∨ Multiset.card lam.parts = 1 := by omega
    rcases hcases with h0 | h1
    · rw [Multiset.card_eq_zero] at h0
      rw [h0, Multiset.sum_zero] at hsum; omega
    · rw [Multiset.card_eq_one] at h1
      obtain ⟨b, hb⟩ := h1
      rw [hb, Multiset.sum_singleton] at hsum
      exact hlam (hb ▸ Multiset.mem_singleton.mpr hsum.symm)
  have hge2 : 2 ≤ 2 * i1 + sigmaLambda lam := by
    rcases Nat.eq_zero_or_pos i1 with h | h
    · have := hσ0 h; omega
    · omega
  have hexp : (2 * i1 + sigmaLambda lam - 2) + (2 * (k + 1 - i1) - sigmaLambda lam) = 2 * k := by
    omega
  rw [partitionProd_surviving_guard lam hlam (fun l => βHensel H x₀ R hHyp l) 0,
    partitionProd_xi_factor H lam a ξ (fun l => βHensel H x₀ R hHyp l)
      (fun l hl => hlower l (Nat.lt_succ_iff.mp (surviving_parts_lt lam hlam hl)))]
  calc
    W𝒪 H ^ (i1 + deltaSave i1 - 1) * ξ ^ (2 * i1 + sigmaLambda lam - 2) * B_coeff H x₀ R i1 lam
          * (partitionProd lam a * ξ ^ (2 * (k + 1 - i1) - sigmaLambda lam))
        = (W𝒪 H ^ (i1 + deltaSave i1 - 1) * B_coeff H x₀ R i1 lam * partitionProd lam a)
            * (ξ ^ (2 * i1 + sigmaLambda lam - 2) * ξ ^ (2 * (k + 1 - i1) - sigmaLambda lam)) := by
          ring
    _ = (W𝒪 H ^ (i1 + deltaSave i1 - 1) * B_coeff H x₀ R i1 lam * partitionProd lam a)
            * ξ ^ ((2 * i1 + sigmaLambda lam - 2) + (2 * (k + 1 - i1) - sigmaLambda lam)) := by
          rw [← pow_add]
    _ = (W𝒪 H ^ (i1 + deltaSave i1 - 1) * B_coeff H x₀ R i1 lam * partitionProd lam a)
            * ξ ^ (2 * k) := by rw [hexp]

#print axioms betaHensel_succ_xi_pow_extraction

end BCIKS20.HenselNumerator
