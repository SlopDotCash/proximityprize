/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HasseIndexShift

/-!
# The structured weight induction (Johnson E2′): the Claim A.2 invariant, assembled

DISPROOF_LOG O154 findings 3–7: the loose per-term wall (`βHenselSuccTermWeightResidual`)
is unprovable through the loose IH (the in-file wave-5 diagnosis), but the paper's
**structured** invariant — `Λ(β_t) ≤ 1 + (t+1)·deg(W) + e_t·Λ_ξ` (Claim A.2, fulltext
3962) — restores the partition cancellation: the per-term ξ-exponents collapse to exactly
`2k` and the W-exponents telescope (the (5.16) display). This file assembles the structured
strong induction, mirroring the in-tree `βHensel_weight_bound` skeleton:

* `structuredBound` — the Claim A.2 invariant value `1 + (t+1)·deg(W) + e_t·Λ_ξ-budget`
  (`e_t = 2t − 1` in ℕ-truncation, so `e_0 = 0`; `Λ_ξ`-budget `(d_R−1)·(D−d_H+1)` from the
  proven `weight_ξ_bound`);
* `βHensel_weight_bound_zero_structured` — the base case, exact at the tight anchor
  `D ≤ d_H + deg(W)` (finding 5: the paper's `Λ(T) = Λ(W) + 1`);
* `StructuredSuccTermBound` — the per-term obligation, now with the **structured** IH (the
  provable form; its arithmetic is findings 3+7, consuming the proven E1′ inventory);
* `βHensel_weight_bound_structured` — the assembled induction.

With a proof of `StructuredSuccTermBound` (the E1′ bricks + the in-tree calculus), the
structured bound composes with the proven `βHensel_weight_bound_of_structured_weight`
collapse into the loose target consumed by the kill-target/Claim-5.10 chain.

## References
* [BCIKS20] §A.4 Claim A.2 (fulltext 3959–3970), the §5 telescoping (1788–1797);
  DISPROOF_LOG O154 findings 3–7; `HasseIndexShift.lean` (the E1′ inventory).
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate BCIKS20AppendixA

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
  [Fact (0 < H.natDegree)]

/-- **The Claim A.2 structured invariant value** at order `t`:
`1 + (t+1)·deg(W) + e_t·(d_R−1)·(D−d_H+1)`, with `e_t = 2t−1` truncated (`e_0 = 0`). -/
noncomputable def structuredBound (H : F[X][Y]) (R : F[X][X][Y]) (D t : ℕ) : ℕ :=
  1 + (t + 1) * (H.leadingCoeff).natDegree
    + (2 * t - 1) * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))

/-- **The structured base case (finding 5, the paper's `Λ(T) = Λ(W) + 1`):** at the tight
anchor `D ≤ d_H + deg(W)`, the order-0 numerator `β₀ = mk X` satisfies the structured
invariant exactly: `Λ(β₀) = D + 1 − d_H ≤ 1 + deg(W) = structuredBound 0`. -/
theorem βHensel_weight_bound_zero_structured (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D
      ≤ WithBot.some (structuredBound H R D 0) := by
  rw [βHensel_zero]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
  have hweq : weight_Λ (Polynomial.X : F[X][Y]) H D
      = WithBot.some (D + 1 - Bivariate.natDegreeY H) := by
    rw [weight_Λ, Polynomial.support_X (by norm_num)]
    simp
  rw [hweq]
  refine WithBot.coe_le_coe.mpr ?_
  unfold structuredBound
  have hdY : Bivariate.natDegreeY H = H.natDegree := rfl
  omega

/-- **The REBASED structured invariant value** (finding 12's anchor catch: the tight
anchor is infeasible for the monisized `H̃`, so the monic route uses the rebased constant
`D + 1 − d_H` in place of `1`): `(D+1−d_H) + (t+1)·deg(W) + e_t·Λ_ξ-budget`. The proven
`structured_weight_collapse_rebased` collapses exactly this into the loose target. -/
noncomputable def structuredBoundRebased (H : F[X][Y]) (R : F[X][X][Y]) (D t : ℕ) : ℕ :=
  (D + 1 - Bivariate.natDegreeY H) + (t + 1) * (H.leadingCoeff).natDegree
    + (2 * t - 1) * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))

/-- **The rebased base case — EXACT at every anchor `D ≥ totalDegree H`** (no tightness
hypothesis; finding 1's rep computation): `Λ(β₀) = Λ(rep Y) = D + 1 − d_H ≤
structuredBoundRebased 0`. This is the base case compatible with the monisized `H̃`
(where the tight anchor of `βHensel_weight_bound_zero_structured` is infeasible). -/
theorem βHensel_weight_bound_zero_rebased (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D
      ≤ WithBot.some (structuredBoundRebased H R D 0) := by
  rw [βHensel_zero]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
  have hweq : weight_Λ (Polynomial.X : F[X][Y]) H D
      = WithBot.some (D + 1 - Bivariate.natDegreeY H) := by
    rw [weight_Λ, Polynomial.support_X (by norm_num)]
    simp
  rw [hweq]
  refine WithBot.coe_le_coe.mpr ?_
  unfold structuredBoundRebased
  omega

/-- **The rebased structured induction** — `βHensel_weight_bound_structured`'s skeleton
with the rebased invariant: usable at EVERY anchor `D ≥ totalDegree H` (in particular at
the monisized `H̃`, where the tight-anchor variant cannot be instantiated). -/
theorem βHensel_weight_bound_rebased (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hterm : ∀ (k : ℕ)
      (_hIH : ∀ l, l < k + 1 →
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some (structuredBoundRebased H R D l))
      (i1 : ℕ) (_hi1 : i1 ∈ Finset.range (k + 2))
      (lam : Nat.Partition (k + 1 - i1)) (_hlam : (k + 1) ∉ lam.parts),
        weight_Λ_over_𝒪 hH
            ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeff H x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
          ≤ WithBot.some (structuredBoundRebased H R D (k + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some (structuredBoundRebased H R D t) := by
  classical
  induction t using Nat.strong_induction_on with
  | _ t hIH =>
    match t with
    | 0 => exact βHensel_weight_bound_zero_rebased x₀ R hHyp hH hDH
    | (k + 1) =>
        rw [βHensel_succ]
        refine le_trans (weight_Λ_over_𝒪_neg H hH hDH _) ?_
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun i1 hi1 => ?_)
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun lam hlam => ?_)
        exact hterm k (fun l hl => hIH l (by omega)) i1 hi1 lam
          (Finset.mem_filter.mp hlam).2

/-- **The structured per-term obligation** — the provable form of the per-term wall: the
`(A.1)` recursion term at order `k + 1`, bounded by the structured invariant, **given the
structured IH** for all lower orders. Findings 3+7 verify its arithmetic by hand (the `2k`
ξ-collapse, the W-telescoping, the E1′ B-bound); the proven E1′ inventory
(`HasseIndexShift.lean`) and the in-tree weight calculus are its ingredients. -/
def StructuredSuccTermBound (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) (k : ℕ)
    (_hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (structuredBound H R D l))
    (i1 : ℕ) (_hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (_hlam : (k + 1) ∉ lam.parts) : Prop :=
  weight_Λ_over_𝒪 hH
      ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
        * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
        * B_coeff H x₀ R i1 lam
        * partitionProd lam
            (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
    ≤ WithBot.some (structuredBound H R D (k + 1))

/-- **THE STRUCTURED WEIGHT INDUCTION (E2′, assembled).** Mirrors the in-tree
`βHensel_weight_bound` skeleton with the structured target: given the base anchor and the
structured per-term bound, every Hensel numerator satisfies the Claim A.2 invariant
`Λ(β_t) ≤ 1 + (t+1)·deg(W) + e_t·Λ_ξ`. -/
theorem βHensel_weight_bound_structured (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hterm : ∀ (k : ℕ)
      (hIH : ∀ l, l < k + 1 →
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some (structuredBound H R D l))
      (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2))
      (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts),
        StructuredSuccTermBound x₀ R hHyp hH D k hIH i1 hi1 lam hlam)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some (structuredBound H R D t) := by
  classical
  induction t using Nat.strong_induction_on with
  | _ t hIH =>
    match t with
    | 0 => exact βHensel_weight_bound_zero_structured x₀ R hHyp hH hDH htight
    | (k + 1) =>
        rw [βHensel_succ]
        refine le_trans (weight_Λ_over_𝒪_neg H hH hDH _) ?_
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun i1 hi1 => ?_)
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun lam hlam => ?_)
        exact hterm k (fun l hl => hIH l (by omega)) i1 hi1 lam
          (Finset.mem_filter.mp hlam).2

/-! ## The per-term decomposition engine (transcription step (iii)) -/

/-- `ℕ`-scalar action on `WithBot ℕ` coerces: `n • (x : WithBot ℕ) = ↑(n * x)`. -/
theorem nsmul_coe_withBot (n x : ℕ) :
    n • (WithBot.some x : WithBot ℕ) = WithBot.some (n * x) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul, ih]
      have : WithBot.some (k * x) + WithBot.some x = WithBot.some (k * x + x) := rfl
      rw [this]
      congr 1
      ring

/-- **The per-term decomposition engine.** `StructuredSuccTermBound` reduces to pure
`ℕ`-arithmetic: given a ξ-weight budget (`weight_ξ_bound`'s output), a B-coefficient
budget (the E1′ inventory's output), and the closing inequality (finding 8's
hand-verified bookkeeping), the per-term bound holds. All weight-calculus steps —
the three `_mul_le` splits, the two `_pow_le` powers, `_W`, and the PROVEN structured
partition product — are discharged here once and for all. -/
theorem structuredSuccTermBound_of_budgets (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (k : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (structuredBound H R D l))
    (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts)
    {Lξ nB : ℕ}
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ WithBot.some Lξ)
    (hB : weight_Λ_over_𝒪 hH (B_coeff H x₀ R i1 lam) D ≤ WithBot.some nB)
    (hξDef : Lξ = (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))
    (harith :
      (i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree
        + (2 * i1 + sigmaLambda lam - 2) * Lξ
        + nB
        + (sigmaLambda lam
            + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (2 * (k + 1 - i1) - sigmaLambda lam) * Lξ)
      ≤ structuredBound H R D (k + 1)) :
    StructuredSuccTermBound x₀ R hHyp hH D k hIH i1 hi1 lam hlam := by
  unfold StructuredSuccTermBound
  -- three multiplicative splits
  refine le_trans (weight_Λ_over_𝒪_mul_le H hH hDH _ _) ?_
  refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) le_rfl) ?_
  refine le_trans (add_le_add
    (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) le_rfl) le_rfl) ?_
  -- bound the four factors
  have hW : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)) D
      ≤ WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree) := by
    refine le_trans (weight_Λ_over_𝒪_pow_le H hH hDH _ _) ?_
    refine le_trans (nsmul_le_nsmul_right (weight_Λ_over_𝒪_W H hH hDH) _) ?_
    rw [nsmul_coe_withBot]
  have hXi : weight_Λ_over_𝒪 hH
      ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)) D
      ≤ WithBot.some ((2 * i1 + sigmaLambda lam - 2) * Lξ) := by
    refine le_trans (weight_Λ_over_𝒪_pow_le H hH hDH _ _) ?_
    refine le_trans (nsmul_le_nsmul_right hξ _) ?_
    rw [nsmul_coe_withBot]
  have hPi : weight_Λ_over_𝒪 hH
      (partitionProd lam (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
      ≤ WithBot.some (sigmaLambda lam
          + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
          + (2 * (k + 1 - i1) - sigmaLambda lam) * Lξ) := by
    refine partitionProd_βHensel_weight_structured_le H x₀ R hHyp hH hDH k i1
      (H.leadingCoeff).natDegree Lξ ?_ lam hlam
    intro l hl
    have := hIH l hl
    unfold structuredBound at this
    rwa [← hξDef] at this
  refine le_trans (add_le_add (add_le_add (add_le_add hW hXi) hB) hPi) ?_
  have hsum : (WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree)
        + WithBot.some ((2 * i1 + sigmaLambda lam - 2) * Lξ)
        + WithBot.some nB
        + WithBot.some (sigmaLambda lam
            + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (2 * (k + 1 - i1) - sigmaLambda lam) * Lξ))
      = WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree
          + (2 * i1 + sigmaLambda lam - 2) * Lξ
          + nB
          + (sigmaLambda lam
              + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
              + (2 * (k + 1 - i1) - sigmaLambda lam) * Lξ)) := rfl
  rw [hsum]
  exact WithBot.coe_le_coe.mpr harith

/-! ## The closing inequality (transcription step (iv), finding 8) -/

/-- **The closing `ℕ`-inequality** (finding 8's bookkeeping): the engine's `harith`
hypothesis follows from the single reduced need `nB + (m−1) + (δ+m−2)·degW ≤ Lξ` — the
exponent totals collapse (`ξ`-total `= 2k` for every case; `W`-total `= k+δ+m`), and the
excess `(δ+m−1)`-fold `degW`/unit mass is paid from the `Lξ` headroom. Truncation safety:
`i1 = 0` forces `m ≥ 2` (the surviving-partition fact), `m ≤ S` (parts are positive). -/
theorem harith_of_reduced {i1 k m δ degW Lξ nB : ℕ}
    (hδ : δ = if i1 = 0 then 1 else 0)
    (hm2 : i1 = 0 → 2 ≤ m)
    (hm1 : 1 ≤ m)
    (hi1k : i1 ≤ k + 1)
    (hmS : m ≤ k + 1 - i1)
    (hreduced : nB + (m - 1) + (δ + m - 2) * degW ≤ Lξ) :
    (i1 + δ - 1) * degW + (2 * i1 + m - 2) * Lξ + nB
        + (m + ((k + 1 - i1) + m) * degW + (2 * (k + 1 - i1) - m) * Lξ)
      ≤ 1 + (k + 2) * degW + (2 * (k + 1) - 1) * Lξ := by
  rcases Nat.eq_zero_or_pos i1 with hi0 | hi1pos
  · -- `i1 = 0`, `δ = 1`
    subst hi0
    have hδ1 : δ = 1 := by simpa using hδ
    subst hδ1
    have hm2' : 2 ≤ m := hm2 rfl
    -- truncations: (0+1−1) = 0; (0+m−2) = m−2; S = k+1; (2(k+1)−m) genuine since m ≤ k+1
    have h1 : (0 + 1 - 1) * degW = 0 := by norm_num
    have h2 : 2 * 0 + m - 2 = m - 2 := by omega
    have h3 : k + 1 - 0 = k + 1 := by omega
    rw [h1, h2, h3]
    have hred : nB + (m - 1) + (1 + m - 2) * degW ≤ Lξ := hreduced
    have hexp : (1 : ℕ) + m - 2 = m - 1 := by omega
    rw [hexp] at hred
    -- ξ-total: (m−2) + (2(k+1)−m) = 2k; target ξ: 2(k+1)−1 = 2k+1
    have hxi : (m - 2) + (2 * (k + 1) - m) = 2 * k := by omega
    have htgt : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [htgt]
    -- W-total: (k+1+m); excess over (k+2) is (m−1)
    have hWsplit : ((k + 1) + m) * degW = (k + 2) * degW + (m - 1) * degW := by
      have : (k + 1) + m = (k + 2) + (m - 1) := by omega
      rw [this, add_mul]
    have hLsplit : (2 * k + 1) * Lξ = 2 * k * Lξ + Lξ := by ring
    have hxisplit : (m - 2) * Lξ + (2 * (k + 1) - m) * Lξ = 2 * k * Lξ := by
      rw [← add_mul, hxi]
    -- assemble
    calc 0 + (m - 2) * Lξ + nB + (m + ((k + 1) + m) * degW + (2 * (k + 1) - m) * Lξ)
        = (nB + (m - 1) + (m - 1) * degW) + 1 + (k + 2) * degW
            + ((m - 2) * Lξ + (2 * (k + 1) - m) * Lξ) := by
          rw [hWsplit]
          omega
      _ = (nB + (m - 1) + (m - 1) * degW) + 1 + (k + 2) * degW + 2 * k * Lξ := by
          rw [hxisplit]
      _ ≤ Lξ + 1 + (k + 2) * degW + 2 * k * Lξ := by
          have := hred
          omega
      _ = 1 + (k + 2) * degW + (2 * k * Lξ + Lξ) := by ring
      _ = 1 + (k + 2) * degW + (2 * k + 1) * Lξ := by rw [← hLsplit]
  · -- `i1 ≥ 1`, `δ = 0`
    have hδ0 : δ = 0 := by
      rw [hδ]
      simp [Nat.pos_iff_ne_zero.mp hi1pos]
    subst hδ0
    have h1 : i1 + 0 - 1 = i1 - 1 := by omega
    rw [h1]
    have hred : nB + (m - 1) + (0 + m - 2) * degW ≤ Lξ := hreduced
    have hexp : (0 : ℕ) + m - 2 = m - 2 := by omega
    rw [hexp] at hred
    have htgt : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [htgt]
    -- W-total: (i1−1) + (k+1−i1+m) = k+m; excess over (k+2) requires care at m ≤ 1:
    -- for m = 1 the W-total is k+1 ≤ k+2 outright and the ξ-headroom is untouched.
    have hxi : (2 * i1 + m - 2) + (2 * (k + 1 - i1) - m) = 2 * k := by omega
    have hxisplit : (2 * i1 + m - 2) * Lξ + (2 * (k + 1 - i1) - m) * Lξ
        = 2 * k * Lξ := by rw [← add_mul, hxi]
    have hWtotal : (i1 - 1) * degW + ((k + 1 - i1) + m) * degW
        = (k + m) * degW := by
      rw [← add_mul]
      congr 1
      omega
    rcases Nat.lt_or_ge m 2 with hmlt | hmge
    · -- m = 1: W-total = k+1 ≤ k+2, ξ untouched, reduced gives nB ≤ Lξ
      have hm1' : m = 1 := by omega
      subst hm1'
      have hWle : (k + 1) * degW ≤ (k + 2) * degW :=
        Nat.mul_le_mul_right _ (by omega)
      have hnB : nB ≤ Lξ := by
        have := hred
        omega
      calc (i1 - 1) * degW + (2 * i1 + 1 - 2) * Lξ + nB
            + (1 + ((k + 1 - i1) + 1) * degW + (2 * (k + 1 - i1) - 1) * Lξ)
          = (k + 1) * degW + 2 * k * Lξ + nB + 1 := by
            rw [← hxisplit]
            have := hWtotal
            omega
        _ ≤ (k + 2) * degW + 2 * k * Lξ + Lξ + 1 := by
            have := hWle
            have := hnB
            omega
        _ = 1 + (k + 2) * degW + (2 * k + 1) * Lξ := by ring
    · -- m ≥ 2: split the W-excess (m−2)·degW and pay from Lξ
      have hWsplit : (k + m) * degW = (k + 2) * degW + (m - 2) * degW := by
        have : k + m = (k + 2) + (m - 2) := by omega
        rw [this, add_mul]
      calc (i1 - 1) * degW + (2 * i1 + m - 2) * Lξ + nB
            + (m + ((k + 1 - i1) + m) * degW + (2 * (k + 1 - i1) - m) * Lξ)
          = (nB + (m - 1) + (m - 2) * degW) + 1 + (k + 2) * degW + 2 * k * Lξ := by
            rw [← hxisplit]
            have h := hWtotal
            have h2 := hWsplit
            omega
        _ ≤ Lξ + 1 + (k + 2) * degW + 2 * k * Lξ := by
            have := hred
            omega
        _ = 1 + (k + 2) * degW + (2 * k + 1) * Lξ := by ring

/-- **The closing inequality at the top boundary** `i1 = k + 1` (the empty partition,
`m = 0` — the only case with no parts, since partitions of positive numbers have parts):
the per-term reduces to `nB ≤ Lξ` with room to spare. -/
theorem harith_of_reduced_top {k degW Lξ nB : ℕ} (hnB : nB ≤ Lξ) :
    ((k + 1) + 0 - 1) * degW + (2 * (k + 1) + 0 - 2) * Lξ + nB
        + (0 + ((k + 1 - (k + 1)) + 0) * degW + (2 * (k + 1 - (k + 1)) - 0) * Lξ)
      ≤ 1 + (k + 2) * degW + (2 * (k + 1) - 1) * Lξ := by
  have h1 : (k + 1) + 0 - 1 = k := by omega
  have h2 : 2 * (k + 1) + 0 - 2 = 2 * k := by omega
  have h3 : k + 1 - (k + 1) = 0 := by omega
  rw [h1, h2, h3]
  have htgt : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [htgt]
  have hW : k * degW ≤ (k + 2) * degW := Nat.mul_le_mul_right _ (by omega)
  have hL : (2 * k + 1) * Lξ = 2 * k * Lξ + Lξ := by ring
  calc k * degW + 2 * k * Lξ + nB + (0 + 0 * degW + 0 * Lξ)
      = k * degW + 2 * k * Lξ + nB := by ring_nf
    _ ≤ (k + 2) * degW + 2 * k * Lξ + Lξ := by
        have := hW
        have := hnB
        omega
    _ ≤ 1 + (k + 2) * degW + (2 * k * Lξ + Lξ) := by omega
    _ = 1 + (k + 2) * degW + (2 * k + 1) * Lξ := by rw [← hL]

/-! ## The threaded per-term theorem: `StructuredSuccTermBound` from the B-budget alone -/

/-- **The per-term theorem, threaded** (engine + closing inequality + partition facts):
`StructuredSuccTermBound` holds given only the ξ-budget (the proven `weight_ξ_bound`'s
output shape) and a B-budget meeting finding 8's reduced need. The partition facts
(`m ≥ 1` when the partition is of a positive number; `m ≥ 2` at `i1 = 0` from the
surviving-partition hypothesis; the top boundary `i1 = k+1` with the empty partition)
are derived inline from `parts_pos`/`parts_sum`. -/
theorem structuredSuccTermBound_of_B_budget (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (k : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (structuredBound H R D l))
    (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts)
    {nB : ℕ}
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
      ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (hB : weight_Λ_over_𝒪 hH (B_coeff H x₀ R i1 lam) D ≤ WithBot.some nB)
    (hreduced : nB + (sigmaLambda lam - 1)
        + (deltaSave i1 + sigmaLambda lam - 2) * (H.leadingCoeff).natDegree
      ≤ (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) :
    StructuredSuccTermBound x₀ R hHyp hH D k hIH i1 hi1 lam hlam := by
  classical
  have hi1le : i1 ≤ k + 1 := by
    have := Finset.mem_range.mp hi1
    omega
  refine structuredSuccTermBound_of_budgets x₀ R hHyp hH hDH k hIH i1 hi1 lam hlam
    hξ hB rfl ?_
  unfold structuredBound
  rcases Nat.eq_or_lt_of_le hi1le with htop | hlt
  · -- `i1 = k + 1`: the empty partition
    subst htop
    have hm0 : sigmaLambda lam = 0 := by
      rw [sigmaLambda]
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hne)
      have hpos := lam.parts_pos ha
      have hsum := lam.parts_sum
      have hle : a ≤ lam.parts.sum := Multiset.le_sum_of_mem ha
      omega
    have hδ : deltaSave (k + 1) = 0 := by
      rw [deltaSave]
      simp
    rw [hm0, hδ]
    have hred : nB ≤ (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) := by
      have := hreduced
      omega
    exact harith_of_reduced_top hred
  · -- `i1 ≤ k`: nonempty partition
    have hpos : 0 < k + 1 - i1 := by omega
    have hm1 : 1 ≤ sigmaLambda lam := by
      rw [sigmaLambda]
      by_contra hne
      have hempty : lam.parts = 0 := Multiset.card_eq_zero.mp (by omega)
      have hsum := lam.parts_sum
      rw [hempty] at hsum
      simp at hsum
      omega
    have hm2 : i1 = 0 → 2 ≤ sigmaLambda lam := by
      intro hi0
      subst hi0
      by_contra hne
      have hm1' : Multiset.card lam.parts = 1 := by
        rw [sigmaLambda] at hm1 hne
        omega
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hm1'
      have hsum := lam.parts_sum
      rw [ha] at hsum
      simp at hsum
      apply hlam
      rw [ha]
      have hone : a = k + 1 := by omega
      rw [hone] at *
      exact Multiset.mem_singleton_self _
    have hmS : sigmaLambda lam ≤ k + 1 - i1 := by
      rw [sigmaLambda]
      calc Multiset.card lam.parts
          = (lam.parts.map (fun _ => 1)).sum := by simp
        _ ≤ (lam.parts.map id).sum := Multiset.sum_map_le_sum_map _ _
            (fun l hl => lam.parts_pos hl)
        _ = lam.parts.sum := by simp
        _ = k + 1 - i1 := lam.parts_sum
    have hδdef : deltaSave i1 = if i1 = 0 then 1 else 0 := by
      rw [deltaSave]
    refine harith_of_reduced hδdef hm2 hm1 hi1le hmS ?_
    have := hreduced
    rw [hδdef] at this
    exact this

/-! ## The closing inequality, rebased (B₀-weighted; subsumes the `B₀ = 1` case) -/

/-- **The generalized closing inequality** (finding 12's rebased frame): with the rebased
IH constant `B₀` (the structured case is `B₀ = 1`; the monisized-`H̃` case is
`B₀ = D+1−d_H`), the per-term bound at order `k+1` follows from the single reduced need
`nB + (m−1)·B₀ + (δ+m−2)·degW ≤ Lξ`. Same exponent collapses as `harith_of_reduced`
(ξ-total `2k`, W-total `k+δ+m`); the `B₀`-mass `m·B₀` splits as `(m−1)·B₀ + B₀` with the
excess paid from `Lξ` via the reduced need. -/
theorem harith_of_reduced_general {i1 k m δ degW Lξ nB B0 : ℕ}
    (hδ : δ = if i1 = 0 then 1 else 0)
    (hm2 : i1 = 0 → 2 ≤ m)
    (hm1 : 1 ≤ m)
    (hi1k : i1 ≤ k + 1)
    (hmS : m ≤ k + 1 - i1)
    (hreduced : nB + (m - 1) * B0 + (δ + m - 2) * degW ≤ Lξ) :
    (i1 + δ - 1) * degW + (2 * i1 + m - 2) * Lξ + nB
        + (m * B0 + ((k + 1 - i1) + m) * degW + (2 * (k + 1 - i1) - m) * Lξ)
      ≤ B0 + (k + 2) * degW + (2 * (k + 1) - 1) * Lξ := by
  have htgt : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [htgt]
  rcases Nat.eq_zero_or_pos i1 with hi0 | hi1pos
  · -- `i1 = 0`, `δ = 1`
    subst hi0
    have hδ1 : δ = 1 := by simpa using hδ
    subst hδ1
    have hm2' : 2 ≤ m := hm2 rfl
    have h1 : (0 : ℕ) + 1 - 1 = 0 := by omega
    have h2 : 2 * 0 + m - 2 = m - 2 := by omega
    have h3 : k + 1 - 0 = k + 1 := by omega
    rw [h1, h2, h3]
    have hred : nB + (m - 1) * B0 + (m - 1) * degW ≤ Lξ := by
      have := hreduced
      have hexp : (1 : ℕ) + m - 2 = m - 1 := by omega
      rwa [hexp] at this
    have hxisplit : (m - 2) * Lξ + (2 * (k + 1) - m) * Lξ = 2 * k * Lξ := by
      rw [← add_mul]
      congr 1
      omega
    have hWsplit : ((k + 1) + m) * degW = (k + 2) * degW + (m - 1) * degW := by
      have : (k + 1) + m = (k + 2) + (m - 1) := by omega
      rw [this, add_mul]
    have hB0split : m * B0 = (m - 1) * B0 + B0 := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [add_mul, one_mul]
    calc 0 * degW + (m - 2) * Lξ + nB
          + (m * B0 + ((k + 1) + m) * degW + (2 * (k + 1) - m) * Lξ)
        = m * B0 + (((k + 1) + m) * degW
            + ((m - 2) * Lξ + (2 * (k + 1) - m) * Lξ) + nB) := by ring
      _ = ((m - 1) * B0 + B0) + (((k + 2) * degW + (m - 1) * degW)
            + 2 * k * Lξ + nB) := by rw [hWsplit, hB0split, hxisplit]
      _ = (nB + (m - 1) * B0 + (m - 1) * degW) + B0 + (k + 2) * degW + 2 * k * Lξ := by
          ring
      _ ≤ Lξ + B0 + (k + 2) * degW + 2 * k * Lξ := by
          have := hred
          omega
      _ ≤ B0 + (k + 2) * degW + (2 * k + 1) * Lξ := by
          have : (2 * k + 1) * Lξ = 2 * k * Lξ + Lξ := by ring
          omega
  · -- `i1 ≥ 1`, `δ = 0`
    have hδ0 : δ = 0 := by
      rw [hδ]
      simp [Nat.pos_iff_ne_zero.mp hi1pos]
    subst hδ0
    have h1 : i1 + 0 - 1 = i1 - 1 := by omega
    rw [h1]
    have hxisplit : (2 * i1 + m - 2) * Lξ + (2 * (k + 1 - i1) - m) * Lξ
        = 2 * k * Lξ := by
      rw [← add_mul]
      congr 1
      omega
    have hWtotal : (i1 - 1) * degW + ((k + 1 - i1) + m) * degW
        = (k + m) * degW := by
      rw [← add_mul]
      congr 1
      omega
    rcases Nat.lt_or_ge m 2 with hmlt | hmge
    · -- `m = 1`
      have hm1' : m = 1 := by omega
      subst hm1'
      have hred : nB ≤ Lξ := by
        have := hreduced
        omega
      have hWle : (k + 1) * degW ≤ (k + 2) * degW :=
        Nat.mul_le_mul_right _ (by omega)
      calc (i1 - 1) * degW + (2 * i1 + 1 - 2) * Lξ + nB
            + (1 * B0 + ((k + 1 - i1) + 1) * degW + (2 * (k + 1 - i1) - 1) * Lξ)
          = (k + 1) * degW + 2 * k * Lξ + nB + B0 := by
            rw [← hxisplit]
            have := hWtotal
            omega
        _ ≤ (k + 2) * degW + 2 * k * Lξ + Lξ + B0 := by
            have := hWle
            have := hred
            omega
        _ ≤ B0 + (k + 2) * degW + (2 * k + 1) * Lξ := by
            have : (2 * k + 1) * Lξ = 2 * k * Lξ + Lξ := by ring
            omega
    · -- `m ≥ 2`
      have hred : nB + (m - 1) * B0 + (m - 2) * degW ≤ Lξ := by
        have := hreduced
        have hexp : (0 : ℕ) + m - 2 = m - 2 := by omega
        rwa [hexp] at this
      have hWsplit : (k + m) * degW = (k + 2) * degW + (m - 2) * degW := by
        have : k + m = (k + 2) + (m - 2) := by omega
        rw [this, add_mul]
      have hB0split : m * B0 = (m - 1) * B0 + B0 := by
        conv_lhs => rw [show m = (m - 1) + 1 from by omega]
        rw [add_mul, one_mul]
      have hW2 : (i1 - 1) * degW + ((k + 1 - i1) + m) * degW
          = (k + 2) * degW + (m - 2) * degW := by
        rw [← add_mul]
        have : (i1 - 1) + ((k + 1 - i1) + m) = (k + 2) + (m - 2) := by omega
        rw [this, add_mul]
      calc (i1 - 1) * degW + (2 * i1 + m - 2) * Lξ + nB
            + (m * B0 + ((k + 1 - i1) + m) * degW + (2 * (k + 1 - i1) - m) * Lξ)
          = ((i1 - 1) * degW + ((k + 1 - i1) + m) * degW)
              + ((2 * i1 + m - 2) * Lξ + (2 * (k + 1 - i1) - m) * Lξ)
              + nB + m * B0 := by ring
        _ = ((k + 2) * degW + (m - 2) * degW) + 2 * k * Lξ + nB
              + ((m - 1) * B0 + B0) := by rw [hW2, hxisplit, hB0split]
        _ = (nB + (m - 1) * B0 + (m - 2) * degW) + B0 + (k + 2) * degW + 2 * k * Lξ := by
            ring
        _ ≤ Lξ + B0 + (k + 2) * degW + 2 * k * Lξ := by
            have := hred
            omega
        _ ≤ B0 + (k + 2) * degW + (2 * k + 1) * Lξ := by
            have : (2 * k + 1) * Lξ = 2 * k * Lξ + Lξ := by ring
            omega

/-- **The generalized top boundary** `i1 = k+1` (empty partition, `m = 0`): reduces to
`nB ≤ Lξ` with slack `B₀ + 2·degW`. -/
theorem harith_of_reduced_top_general {k degW Lξ nB B0 : ℕ} (hnB : nB ≤ Lξ) :
    ((k + 1) + 0 - 1) * degW + (2 * (k + 1) + 0 - 2) * Lξ + nB
        + (0 * B0 + ((k + 1 - (k + 1)) + 0) * degW + (2 * (k + 1 - (k + 1)) - 0) * Lξ)
      ≤ B0 + (k + 2) * degW + (2 * (k + 1) - 1) * Lξ := by
  have h1 : (k + 1) + 0 - 1 = k := by omega
  have h2 : 2 * (k + 1) + 0 - 2 = 2 * k := by omega
  have h3 : k + 1 - (k + 1) = 0 := by omega
  rw [h1, h2, h3]
  have htgt : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [htgt]
  have hW : k * degW ≤ (k + 2) * degW := Nat.mul_le_mul_right _ (by omega)
  calc k * degW + 2 * k * Lξ + nB + (0 * B0 + 0 * degW + 0 * Lξ)
      = k * degW + 2 * k * Lξ + nB := by ring_nf
    _ ≤ (k + 2) * degW + 2 * k * Lξ + Lξ + B0 := by
        have := hW
        have := hnB
        omega
    _ ≤ B0 + (k + 2) * degW + (2 * k + 1) * Lξ := by
        have : (2 * k + 1) * Lξ = 2 * k * Lξ + Lξ := by ring
        omega

/-! ## The rebased per-term apparatus: sum evaluation, partition product, threading -/

/-- **The `B₀`-generic structured telescoping** (mirrors the in-tree
`sum_map_structured`): for positive parts,
`∑_{l ∈ parts} (B₀ + (l+1)·w + (2l−1)·x) = card·B₀ + (sum+card)·w + (2·sum−card)·x`. -/
theorem sum_map_structured_general (ms : Multiset ℕ) (B0 w x : ℕ)
    (hpos : ∀ l ∈ ms, 1 ≤ l) :
    (ms.map (fun l => B0 + (l + 1) * w + (2 * l - 1) * x)).sum
      = Multiset.card ms * B0 + (ms.sum + Multiset.card ms) * w
        + (2 * ms.sum - Multiset.card ms) * x := by
  induction ms using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 1 ≤ a := hpos a (Multiset.mem_cons_self a s)
      have hs : ∀ l ∈ s, 1 ≤ l := fun l hl => hpos l (Multiset.mem_cons_of_mem hl)
      rw [Multiset.map_cons, Multiset.sum_cons, ih hs, Multiset.sum_cons,
        Multiset.card_cons]
      have hcard_le : Multiset.card s ≤ s.sum := by
        have h := Multiset.sum_map_le_sum_map (s := s) (fun _ => 1) id
          (fun l hl => hs l hl)
        simpa using h
      have hsplit1 : (Multiset.card s + 1) * B0 = Multiset.card s * B0 + B0 := by
        rw [add_mul, one_mul]
      have hsplit2 : (a + s.sum + (Multiset.card s + 1)) * w
          = (a + 1) * w + (s.sum + Multiset.card s) * w := by
        rw [← add_mul]
        congr 1
        omega
      have hsplit3 : (2 * (a + s.sum) - (Multiset.card s + 1)) * x
          = (2 * a - 1) * x + (2 * s.sum - Multiset.card s) * x := by
        rw [← add_mul]
        congr 1
        omega
      rw [hsplit1, hsplit2, hsplit3]
      ring

/-- **The rebased structured partition-product bound** (mirrors the in-tree
`partitionProd_βHensel_weight_structured_le` with the `B₀`-generic IH): given
`hIH : ∀ l < k+1, Λ_𝒪(β_l) ≤ B₀ + (l+1)·wW + (2l−1)·xξ`, the partition product is
`≤ Σλ·B₀ + ((k+1−i1)+Σλ)·wW + (2(k+1−i1)−Σλ)·xξ`. -/
theorem partitionProd_βHensel_weight_rebased_le (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (k i1 : ℕ) (B0 wW xξ : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (B0 + (l + 1) * wW + (2 * l - 1) * xξ))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts) :
    weight_Λ_over_𝒪 hH
        (partitionProd lam (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
      ≤ WithBot.some
          (sigmaLambda lam * B0 + ((k + 1 - i1) + sigmaLambda lam) * wW
            + (2 * (k + 1 - i1) - sigmaLambda lam) * xξ) := by
  classical
  have hcongr : partitionProd lam
      (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (fun l => βHensel H x₀ R hHyp l) := by
    exact partitionProd_surviving_guard lam hlam (fun l => βHensel H x₀ R hHyp l) 0
  rw [hcongr]
  refine le_trans (partitionProd_weight_le H hH hDH lam
    (fun l => βHensel H x₀ R hHyp l)) ?_
  have hkey : (lam.parts.map (fun l => weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D)).sum
      ≤ WithBot.some
          ((lam.parts.map (fun l => B0 + (l + 1) * wW + (2 * l - 1) * xξ)).sum) := by
    have hmem : ∀ l ∈ lam.parts,
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some (B0 + (l + 1) * wW + (2 * l - 1) * xξ) :=
      fun l hl => hIH l (surviving_parts_lt lam hlam hl)
    revert hmem
    generalize lam.parts = ms
    intro hmem
    induction ms using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
          WithBot.coe_add]
        refine add_le_add (hmem a (Multiset.mem_cons_self a s)) ?_
        exact ih (fun l hl => hmem l (Multiset.mem_cons_of_mem hl))
  refine le_trans hkey ?_
  rw [sum_map_structured_general lam.parts B0 wW xξ (fun l hl => lam.parts_pos hl)]
  rw [lam.parts_sum, sigmaLambda, show Multiset.card lam.parts = lam.parts.card from rfl]

/-- **The threaded REBASED per-term theorem**: the `hterm` obligation of
`βHensel_weight_bound_rebased` holds given only the ξ-budget (= the proven
`weight_ξ_bound`), a B-budget, and the rebased reduced need
`nB + (m−1)·B₀ + (δ+m−2)·degW ≤ Lξ` (finding 12's frame; partition facts derived
inline; both `harith` boundaries covered). -/
theorem rebasedSuccTermBound_of_B_budget (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (k : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (structuredBoundRebased H R D l))
    (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts)
    {nB : ℕ}
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
      ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (hB : weight_Λ_over_𝒪 hH (B_coeff H x₀ R i1 lam) D ≤ WithBot.some nB)
    (hreduced : nB + (sigmaLambda lam - 1) * (D + 1 - Bivariate.natDegreeY H)
        + (deltaSave i1 + sigmaLambda lam - 2) * (H.leadingCoeff).natDegree
      ≤ (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) :
    weight_Λ_over_𝒪 hH
        ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * B_coeff H x₀ R i1 lam
          * partitionProd lam
              (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
      ≤ WithBot.some (structuredBoundRebased H R D (k + 1)) := by
  classical
  have hi1le : i1 ≤ k + 1 := by
    have := Finset.mem_range.mp hi1
    omega
  -- decompose the term and bound the four factors
  refine le_trans (weight_Λ_over_𝒪_mul_le H hH hDH _ _) ?_
  refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) le_rfl) ?_
  refine le_trans (add_le_add
    (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) le_rfl) le_rfl) ?_
  have hW : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)) D
      ≤ WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree) := by
    refine le_trans (weight_Λ_over_𝒪_pow_le H hH hDH _ _) ?_
    exact nsmul_withBot_le _ _ (weight_Λ_over_𝒪_W H hH hDH)
  have hXi : weight_Λ_over_𝒪 hH
      ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)) D
      ≤ WithBot.some ((2 * i1 + sigmaLambda lam - 2)
          * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine le_trans (weight_Λ_over_𝒪_pow_le H hH hDH _ _) ?_
    exact nsmul_withBot_le _ _ hξ
  have hPi : weight_Λ_over_𝒪 hH
      (partitionProd lam (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
      ≤ WithBot.some (sigmaLambda lam * (D + 1 - Bivariate.natDegreeY H)
          + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
          + (2 * (k + 1 - i1) - sigmaLambda lam)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine partitionProd_βHensel_weight_rebased_le x₀ R hHyp hH hDH k i1
      (D + 1 - Bivariate.natDegreeY H) (H.leadingCoeff).natDegree
      ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) ?_ lam hlam
    intro l hl
    have := hIH l hl
    unfold structuredBoundRebased at this
    exact this
  refine le_trans (add_le_add (add_le_add (add_le_add hW hXi) hB) hPi) ?_
  have hsum : (WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree)
        + WithBot.some ((2 * i1 + sigmaLambda lam - 2)
            * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
        + WithBot.some nB
        + WithBot.some (sigmaLambda lam * (D + 1 - Bivariate.natDegreeY H)
            + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (2 * (k + 1 - i1) - sigmaLambda lam)
                * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))))
      = WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree
          + (2 * i1 + sigmaLambda lam - 2)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))
          + nB
          + (sigmaLambda lam * (D + 1 - Bivariate.natDegreeY H)
              + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
              + (2 * (k + 1 - i1) - sigmaLambda lam)
                  * ((Bivariate.natDegreeY R - 1)
                      * (D - Bivariate.natDegreeY H + 1)))) := rfl
  rw [hsum]
  refine WithBot.coe_le_coe.mpr ?_
  unfold structuredBoundRebased
  -- dispatch by partition shape through the generalized closing inequalities
  rcases Nat.eq_or_lt_of_le hi1le with htop | hlt
  · -- `i1 = k+1`: empty partition
    subst htop
    have hm0 : sigmaLambda lam = 0 := by
      rw [sigmaLambda]
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hne)
      have hpos := lam.parts_pos ha
      have hsum' := lam.parts_sum
      have hle : a ≤ lam.parts.sum := Multiset.le_sum_of_mem ha
      omega
    have hδ : deltaSave (k + 1) = 0 := by
      rw [deltaSave]
      simp
    rw [hm0, hδ]
    have hred : nB ≤ (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) := by
      have := hreduced
      omega
    exact harith_of_reduced_top_general hred
  · -- `i1 ≤ k`: nonempty partition
    have hpos : 0 < k + 1 - i1 := by omega
    have hm1 : 1 ≤ sigmaLambda lam := by
      rw [sigmaLambda]
      by_contra hne
      have hempty : lam.parts = 0 := Multiset.card_eq_zero.mp (by omega)
      have hsum' := lam.parts_sum
      rw [hempty] at hsum'
      simp at hsum'
      omega
    have hm2 : i1 = 0 → 2 ≤ sigmaLambda lam := by
      intro hi0
      subst hi0
      by_contra hne
      have hm1' : Multiset.card lam.parts = 1 := by
        rw [sigmaLambda] at hm1 hne
        omega
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hm1'
      have hsum' := lam.parts_sum
      rw [ha] at hsum'
      simp at hsum'
      apply hlam
      rw [ha]
      have hone : a = k + 1 := by omega
      rw [hone] at *
      exact Multiset.mem_singleton_self _
    have hmS : sigmaLambda lam ≤ k + 1 - i1 := by
      rw [sigmaLambda]
      calc Multiset.card lam.parts
          = (lam.parts.map (fun _ => 1)).sum := by simp
        _ ≤ (lam.parts.map id).sum := Multiset.sum_map_le_sum_map _ _
            (fun l hl => lam.parts_pos hl)
        _ = lam.parts.sum := by simp
        _ = k + 1 - i1 := lam.parts_sum
    have hδdef : deltaSave i1 = if i1 = 0 then 1 else 0 := by
      rw [deltaSave]
    refine harith_of_reduced_general hδdef hm2 hm1 hi1le hmS ?_
    have := hreduced
    rwa [hδdef] at this

/-! ## The ANCHORED engine (finding 13 / DISPROOF_LOG O155)

At the paper's anchor `D = d_H + deg W` (the operating point where BCIKS20 A.2/A.4's weight
ledger is exact, `Λ(T) = Λ(W) + 1`), every `i1 ≥ 1` cell and every zero cell of the (A.1)
recursion discharges UNCONDITIONALLY from the landed budget supplier
(`hasseCoeffRepr𝒪_weight_le_of_total`); the `i1 = 0` cells — whose paper treatment uses the
δ-saving of the W-TWISTED clearing, a different `B`-normalization than the in-tree
`Y ↦ T` transcription — remain the single per-term obligation. -/

/-- `Δ_Y^m R = 0` once the Hasse order exceeds the `Y`-degree. -/
theorem hasseDerivY_eq_zero_of_natDegreeY_lt (R : F[X][X][Y]) {m : ℕ}
    (hm : Bivariate.natDegreeY R < m) : hasseDerivY m R = 0 := by
  refine Polynomial.ext fun j => ?_
  rw [hasseDerivY_coeff_cast, Polynomial.coeff_zero]
  have hz : R.coeff (j + m) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by
      have hYd : Bivariate.natDegreeY R = R.natDegree := rfl
      omega)
  rw [hz, mul_zero]

/-- The cell coefficient `B_{i1,λ}` vanishes once the partition card exceeds the
`Y`-degree of `R` (Hasse order beyond the degree): the genuine zero cells. -/
theorem B_coeff_eq_zero_of_natDegreeY_lt (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (hm : Bivariate.natDegreeY R < sigmaLambda lam) :
    B_coeff H x₀ R i1 lam = 0 := by
  rw [B_coeff, hasseCoeffRepr𝒪, hasseDerivY_eq_zero_of_natDegreeY_lt R hm]
  have hX : hasseDerivX i1 (0 : F[X][X][Y]) = 0 := by
    rw [hasseDerivX]
    exact Polynomial.sum_zero_index _
  rw [hX]
  have hE : Bivariate.evalX (Polynomial.C x₀) (0 : F[X][X][Y]) = 0 := by
    rw [Bivariate.evalX_eq_map, Polynomial.map_zero]
  rw [hE, map_zero]
  exact smul_zero _

/-- **The anchored closing arithmetic** for every `i1 ≥ 1` cell (including the top
`m = 0` cell): at the anchor `D = d_H + w` the raw per-term ledger closes with the
supplier's budget `nB = (D_R − m − i1) + (d_R − m)·w` and the proven
`Lξ = (d_R − 1)·(w + 1)`. -/
theorem harith_anchored {k i1 m DR dR dH w D Lξ nB : ℕ}
    (hi1 : 1 ≤ i1) (hi1k : i1 ≤ k + 1) (hms : m ≤ k + 1 - i1) (hmdR : m ≤ dR)
    (hdR2 : 2 ≤ dR) (hdH1 : 1 ≤ dH) (hdHdR : dH ≤ dR) (hdRDR : dR ≤ DR)
    (hD : D = dH + w) (hDR : DR ≤ D)
    (hnB : nB = (DR - m - i1) + (dR - m) * w)
    (hLξ : Lξ = (dR - 1) * (w + 1)) :
    (i1 + 0 - 1) * w + (2 * i1 + m - 2) * Lξ + nB
      + (m + ((k + 1 - i1) + m) * w + (2 * (k + 1 - i1) - m) * Lξ)
    ≤ 1 + (k + 2) * w + (2 * (k + 1) - 1) * Lξ := by
  -- collect the ξ-coefficients: they sum to exactly 2k (the BCIKS20 exponent identity)
  have hxi : (2 * i1 + m - 2) * Lξ + (2 * (k + 1 - i1) - m) * Lξ = (2 * k) * Lξ := by
    rw [← Nat.add_mul]
    congr 1
    omega
  -- collect the W-coefficients: they sum to exactly k + dR
  have hW : (i1 + 0 - 1) * w + (dR - m) * w + ((k + 1 - i1) + m) * w = (k + dR) * w := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    congr 1
    omega
  -- split the target's W- and ξ-budgets
  have hWsplit : (k + dR) * w = (k + 2) * w + (dR - 2) * w := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hxisplit : (2 * (k + 1) - 1) * Lξ = (2 * k) * Lξ + Lξ := by
    have h21 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h21, Nat.add_mul, Nat.one_mul]
  -- the residual Z-need: (DR − m − i1) + m + (dR−2)·w ≤ 1 + Lξ
  have hLexp : Lξ = (dR - 1) * w + (dR - 1) := by
    rw [hLξ, Nat.mul_add, Nat.mul_one]
  have hmerge : (dR - 2) * w + w = (dR - 1) * w := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  -- assemble
  calc (i1 + 0 - 1) * w + (2 * i1 + m - 2) * Lξ + nB
        + (m + ((k + 1 - i1) + m) * w + (2 * (k + 1 - i1) - m) * Lξ)
      = ((i1 + 0 - 1) * w + (dR - m) * w + ((k + 1 - i1) + m) * w)
          + ((2 * i1 + m - 2) * Lξ + (2 * (k + 1 - i1) - m) * Lξ)
          + ((DR - m - i1) + m) := by
        rw [hnB]; ring
    _ = (k + dR) * w + (2 * k) * Lξ + ((DR - m - i1) + m) := by rw [hW, hxi]
    _ = (k + 2) * w + (dR - 2) * w + (2 * k) * Lξ + ((DR - m - i1) + m) := by
        rw [hWsplit]
    _ ≤ (k + 2) * w + (dR - 2) * w + (2 * k) * Lξ + (dH + w) := by
        have : (DR - m - i1) + m ≤ dH + w := by omega
        omega
    _ ≤ 1 + (k + 2) * w + (2 * k) * Lξ + Lξ := by
        have h1 : (dR - 2) * w + (dH + w) ≤ 1 + Lξ := by
          have h2 : (dR - 2) * w + w = (dR - 1) * w := hmerge
          rw [hLexp]
          omega
        omega
    _ = 1 + (k + 2) * w + (2 * (k + 1) - 1) * Lξ := by rw [hxisplit]; ring

/-- **The anchored per-term discharge for `i1 ≥ 1`.** At the anchor every positive-`i1`
cell of the (A.1) recursion satisfies the structured per-term bound: zero cells
(`σλ > d_R`) via the vanishing of `B`, live cells via the landed supplier + the anchored
closing arithmetic. NO per-cell hypothesis remains. -/
theorem anchoredSuccTerm_discharge (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (k : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (structuredBound H R D l))
    (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2)) (hi1pos : 1 ≤ i1)
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts) :
    StructuredSuccTermBound x₀ R hHyp hH D k hIH i1 hi1 lam hlam := by
  by_cases hzero : Bivariate.natDegreeY R < sigmaLambda lam
  · -- the zero cell: B = 0 kills the whole term
    unfold StructuredSuccTermBound
    rw [B_coeff_eq_zero_of_natDegreeY_lt x₀ R i1 lam hzero, mul_zero, zero_mul,
      weight_Λ_over_𝒪_zero]
    exact bot_le
  · push_neg at hzero
    -- the live cell: supplier + anchored arithmetic
    have hdY : Bivariate.natDegreeY H = H.natDegree := rfl
    have hDYle : Bivariate.natDegreeY H ≤ D := by omega
    have hw : D - Bivariate.natDegreeY H = (H.leadingCoeff).natDegree := by omega
    have hδ : deltaSave i1 = 0 := by
      rw [deltaSave, if_neg (by omega : ¬ i1 = 0)]
    have hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
        ≤ WithBot.some
          ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) :=
      ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hD_Rx0
    have hB : weight_Λ_over_𝒪 hH (B_coeff H x₀ R i1 lam) D
        ≤ WithBot.some ((DR - sigmaLambda lam - i1)
            + (Bivariate.natDegreeY R - sigmaLambda lam)
              * (D - Bivariate.natDegreeY H)) :=
      le_trans (B_coeff_weight_le_hasse H x₀ R i1 lam hH hDH)
        (hasseCoeffRepr𝒪_weight_le_of_total hH hDH hDYle x₀ R htotal hvanish i1
          (sigmaLambda lam))
    have hmS : sigmaLambda lam ≤ k + 1 - i1 := by
      rw [sigmaLambda]
      calc Multiset.card lam.parts
          = (lam.parts.map (fun _ => 1)).sum := by simp
        _ ≤ (lam.parts.map id).sum := Multiset.sum_map_le_sum_map _ _
            (fun l hl => lam.parts_pos hl)
        _ = lam.parts.sum := by simp
        _ = k + 1 - i1 := lam.parts_sum
    refine structuredSuccTermBound_of_budgets x₀ R hHyp hH hDH k hIH i1 hi1 lam hlam
      hξ hB rfl ?_
    unfold structuredBound
    rw [hδ, hw]
    exact harith_anchored hi1pos (by have := Finset.mem_range.mp hi1; omega)
      hmS hzero hdR2 (by omega) hdHdR hdRDR (by omega) hDRD rfl rfl

/-- **THE ANCHORED (P1) STRUCTURED BOUND, conditional ONLY on the `i1 = 0` cells.**
At the paper's anchor every other cell is discharged; the `i1 = 0` per-term obligation
(the W-twisted δ-saving, a genuinely different `B`-normalization question) is the single
remaining hypothesis. -/
theorem βHensel_weight_bound_anchored_of_i1zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hzero : ∀ (k : ℕ)
      (hIH : ∀ l, l < k + 1 →
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some (structuredBound H R D l))
      (hi1 : 0 ∈ Finset.range (k + 2))
      (lam : Nat.Partition (k + 1 - 0)) (hlam : (k + 1) ∉ lam.parts),
        StructuredSuccTermBound x₀ R hHyp hH D k hIH 0 hi1 lam hlam)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some (structuredBound H R D t) := by
  refine βHensel_weight_bound_structured x₀ R hHyp hH hDH htight
    (fun k hIH i1 hi1 lam hlam => ?_) t
  rcases Nat.eq_zero_or_pos i1 with h0 | hpos
  · subst h0
    exact hzero k hIH hi1 lam hlam
  · exact anchoredSuccTerm_discharge x₀ R hHyp hH hDH htight hWdeg hD_Rx0 hdR2 hdHdR
      htotal hvanish hDRD hdRDR k hIH i1 hi1 hpos lam hlam

/-- **The anchored (P1) LOOSE bound** — the Claim-A.2 target `(2t+1)·d_R·D`, conditional
only on the `i1 = 0` cells, via the proven structured collapse. -/
theorem βHensel_weight_bound_anchored_loose_of_i1zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hzero : ∀ (k : ℕ)
      (hIH : ∀ l, l < k + 1 →
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some (structuredBound H R D l))
      (hi1 : 0 ∈ Finset.range (k + 2))
      (lam : Nat.Partition (k + 1 - 0)) (hlam : (k + 1) ∉ lam.parts),
        StructuredSuccTermBound x₀ R hHyp hH D k hIH 0 hi1 lam hlam)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHdR hWdeg t ?_
  have h := βHensel_weight_bound_anchored_of_i1zero x₀ R hHyp hH hDH htight hWdeg
    hD_Rx0 hdR2 hdHdR htotal hvanish hDRD hdRDR hzero t
  unfold structuredBound at h
  exact h

/-! ## The order-1 value lemma (finding 14's audit artifact) -/

/-- **`β₁ = −B_{1,∅}` (exact value).** At order 1 the (A.1) sum has exactly one surviving
cell — `i1 = 1` with the empty partition (the `i1 = 0` cell is the excluded indiscrete
`λ^{(1)}`) — so `βHensel 1 = −B_coeff 1 ∅`. This is the precise object finding 14's
normalization audit tests: the (P2) lift identity at `t = 1` is an explicit statement
about this single coefficient. -/
theorem βHensel_one (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 1
      = - B_coeff H x₀ R 1 (default : Nat.Partition 0) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, βHensel_succ]
  congr 1
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  -- the `i1 = 0` cell: the only partition of 1 is the excluded indiscrete one
  have h0 : (Finset.univ : Finset (Nat.Partition (0 + 1 - 0))).filter
      (fun lam => (0 + 1) ∉ lam.parts) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro lam _
    refine not_not_intro ?_
    have huniq : lam = (Nat.Partition.indiscrete 1 : Nat.Partition (0 + 1 - 0)) :=
      Subsingleton.elim (α := Nat.Partition 1) lam _
    rw [huniq,
      show ((Nat.Partition.indiscrete 1 : Nat.Partition (0 + 1 - 0))).parts = {1} from
        Nat.Partition.indiscrete_parts one_ne_zero]
    exact Multiset.mem_singleton_self 1
  -- the `i1 = 1` cell: the unique empty partition survives
  have h1 : (Finset.univ : Finset (Nat.Partition (0 + 1 - 1))).filter
      (fun lam => (0 + 1) ∉ lam.parts) = Finset.univ := by
    refine Finset.filter_true_of_mem ?_
    intro lam _
    have hp : lam.parts = 0 :=
      Nat.Partition.partition_zero_parts (p := lam)
    rw [hp]
    simp
  have huniv : (Finset.univ : Finset (Nat.Partition (0 + 1 - 1)))
      = {(Nat.Partition.indiscrete 0 : Nat.Partition (0 + 1 - 1))} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun x _ => ?_⟩
    exact Subsingleton.elim (α := Nat.Partition 0) x _
  rw [h0, h1, Finset.sum_empty, zero_add, huniv, Finset.sum_singleton]
  -- evaluate the surviving term: all four factors but `B` are `1`
  have hδ : deltaSave 1 = 0 := by rw [deltaSave]; simp
  have hσ : ∀ lam : Nat.Partition (0 + 1 - 1), sigmaLambda lam = 0 := fun lam => by
    rw [sigmaLambda, Nat.Partition.partition_zero_parts (p := lam)]
    rfl
  have hprod : ∀ lam : Nat.Partition (0 + 1 - 1), partitionProd lam
      (fun l => if _h : l < 0 + 1 then βHensel H x₀ R hHyp l else 0) = 1 := fun lam => by
    rw [partitionProd, Nat.Partition.partition_zero_parts (p := lam)]
    rfl
  rw [hδ, hσ, hprod]
  norm_num
  first
  | rfl
  | exact congrArg _ (Subsingleton.elim _ _)

/-! ## D-monotonicity: converting the anchored bound to any larger weight parameter

The anchored engine runs at the per-factor parameter `D₀ = d_H + degW`; downstream
consumers fix a (possibly larger) global `D`. Raising the parameter costs at most
`(d_H − 1)·(D − D₀)` on canonical representatives (T-degree ≤ d_H − 1), which the loose
target absorbs with room to spare. -/

/-- Raising the weight parameter from `D₀` to `D` costs at most `dT·(D − D₀)` for a
polynomial supported in degrees `≤ dT`. -/
theorem weight_Λ_mono_D {f H : F[X][Y]} {D₀ D dT : ℕ}
    (hdeg : ∀ b ∈ f.support, b ≤ dT) :
    weight_Λ f H D ≤ weight_Λ f H D₀ + WithBot.some (dT * (D - D₀)) := by
  unfold weight_Λ
  refine Finset.sup_le fun b hb => ?_
  have h1 : WithBot.some (b * (D₀ + 1 - Bivariate.natDegreeY H) + (f.coeff b).natDegree)
      ≤ f.support.sup (fun deg => WithBot.some
          (deg * (D₀ + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree)) :=
    Finset.le_sup (f := fun deg => WithBot.some
      (deg * (D₀ + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree)) hb
  have hb' := hdeg b hb
  have h3 : b * (D + 1 - Bivariate.natDegreeY H)
      ≤ b * (D₀ + 1 - Bivariate.natDegreeY H) + dT * (D - D₀) := by
    have hstep : D + 1 - Bivariate.natDegreeY H
        ≤ (D₀ + 1 - Bivariate.natDegreeY H) + (D - D₀) := by omega
    calc b * (D + 1 - Bivariate.natDegreeY H)
        ≤ b * ((D₀ + 1 - Bivariate.natDegreeY H) + (D - D₀)) :=
          Nat.mul_le_mul_left b hstep
      _ = b * (D₀ + 1 - Bivariate.natDegreeY H) + b * (D - D₀) := Nat.mul_add b _ _
      _ ≤ b * (D₀ + 1 - Bivariate.natDegreeY H) + dT * (D - D₀) := by
          have := Nat.mul_le_mul_right (D - D₀) hb'
          omega
  refine le_trans (WithBot.coe_le_coe.mpr
    (show b * (D + 1 - Bivariate.natDegreeY H) + (f.coeff b).natDegree
        ≤ (b * (D₀ + 1 - Bivariate.natDegreeY H) + (f.coeff b).natDegree)
          + dT * (D - D₀) by omega)) ?_
  rw [WithBot.coe_add]
  exact add_le_add h1 le_rfl

/-- The `𝒪`-weight is `D`-monotone up to `(d_H − 1)·(D − D₀)`: canonical representatives
have T-degree `≤ d_H − 1`. -/
theorem weight_Λ_over_𝒪_mono_D {H : F[X][Y]} (hH : 0 < H.natDegree) (a : 𝒪 H)
    {D₀ D : ℕ} :
    weight_Λ_over_𝒪 hH a D
      ≤ weight_Λ_over_𝒪 hH a D₀ + WithBot.some ((H.natDegree - 1) * (D - D₀)) := by
  unfold weight_Λ_over_𝒪
  refine weight_Λ_mono_D ?_
  intro b hb
  have h1 := Polynomial.le_natDegree_of_mem_supp b hb
  have hne : canonicalRepOf𝒪 hH a ≠ 0 := by
    intro h0
    rw [h0] at hb
    simp at hb
  have h2 : (canonicalRepOf𝒪 hH a).natDegree < (H_tilde' H).natDegree :=
    Polynomial.natDegree_lt_natDegree hne (canonicalRepOf𝒪_degree_lt hH a)
  have h3 := natDegree_H_tilde' hH
  omega

/-- **The anchored (P1) bound delivered at ANY consumer parameter `D ≥ D₀`** (conditional
only on the `i1 = 0` cells at the anchor `D₀`): run the anchored engine at the per-factor
`D₀ = d_H + degW`, convert upward by `D`-monotonicity, absorb the premium into the loose
target. -/
theorem βHensel_weight_bound_at_of_anchored (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D₀ D : ℕ}
    (hD₀D : D₀ ≤ D)
    (hDH : Bivariate.totalDegree H ≤ D₀)
    (htight : D₀ ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D₀)
    (hD_Rx0 : D₀ ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D₀) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hzero : ∀ (k : ℕ)
      (hIH : ∀ l, l < k + 1 →
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D₀
          ≤ WithBot.some (structuredBound H R D₀ l))
      (hi1 : 0 ∈ Finset.range (k + 2))
      (lam : Nat.Partition (k + 1 - 0)) (hlam : (k + 1) ∉ lam.parts),
        StructuredSuccTermBound x₀ R hHyp hH D₀ k hIH 0 hi1 lam hlam)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine le_trans (weight_Λ_over_𝒪_mono_D hH _ (D₀ := D₀) (D := D)) ?_
  have h := βHensel_weight_bound_anchored_loose_of_i1zero x₀ R hHyp hH hDH htight hWdeg
    hD_Rx0 hdR2 hdHdR htotal hvanish hDRD hdRDR hzero t
  refine le_trans (add_le_add h le_rfl) ?_
  rw [← WithBot.coe_add]
  refine WithBot.coe_le_coe.mpr ?_
  have hdY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hsplit : (2 * t + 1) * Bivariate.natDegreeY R * D
      = (2 * t + 1) * Bivariate.natDegreeY R * D₀
        + (2 * t + 1) * Bivariate.natDegreeY R * (D - D₀) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hcoef : (H.natDegree - 1) * (D - D₀)
      ≤ (2 * t + 1) * Bivariate.natDegreeY R * (D - D₀) := by
    refine Nat.mul_le_mul_right (D - D₀) ?_
    calc H.natDegree - 1 ≤ Bivariate.natDegreeY R := by omega
      _ ≤ (2 * t + 1) * Bivariate.natDegreeY R :=
          Nat.le_mul_of_pos_left _ (by omega)
  omega

/-! ## The capstone composition: (P1) conditional only on the per-cell B-budgets -/

/-- **The (P1) weight bound, conditional ONLY on the per-cell B-coefficient budgets.**
Composes the entire rebased apparatus: the proven `ClaimA2.weight_ξ_bound` supplies the
ξ-budget; the per-cell budget hypothesis supplies `nB` with the rebased reduced need;
`rebasedSuccTermBound_of_B_budget` (the threaded per-term theorem) discharges every cell;
`βHensel_weight_bound_rebased` (the assembled induction) closes the invariant; and the
in-tree `βHensel_weight_bound_of_structured_weight_rebased` collapses it into the loose
Claim-A.2 target `(2t+1)·d_R·D` consumed by the kill-target/Claim-5.10 chain. -/
theorem βHensel_weight_bound_of_cell_budgets (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hbudget : ∀ (k i1 : ℕ), i1 ∈ Finset.range (k + 2) →
      ∀ lam : Nat.Partition (k + 1 - i1), (k + 1) ∉ lam.parts →
      ∃ nB : ℕ,
        weight_Λ_over_𝒪 hH (B_coeff H x₀ R i1 lam) D ≤ WithBot.some nB ∧
        nB + (sigmaLambda lam - 1) * (D + 1 - Bivariate.natDegreeY H)
            + (deltaSave i1 + sigmaLambda lam - 2) * (H.leadingCoeff).natDegree
          ≤ (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine βHensel_weight_bound_of_structured_weight_rebased H x₀ R hHyp hH hdR2 hdHR hWdeg t ?_
  have hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
      ≤ WithBot.some
        ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) :=
    ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hD_Rx0
  have hcore := βHensel_weight_bound_rebased x₀ R hHyp hH hDH
    (fun k hIH i1 hi1 lam hlam => by
      obtain ⟨nB, hB, hred⟩ := hbudget k i1 hi1 lam hlam
      exact rebasedSuccTermBound_of_B_budget x₀ R hHyp hH hDH k hIH i1 hi1 lam hlam
        hξ hB hred) t
  unfold structuredBoundRebased at hcore
  exact hcore

/-! ## Source audit -/

#print axioms harith_of_reduced
#print axioms harith_of_reduced_top
#print axioms harith_of_reduced_general
#print axioms harith_of_reduced_top_general
#print axioms sum_map_structured_general
#print axioms partitionProd_βHensel_weight_rebased_le
#print axioms rebasedSuccTermBound_of_B_budget
#print axioms βHensel_weight_bound_of_cell_budgets
#print axioms hasseDerivY_eq_zero_of_natDegreeY_lt
#print axioms B_coeff_eq_zero_of_natDegreeY_lt
#print axioms harith_anchored
#print axioms anchoredSuccTerm_discharge
#print axioms βHensel_weight_bound_anchored_of_i1zero
#print axioms βHensel_weight_bound_anchored_loose_of_i1zero
#print axioms βHensel_one
#print axioms weight_Λ_mono_D
#print axioms weight_Λ_over_𝒪_mono_D
#print axioms βHensel_weight_bound_at_of_anchored
#print axioms structuredSuccTermBound_of_B_budget
#print axioms nsmul_coe_withBot
#print axioms structuredSuccTermBound_of_budgets
#print axioms βHensel_weight_bound_zero_rebased
#print axioms βHensel_weight_bound_rebased
#print axioms βHensel_weight_bound_zero_structured
#print axioms βHensel_weight_bound_structured

end BCIKS20.HenselNumerator
