/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedLiftIdentity
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Supply

/-!
# The cleared Claim 5.10 kill chain — `killTargetC` and its weight bound (#357 route a)

The per-point half of [BCIKS20] §5.2.7 (Claim 5.10) re-founded at the ORIGINAL non-monic
factor on the cleared recursion `βHenselC`: the cleared lift identity reads
`embed (βHenselC t) = αGenuine t · Ŵ^{t+1} · ξ̂^{2t−1}` (`LiftIdentityAtC`), so the cleared
sum and kill target carry balancing `W𝒪`-powers — each summand carries
`Ŵ^{(t+1)+(n−t)} = Ŵ^{n+1}` and `ξ̂^{(2t−1)+(2n−(2t−1))} = ξ̂^{2n}`, both telescoping to the
uniform factors.  Mirror of the landed monic chain (`Kill.lean` / `Supply.lean`) with the
`W`-power carried instead of killed:

* `embed_W𝒪` / `π_z_W𝒪` — the `W𝒪` computations.
* `clearedSumC` — `B_e := ∑_{t<n} βHenselC t · ξ^{2n−(2t−1)} · W𝒪^{n−t} · oScalar (e^t)`.
* `killTargetC` — `β̃_e := B_e − groundAffine a b · ξ^{2n} · W𝒪^{n+1}`.
* `embed_clearedSumC` — the clearing identity (per-`t` `LiftIdentityAtC` ⟹ uniform powers).
* `π_z_killTargetC` / `mem_S_β_killTargetC_of_pin_agree` — per-place computation/membership
  under the cleared pinning `π_z (βHenselC t) = c t · ξ_z^{2t−1} · W_z^{t+1}`.
* `coeff_sum_eq_ground_of_largeC` (+ `_fin`) — **the kill**: `Lemma_A_1` largeness forces
  the genuine coefficient sum to the ground-affine value, cancelling BOTH nonzero uniform
  factors (`embeddingOf𝒪Into𝕃_ξ_ne_zero`, `liftToFunctionField_leadingCoeff_ne_zero` —
  monicity-FREE).
* `killBudgetC` + `weight_killTargetC_le` — the explicit ℕ-weight budget
  `(2n+1)·d_R·D + 2n·xw + (n+1)·degW + 1` from the LANDED anchored bound
  `βHenselC_weight_bound_anchored_loose`, via the `Λ_𝒪` calculus.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 — §5.2.6–5.2.7, Appendix A (Lemma A.1, A.4).
* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange
open BCIKS20.Claim510Kill
open BCIKS20.Claim510Supply (weight_oScalar_le weight_groundAffine_le)

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510KillC

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The embedding of `W𝒪` is the lifted leading coefficient `Ŵ`. -/
@[simp]
theorem embed_W𝒪 :
    embeddingOf𝒪Into𝕃 H (W𝒪 H) = liftToFunctionField (H := H) H.leadingCoeff := by
  rw [W𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

/-- The place value of `W𝒪` is the evaluated leading coefficient `W(z)`. -/
@[simp]
theorem π_z_W𝒪 (z : F) (root : rationalRoot (H_tilde' H) z) :
    π_z z root (W𝒪 H) = (H.leadingCoeff).eval z := by
  rw [W𝒪, π_z_mk, Polynomial.evalEval_C]

variable (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)

/-- The cleared coefficient sum at the cleared recursion:
`B_e = ∑_{t<n} βHenselC t · ξ^{2n−(2t−1)} · W𝒪^{n−t} · (e^t)`. -/
noncomputable def clearedSumC (n : ℕ) (e : F) : 𝒪 H :=
  ∑ t ∈ Finset.range n,
    βHenselC (H := H) x₀ R hHyp t
      * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))
      * (W𝒪 H) ^ (n - t)
      * oScalar H (e ^ t)

/-- The cleared kill target `β̃_e = B_e − (a + Z·b)·ξ^{2n}·W𝒪^{n+1}`. -/
noncomputable def killTargetC (n : ℕ) (e a b : F) : 𝒪 H :=
  clearedSumC H x₀ R hHyp n e
    - groundAffine H a b * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n) * (W𝒪 H) ^ (n + 1)

/-- **The clearing identity** (non-monic `H`): the embedding of the cleared sum is the
genuine coefficient sum times the uniform `Ŵ^{n+1}·ξ̂^{2n}` powers, via the per-`t` cleared
lift identity — each summand carries `Ŵ^{(t+1)+(n−t)} = Ŵ^{n+1}` and
`ξ̂^{(2t−1)+(2n−(2t−1))} = ξ̂^{2n}`. -/
theorem embed_clearedSumC {n : ℕ}
    (hlift : ∀ t, t < n → LiftIdentityAtC x₀ R hHyp t) (e : F) :
    embeddingOf𝒪Into𝕃 H (clearedSumC H x₀ R hHyp n e)
      = (∑ t ∈ Finset.range n,
          liftConst H (e ^ t) * αGenuine H x₀ R hHyp t)
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (n + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) := by
  rw [clearedSumC, map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  have hid := hlift t ht
  rw [LiftIdentityAtC] at hid
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, embed_oScalar, embed_W𝒪, hid]
  have hexpW : (t + 1) + (n - t) = n + 1 := by omega
  have hexpξ : (2 * t - 1) + (2 * n - (2 * t - 1)) = 2 * n := by omega
  calc αGenuine H x₀ R hHyp t
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n - (2 * t - 1))
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (n - t)
        * liftConst H (e ^ t)
      = liftConst H (e ^ t) * αGenuine H x₀ R hHyp t
          * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (n - t))
          * ((embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n - (2 * t - 1))) := by
        ring
    _ = liftConst H (e ^ t) * αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (n + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) := by
        rw [← pow_add, ← pow_add, hexpW, hexpξ]

/-- **The per-place computation of the cleared kill target.**  Under the cleared per-place
pinning `π_z (βHenselC t) = c t · ξ_z^{2t−1} · W_z^{t+1}`, the kill target reads
`ξ_z^{2n}·W_z^{n+1}·(∑_t c t·e^t − (a + z·b))` at the place. -/
theorem π_z_killTargetC {n : ℕ} (e a b : F) (z : F)
    (root : rationalRoot (H_tilde' H) z) (c : ℕ → F)
    (hpin : ∀ t, t < n →
      π_z z root (βHenselC (H := H) x₀ R hHyp t)
        = c t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
            * ((H.leadingCoeff).eval z) ^ (t + 1)) :
    π_z z root (killTargetC H x₀ R hHyp n e a b)
      = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n)
          * ((H.leadingCoeff).eval z) ^ (n + 1)
          * ((∑ t ∈ Finset.range n, c t * e ^ t) - (a + z * b)) := by
  rw [killTargetC, map_sub, clearedSumC, map_sum]
  rw [map_mul, map_mul, map_pow, map_pow, π_z_groundAffine, π_z_W𝒪]
  have hsum : ∀ t ∈ Finset.range n,
      π_z z root (βHenselC (H := H) x₀ R hHyp t
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))
          * (W𝒪 H) ^ (n - t) * oScalar H (e ^ t))
        = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n)
            * ((H.leadingCoeff).eval z) ^ (n + 1) * (c t * e ^ t) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, π_z_oScalar, π_z_W𝒪, hpin t ht]
    have hexpW : (t + 1) + (n - t) = n + 1 := by omega
    have hexpξ : (2 * t - 1) + (2 * n - (2 * t - 1)) = 2 * n := by omega
    calc c t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
          * ((H.leadingCoeff).eval z) ^ (t + 1)
          * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n - (2 * t - 1))
          * ((H.leadingCoeff).eval z) ^ (n - t) * e ^ t
        = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ ((2 * t - 1) + (2 * n - (2 * t - 1)))
            * ((H.leadingCoeff).eval z) ^ ((t + 1) + (n - t)) * (c t * e ^ t) := by
          rw [pow_add, pow_add]; ring
      _ = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n)
            * ((H.leadingCoeff).eval z) ^ (n + 1) * (c t * e ^ t) := by
          rw [hexpW, hexpξ]
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum]
  ring

/-- **Pinned + agreeing places lie in the vanishing set of the cleared kill target.** -/
theorem mem_S_β_killTargetC_of_pin_agree {n : ℕ} (e a b : F) (z : F)
    (root : rationalRoot (H_tilde' H) z) (c : ℕ → F)
    (hpin : ∀ t, t < n →
      π_z z root (βHenselC (H := H) x₀ R hHyp t)
        = c t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
            * ((H.leadingCoeff).eval z) ^ (t + 1))
    (hagree : (∑ t ∈ Finset.range n, c t * e ^ t) = a + z * b) :
    z ∈ S_β (killTargetC H x₀ R hHyp n e a b) := by
  refine ⟨root, ?_⟩
  rw [π_z_killTargetC H x₀ R hHyp e a b z root c hpin, hagree, sub_self, mul_zero]

/-- **The cleared Claim 5.10 per-point kill.**  `Lemma_A_1` largeness for the cleared kill
target forces the genuine coefficient sum at the node `e` to be the ground-affine value —
cancelling BOTH nonzero uniform factors `ξ̂^{2n}` and `Ŵ^{n+1}` (monicity-free). -/
theorem coeff_sum_eq_ground_of_largeC {n : ℕ}
    (hlift : ∀ t, t < n → LiftIdentityAtC x₀ R hHyp t)
    (e a b : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (hlarge : Set.ncard (S_β (killTargetC H x₀ R hHyp n e a b))
      > (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTargetC H x₀ R hHyp n e a b) D) * H.natDegree) :
    ∑ t ∈ Finset.range n, liftConst H (e ^ t) * αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  have hzero : embeddingOf𝒪Into𝕃 H (killTargetC H x₀ R hHyp n e a b) = 0 :=
    Lemma_A_1 (Fact.out (p := 0 < H.natDegree)) _ D hD hlarge
  rw [killTargetC, map_sub, map_mul, map_mul, map_pow, map_pow, embed_groundAffine,
    embed_W𝒪, embed_clearedSumC H x₀ R hHyp hlift e, sub_eq_zero] at hzero
  have hξpow : (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) ≠ 0 :=
    pow_ne_zero _ (embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp)
  have hWpow : (liftToFunctionField (H := H) H.leadingCoeff) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hzero' : (∑ t ∈ Finset.range n, liftConst H (e ^ t) * αGenuine H x₀ R hHyp t)
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (n + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n)
      = liftToFunctionField (H := H)
            (Polynomial.C a + Polynomial.X * Polynomial.C b)
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (n + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) := by
    rw [hzero]; ring
  exact mul_right_cancel₀ hWpow (mul_right_cancel₀ hξpow hzero')

/-- **The Fin-indexed corollary** in exactly the `hvals` shape consumed by
`Claim59Lagrange.gammaGenuine_paperZ_linear_of_vandermonde_values`. -/
theorem coeff_sum_eq_ground_of_largeC_fin {n : ℕ}
    (hlift : ∀ t, t < n → LiftIdentityAtC x₀ R hHyp t)
    (e a b : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (hlarge : Set.ncard (S_β (killTargetC H x₀ R hHyp n e a b))
      > (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTargetC H x₀ R hHyp n e a b) D) * H.natDegree) :
    ∑ s : Fin n, liftConst H (e ^ (s : ℕ)) * αGenuine H x₀ R hHyp (s : ℕ)
      = liftToFunctionField (H := H)
          (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun t => liftConst H (e ^ t) * αGenuine H x₀ R hHyp t) n]
  exact coeff_sum_eq_ground_of_largeC H x₀ R hHyp hlift e a b hD hlarge

/-! ## The cleared kill-target weight bound (brick `cleared_kill_weight`) -/

/-- The explicit ℕ-budget for the cleared kill target, at the per-factor anchor `D`:
`(2n+1)·d_R·D` for the top `βHenselC` order (the LANDED anchored loose bound), `2n·xw` for
the `ξ`-power, `(n+1)·degW` for the carried `W𝒪`-power, and `1` for the ground line. -/
def killBudgetC (n D dR xw wdeg : ℕ) : ℕ :=
  (2 * n + 1) * dR * D + 2 * n * xw + (n + 1) * wdeg + 1

/-- **The cleared kill-target weight bound** (the weld's `hweight` input, non-monic):
under the anchored hypothesis set of `βHenselC_weight_bound_anchored_loose` (the
per-factor anchor `D = tot H` witnessed by `htight`/`hWdeg`, the anchored shape
`htotal`/`hvanish`/`hDRD`/`hdRDR` of `R`, and the `W`-divisibility family `hdvd`) and a
`ξ`-weight bound `xw`,
`Λ_𝒪(killTargetC n e a b) ≤ killBudgetC n D d_R xw degW`. -/
theorem weight_killTargetC_le
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ m i, ((R.coeff m).coeff i).natDegree ≤ DR - m - i)
    (hvanish : ∀ m i, DR < m + i → ((R.coeff m).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hdvd : ∀ mm : ℕ, H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY mm R))).coeff (Bivariate.natDegreeY R - mm))
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (n : ℕ) (e a b : F) :
    weight_Λ_over_𝒪 hH (killTargetC H x₀ R hHyp n e a b) D
      ≤ (WithBot.some (killBudgetC n D (Bivariate.natDegreeY R) xw
          (H.leadingCoeff).natDegree) : WithBot ℕ) := by
  set B : ℕ := killBudgetC n D (Bivariate.natDegreeY R) xw (H.leadingCoeff).natDegree
    with hB
  -- per-term bound for the cleared sum
  have hterm : ∀ t ∈ Finset.range n,
      weight_Λ_over_𝒪 hH
        (βHenselC (H := H) x₀ R hHyp t
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))
          * (W𝒪 H) ^ (n - t) * oScalar H (e ^ t)) D
        ≤ (WithBot.some B : WithBot ℕ) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 : weight_Λ_over_𝒪 hH (βHenselC (H := H) x₀ R hHyp t) D
        ≤ (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) :=
      βHenselC_weight_bound_anchored_loose x₀ R hHyp hH hD htight hWdeg hD_Rx0
        hdR2 hdHdR htotal hvanish hDRD hdRDR hdvd t
    have h2 : weight_Λ_over_𝒪 hH
        ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))) D
        ≤ (WithBot.some ((2 * n - (2 * t - 1)) * xw) : WithBot ℕ) :=
      (weight_Λ_over_𝒪_pow_le H hH hD _ _).trans (nsmul_withBot_le _ _ hξw)
    have hW : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (n - t)) D
        ≤ (WithBot.some ((n - t) * (H.leadingCoeff).natDegree) : WithBot ℕ) :=
      (weight_Λ_over_𝒪_pow_le H hH hD _ _).trans
        (nsmul_withBot_le _ _ (weight_Λ_over_𝒪_W H hH hD))
    have h3 := weight_oScalar_le H hH hD (e ^ t)
    have h12 : weight_Λ_over_𝒪 hH
        (βHenselC (H := H) x₀ R hHyp t
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))) D
        ≤ (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D
            + (2 * n - (2 * t - 1)) * xw) : WithBot ℕ) := by
      refine (weight_Λ_over_𝒪_mul_le H hH hD _ _).trans ?_
      refine le_trans (add_le_add h1 h2) ?_
      rw [← WithBot.coe_add]
    have h123 : weight_Λ_over_𝒪 hH
        (βHenselC (H := H) x₀ R hHyp t
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))
          * (W𝒪 H) ^ (n - t)) D
        ≤ (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D
            + (2 * n - (2 * t - 1)) * xw
            + (n - t) * (H.leadingCoeff).natDegree) : WithBot ℕ) := by
      refine (weight_Λ_over_𝒪_mul_le H hH hD _ _).trans ?_
      refine le_trans (add_le_add h12 hW) ?_
      rw [← WithBot.coe_add]
    refine (weight_Λ_over_𝒪_mul_le H hH hD _ _).trans ?_
    refine le_trans (add_le_add h123 h3) ?_
    have harith : ((2 * t + 1) * Bivariate.natDegreeY R * D
          + (2 * n - (2 * t - 1)) * xw
          + (n - t) * (H.leadingCoeff).natDegree) + 0 ≤ B := by
      rw [hB, killBudgetC]
      have e1 : (2 * t + 1) * Bivariate.natDegreeY R * D
          ≤ (2 * n + 1) * Bivariate.natDegreeY R * D :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      have e2 : (2 * n - (2 * t - 1)) * xw ≤ 2 * n * xw :=
        Nat.mul_le_mul_right _ (by omega)
      have e3 : (n - t) * (H.leadingCoeff).natDegree
          ≤ (n + 1) * (H.leadingCoeff).natDegree :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rw [← WithBot.coe_add]
    exact_mod_cast harith
  -- the cleared-sum bound
  have hsum : weight_Λ_over_𝒪 hH (clearedSumC H x₀ R hHyp n e) D
      ≤ (WithBot.some B : WithBot ℕ) := by
    rw [clearedSumC]
    refine (weight_Λ_over_𝒪_sum_le H hH hD _ _).trans ?_
    exact Finset.sup_le hterm
  -- the ground-affine·ξ^{2n}·W𝒪^{n+1} bound
  have hground : weight_Λ_over_𝒪 hH
      (groundAffine H a b * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n) * (W𝒪 H) ^ (n + 1)) D
      ≤ (WithBot.some B : WithBot ℕ) := by
    have h1 := weight_groundAffine_le H hH hD a b
    have h2 : weight_Λ_over_𝒪 hH ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * n)) D
        ≤ (WithBot.some (2 * n * xw) : WithBot ℕ) :=
      (weight_Λ_over_𝒪_pow_le H hH hD _ _).trans (nsmul_withBot_le _ _ hξw)
    have hW2 : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (n + 1)) D
        ≤ (WithBot.some ((n + 1) * (H.leadingCoeff).natDegree) : WithBot ℕ) :=
      (weight_Λ_over_𝒪_pow_le H hH hD _ _).trans
        (nsmul_withBot_le _ _ (weight_Λ_over_𝒪_W H hH hD))
    have h12 : weight_Λ_over_𝒪 hH
        (groundAffine H a b * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n)) D
        ≤ (WithBot.some (1 + 2 * n * xw) : WithBot ℕ) := by
      refine (weight_Λ_over_𝒪_mul_le H hH hD _ _).trans ?_
      refine le_trans (add_le_add h1 h2) ?_
      rw [← WithBot.coe_add]
    refine (weight_Λ_over_𝒪_mul_le H hH hD _ _).trans ?_
    refine le_trans (add_le_add h12 hW2) ?_
    rw [← WithBot.coe_add]
    have harith : (1 + 2 * n * xw) + (n + 1) * (H.leadingCoeff).natDegree ≤ B := by
      rw [hB, killBudgetC]
      omega
    exact_mod_cast harith
  -- assemble: `killTargetC = clearedSumC − ground·ξ^{2n}·W𝒪^{n+1}`
  rw [killTargetC, sub_eq_add_neg]
  refine (weight_Λ_over_𝒪_add_le H hH hD _ _).trans ?_
  refine max_le hsum ?_
  exact (weight_Λ_over_𝒪_neg H hH hD _).trans hground

end BCIKS20.Claim510KillC

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510KillC.embed_W𝒪
#print axioms BCIKS20.Claim510KillC.π_z_W𝒪
#print axioms BCIKS20.Claim510KillC.embed_clearedSumC
#print axioms BCIKS20.Claim510KillC.π_z_killTargetC
#print axioms BCIKS20.Claim510KillC.mem_S_β_killTargetC_of_pin_agree
#print axioms BCIKS20.Claim510KillC.coeff_sum_eq_ground_of_largeC
#print axioms BCIKS20.Claim510KillC.coeff_sum_eq_ground_of_largeC_fin
#print axioms BCIKS20.Claim510KillC.weight_killTargetC_le
