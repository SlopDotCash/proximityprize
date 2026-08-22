/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.VandermondeAgreement

/-!
# Claim 5.10 per-point kill — ground-affine values of the genuine branch (#302 hlin, B1)

The per-point half of [BCIKS20] §5.2.7 (Claim 5.10): at an evaluation node `e ∈ F` (in the
application `e = ω − x₀` for a heavy Reed–Solomon coordinate `ω`), the coefficient sum
`∑_{t<n} (e)^t·αGenuine t` of the genuine Hensel branch is **ground-line affine**
`lift (C a + Z·C b)` — produced by the Appendix-A vanishing kernel `Lemma_A_1` applied to a
cleared `𝒪`-element.

Construction (monic `H`, where `W = 1` and the lift identity reads
`embed (βHensel t) = αGenuine t · ξ̂^{2t−1}`):

* `oScalar`/`groundAffine` — the scalar and ground-affine elements of `𝒪 H`, with their
  `embeddingOf𝒪Into𝕃` and `π_z` computations;
* `clearedSum` — `B_e := ∑_{t<n} βHensel t · ξ^{E−e_t} · oScalar (e^t)` with `E := 2n`,
  satisfying `embed B_e = (∑_t liftConst (e^t)·α_t) · ξ̂^E`;
* `killTarget` — `β̃_e := B_e − groundAffine a b · ξ^E`, with
  `π_z β̃_e = ξ_z^E·(∑_t c_t(z)·e^t − (a + z·b))` under the per-place coefficient pinning —
  so β̃_e **vanishes at every place where the decoded values agree with the affine pair**;
* `coeff_sum_eq_ground_of_large` — **the kill**: `Lemma_A_1` largeness for `β̃_e` forces
  `∑_t liftConst (e^t)·α_t = lift (C a + Z·C b)` — exactly the `hvals` input of the
  Vandermonde globalization (`Claim59Vandermonde`), hence of the `d_H ≥ 2` collapse.

The remaining honest inputs (carried as hypotheses, produced by the decoded/pigeonhole
lanes): the per-place coefficient pinning `π_z (βHensel t) = c_t(z)·ξ_z^{e_t}` (Hensel
uniqueness over `F` at each good place — the `DecodedProximateRoot`/`PlaceSeriesCanonical`
surface), the per-place agreement `∑_t c_t(z)·e^t = a + z·b`, and the `Lemma_A_1`
cardinality (from the heavy-point budget, `Hab25HeavyPoints`).

## Main results

* `embed_clearedSum` — the clearing identity.
* `π_z_killTarget` — the per-place computation of the kill target.
* `mem_S_β_killTarget_of_pin_agree` — pinned + agreeing places lie in `S_β β̃_e`.
* `coeff_sum_eq_ground_of_large` — **the Claim 5.10 per-point conclusion**.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 — §5.2.6–5.2.7, Appendix A (Lemma A.1).
* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510Kill

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The scalar element of `𝒪 H`. -/
noncomputable def oScalar (a : F) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C (Polynomial.C a))

/-- The ground-affine element `a + Z·b` of `𝒪 H` (`Z` = the inner/substitution variable). -/
noncomputable def groundAffine (a b : F) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H})
    (Polynomial.C (Polynomial.C a + Polynomial.X * Polynomial.C b))

@[simp]
theorem embed_oScalar (a : F) :
    embeddingOf𝒪Into𝕃 H (oScalar H a) = liftConst H a := by
  rw [oScalar, embeddingOf𝒪Into𝕃_mk, liftBivariate_C, liftConst_apply]

@[simp]
theorem embed_groundAffine (a b : F) :
    embeddingOf𝒪Into𝕃 H (groundAffine H a b)
      = liftToFunctionField (H := H)
          (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  rw [groundAffine, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

@[simp]
theorem π_z_oScalar (z : F) (root : rationalRoot (H_tilde' H) z) (a : F) :
    π_z z root (oScalar H a) = a := by
  rw [oScalar, π_z_mk, Polynomial.evalEval_C, Polynomial.eval_C]

@[simp]
theorem π_z_groundAffine (z : F) (root : rationalRoot (H_tilde' H) z) (a b : F) :
    π_z z root (groundAffine H a b) = a + z * b := by
  rw [groundAffine, π_z_mk, Polynomial.evalEval_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C]

variable (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)

/-- The cleared coefficient sum `B_e = ∑_{t<n} βHensel t · ξ^{2n−(2t−1)} · (e^t)`. -/
noncomputable def clearedSum (n : ℕ) (e : F) : 𝒪 H :=
  ∑ t ∈ Finset.range n,
    βHensel H x₀ R hHyp t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))
      * oScalar H (e ^ t)

/-- The kill target `β̃_e = B_e − (a + Z·b)·ξ^{2n}`. -/
noncomputable def killTarget (n : ℕ) (e a b : F) : 𝒪 H :=
  clearedSum H x₀ R hHyp n e
    - groundAffine H a b * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n)

/-- **The clearing identity** (monic `H`): the embedding of the cleared sum is the genuine
coefficient sum times the uniform `ξ̂^{2n}` power, via the per-`t` lift identity. -/
theorem embed_clearedSum (hlc : H.leadingCoeff = 1) {n : ℕ}
    (hlift : ∀ t, t < n → S5Genuine.LiftIdentityAt H x₀ R hHyp t) (e : F) :
    embeddingOf𝒪Into𝕃 H (clearedSum H x₀ R hHyp n e)
      = (∑ t ∈ Finset.range n,
          liftConst H (e ^ t) * αGenuine H x₀ R hHyp t)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) := by
  rw [clearedSum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  have hid := hlift t ht
  rw [S5Genuine.LiftIdentityAt] at hid
  rw [map_mul, map_mul, map_pow, embed_oScalar, hid, hlc, map_one, one_pow, mul_one]
  have hexp : (2 * t - 1) + (2 * n - (2 * t - 1)) = 2 * n := by omega
  calc αGenuine H x₀ R hHyp t
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n - (2 * t - 1))
        * liftConst H (e ^ t)
      = liftConst H (e ^ t) * αGenuine H x₀ R hHyp t
          * ((embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n - (2 * t - 1))) := by
        ring
    _ = liftConst H (e ^ t) * αGenuine H x₀ R hHyp t
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) := by
        rw [← pow_add, hexp]

/-- **The per-place computation of the kill target.**  Under the per-place coefficient
pinning `π_z (βHensel t) = c t · ξ_z^{2t−1}`, the kill target reads
`ξ_z^{2n}·(∑_t c t·e^t − (a + z·b))` at the place. -/
theorem π_z_killTarget {n : ℕ} (e a b : F) (z : F)
    (root : rationalRoot (H_tilde' H) z) (c : ℕ → F)
    (hpin : ∀ t, t < n →
      π_z z root (βHensel H x₀ R hHyp t)
        = c t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    π_z z root (killTarget H x₀ R hHyp n e a b)
      = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n)
          * ((∑ t ∈ Finset.range n, c t * e ^ t) - (a + z * b)) := by
  rw [killTarget, map_sub, clearedSum, map_sum]
  rw [map_mul, map_pow, π_z_groundAffine]
  have hsum : ∀ t ∈ Finset.range n,
      π_z z root (βHensel H x₀ R hHyp t
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1)) * oScalar H (e ^ t))
        = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) * (c t * e ^ t) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [map_mul, map_mul, map_pow, π_z_oScalar, hpin t ht]
    have hexp : (2 * t - 1) + (2 * n - (2 * t - 1)) = 2 * n := by omega
    calc c t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)
          * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n - (2 * t - 1)) * e ^ t
        = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ ((2 * t - 1) + (2 * n - (2 * t - 1)))
            * (c t * e ^ t) := by rw [pow_add]; ring
      _ = (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) * (c t * e ^ t) := by rw [hexp]
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum]
  ring

/-- **Pinned + agreeing places lie in the vanishing set of the kill target.** -/
theorem mem_S_β_killTarget_of_pin_agree {n : ℕ} (e a b : F) (z : F)
    (root : rationalRoot (H_tilde' H) z) (c : ℕ → F)
    (hpin : ∀ t, t < n →
      π_z z root (βHensel H x₀ R hHyp t)
        = c t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hagree : (∑ t ∈ Finset.range n, c t * e ^ t) = a + z * b) :
    z ∈ S_β (killTarget H x₀ R hHyp n e a b) := by
  refine ⟨root, ?_⟩
  rw [π_z_killTarget H x₀ R hHyp e a b z root c hpin, hagree, sub_self, mul_zero]

/-- **The Claim 5.10 per-point kill.**  `Lemma_A_1` largeness for the kill target forces the
genuine coefficient sum at the node `e` to be the ground-affine value — exactly the `hvals`
input of the Vandermonde globalization (`Claim59Vandermonde`). -/
theorem coeff_sum_eq_ground_of_large (hlc : H.leadingCoeff = 1) {n : ℕ}
    (hlift : ∀ t, t < n → S5Genuine.LiftIdentityAt H x₀ R hHyp t)
    (e a b : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (hlarge : Set.ncard (S_β (killTarget H x₀ R hHyp n e a b))
      > (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTarget H x₀ R hHyp n e a b) D) * H.natDegree) :
    ∑ t ∈ Finset.range n, liftConst H (e ^ t) * αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  have hzero : embeddingOf𝒪Into𝕃 H (killTarget H x₀ R hHyp n e a b) = 0 :=
    Lemma_A_1 (Fact.out (p := 0 < H.natDegree)) _ D hD hlarge
  rw [killTarget, map_sub, map_mul, map_pow, embed_groundAffine,
    embed_clearedSum H x₀ R hHyp hlc hlift e, sub_eq_zero] at hzero
  have hξ : embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ≠ 0 :=
    embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp
  have hξpow : (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * n) ≠ 0 :=
    pow_ne_zero _ hξ
  exact mul_right_cancel₀ hξpow hzero

/-- **The Fin-indexed corollary** in exactly the `hvals` shape consumed by
`Claim59Lagrange.gammaGenuine_paperZ_linear_of_vandermonde_values`. -/
theorem coeff_sum_eq_ground_of_large_fin (hlc : H.leadingCoeff = 1) {n : ℕ}
    (hlift : ∀ t, t < n → S5Genuine.LiftIdentityAt H x₀ R hHyp t)
    (e a b : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (hlarge : Set.ncard (S_β (killTarget H x₀ R hHyp n e a b))
      > (weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
          (killTarget H x₀ R hHyp n e a b) D) * H.natDegree) :
    ∑ s : Fin n, liftConst H (e ^ (s : ℕ)) * αGenuine H x₀ R hHyp (s : ℕ)
      = liftToFunctionField (H := H)
          (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun t => liftConst H (e ^ t) * αGenuine H x₀ R hHyp t) n]
  exact coeff_sum_eq_ground_of_large H x₀ R hHyp hlc hlift e a b hD hlarge

end BCIKS20.Claim510Kill

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Kill.embed_clearedSum
#print axioms BCIKS20.Claim510Kill.π_z_killTarget
#print axioms BCIKS20.Claim510Kill.mem_S_β_killTarget_of_pin_agree
#print axioms BCIKS20.Claim510Kill.coeff_sum_eq_ground_of_large
#print axioms BCIKS20.Claim510Kill.coeff_sum_eq_ground_of_large_fin
