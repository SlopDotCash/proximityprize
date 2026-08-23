/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.SlicedComposition

/-!
# Cell pinning from heavy agreement (#302): the surface is Z-AFFINE

The MCA pair-conjecture consumers
(`mca_johnson_bound_CONJECTURE_pair_of_decode_family_pinning`) need, per large cell, the
**affine pinning** `∃ v₀ v₁, ∀ γ, P γ = v₀ + C γ * v₁`.  This file produces it from the
SAME heavy-agreement package that drives the hlin capstone — the positive (Claim 5.9)
output rather than the contradiction:

* `gammaGenuine_paperZ_linear_of_heavy_agreement` — the paper-faithful Claim 5.9 from the
  agreement data (the `natDegree_eq_one` weld's twin: same inputs, the
  `gammaGenuine_paperZ_linear` conclusion via the Vandermonde globalization);
* `embed_aPre_eq_alphaGenuine` — for monic `H` the normalized place numerators embed to
  the genuine Hensel coefficients (`LiftIdentityAt` + the `ξ`-unit cancellation in the
  field `𝕃`);
* `aPre_eq_groundAffine_of_paperZ` — the `𝒪`-level affinization: each `aPre t` IS the
  ground-affine element `a t + Z·b t` (embed-injectivity);
* **`taylor_coeff_affine_of_heavy_agreement`** — THE CELL PINNING: every `(X−x₀)`-Taylor
  coefficient of the decoded surface `w` is `Z`-affine, `C (a t) + X·C (b t)` — read the
  ground-affine identification at the witnessed places through Seam B's coefficient
  reading and identify polynomials by counting (`|S₀| > max Bw 1` places).

Consequence: the decode at EVERY scalar `γ` is `v₀ + γ·v₁` with
`v₀ = Σ a t·(X−x₀)ᵗ`, `v₁ = Σ b t·(X−x₀)ᵗ` — the consumer's pinning shape, for the
whole cell at once.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.Claim59Lagrange BCIKS20.Claim510Kill
open ArkLib ArkLib.DecodedProximateRoot

namespace BCIKS20.Claim510CellPinning

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Claim 5.9 (paper-faithful) from the heavy-agreement package** — the
`natDegree_eq_one_of_heavy_agreement` twin with the positive conclusion. -/
theorem gammaGenuine_paperZ_linear_of_heavy_agreement [Fintype F]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (hagree : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z root (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t) * (e j) ^ t)
        = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    ZLinearClosureAudit.gammaGenuine_paperZ_linear H x₀ R hHyp := by
  classical
  refine gammaGenuine_paperZ_linear_of_vandermonde_values H hHyp htail e he u₀ u₁
    fun j => ?_
  refine coeff_sum_eq_ground_of_large_fin H x₀ R hHyp hlc
    (fun t _ => Claim510Weld.liftIdentity_of_monic H x₀ R hHyp hlc t)
    (e j) (u₀ j) (u₁ j) hD ?_
  refine Claim510Weld.largeness_of_card H x₀ R hHyp (e j) (u₀ j) (u₁ j) (matchingSet j)
    (fun z hz => ?_) (hweight j) (hcard j)
  obtain ⟨root, hroot⟩ := hagree j z hz
  exact mem_S_β_killTarget_of_pin_agree H x₀ R hHyp (e j) (u₀ j) (u₁ j) z root
    (fun t => π_z z root (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t))
    (fun t _ => BCIKS20.Claim510Supply.pi_z_pinning_of_monic H x₀ R hHyp hlc z root t)
    hroot

/-- **The normalized numerators embed to the genuine coefficients** (monic):
`embed(aPre t) = αGenuine t`, by the lift identity and `ξ`-unit cancellation. -/
theorem embed_aPre_eq_alphaGenuine
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t)
      = αGenuine H x₀ R hHyp t := by
  have hlift := Claim510Weld.liftIdentity_of_monic H x₀ R hHyp hlc t
  rw [S5Genuine.LiftIdentityAt, hlc] at hlift
  simp only [map_one, one_pow, mul_one] at hlift
  -- embed(βHensel t) = αGenuine t · embed(ξ)^{2t−1}
  have hsplit := congrArg (embeddingOf𝒪Into𝕃 H)
    (BCIKS20.Claim510Supply.betaHensel_eq_aPre_mul_xi_pow H x₀ R hHyp hlc t)
  rw [map_mul, map_pow] at hsplit
  -- cancel the unit power
  have hu : IsUnit ((embeddingOf𝒪Into𝕃 H) (ξ x₀ R H hHyp) ^ (2 * t - 1)) :=
    ((BCIKS20.HenselNumerator.isUnit_ξ_of_monic (H := H) x₀ R hHyp hlc).map
      (embeddingOf𝒪Into𝕃 H)).pow _
  exact hu.mul_right_cancel (by rw [← hsplit, hlift])

/-- **The `𝒪`-level affinization**: under `paperZ`-linearity, each `aPre t` IS the
ground-affine element (embed-injectivity). -/
theorem aPre_eq_groundAffine_of_paperZ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hab : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    (t : ℕ) :
    BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t = groundAffine H (a t) (b t) := by
  refine embeddingOf𝒪Into𝕃_injective (Fact.out (p := 0 < H.natDegree)) ?_
  rw [embed_aPre_eq_alphaGenuine x₀ R hHyp hlc t, hab t, embed_groundAffine]

/-- **THE CELL PINNING: the decoded surface is `Z`-AFFINE.**  Under the heavy-agreement
package (with the tail), Seam B's coefficient reading at `> max Bw 1` witnessed places
identifies every `(X−x₀)`-Taylor coefficient of `w` with a ground-affine polynomial:
`(taylor x₀ w).coeff t = C (a t) + X·C (b t)` for every `t`.  Hence the decode at EVERY
scalar `γ` is `v₀ + γ·v₁` — the MCA pair-conjecture's pinning shape, cell-wide. -/
theorem taylor_coeff_affine_of_heavy_agreement [Fintype F] [DecidableEq F]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card)
    -- the identification places: one designated witnessed set with the counting leg
    (S₀ : Finset F)
    (hbase₀ : ∀ z ∈ S₀, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsep₀ : ∀ z ∈ S₀,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    ∃ a b : ℕ → F, (∀ t, n ≤ t → a t = 0 ∧ b t = 0) ∧
      ∀ t, (Polynomial.taylor (Polynomial.C x₀) w).coeff t
        = Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t) := by
  classical
  have hlc : H.leadingCoeff = 1 := hmonic.leadingCoeff
  have hξ : ξ x₀ R H hHyp ≠ 0 :=
    BCIKS20.Claim510AgreementSupply.xi_ne_zero_of_monic hHyp hlc
  -- the agreement input from Seam B
  have hagree := BCIKS20.Claim510AgreementSupply.hagree_of_decoded hHyp hξ hlc e u₀ u₁
    matchingSet root
    (fun z => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
    hdeg hdvd hbaseA hsepA hfold
  -- Claim 5.9: paperZ linearity
  obtain ⟨a, b, hab⟩ := gammaGenuine_paperZ_linear_of_heavy_agreement x₀ R hHyp hlc
    htail e he u₀ u₁ hD matchingSet hagree hweight hcard
  -- normalize the tail of (a, b): replace by 0 past n (the αGenuine tail forces the
  -- ground-affine to be 0 there only up to lift-injectivity; we simply REDEFINE)
  refine ⟨fun t => if t < n then a t else 0, fun t => if t < n then b t else 0,
    fun t ht => by simp [Nat.not_lt.mpr ht], fun t => ?_⟩
  by_cases ht : t < n
  · -- the genuine content: identify the Taylor coefficient with C (a t) + X·C (b t)
    simp only [if_pos ht]
    -- per-place reading at S₀
    have hread : ∀ z ∈ S₀,
        ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z = a t + z * b t := by
      intro z hz
      have h1 := BCIKS20.Claim510AgreementSupply.pi_z_aPre_eq_taylor_coeff hHyp hξ hlc
        z (root z)
        (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
        hdvd (hbase₀ z hz) (hsep₀ z hz) t
      have h2 : BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t
          = groundAffine H (a t) (b t) :=
        aPre_eq_groundAffine_of_paperZ x₀ R hHyp hlc hab t
      rw [h2, π_z_groundAffine] at h1
      exact h1.symm
    -- polynomial identification by counting
    set Dt : F[X] := (Polynomial.taylor (Polynomial.C x₀) w).coeff t
      - (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)) with hDt
    have hDtdeg : Dt.natDegree ≤ max Bw 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      refine max_le_max (hBw t) ?_
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simp only [Polynomial.natDegree_C, max_le_iff]
      refine ⟨Nat.zero_le _, ?_⟩
      refine le_trans Polynomial.natDegree_mul_le ?_
      simp [Polynomial.natDegree_X_le]
    have hDtvan : ∀ z ∈ S₀, Dt.eval z = 0 := by
      intro z hz
      rw [hDt]
      simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      rw [hread z hz]
      ring
    have hDt0 : Dt = 0 := by
      by_contra hne
      have hsub : S₀ ⊆ Dt.roots.toFinset := by
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact hDtvan z hz
      have hle : S₀.card ≤ max Bw 1 :=
        le_trans (Finset.card_le_card hsub)
          (le_trans (Multiset.toFinset_card_le _)
            (le_trans (Polynomial.card_roots' _) hDtdeg))
      omega
    have := sub_eq_zero.mp (hDt ▸ hDt0)
    exact this
  · -- past the degree: the Taylor coefficient vanishes
    simp only [if_neg ht]
    have hwt : (Polynomial.taylor (Polynomial.C x₀) w).natDegree < n := by
      rwa [Polynomial.natDegree_taylor]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hwt (Nat.not_lt.mp ht))]
    simp

/-- **The consumer pair (the `hdata` pinning leg, cell-wide)**: from the heavy-agreement
package, the pair `(v₀, v₁)` with `natDegree < n` such that EVERY decode reading of the
surface is `v₀ + γ·v₁` — for any cell whose decodes are the surface's Taylor sections
(the S10/Claim-5.7 capture output shape). -/
theorem exists_pinning_pair_of_heavy_agreement [Fintype F] [DecidableEq F]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic)
    {n : ℕ} (hn : 0 < n)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F)
    (hbase₀ : ∀ z ∈ S₀, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsep₀ : ∀ z ∈ S₀,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < n ∧ v₁.natDegree < n ∧
      ∀ γ : F,
        (∑ t ∈ Finset.range n,
          Polynomial.C (((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval γ)
            * (Polynomial.X - Polynomial.C x₀) ^ t)
        = v₀ + Polynomial.C γ * v₁ := by
  classical
  obtain ⟨a, b, htail_ab, hcoeff⟩ := taylor_coeff_affine_of_heavy_agreement x₀ R hHyp
    hH hmonic htail e he u₀ u₁ hD matchingSet root hdeg hdvd hbaseA hsepA hfold
    hweight hcard S₀ hbase₀ hsep₀ hBw hS₀
  refine ⟨∑ t ∈ Finset.range n,
      Polynomial.C (a t) * (Polynomial.X - Polynomial.C x₀) ^ t,
    ∑ t ∈ Finset.range n,
      Polynomial.C (b t) * (Polynomial.X - Polynomial.C x₀) ^ t, ?_, ?_, ?_⟩
  · -- degree of v₀
    have hterm : ∀ t ∈ Finset.range n,
        (Polynomial.C (a t) * (Polynomial.X - Polynomial.C x₀) ^ t).natDegree ≤ n - 1 := by
      intro t ht
      rw [Finset.mem_range] at ht
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h2 : ((Polynomial.X - Polynomial.C x₀ : F[X]) ^ t).natDegree ≤ t := by
        refine le_trans Polynomial.natDegree_pow_le ?_
        rw [Polynomial.natDegree_X_sub_C]
        omega
      simp only [Polynomial.natDegree_C]
      omega
    have hle := Polynomial.natDegree_sum_le_of_forall_le _ _ hterm
    omega
  · -- degree of v₁
    have hterm : ∀ t ∈ Finset.range n,
        (Polynomial.C (b t) * (Polynomial.X - Polynomial.C x₀) ^ t).natDegree ≤ n - 1 := by
      intro t ht
      rw [Finset.mem_range] at ht
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h2 : ((Polynomial.X - Polynomial.C x₀ : F[X]) ^ t).natDegree ≤ t := by
        refine le_trans Polynomial.natDegree_pow_le ?_
        rw [Polynomial.natDegree_X_sub_C]
        omega
      simp only [Polynomial.natDegree_C]
      omega
    have hle := Polynomial.natDegree_sum_le_of_forall_le _ _ hterm
    omega
  · intro γ
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hcoeff t]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    rw [map_add, add_mul, map_mul]
    ring

end BCIKS20.Claim510CellPinning

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.Claim510CellPinning.gammaGenuine_paperZ_linear_of_heavy_agreement
#print axioms BCIKS20.Claim510CellPinning.embed_aPre_eq_alphaGenuine
#print axioms BCIKS20.Claim510CellPinning.aPre_eq_groundAffine_of_paperZ
#print axioms BCIKS20.Claim510CellPinning.taylor_coeff_affine_of_heavy_agreement
#print axioms BCIKS20.Claim510CellPinning.exists_pinning_pair_of_heavy_agreement
