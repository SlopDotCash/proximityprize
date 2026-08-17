/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.CurvesBridge
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.DescendedRset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# §6 joint-agreement from the `hfactor`-free descended residual bundle (issue #8)

`CurvesBridge.lean` exposes the strict-Johnson §6 joint-agreement front door
`RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_natCeil_counting`, whose
per-solution counting package `hcounting` still supplies the **legacy** `Claim57Residuals` instance
  —
the bundle that carries the `hfactor` field (`pg_Rset ⟹ Eq-5.12 factor list`).

This file completes the issue-#8 rewiring at the §6 level: it lets callers supply the
**`hfactor`-free** `Claim57ResidualsDescended` bundle (`DescendedRset.lean`) plus the explicit
  legacy
coincidence hypothesis `pg_RsetDescended = pg_Rset`, instead of a legacy `Claim57Residuals`
  instance.
The full instance is reconstructed internally via `Claim57Residuals.ofDescended`, so the §6
  conclusion
no longer forces callers through the `hfactor` obligation — exactly the "replace the typeclass
dependency in downstream consumers" acceptance criterion, carried all the way to the §6 keystone.

Builds on the BCIKS20 cone (verified green under the rc2 toolchain).
-/

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal Polynomial

namespace ProximityGap

open Polynomial ReedSolomon Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]
  [DecidableEq (Polynomial F)]

/-- **Strict-Johnson §6 joint-agreement from the descended (`hfactor`-free) residual bundle.**

Same conclusion as
`RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_natCeil_counting`, but the
per-`ModifiedGuruswami`-solution counting package `hcounting` provides a
`Claim57ResidualsDescended` bundle (no `hfactor`) together with the explicit coincidence hypothesis
`pg_RsetDescended = pg_Rset`; the legacy `Claim57Residuals` instance is rebuilt internally with
`Claim57Residuals.ofDescended`.  This removes the legacy `hfactor` field from the §6 caller's
obligation, leaving only the honest descended residuals plus the documented coincidence. -/
theorem
  RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_natCeil_counting_descended
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hcounting : ∀ {Q : F[Z][X][Y]} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁),
      ∃ (x₀ : F) (hres_d : Claim57ResidualsDescended (F := F) k (δ : ℚ) x₀ h_gs)
        (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs
          = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs) (D t : ℕ),
        letI : Claim57Residuals (F := F) k (δ : ℚ) x₀ h_gs :=
          Claim57Residuals.ofDescended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) (δ : ℚ) x₀ h_gs hres_d hcoincide
        (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
            (2 * k + 1)
              * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
              * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
              * D ∧
          (2 * k + 1)
            * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
            * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
            * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) ∧
          ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
              #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
            (n - k) * t)
    (hunique : ∀ {Q : F[Z][X][Y]} (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
      (P : F → Polynomial F),
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  refine RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_natCeil_counting
    (F := F) (n := n) (m := m) (k := k) (ωs := ωs) hk δ u₀ u₁ hDx hYZ hprob hJ hδ
    (fun {Q} h_gs => ?_) hunique
  obtain ⟨x₀, hres_d, hcoincide, D, t, hcov, hthr, hsm⟩ := hcounting h_gs
  exact ⟨x₀, Claim57Residuals.ofDescended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) (δ : ℚ) x₀ h_gs hres_d hcoincide, D, t, hcov, hthr, hsm⟩

end ProximityGap

/-! ## Axiom audit (issue #8). -/
open ProximityGap
#print axioms
  RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_natCeil_counting_descended
