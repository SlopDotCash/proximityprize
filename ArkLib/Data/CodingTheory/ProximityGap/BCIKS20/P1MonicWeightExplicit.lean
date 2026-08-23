/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality

/-!
# BCIKS20 Appendix A.4 (P1) — the open weight core isolated to one explicit element (#138)

For monic `H`, separability makes `ξ` a unit in `𝒪 H` (`isUnit_ξ_of_monic`), so the successor
clearing `βHensel (t+1) = a · ξ^{2t+1}` has a **unique** solution — existence is the already-proven
divisibility `xi_pow_dvd_βHensel_succ_of_monic`.  Consequently the carved successor weight predicate
`SuccDivWeightLe_of_monic` (an *existential* over `a` paired with a weight bound) collapses to a
weight bound on this **single explicit element**, with the existential eliminated and the
divisibility conjunct discharged.

* `henselQuotient` — the explicit divisibility witness `a` with `βHensel (t+1) = a · ξ^{2t+1}`.
* `henselQuotient_mul_xi` — `henselQuotient t · ξ^{2t+1} = βHensel (t+1)` (the proven clearing).
* `succDivWeightLe_iff_henselQuotient_weight` — the entire open #138 weight core (monic case) is
  EXACTLY `∀ t, weight_Λ_over_𝒪 hH (henselQuotient t) D ≤ 1`: no existential, divisibility gone.

This pins the remaining open content of #138 (monic, the only correct case — `restrictedFaaDiBruno
Match_of_monic`/§139) to a weight bound on a concrete `𝒪`-element.  That bound is **false without a
`deg R` bound** (`P1MonicWeightRefutation.weight_refuted` — the `ξ`-division shifts injected `X`-degree
onto a `Y`-power, breaking `Λ ≤ Λ(Y) = 1`) and **holds with one** (`P1MonicWeightHolds.weight_holds`);
the genuine BCIKS20 invariant is this weight bound under the paper's degree-bounded `R`.  The general
proof is the Newton-cancellation that absorbs `Λ(ξ⁻¹)` — out of reach of the merely *sub*-additive
weight calculus (`weight_Λ_over_𝒪_mul_le`), hence the genuine remaining core.  Axiom-clean.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The explicit `𝒪`-quotient witness `a` of the successor clearing
`βHensel (t+1) = a · ξ^{2t+1}` for monic `H` (the chosen witness of the proven divisibility
`xi_pow_dvd_βHensel_succ_of_monic`; unique since `ξ` is a unit). -/
noncomputable def henselQuotient (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (t : ℕ) : 𝒪 H :=
  (xi_pow_dvd_βHensel_succ_of_monic H x₀ R hHyp hlc t).choose

/-- The explicit quotient clears: `henselQuotient t · ξ^{2t+1} = βHensel (t+1)`.  This is the
divisibility conjunct of `SuccDivWeightLe_of_monic`, now with the explicit witness in hand. -/
lemma henselQuotient_mul_xi (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (t : ℕ) :
    henselQuotient H x₀ R hHyp hlc t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)
      = βHensel H x₀ R hHyp (t + 1) :=
  (xi_pow_dvd_βHensel_succ_of_monic H x₀ R hHyp hlc t).choose_spec.symm

/-- **The open #138 weight core (monic case) isolated to one explicit element.**

For monic `H`, the carved successor predicate `SuccDivWeightLe_of_monic` (the existential
`∀ t, ∃ a, βHensel (t+1) = a·ξ^{2t+1} ∧ Λ_𝒪(a) ≤ 1`) is **equivalent** to the weight bound on the
single explicit quotient `henselQuotient t`.  Forward: `ξ^{2t+1}` a unit ⇒ the witness `a` is forced
equal to `henselQuotient t` (`IsUnit.mul_left_inj`).  Backward: `henselQuotient` clears
(`henselQuotient_mul_xi`), supplying the existential.  This eliminates the existential and discharges
the divisibility, leaving the weight bound on a concrete `𝒪`-element as the *entire* remaining open
content of #138 (monic). -/
theorem succDivWeightLe_iff_henselQuotient_weight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (D : ℕ) (hH : 0 < H.natDegree) :
    (∀ t : ℕ, ∃ a : 𝒪 H,
        βHensel H x₀ R hHyp (t + 1) = a * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)
          ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
      ↔ (∀ t : ℕ, weight_Λ_over_𝒪 hH (henselQuotient H x₀ R hHyp hlc t) D ≤ WithBot.some 1) := by
  constructor
  · intro hh t
    obtain ⟨a, ha_eq, ha_wt⟩ := hh t
    have hv : IsUnit ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)) :=
      (isUnit_ξ_of_monic H x₀ R hHyp hlc).pow (2 * t + 1)
    have h1 : a * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)
        = henselQuotient H x₀ R hHyp hlc t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) := by
      rw [← ha_eq, henselQuotient_mul_xi]
    have hcancel : a = henselQuotient H x₀ R hHyp hlc t := hv.mul_left_inj.mp h1
    rw [← hcancel]; exact ha_wt
  · intro hh t
    exact ⟨henselQuotient H x₀ R hHyp hlc t,
      (henselQuotient_mul_xi H x₀ R hHyp hlc t).symm, hh t⟩

end BCIKS20.HenselNumerator

section AxiomAudit
#print axioms BCIKS20.HenselNumerator.henselQuotient_mul_xi
#print axioms BCIKS20.HenselNumerator.succDivWeightLe_iff_henselQuotient_weight
end AxiomAudit
