/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2RootBridge
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine

/-!
# BCIKS20 P2 root bridge consumers for the genuine §5 claims

This cold module keeps the analytic P2 root/equality surfaces from `P2RootBridge` connected to
the genuine §5 Claim 5.8/5.8' API in `S5Genuine`, without touching either hot source file.

The hard #139 content remains the term-level Faà-di-Bruno / `(A.1)` partition equality.  The
wrappers here only say that, once the assembled Hensel numerator is known to be a root of `Q`
(or equal to the genuine Hensel lift, or once the all-order monic P2 theorem is available), the
already-proven §5 largeness argument can consume the result through `LiftIdentityAt`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.S5Genuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The downstream `LiftIdentityAt` predicate supplied directly by the analytic assembled-root
form of P2. -/
theorem LiftIdentityAt.of_assembledRoot {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) (t : ℕ) :
    LiftIdentityAt H x₀ R hHyp t :=
  BCIKS20.HenselNumerator.βHensel_lift_identity_of_assembledSeries_isRoot
    H x₀ R hHyp hroot t

/-- The downstream `LiftIdentityAt` predicate supplied by identifying the assembled numerator
series with the genuine Hensel lift. -/
theorem LiftIdentityAt.of_assembled_eq_gamma {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (heq : βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp) (t : ℕ) :
    LiftIdentityAt H x₀ R hHyp t := by
  have hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 := by
    rw [heq]
    exact gammaGenuine_root hHyp
  exact LiftIdentityAt.of_assembledRoot H hHyp hroot t

/-- The downstream `LiftIdentityAt` predicate supplied by the all-order monic P2 theorem. -/
theorem LiftIdentityAt.of_leadingCoeff_one {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    LiftIdentityAt H x₀ R hHyp t :=
  LiftIdentityAt.of_restrictedMatch H hHyp
    (BCIKS20.HenselNumerator.restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc) t

/-- Claim 5.8 from the analytic assembled-root form of P2. -/
theorem claim58_genuine_via_assembledRoot {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 :=
  claim58_genuine H hHyp hlarge (LiftIdentityAt.of_assembledRoot H hHyp hroot t)

/-- Claim 5.8 from the assembled-series equality with the genuine Hensel lift. -/
theorem claim58_genuine_via_assembled_eq_gamma {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (heq : βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp)
    {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 :=
  claim58_genuine H hHyp hlarge (LiftIdentityAt.of_assembled_eq_gamma H hHyp heq t)

/-- Claim 5.8 from the all-order monic P2 theorem. -/
theorem claim58_genuine_via_leadingCoeff_one {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 :=
  claim58_genuine H hHyp hlarge (LiftIdentityAt.of_leadingCoeff_one H hHyp hlc t)

/-- Claim 5.8' tail vanishing from the analytic assembled-root form of P2. -/
theorem claim58prime_genuine_tail_via_assembledRoot {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
  claim58prime_genuine_tail H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_assembledRoot H hHyp hroot t)

/-- Claim 5.8' polynomial form from the analytic assembled-root form of P2. -/
theorem claim58prime_genuine_via_assembledRoot {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : (𝕃 H)⟦X⟧) :=
  claim58prime_genuine H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_assembledRoot H hHyp hroot t)

/-- Claim 5.8' tail vanishing from the assembled-series equality with the genuine Hensel lift. -/
theorem claim58prime_genuine_tail_via_assembled_eq_gamma {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (heq : βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
  claim58prime_genuine_tail H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_assembled_eq_gamma H hHyp heq t)

/-- Claim 5.8' tail vanishing from the all-order monic P2 theorem. -/
theorem claim58prime_genuine_tail_via_leadingCoeff_one {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
  claim58prime_genuine_tail H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_leadingCoeff_one H hHyp hlc t)

/-- Claim 5.8' polynomial form from the assembled-series equality with the genuine Hensel lift. -/
theorem claim58prime_genuine_via_assembled_eq_gamma {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (heq : βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : (𝕃 H)⟦X⟧) :=
  claim58prime_genuine H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_assembled_eq_gamma H hHyp heq t)

/-- Claim 5.8' polynomial form from the all-order monic P2 theorem. -/
theorem claim58prime_genuine_via_leadingCoeff_one {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : (𝕃 H)⟦X⟧) :=
  claim58prime_genuine H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_leadingCoeff_one H hHyp hlc t)

#print axioms LiftIdentityAt.of_assembledRoot
#print axioms LiftIdentityAt.of_assembled_eq_gamma
#print axioms LiftIdentityAt.of_leadingCoeff_one
#print axioms claim58_genuine_via_assembledRoot
#print axioms claim58_genuine_via_assembled_eq_gamma
#print axioms claim58_genuine_via_leadingCoeff_one
#print axioms claim58prime_genuine_tail_via_assembledRoot
#print axioms claim58prime_genuine_via_assembledRoot
#print axioms claim58prime_genuine_tail_via_assembled_eq_gamma
#print axioms claim58prime_genuine_via_assembled_eq_gamma
#print axioms claim58prime_genuine_tail_via_leadingCoeff_one
#print axioms claim58prime_genuine_via_leadingCoeff_one

end BCIKS20.HenselNumerator.S5Genuine
