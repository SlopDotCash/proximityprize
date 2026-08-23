/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LocalizedPlaceEvaluation
import ArkLib.Data.Polynomial.RationalFunctionsStrong

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- `emb ξ ≠ 0` from `ξ ≠ 0` (the embedding is injective). -/
theorem emb_ξ_ne_zero {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) :
    embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0 := by
  intro h0
  exact hξ (embeddingOf𝒪Into𝕃_injective (Fact.out) (by rw [h0, map_zero]))

/-- **The localization-to-`𝕃` injection (step 2 of the `hαβ` plan):** the `awayLift` of the
embedding `𝒪 H ↪ 𝕃 H` along the inverted `ξ`. -/
noncomputable def embLoc {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) :
    Localization.Away (ξ x₀ R H hHyp) →+* 𝕃 H :=
  Localization.awayLift (embeddingOf𝒪Into𝕃 H) (ξ x₀ R H hHyp)
    (isUnit_iff_ne_zero.mpr (emb_ξ_ne_zero hHyp hξ))

/-- `embLoc` restricts to the embedding on `𝒪 H`. -/
theorem embLoc_comp {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (a : 𝒪 H) :
    embLoc hHyp hξ (algebraMap (𝒪 H) (Localization.Away (ξ x₀ R H hHyp)) a)
      = embeddingOf𝒪Into𝕃 H a := by
  unfold embLoc
  exact IsLocalization.lift_eq _ a

set_option maxHeartbeats 1000000 in
/-- **`embLoc` is injective** (`lift_injective_iff`: both sides reduce to `x = y` — the
structure map is injective since `ξ ≠ 0` in the domain `𝒪 H`, and the embedding is injective). -/
theorem embLoc_injective {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) :
    Function.Injective (embLoc hHyp hξ) := by
  unfold embLoc Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  haveI hdom : IsDomain (𝒪 H) := by
    refine (Ideal.Quotient.isDomain_iff_prime _).mpr ?_
    have hirr : Irreducible (H_tilde' H) :=
      irreducibleHTilde'OfIrreducible (H := H) (Fact.out) (Fact.out)
    exact (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  constructor
  · intro h
    obtain ⟨c, hc⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers (ξ x₀ R H hHyp)) _).mp h
    obtain ⟨n, hn⟩ := c.2
    have hc0 : (c : 𝒪 H) ≠ 0 := by
      rw [← hn]
      exact pow_ne_zero _ hξ
    have hxy : x = y := by
      have hc' : (c : 𝒪 H) * x = (c : 𝒪 H) * y := by
        simpa [mul_comm] using hc
      exact mul_left_cancel₀ hc0 hc'
    rw [hxy]
  · intro h
    rw [embeddingOf𝒪Into𝕃_injective (Fact.out) h]

end ArkLib

#print axioms ArkLib.embLoc
#print axioms ArkLib.embLoc_comp
#print axioms ArkLib.embLoc_injective
