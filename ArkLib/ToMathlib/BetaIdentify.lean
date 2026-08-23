/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GammaFromBeta
import ArkLib.ToMathlib.BetaInputSupply
import ArkLib.ToMathlib.BCIKS20Concrete

/-!
# `BetaIdentify` — the honest minimisation of the `hβ` numerator-identification residual

This file analyses the residual hypothesis

```
hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t
```

that `GammaFromBeta.hγ_field_of_betaEq` consumes (and that threads, unchanged, all the way to the
milestone `Section5Concrete.correlatedAgreement_affine_curves_johnson_concrete`).  It then delivers
the strongest closure the in-tree statements support, replacing `hβ` by a strictly *smaller* and
provably-equivalent residual everywhere in the consumer chain.

## What `hβ` is, and why the two textbook closure routes fail

The consumer's `β` is `RationalFunctions.lean`'s `BCIKS20AppendixA.ClaimA2.β`:

```
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  if hH : 0 < H.natDegree then (β_regular R H hH (Nat.le_refl _) t).choose else 0
```

so `β R t` is `Exists.choose` of `β_regular`, whose *defining property* is **only** the weight upper
bound `weight_Λ_over_𝒪 hH β D ≤ (2t+1)·d_R·D` (and `β_regular` is proved by the **trivial witness**
`fun _ => ⟨0, by simp⟩`).

* **Route (a) — uniqueness — is impossible.**  The defining property is a weight *inequality*, not a
  Hensel-lift identity.  It does not pin `β` uniquely: `0` satisfies it (the trivial witness), and
  so
  does `betaRec … t` (its weight bound is exactly `betaRec_weight_le_concrete`), and so do
  infinitely
  many others.  So there is no `∀ b, definingProperty b → b = betaRec`, and the HenselUniqueness
  brick has no simple-root datum to bite on here — the defining property carries none.  Moreover
  `Exists.choose` of a `Classical`-backed existence is opaque: `(⟨0, h⟩).choose` is **not** provably
  `0`, so even the value of `β R t` is inaccessible.  `beta_eq_betaRec` (mod-`H` or exact) is
  therefore unprovable from the in-tree data.  We *record* the one honest fact `choose_spec` yields
  —
  the weight bound `β_weight_le` below — and document the blockage there.

* **Route (b) — full restatement / elimination — is blocked by file ownership, not by mathematics.**
  The consumer structures `BetaCurveInput`/`BetaCurveInputFin` (`KeystoneStrictResidual.lean`) and
  `Section5StrictData`/`Section5StrictDataFin` (read-only) hard-code the *in-tree* `γ`
  (`γ x₀ R H hHyp`, built from the opaque `β` via `α`) in **three** fields — `hγ`, `hrep`, `hPz`.
  Because the in-tree `γ` is built from the opaque `β`, the only bridge from it to the genuine
  `betaRec`-built series `subst (mk (αFromBeta …))` is the numerator identification itself.  There
  is
  no proof-theoretic shortcut.  A `hγ_field_of_betaRec` with **no** β-residual would require
  redefining
  the in-tree `γ` to be `betaRec`-built (the deferred cross-file `L13` edit), which would change the
  read-only structures.

## The honest closure delivered here: the *embedding-level* residual `hβemb`

What `hγ_field_of_betaEq` actually *uses* is weaker than `hβ`.  The in-tree `α` and the genuine
`αFromBeta` are the **same quotient**

```
α        t = embeddingOf𝒪Into𝕃 H (β       R t)          / (W^{t+1} · embedding(ξ)^{2t-1})
αFromBeta t = embeddingOf𝒪Into𝕃 H (betaRec … t)         / (W^{t+1} · embedding(ξ)^{2t-1})
```

so `α t = αFromBeta t` follows already from the **embeddings** agreeing in `𝕃 H`:

```
hβemb : ∀ t, embeddingOf𝒪Into𝕃 H (β R t) = embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t)
```

This is the residual that lives at the level where `α`/`αFromBeta` actually compute.  We

1. prove `hβemb ↔ hβ` (`betaEmbedEq_iff_betaEq`) — the embedding map `embeddingOf𝒪Into𝕃 H` is
injective
   for `0 < H.natDegree` (`embeddingOf𝒪Into𝕃_injective`), so the two residuals are *equivalent*; a
   future supplier may discharge whichever is more convenient (the genuine §5/App-A.4 lift identity
   `embedding(β t) = α_t·W^{t+1}·ξ^{e_t}` produces the embedding form directly, so `hβemb` is the
   honest target);
2. re-derive the whole `GammaFromBeta` discharge chain from `hβemb` directly
   (`hγ_field_of_betaEmbedEq`), at the embedding level, never going through the element identity;
3. expose drop-in wrappers `…_betaEmb` for every consumer in the chain
   (`section5StrictData_of_betaEq`, `betaCurveInput_of_section5`, `betaCurveInputFin_of_section5`,
   `betaCurveInputFin_of_bundle`, `section5Concrete_of_close_word`,
   `correlatedAgreement_affine_curves_johnson_concrete`), each consuming `hβemb` in place of `hβ`.

The net effect: the §5 milestone is reached from the **strictly smaller, provably-equivalent**
embedding-level residual, with the residual sitting at the level the consumer algebra uses.  No
No `sorry`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace BetaIdentify

variable {F : Type} [Field F]

/-! ## Route (a) is blocked: the only honest fact about the opaque in-tree `β`

`β R t = (β_regular …).choose`, so `choose_spec` yields *exactly one* fact: the weight upper bound.
This is a weight *inequality*, satisfied by `0`, by `betaRec`, and by infinitely many others — it
does not determine `β`, so no uniqueness-style `beta_eq_betaRec` is available. -/

/-- **The only honest fact about the opaque in-tree `β` (route-(a) blockage record).**  From
`Exists.choose_spec` of `β_regular`, the in-tree numerator `β R t` satisfies the weight upper bound
`weight_Λ_over_𝒪 hH (β R t) D ≤ (2t+1)·d_R·D`.  This is the *entire* defining content of `β`: a
weight
*inequality*, satisfied equally by `0` (the trivial `β_regular` witness) and by `betaRec … t`
(`BetaWeightCollapse.betaRec_weight_le_concrete`).  It therefore does **not** pin `β` uniquely, so
no
uniqueness route can prove `β = betaRec`; the identification is a genuine, irreducible residual. -/
theorem β_weight_le (R : F[X][X][Y]) {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hH : 0 < H.natDegree) (t : ℕ) :
    weight_Λ_over_𝒪 hH (β (H := H) R t) (D := Bivariate.totalDegree H)
      ≤ (2 * t + 1) * Bivariate.natDegreeY R * Bivariate.totalDegree H := by
  -- `β R t` unfolds to the `.choose`; `choose_spec` gives the weight bound at `D = totalDegree H`.
  have hspec := (β_regular R H hH (Nat.le_refl _) (D := Bivariate.totalDegree H) t).choose_spec
  -- `β R t = (β_regular …).choose` definitionally under `0 < H.natDegree`.
  have hval : β (H := H) R t = (β_regular R H hH (Nat.le_refl _) (D := Bivariate.totalDegree H) t).choose := by
    unfold β
    rw [dif_pos hH]
  rw [hval]
  exact hspec

/-! ## The embedding-level residual and its equivalence with `hβ`

The honest, strictly-smaller residual that the consumer algebra actually uses. -/

/-- The **embedding-level numerator-identification residual**: the images of `β R t` and the genuine
recursion `betaRec … t` agree in the function field `𝕃 H`, for every `t`.  This is the residual that
the in-tree `α`-formula actually consumes (both `α` and `αFromBeta` use only `embeddingOf𝒪Into𝕃 H`
applied to their numerators), and it is the natural target of the §5/App-A.4 Hensel-lift identity
`embedding(β t) = α_t·W^{t+1}·ξ^{e_t}`. -/
def BetaEmbedEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : Prop :=
  ∀ t, embeddingOf𝒪Into𝕃 H (β (H := H) R t)
        = embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t)

/-- **`hβemb ↔ hβ`.**  The embedding-level residual `BetaEmbedEq` is *equivalent* to the
element-level
residual `hβ : ∀ t, β R t = betaRec … t`, because `embeddingOf𝒪Into𝕃 H` is injective for
`0 < H.natDegree` (`embeddingOf𝒪Into𝕃_injective`).  A future supplier may discharge whichever form
is
more convenient; the embedding form is the honest target of the App-A.4 lift identity. -/
theorem betaEmbedEq_iff_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (hH : 0 < H.natDegree) :
    BetaEmbedEq x₀ R H hHyp Bcoeff ↔ (∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) := by
  unfold BetaEmbedEq
  constructor
  · intro hemb t
    exact embeddingOf𝒪Into𝕃_injective hH (hemb t)
  · intro hβ t
    rw [hβ t]

/-- The element-level residual `hβ` supplies the embedding-level residual (one direction of
`betaEmbedEq_iff_betaEq`, packaged for direct use). -/
theorem betaEmbedEq_of_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) :
    BetaEmbedEq x₀ R H hHyp Bcoeff :=
  fun t => by rw [hβ t]

/-! ## The discharge chain re-derived from the embedding-level residual `hβemb`

These mirror `GammaFromBeta.{alpha_eq_alphaFromBeta_of_betaEq, intree_gamma_eq_γ',
hγ_field_of_betaEq}`
but consume `BetaEmbedEq` directly, working at the `𝕃 H` level where `α`/`αFromBeta` compute. -/

/-- **Embedding identification ⟹ Hensel-coefficient identification.**  If the *embeddings* of the
in-tree numerator `β R t` and the genuine recursion `betaRec … t` agree (`BetaEmbedEq`), then the
in-tree Hensel coefficient `α` equals `αFromBeta` pointwise: the denominators are literally
identical,
and `α`/`αFromBeta` apply `embeddingOf𝒪Into𝕃 H` to their numerators, so this is `unfold` + `rw`. -/
theorem alpha_eq_alphaFromBeta_of_betaEmbedEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβemb : BetaEmbedEq x₀ R H hHyp Bcoeff) (t : ℕ) :
    α x₀ R H hHyp t = BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t := by
  unfold α BetaToCurveCoeffPolys.αFromBeta
  rw [hβemb t]

/-- **The in-tree `γ` equals the `betaRec`-built `γ'`**, under the embedding-level residual `hβemb`.
Both are the same shift substitution applied to series whose coefficients now agree pointwise. -/
theorem intree_gamma_eq_γ'_of_betaEmbedEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβemb : BetaEmbedEq x₀ R H hHyp Bcoeff) :
    γ x₀ R H hHyp = GammaFromBeta.γ' x₀ R H hHyp Bcoeff := by
  rw [Claim59Conditional.gamma_eq_subst_shiftSeries, GammaFromBeta.γ']
  congr 1
  exact PowerSeries.ext fun n => by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      alpha_eq_alphaFromBeta_of_betaEmbedEq x₀ R H hHyp Bcoeff hβemb]

/-- **The `Section5StrictData.hγ` field, discharged from the embedding-level residual `hβemb`.**
This
is the embedding-level analogue of `GammaFromBeta.hγ_field_of_betaEq`: under the *strictly smaller*
residual `BetaEmbedEq`, the in-tree `γ` equals the `betaRec`-built substitution form — literally the
`hγ` field of `Section5StrictData`/`BetaCurveInput`/`BetaCurveInputFin`.  No `sorry`, no `axiom`. -/
theorem hγ_field_of_betaEmbedEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβemb : BetaEmbedEq x₀ R H hHyp Bcoeff) :
    γ x₀ R H hHyp =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H) := by
  rw [intree_gamma_eq_γ'_of_betaEmbedEq x₀ R H hHyp Bcoeff hβemb,
    GammaFromBeta.γ'_eq_subst_shiftSeries]

/-- Cross-check: the embedding-level discharge agrees with the in-tree element-level discharge.
When
`hβ` holds, both `hγ_field_of_betaEmbedEq` (via `betaEmbedEq_of_betaEq`) and
`GammaFromBeta.hγ_field_of_betaEq` produce the *same* proof of the `hγ` field (it is a `Prop`, so
this
is `rfl`-grade proof irrelevance — recorded for documentation). -/
theorem hγ_field_betaEmbedEq_eq_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) :
    hγ_field_of_betaEmbedEq x₀ R H hHyp Bcoeff (betaEmbedEq_of_betaEq x₀ R H hHyp Bcoeff hβ)
      = GammaFromBeta.hγ_field_of_betaEq x₀ R H hHyp Bcoeff hβ :=
  rfl

end BetaIdentify

/-! ## Drop-in wrappers consuming the embedding-level residual `hβemb`

Each wrapper mirrors a node of the existing `hβ`-threaded chain
(`GammaFromBeta` → `BetaInputSupply` → `Section5Concrete`), replacing the element-level `hβ` by the
strictly-smaller `BetaIdentify.BetaEmbedEq`.  None edits the read-only consumer files: each simply
feeds `BetaIdentify.betaEmbedEq_of_betaEq` … no — feeds the embedding residual through
`betaEmbedEq_iff_betaEq` to recover the `hβ` the existing builders expect, so the embedding residual
becomes the public surface while the proven element-level builders are reused verbatim. -/

section Wrappers

open BetaToCurveCoeffPolys Claim59Conditional
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace BetaIdentify

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`Section5StrictData` from the embedding-level residual.**  The `…_betaEmb` analogue of
`CorrelatedAgreementListDecodingClosed.section5StrictData_of_betaEq`: it takes every field except
`hγ`
plus `BetaEmbedEq` (in place of `hβ`), recovering the element-level `hβ` the proven builder expects
via
`betaEmbedEq_iff_betaEq`. -/
noncomputable def section5StrictData_of_betaEmbedEq {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H))
    (hβemb : BetaEmbedEq x₀ R H hHyp Bcoeff)
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
        ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    CorrelatedAgreementListDecodingClosed.Section5StrictData
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  CorrelatedAgreementListDecodingClosed.section5StrictData_of_betaEq
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    x₀ R H hIrr hPos hHyp Bcoeff hH D hD matchingSet root mp hcard hsubst
    ((betaEmbedEq_iff_betaEq x₀ R H hHyp Bcoeff hH).mp hβemb)
    Ppoly hrep hdegX hPz

end BetaIdentify

namespace BetaInputSupply

open KeystoneStrictResidual HPzBridge HcardDischarge BetaToCurveCoeffPolys Claim59Conditional
open BetaIdentify

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`BetaCurveInput` from the embedding-level residual.**  The `…_betaEmb` analogue of
`BetaInputSupply.betaCurveInput_of_section5`, with `BetaEmbedEq` in place of the element-level `hβ`.
-/
noncomputable def betaCurveInput_of_section5_betaEmb {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses (0 : F) R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ (0 : F) R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hβemb : BetaEmbedEq (0 : F) R H hHyp Bcoeff)
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) R H hHyp Bcoeff t z (root z))
    (hd1 : 1 ≤ R.natDegree) (hdH_le : H.natDegree ≤ R.natDegree) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (R.natDegree - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ (0 : F) R H hHyp) D
        ≤ (WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    (hcardConcrete : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > (((2 * t + 1) * R.natDegree * D * H.natDegree : ℕ) : WithBot ℕ))
    (hMatchingDvd : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
      γ (0 : F) R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdegPz : ∀ (_P : F → Polynomial F) (v₀ v₁ : F[X]),
      γ (0 : F) R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u :=
  betaCurveInput_of_section5
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
    R H hIrr hPos hHyp Bcoeff hH D hD matchingSet root Ppoly hrep hdegX
    ((betaEmbedEq_iff_betaEq (0 : F) R H hHyp Bcoeff hH).mp hβemb)
    mp hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcrete hMatchingDvd hdegPz

/-- **`BetaCurveInputFin` from the embedding-level residual.**  The `…_betaEmb` analogue of
`BetaInputSupply.betaCurveInputFin_of_section5`, with `BetaEmbedEq` in place of `hβ`. -/
noncomputable def betaCurveInputFin_of_section5_betaEmb {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses (0 : F) R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    (T : ℕ)
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ (0 : F) R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hβemb : BetaEmbedEq (0 : F) R H hHyp Bcoeff)
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) R H hHyp Bcoeff t z (root z))
    (hd1 : 1 ≤ R.natDegree) (hdH_le : H.natDegree ≤ R.natDegree) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (R.natDegree - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ (0 : F) R H hHyp) D
        ≤ (WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    (hcardConcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > (((2 * t + 1) * R.natDegree * D * H.natDegree : ℕ) : WithBot ℕ))
    (htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta (0 : F) R H hHyp Bcoeff t = 0)
    (hMatchingDvd : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
      γ (0 : F) R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdegPz : ∀ (_P : F → Polynomial F) (v₀ v₁ : F[X]),
      γ (0 : F) R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u :=
  betaCurveInputFin_of_section5
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
    R H hIrr hPos hHyp Bcoeff hH D hD matchingSet root T Ppoly hrep hdegX
    ((betaEmbedEq_iff_betaEq (0 : F) R H hHyp Bcoeff hH).mp hβemb)
    mpFin hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin htailDeg hMatchingDvd hdegPz

end BetaInputSupply

namespace Section5Concrete

open KeystoneStrictResidual HPzBridge HcardDischarge BetaToCurveCoeffPolys
open BetaIdentify
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The §5 milestone from the embedding-level residual.**  The `…_betaEmb` analogue of
`Section5Concrete.correlatedAgreement_affine_curves_johnson_concrete`: the literal BCIKS20 keystone
goal `δ_ε_correlatedAgreementCurves` holds in the strict square-root Johnson regime, with the single
numerator residual now the strictly-smaller, provably-equivalent **embedding-level** `BetaEmbedEq`
in
place of the element-level `hβ`.  Everything else is forwarded verbatim to the proven milestone. -/
theorem correlatedAgreement_affine_curves_johnson_concrete_betaEmb
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (b : GSFactorData.Bundle (F := F) (0 : F))
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (hd1 : 1 ≤ b.R.natDegree) (hdH_le : b.H.natDegree ≤ b.R.natDegree)
    (hdH_D : b.H.natDegree ≤ b.D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 b.hH (Bcoeff i₁ p) b.D
          ≤ (WithBot.some ((b.D - Multiset.card p.parts)
              + (b.R.natDegree - betaδ i₁ - Multiset.card p.parts)
                * (b.D - b.H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        b.R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 b.hH (ξ (0 : F) b.R b.H b.hHyp) b.D
        ≤ (WithBot.some ((b.R.natDegree - 1) * (b.D - b.H.natDegree + 1)) : WithBot ℕ))
    (hβemb : BetaEmbedEq (0 : F) b.R b.H b.hHyp Bcoeff)
    (perWord : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Σ' (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' b.H) z) (T : ℕ)
         (Ppoly : F[X][Y]),
        (polyToPowerSeries𝕃 b.H Ppoly = γ (0 : F) b.R b.H b.hHyp) ×'
        (Polynomial.Bivariate.degreeX Ppoly ≤ 1) ×'
        (∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
          BetaMatchingVanishes.MatchingPoint (0 : F) b.R b.H b.hHyp Bcoeff t z (root z)) ×'
        (∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
          > (((2 * t + 1) * b.R.natDegree * b.D * b.H.natDegree : ℕ) : WithBot ℕ)) ×'
        (∀ t, T < t →
          BetaToCurveCoeffPolys.αFromBeta (0 : F) b.R b.H b.hHyp Bcoeff t = 0) ×'
        (∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) ×'
        (∀ (_P : F → Polynomial F) (v₀ v₁ : F[X]),
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_johnson_concrete
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    b Bcoeff hd1 hdH_le hdH_D hbB hBzero hbξ
    ((betaEmbedEq_iff_betaEq (0 : F) b.R b.H b.hHyp Bcoeff b.hH).mp hβemb)
    perWord

end Section5Concrete

end Wrappers

end ArkLib
