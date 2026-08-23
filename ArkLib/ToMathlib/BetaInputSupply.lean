/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.KeystoneStrictResidual
import ArkLib.ToMathlib.KeystoneAssembly
import ArkLib.ToMathlib.GammaFromBeta
import ArkLib.ToMathlib.HPzBridge
import ArkLib.ToMathlib.MpProducer
import ArkLib.ToMathlib.HenselDatumProducer
import ArkLib.ToMathlib.BetaWeightCollapse
import ArkLib.ToMathlib.IngredientCBridge
import ArkLib.ToMathlib.SubstFieldCaveat

/-!
# Instantiation lemmas for the §5 input bundle `BetaCurveInput`

The keystone front door
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec`
consumes, per received curve `u`, the genuine BCIKS20 §5 / App-A.4 *input* bundle
`KeystoneStrictResidual.BetaCurveInput u` (`KeystoneStrictResidual.lean`).  That bundle has many
fields; this file builds it **field by field from more primitive §5 data**, discharging or reducing
every field that the 28 verified bricks already handle and leaving only the genuine geometric inputs
as documented named hypotheses.

## Per-field disposition (see `betaCurveInput_of_section5` below)

* `x₀, R, H, hHyp, Bcoeff, hH, D, hD, matchingSet, root, Ppoly, hrep, hdegX` — **carried through**:
  these are the abstract §5 function-field setup, the GS-interpolant factorization data `(R, H)` and
  the Prop-5.5 polynomial representative `(Ppoly, hrep, hdegX)`.  No brick *creates* them; they are
  the genuine output of the (in-tree) GS interpolation chain, supplied as inputs.
* `hsubst` — **discharged by `SubstFieldCaveat` at `x₀ = 0`** (the F1 caveat: over the field `𝕃 H`
  the BCIKS substitution `X ↦ X − x₀` satisfies `HasSubst` *iff* `x₀ = 0`).  This is the genuine
  geometric reduction: centring the GS lift at the origin makes `hsubst` automatic.
* `hγ` — **reduced to `hβ`** (the numerator identification `β R t = betaRec …`) via
  `GammaFromBeta.hγ_field_of_betaEq`.  `hβ` is the single honest §5 / App-A.4 residual (it becomes
  `rfl` once the in-tree `β_regular` is replaced by `betaRec`, the deferred `L13` drop-in).
* `mp` — **reduced** from the abstract `BetaMatchingVanishes.MatchingPoint` bundle to the *smallest*
  per-point Hensel inputs via `MpProducer.mkMatchingPoint` (the explicit ingredient-C per-`z` root
  geometry — root membership, mod-`X` congruences, unit derivative — plus the `π_z`-specialised
  bridging facts).  Carried as a per-point producer hypothesis (genuine §5 input).
* `hcard` — **reduced** from the opaque `weight_Λ_over_𝒪`-comparison to a *concrete arithmetic*
  cardinality bound `#matchingSet > (2t+1)·d·D·d_H` via the verified weight collapse
  `BetaWeightCollapse.betaRec_weight_le_concrete` (`d = R.natDegree`).  The collapse's App-A budget
  inputs (`hbB`, `hBzero`, `hbξ`) are carried as documented hypotheses.
* `hPz` — **reduced** (uniformly in the decoded family `P`) from the per-`z` polynomial identity to
  the per-`z` Hensel root datum via `HPzBridge.hPz_of_henselDatum`.

The measure of success: the hypothesis list of `betaCurveInput_of_section5` is strictly more
primitive than the raw `BetaCurveInput` bundle — `hsubst` is gone (discharged), `hγ` is replaced by
the single `hβ`, the opaque `weight_Λ_over_𝒪` of `hcard` is replaced by concrete arithmetic, and the
abstract `MatchingPoint`/identity fields are replaced by their smallest Hensel inputs.

No `sorry`/`axiom`/`native_decide`; `#print axioms` at the bottom shows only
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling `KeystoneStrictResidual.lean`.
set_option linter.style.longLine false
-- The wrapper carries `[DecidableEq ι]`/`[Nonempty ι]` because the downstream keystone *proof*
-- needs them; the unused-binder linter only inspects types, so disable it.
set_option linter.unusedDecidableInType false


open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace BetaInputSupply

open KeystoneStrictResidual HPzBridge HcardDischarge BetaToCurveCoeffPolys Claim59Conditional
open ProximityGap Polynomial Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Per-field supply lemma: `hsubst` discharged at the centre `x₀ = 0` (F1)

Over the field `𝕃 H` the BCIKS shift series `X ↦ X − x₀` has constant coefficient `fieldTo𝕃 (-x₀)`,
which is nilpotent (= zero, the ring being reduced) iff `x₀ = 0`.  Centring the GS lift therefore
makes the `hsubst` field automatic — `SubstFieldCaveat.shiftSeries` and
`Claim59Conditional.shiftSeries`
are the same definition, so the proof transfers definitionally. -/

omit [Fintype F] [DecidableEq F] in
/-- **`hsubst` at the centre.**  For `x₀ = 0` the BCIKS substitution underlying `γ` is valid: the
`hsubst` field of `BetaCurveInput` holds for free.  (`SubstFieldCaveat.hasSubst_shiftSeries_zero`
applied to the defeq `Claim59Conditional.shiftSeries 0 H`.) -/
theorem hsubst_field_of_centre {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    PowerSeries.HasSubst (Claim59Conditional.shiftSeries (0 : F) H) :=
  SubstFieldCaveat.hasSubst_shiftSeries_zero

/-! ## Per-field supply lemma: the concrete `hcard` bridge

`hcard` compares `#matchingSet` to the opaque weight `weight_Λ_over_𝒪 hH (betaRec … t) D · d_H`.
The verified collapse `BetaWeightCollapse.betaRec_weight_le_concrete` bounds the weight above by the
concrete `(2t+1)·d·D` (with `d = R.natDegree`); multiplying by `d_H` and chaining gives the field
from a *concrete arithmetic* cardinality hypothesis. -/

omit [Fintype F] [DecidableEq F] in
/-- Multiplying a `WithBot ℕ` weight bound on the right by a nat is monotone, and the product of
two nat-coercions is the nat-coercion of the product.  Proven by `WithBot` casework (the only
nontrivial branch is `a = some a₀`, where it reduces to `Nat.mul_le_mul_right`). -/
private theorem withBot_mul_right_le {a : WithBot ℕ} {c d : ℕ}
    (h : a ≤ (c : WithBot ℕ)) : a * (d : WithBot ℕ) ≤ ((c * d : ℕ) : WithBot ℕ) := by
  have hcd : ((c * d : ℕ) : WithBot ℕ) = (c : WithBot ℕ) * (d : WithBot ℕ) := by
    push_cast; ring
  rw [hcd]
  gcongr

omit [Fintype F] [DecidableEq F] in
/-- **The concrete `hcard` bridge (per index `t`).**  Under the App-A weight-budget inputs of
`betaRec_weight_le_concrete` (`hbB`, `hBzero`, `hbξ`) and the standing degree facts, a *concrete*
cardinality bound `#matchingSet > (2t+1)·d·D·d_H` (with `d = R.natDegree`) implies the genuine
`hcard`-field inequality `#matchingSet > weight_Λ_over_𝒪 hH (betaRec … t) D · d_H`. -/
theorem hcard_of_concrete (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D d : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd1 : 1 ≤ d) (hdH_le : H.natDegree ≤ d) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (d - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        d - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D
        ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    {matchingSet : Finset F} {t : ℕ}
    (hconcrete : (↑matchingSet.card : WithBot ℕ) > (((2 * t + 1) * d * D * H.natDegree : ℕ) : WithBot ℕ)) :
    (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree := by
  have hwt : weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ) :=
    betaRec_weight_le_concrete x₀ R H hHyp Bcoeff hD hH hd1 hdH_le hdH_D
      hbB hBzero hbξ t
  have hmul : weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * (H.natDegree : WithBot ℕ)
      ≤ ((((2 * t + 1) * d * D) * H.natDegree : ℕ) : WithBot ℕ) :=
    withBot_mul_right_le (by simpa using hwt)
  -- Align the two concrete nat products and chain `≤ < `.
  refine lt_of_le_of_lt hmul ?_
  have : (((2 * t + 1) * d * D) * H.natDegree : ℕ) = ((2 * t + 1) * d * D * H.natDegree : ℕ) := by
    ring
  rw [this]
  exact hconcrete

omit [Fintype F] [DecidableEq F] in
/-- **The finite-range concrete `hcardFin` bridge.**  This is the corrected F5-compatible variant of
`hcard_of_concrete`: a concrete arithmetic cardinality bound only on the finite range `[k,T]` yields
the exact `Section5StrictDataFin.hcardFin` field consumed by `KeystoneAssembly`. -/
theorem hcardFin_of_concrete (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D d k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd1 : 1 ≤ d) (hdH_le : H.natDegree ≤ d) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (d - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        d - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D
        ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    {matchingSet : Finset F}
    (hconcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > (((2 * t + 1) * d * D * H.natDegree : ℕ) : WithBot ℕ)) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree := by
  intro t hkt htT
  exact hcard_of_concrete x₀ R H hHyp Bcoeff hD hH hd1 hdH_le hdH_D
    hbB hBzero hbξ (hconcreteFin t hkt htT)

/-! ## Corrected finite §5 bundle from centered concrete inputs

The final strict path consumes `HcardDischarge.Section5StrictDataFin`, not the older infinite-tail
`BetaCurveInput`.  The wrapper below is the centered, concrete-cardinality version of
`KeystoneAssembly.section5DataFin_of_producers`: it discharges `hsubst` at `x₀ = 0`, converts the
finite arithmetic L9/L10 bound with `hcardFin_of_concrete`, and accepts the smaller
`SepHenselInput` surface for `hPz`. -/

/-- **Centered concrete finite §5 input supply.**

Builds the corrected `Section5StrictDataFin` bundle consumed by
`KeystoneAssembly.keystone_of_section5Inputs_strict` from primitive centered §5 data.  Compared with
`KeystoneAssembly.section5DataFin_of_producers`, this wrapper removes two plumbing fields:

* `hsubst`, supplied by `hsubst_field_of_centre`;
* opaque `hcardFin`, supplied from the concrete finite cardinality inequality via
  `hcardFin_of_concrete`.

It also lowers the Hensel input from raw `HPzBridge.HenselDatum` to the separable
`HenselDatumProducer.SepHenselInput`, using `HenselDatumProducer.henselDatum_of_sepInput`. -/
noncomputable def section5DataFin_of_centered_concrete {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (b : GSFactorData.Bundle (F := F) (0 : F))
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    -- the Prop-5.5 linear representative of `γ` (fixes `T := Ppoly.natDegree`):
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ (0 : F) b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- finite-range per-point matching producer:
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) b.R b.H b.hHyp Bcoeff t z (root z))
    -- concrete finite L9/L10 weight-collapse inputs (`d = b.R.natDegree`):
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
    (hcardConcreteFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree →
        (↑matchingSet.card : WithBot ℕ)
          > (((2 * t + 1) * b.R.natDegree * b.D * b.H.natDegree : ℕ) : WithBot ℕ))
    -- the numerator residual replacing `hγ`:
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec (0 : F) b.R b.H b.hHyp Bcoeff t)
    -- per-`z` separable Hensel input + degree bounds (yielding `hPz`):
    (hSep : ∀ v₀ v₁ : F[X],
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.SepHenselInput
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  KeystoneAssembly.section5DataFin_of_producers
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    (x₀ := (0 : F)) b Bcoeff matchingSet root Ppoly hrep hdegX mpPoint
    (hcardFin_of_concrete (0 : F) b.R b.H b.hHyp Bcoeff b.hD b.hH
      hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin)
    hsubst_field_of_centre hβ
    (fun v₀ v₁ hlin => HenselDatumProducer.henselDatum_of_sepInput (hSep v₀ v₁ hlin))
    hdeg

/-! ## Matching-divisibility finite §5 bundle from centered concrete inputs

The GS extractor naturally supplies matching-factor divisibility over the pushed-forward coefficient
ring rather than an already-separated Hensel witness.  The wrapper below exposes that route directly
for the finite strict supplier consumed by `KeystoneAssembly`, reusing
`HenselDatumProducer.henselDatum_of_matchingDvdInput` for the final `hPz` field. -/

/-- **Centered concrete finite §5 input supply from matching divisibility.**

This is the `MatchingDvdInput` counterpart of `section5DataFin_of_centered_concrete`.  It keeps the
same centered setup, finite cardinality bridge, numerator identification, and degree hypotheses, but
accepts the GS-extractor-faithful matching-divisibility input for every linear representative. -/
noncomputable def section5DataFin_of_centered_concrete_matchingDvd {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (b : GSFactorData.Bundle (F := F) (0 : F))
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    -- the Prop-5.5 linear representative of `γ` (fixes `T := Ppoly.natDegree`):
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ (0 : F) b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- finite-range per-point matching producer:
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) b.R b.H b.hHyp Bcoeff t z (root z))
    -- concrete finite L9/L10 weight-collapse inputs (`d = b.R.natDegree`):
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
    (hcardConcreteFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree →
        (↑matchingSet.card : WithBot ℕ)
          > (((2 * t + 1) * b.R.natDegree * b.D * b.H.natDegree : ℕ) : WithBot ℕ))
    -- the numerator residual replacing `hγ`:
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec (0 : F) b.R b.H b.hHyp Bcoeff t)
    -- per-`z` matching-divisibility input + degree bounds (yielding `hPz`):
    (hMatchingDvd : ∀ v₀ v₁ : F[X],
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.MatchingDvdInput
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  KeystoneAssembly.section5DataFin_of_producers
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    (x₀ := (0 : F)) b Bcoeff matchingSet root Ppoly hrep hdegX mpPoint
    (hcardFin_of_concrete (0 : F) b.R b.H b.hHyp Bcoeff b.hD b.hH
      hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin)
    hsubst_field_of_centre hβ
    (fun v₀ v₁ hlin =>
      HenselDatumProducer.henselDatum_of_matchingDvdInput (hMatchingDvd v₀ v₁ hlin))
    hdeg

/-! ## The assembly: `betaCurveInput_of_section5`

We assemble `BetaCurveInput u` from the reduced, per-field primitive data.  The remaining named
hypotheses are exactly the genuine §5 / App-A.4 geometric inputs (none is `≡` the conclusion). -/

/-- **The §5 input-bundle instantiation lemma.**

Builds `KeystoneStrictResidual.BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u`
(the genuine §5 / App-A.4 input bundle the keystone Johnson branch consumes) from the reduced,
per-field primitive data:

Carried-through §5 setup (the GS-interpolant factorization + Prop-5.5 representative — no brick
creates these, they are genuine inputs):
* `R, H, hHyp, Bcoeff, hH, D, hD` — the function-field / numerator setup;
* `matchingSet, root` — the geometric large set with its rational-root section;
* `Ppoly, hrep, hdegX` — the Prop-5.5 linear-in-`Z` polynomial representative of `γ`.

Discharged / reduced fields:
* **`x₀ = 0`** — the F1 centring; makes `hsubst` automatic via `hsubst_field_of_centre`;
* `hβ` (the numerator identification) replaces the `hγ` field, discharged by
  `GammaFromBeta.hγ_field_of_betaEq`;
* `mp` is supplied directly (already in `MatchingPoint` shape — callers use
`MpProducer.mkMatchingPoint`
  to build each point from the smallest Hensel inputs);
* `hcardConcrete` (a *concrete arithmetic* per-`t` cardinality bound) plus the App-A weight budgets
  `hbB`/`hBzero`/`hbξ` produce the genuine `hcard` field via `hcard_of_concrete`;
* `hHensel`/`hdegPz` (per `P`, per `(v₀,v₁)`: the per-`z` Hensel root datum and the curve-parameter
  degree bounds) produce the `hPz` field via `HPzBridge.hPz_of_henselDatum`.

Conclusion: the full `BetaCurveInput` bundle. -/
noncomputable def betaCurveInput_of_section5 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    -- §5 function-field setup (carried through):
    (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses (0 : F) R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    -- Prop-5.5 representative (carried through):
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ (0 : F) R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- the single honest §5 / App-A.4 numerator-identification residual (replaces `hγ`):
    (hβ : ∀ t, β (H := H) R t = betaRec (0 : F) R H hHyp Bcoeff t)
    -- ingredient-C per-point matching (genuine §5 input; built per point via `MpProducer`):
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) R H hHyp Bcoeff t z (root z))
    -- the concrete L9/L10 weight-collapse data (`d = R.natDegree`):
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
    -- the §5 specialisation bridge, reduced to the per-`z` matching-divisibility input:
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
    BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u where
  x₀ := (0 : F)
  R := R
  H := H
  hHirr := hIrr
  hHpos := hPos
  hHyp := hHyp
  Bcoeff := Bcoeff
  hH := hH
  D := D
  hD := hD
  matchingSet := matchingSet
  root := root
  hsubst := hsubst_field_of_centre
  hγ := GammaFromBeta.hγ_field_of_betaEq (0 : F) R H hHyp Bcoeff hβ
  Ppoly := Ppoly
  hrep := hrep
  hdegX := hdegX
  mp := mp
  hcard := by
    intro t hkt
    exact hcard_of_concrete (0 : F) R H hHyp Bcoeff hD hH hd1 hdH_le hdH_D
      hbB hBzero hbξ (hcardConcrete t hkt)
  hPz := by
    intro P v₀ v₁ hlin
    exact hPz_of_matchingDvdInput (fun v₀' v₁' hlin' => hMatchingDvd P v₀' v₁' hlin') (hdegPz P) v₀ v₁ hlin

/-! ## The satisfiable assembly: `betaCurveInputFin_of_section5`

The F5-corrected counterpart of `betaCurveInput_of_section5`: builds the *satisfiable*
`KeystoneStrictResidual.BetaCurveInputFin u` from centered concrete finite-range §5 data.  The
over-strong infinite-range `hcard`/`mp` of `betaCurveInput_of_section5` are replaced by the
truncation index `T`, the finite-range concrete cardinality bound `hcardConcreteFin` (converted to
`hcardFin` via `hcardFin_of_concrete`), the finite-range matching producer `mpFin`, and the explicit
algebraic-degree datum `htailDeg` (the bounded-`Z`-degree truncation of `γ`, Prop 5.5).  Because the
cardinality budget is required only on `[k, T]`, the bundle is satisfiable in principle (no
remaining `∀-t` blowup — see `KeystoneStrictResidual.betaCurveInputFin_hcardFin_satisfiable`). -/

/-- **The F5-corrected §5 input-bundle instantiation lemma (satisfiable).**

Builds `KeystoneStrictResidual.BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ)
u`
from the reduced, per-field primitive data, with the finite-range counting interface that makes the
weight budget satisfiable.  Differs from `betaCurveInput_of_section5` only in:
* a truncation index `T` with finite-range `mpFin`/`hcardConcreteFin` (vs. infinite-range
`mp`/`hcardConcrete`);
* the explicit algebraic-degree datum `htailDeg` covering `t > T`. -/
noncomputable def betaCurveInputFin_of_section5 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    -- §5 function-field setup (carried through):
    (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses (0 : F) R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    -- the Lemma-A.1 truncation index:
    (T : ℕ)
    -- Prop-5.5 representative (carried through):
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ (0 : F) R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- the single honest §5 / App-A.4 numerator-identification residual (replaces `hγ`):
    (hβ : ∀ t, β (H := H) R t = betaRec (0 : F) R H hHyp Bcoeff t)
    -- ingredient-C per-point matching over the **finite** range `k ≤ t ≤ T`:
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) R H hHyp Bcoeff t z (root z))
    -- the concrete L9/L10 weight-collapse data (`d = R.natDegree`):
    (hd1 : 1 ≤ R.natDegree) (hdH_le : H.natDegree ≤ R.natDegree) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (R.natDegree - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ (0 : F) R H hHyp) D
        ≤ (WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    -- the **finite-range** concrete cardinality bound (satisfiable for a fixed large
    -- `matchingSet`):
    (hcardConcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > (((2 * t + 1) * R.natDegree * D * H.natDegree : ℕ) : WithBot ℕ))
    -- the algebraic-degree datum: beyond `T` the Hensel coefficients vanish (bounded `Z`-degree):
    (htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta (0 : F) R H hHyp Bcoeff t = 0)
    -- the §5 specialisation bridge, reduced to the per-`z` matching-divisibility input:
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
    BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u where
  x₀ := (0 : F)
  R := R
  H := H
  hHirr := hIrr
  hHpos := hPos
  hHyp := hHyp
  Bcoeff := Bcoeff
  hH := hH
  D := D
  hD := hD
  matchingSet := matchingSet
  root := root
  T := T
  hsubst := hsubst_field_of_centre
  hγ := GammaFromBeta.hγ_field_of_betaEq (0 : F) R H hHyp Bcoeff hβ
  Ppoly := Ppoly
  hrep := hrep
  hdegX := hdegX
  mpFin := mpFin
  hcardFin := hcardFin_of_concrete (0 : F) R H hHyp Bcoeff hD hH hd1 hdH_le hdH_D
    hbB hBzero hbξ hcardConcreteFin
  htailDeg := htailDeg
  hPz := by
    intro P v₀ v₁ hlin
    exact hPz_of_matchingDvdInput (fun v₀' v₁' hlin' => hMatchingDvd P v₀' v₁' hlin') (hdegPz P) v₀ v₁ hlin

end BetaInputSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BetaInputSupply.hsubst_field_of_centre
#print axioms ArkLib.BetaInputSupply.hcard_of_concrete
#print axioms ArkLib.BetaInputSupply.hcardFin_of_concrete
#print axioms ArkLib.BetaInputSupply.section5DataFin_of_centered_concrete
#print axioms ArkLib.BetaInputSupply.section5DataFin_of_centered_concrete_matchingDvd
#print axioms ArkLib.BetaInputSupply.betaCurveInput_of_section5
#print axioms ArkLib.BetaInputSupply.betaCurveInputFin_of_section5
