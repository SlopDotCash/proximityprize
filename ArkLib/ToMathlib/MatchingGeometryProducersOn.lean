/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingGeometryProducers
import ArkLib.ToMathlib.BetaMatchingVanishesOn

/-!
# Issue #304 — restricted-root (`rootOn`) versions of the §5 keystone producers

`ArkLib/ToMathlib/BetaMatchingVanishesOn.lean` (satisfiability finding #3) established that
total root families `root : (z : F) → rationalRoot (H_tilde' H) z` are unsatisfiable for
typical irreducible GS factors (empty fibres at non-split `z`); the honest shape is
`rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z`.  That file repaired the
ingredient-C **consumer** chain.  This file repairs the **producer** side
(`ArkLib/ToMathlib/MatchingGeometryProducers.lean`), which still takes total families.

The repair is cheap because the underlying supply machinery is genuinely per-point:
`MpFinSupply.mkMatchingPoint_of_graph_vanishing` consumes a single
`root : rationalRoot (H_tilde' H) z` at a single `z`; the total family in
`MpFinSupply.mpFin_of_close_word` is only ever evaluated at matching-set members.  So the
restricted producers are obtained by re-threading the same per-point constructors with
`rootOn z hz` in place of `root z` — no analysis is re-proven.

What is proven here (all axiom-clean, no sorry):

* `mpFinOn_of_close_word` — restricted-root threading of the per-point constructor over the
  finite counting range (the `rootOn` analogue of `MpFinSupply.mpFin_of_close_word`).
* `mpFinOn_of_henselData_polyProximate` (+ `_dvd` variant) — the `rootOn` analogues of the
  `mpPoint` producer upgrades of `MatchingGeometryProducers`: per-`(t,z)` `haP_coeff`
  discharged by truncation (`coeff_coe_eq_zero_of_natDegree_lt`), `t`-uniform unit readings,
  and the only per-`(t,z)` input being the L12 `α_t`-identity `hαβ` — now stated at
  `rootOn z hz`, demanding no rational roots off the matching set.
* `mpPointOn_of_polyProximate_at_T` — **the restricted `mpPoint` producer**: identical to
  `mpPoint_of_polyProximate_at_T` except that the total `root` is replaced by `rootOn`, the
  `hαβ` reading uses `rootOn z hz`, and the conclusion is the membership-dependent family
  `∀ t ∈ [k, deg Ppoly], ∀ z (hz : z ∈ matchingSet), MatchingPoint … (rootOn z hz)`.
* `mpPoint_total_of_mpPointOn` — strictness bridge: whenever a total family happens to
  exist, instantiating `rootOn := fun z _ => root z` in the restricted producer yields
  *verbatim* (definitionally) the total-shape `mpPoint` field that
  `KeystoneAssembly.section5DataFin_of_producers` / `section5DataFin_of_producers_badSet`
  consume.  So the restricted producers strictly generalize the total ones.
* `tail_zero_on_finite_rangeOn` / `tail_zero_of_finite_card_and_degreeOn` — the bridging
  lemmas for the remaining bundle fields: the **only** field of `Section5StrictDataFin`
  whose type consumes `root` is `mpFin`, and the only consumer of `mpFin` is
  `HcardDischarge.tail_zero_on_finite_range` (fired inside
  `curveCoeffPolys_of_section5DataFin` via `tail_zero_of_finite_card_and_degree`), whose
  conclusion `αFromBeta … t = 0` is root-free.  Both are re-proven here from the restricted
  data via `BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn`, so the
  restricted producers supply everything the `root`/`mpFin` fields are consumed for.

## The one remaining total-root choke point

`Section5StrictDataFin` (`ArkLib/ToMathlib/HcardDischarge.lean`) stores the **data field**
`root : (z : F) → rationalRoot (H_tilde' H) z`, and its `mpFin` field is typed at `root z`.
Constructing the bundle therefore still demands a total family, even though (a) every use
of `root` in the bundle's consumers is at matching-set members only, and (b) the full
analytic content extracted from `root`/`mpFin`/`hcardFin` — the α-tail vanishing — is
recovered in restricted form by `tail_zero_of_finite_card_and_degreeOn` below.  The honest
repair is the field migration `root ↦ rootOn` inside `Section5StrictDataFin` (touching
`HcardDischarge`, `KeystoneAssembly`, and the bundle construction sites) — a source edit
outside this file's scope.  Until that migration, `section5DataFin_of_producers` /
`…_badSet` remain callable from the restricted producers only when a total family exists
(`mpPoint_total_of_mpPointOn`); for non-fibrewise-totally-split GS factors the bundle
itself is the unsatisfiable object, exactly as finding #3 predicts.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open PowerSeries

namespace ArkLib

open BetaToCurveCoeffPolys

namespace Match304

section MpPointOn

variable {F : Type} [Field F]
variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-- **Restricted-root finite-range threading.**  The `rootOn` analogue of
`MpFinSupply.mpFin_of_close_word`: the per-point constructor
`MpFinSupply.mkMatchingPoint_of_graph_vanishing` is genuinely pointwise in `z` (it takes a
single rational root at a single place), so threading it over the finite counting range
needs the root section only at matching-set members. -/
def mpFinOn_of_close_word {k T : ℕ} {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (geom : (z : F) → z ∈ matchingSet → MpFinSupply.PlaceGeometry (F := F) z)
    (bridge : ∀ t, k ≤ t → t ≤ T → ∀ z, (hz : z ∈ matchingSet) →
      MpFinSupply.BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        t z (rootOn z hz) (geom z hz).aβ (geom z hz).aP) :
    ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz) :=
  fun t hkt htT z hz =>
    MpFinSupply.mkMatchingPoint_of_graph_vanishing (geom z hz) (bridge t hkt htT z hz)

/-- **Restricted-root `mpFin` producer with the decoded-polynomial proximate root.**
The `rootOn` analogue of `Match304.mpFin_of_henselData_polyProximate`: same Hensel-datum
geometry, same mechanical discharges (`haP_coeff` by truncation, `t`-uniform unit readings),
but the L12 `α_t`-identity `hαβ` is read at `rootOn z hz` — no rational roots are demanded
off the matching set.  No analysis is re-proven: the per-point constructors are re-threaded
through `mpFinOn_of_close_word`. -/
def mpFinOn_of_henselData_polyProximate {k T : ℕ} {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ a₀ : (z : F) → PowerSeries F)
    (Pz : (z : F) → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_root : ∀ z ∈ matchingSet, (f z).IsRoot ((Pz z : PowerSeries F)))
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet,
      (Pz z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : F → F) (a e : ℕ → F → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      PowerSeries.coeff t (aβ z) =
        (π_z z (rootOn z hz)) (betaRec x₀ R H hHyp Bcoeff t) / (w z ^ a t z * x z ^ e t z))
    (hw : ∀ z ∈ matchingSet, w z ≠ 0)
    (hx : ∀ z ∈ matchingSet, x z ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz) :=
  mpFinOn_of_close_word
    (geom := fun z hz =>
      MpFinSupply.placeGeometry_of_henselDatum (z := z) (f z) (aβ z)
        ((Pz z : PowerSeries F)) (a₀ z)
        (haβ_root z hz) (haP_root z hz) (haβ_cong z hz) (haP_cong z hz) (hsep z hz))
    (bridge := fun t hkt htT z hz =>
      MpFinSupply.bridgeData_of_L12 (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp)
        (Bcoeff := Bcoeff) (t := t) (z := z) (root := rootOn z hz)
        (hαβ t hkt htT z hz) (hw z hz) (hx z hz)
        (coeff_coe_eq_zero_of_natDegree_lt (hPdeg z hz) hkt))

/-- **Restricted-root `mpFin` producer, `MatchingExtractor`/divisibility route.**  As
`mpFinOn_of_henselData_polyProximate`, but the proximate-root membership arrives as the GS
matching-factor divisibility `(Y − P_z) ∣ f_z` (the Gap-B keystone / `MatchingExtractor`
output shape), converted inside `MpFinSupply.placeGeometry_of_matchingDvd`. -/
def mpFinOn_of_henselData_dvd_polyProximate {k T : ℕ} {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ a₀ : (z : F) → PowerSeries F)
    (Pz : (z : F) → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_dvd : ∀ z ∈ matchingSet,
      (Polynomial.X - Polynomial.C ((Pz z : PowerSeries F))) ∣ f z)
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet,
      (Pz z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : F → F) (a e : ℕ → F → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      PowerSeries.coeff t (aβ z) =
        (π_z z (rootOn z hz)) (betaRec x₀ R H hHyp Bcoeff t) / (w z ^ a t z * x z ^ e t z))
    (hw : ∀ z ∈ matchingSet, w z ≠ 0)
    (hx : ∀ z ∈ matchingSet, x z ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz) :=
  mpFinOn_of_close_word
    (geom := fun z hz =>
      MpFinSupply.placeGeometry_of_matchingDvd (z := z) (f z) (aβ z)
        ((Pz z : PowerSeries F)) (a₀ z)
        (haβ_root z hz) (haP_dvd z hz) (haβ_cong z hz) (haP_cong z hz) (hsep z hz))
    (bridge := fun t hkt htT z hz =>
      MpFinSupply.bridgeData_of_L12 (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp)
        (Bcoeff := Bcoeff) (t := t) (z := z) (root := rootOn z hz)
        (hαβ t hkt htT z hz) (hw z hz) (hx z hz)
        (coeff_coe_eq_zero_of_natDegree_lt (hPdeg z hz) hkt))

/-- **The restricted-root `mpPoint` family in the `section5DataFin_of_producers` shape**
(`T := Ppoly.natDegree`): identical to `mpPoint_of_polyProximate_at_T` except that the total
family `root : (z : F) → rationalRoot …` is replaced by the honest membership-dependent
`rootOn : ∀ z ∈ matchingSet, rationalRoot …` (satisfiability finding #3), the L12 reading
`hαβ` is taken at `rootOn z hz`, and the conclusion is the membership-dependent matching
family.  Pure instantiation of `mpFinOn_of_henselData_polyProximate`. -/
noncomputable def mpPointOn_of_polyProximate_at_T
    {k : ℕ} (Ppoly : F[X][Y]) {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ a₀ : (z : F) → PowerSeries F)
    (Pz : (z : F) → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_root : ∀ z ∈ matchingSet, (f z).IsRoot ((Pz z : PowerSeries F)))
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet,
      (Pz z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : F → F) (a e : ℕ → F → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      PowerSeries.coeff t (aβ z) =
        (π_z z (rootOn z hz)) (betaRec x₀ R H hHyp Bcoeff t) / (w z ^ a t z * x z ^ e t z))
    (hw : ∀ z ∈ matchingSet, w z ≠ 0)
    (hx : ∀ z ∈ matchingSet, x z ≠ 0) :
    ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz) :=
  mpFinOn_of_henselData_polyProximate (k := k) (T := Ppoly.natDegree)
    f aβ a₀ Pz hPdeg haβ_root haP_root haβ_cong haP_cong hsep w x a e hαβ hw hx

/-- **Strictness bridge: the restricted producer recovers the total-shape `mpPoint` field
whenever a total family exists.**  Instantiating `rootOn := fun z _ => root z` in any
restricted family yields — definitionally — the exact total-shape `mpPoint` input of
`KeystoneAssembly.section5DataFin_of_producers` / `section5DataFin_of_producers_badSet`.
So the restricted producers strictly generalize the total ones; the total form is needed
only because `Section5StrictDataFin.root` is (still) a total data field. -/
def mpPoint_total_of_mpPointOn {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mpOn : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z
        ((fun z (_ : z ∈ matchingSet) => root z) z hz)) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  mpOn

end MpPointOn

/-! ## The bridging lemmas for the `Section5StrictDataFin.root`/`mpFin` fields

`root` is consumed by exactly one field of `Section5StrictDataFin` — `mpFin` — and `mpFin`
is consumed by exactly one downstream lemma — `HcardDischarge.tail_zero_on_finite_range`
(fired inside `curveCoeffPolys_of_section5DataFin` via
`tail_zero_of_finite_card_and_degree`), whose conclusion `αFromBeta … t = 0` does not
mention `root` at all.  Both are re-proven here from the restricted data, so the restricted
producers supply the full analytic content the total fields are consumed for. -/

section TailZeroOn

variable {F : Type} [Field F]

/-- **Restricted-root finite-range counting branch** — the `rootOn` analogue of
`HcardDischarge.tail_zero_on_finite_range`: from the membership-dependent matching family
and the finite-range weight bound, the Hensel-lift coefficient `αFromBeta … t` vanishes on
`[k, T]`.  Routed through the restricted consumer chain
(`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn`). -/
theorem tail_zero_on_finite_rangeOn (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mpFinOn : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    ∀ t, k ≤ t → t ≤ T → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t hkt htT
  have hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
    BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn
      x₀ R H hHyp Bcoeff t hH D hD (mpFinOn t hkt htT) (hcardFin t hkt htT)
  exact alphaFromBeta_eq_zero_of_embedding_zero x₀ R H hHyp Bcoeff hemb

/-- **Restricted-root composed truncation** — the `rootOn` analogue of
`HcardDischarge.tail_zero_of_finite_card_and_degree`: restricted finite-range counting data
plus the algebraic-degree datum give the full infinite α-tail vanishing that the
power-series-truncation consumer (`curveCoeffPolys_of_section5DataFin`'s engine) needs.
This is everything `Section5StrictDataFin` extracts from its `root`/`mpFin`/`hcardFin`
fields, now available without any total root family. -/
theorem tail_zero_of_finite_card_and_degreeOn (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mpFinOn : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
  HcardDischarge.tail_zero_of_range_and_degree
    (tail_zero_on_finite_rangeOn x₀ R H hHyp Bcoeff hH D hD k T mpFinOn hcardFin)
    htailDeg

end TailZeroOn

end Match304

end ArkLib

-- Axiom audit: every declaration must rest only on [propext, Classical.choice, Quot.sound].
#print axioms ArkLib.Match304.mpFinOn_of_close_word
#print axioms ArkLib.Match304.mpFinOn_of_henselData_polyProximate
#print axioms ArkLib.Match304.mpFinOn_of_henselData_dvd_polyProximate
#print axioms ArkLib.Match304.mpPointOn_of_polyProximate_at_T
#print axioms ArkLib.Match304.mpPoint_total_of_mpPointOn
#print axioms ArkLib.Match304.tail_zero_on_finite_rangeOn
#print axioms ArkLib.Match304.tail_zero_of_finite_card_and_degreeOn
