/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed

/-!
# `hcard` satisfiability triage and the corrected finite-range interface

## The satisfiability question (F5 finding)

`Section5StrictData.hcard`
(`ArkLib/ToMathlib/CorrelatedAgreementListDecodingClosed.lean`) currently demands the
**Lemma-A.1 counting bound for every tail index simultaneously**:

```
hcard : ∀ t, k ≤ t → (#matchingSet : WithBot ℕ)
          > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
```

Against the *genuine* [BCIKS20] App-A.2 / L10 weight bound this is **OVER-STRONG**, for the
same structural reason as the earlier F3 `htele` trap:

* The proven L10 weight bound (`RationalFunctions.β_regular`, in the shape
  `weight_Λ_over_𝒪 hH β D ≤ (2*t+1) * Bivariate.natDegreeY R * D`) **grows linearly and
  unboundedly in `t`**.  The genuine `betaRec … t` numerator is a sum of products of `t`
  earlier `betaRec` factors with powers of `W` and `ξ`, so the `X`-degree of its canonical
  representative — and hence its `Λ`-weight — increases without bound as `t → ∞`.
* `matchingSet : Finset F` is **fixed** (it is the §5 agreement set `S_β`, of size
  `≈ (1-δ)·|domain|`, independent of `t`).
* A fixed finite cardinality cannot dominate an unbounded sequence: there is **no**
  `matchingSet` for which `#matchingSet > weight(betaRec t)·d_H` holds for *all* `t ≥ k`
  once the weight bound is taken at face value.  Hence `hcard` is not satisfiable from the
  §5 largeness hypothesis `hlarge` alone — it would require a (false) uniform-in-`t` bound.

The Lemma-A.1 counting argument is genuinely available only for the **finite range**
`k ≤ t ≤ T`, where `T` is the largest index with `weight(betaRec T)·d_H < #matchingSet`
(`T ≈ #matchingSet / (2·d_R·D·d_H)`).  This is exactly how [BCIKS20] App-A.4 uses it: per-`t`
for `t` up to a degree bound `T`.

For `t > T` the counting argument **cannot** fire.  The resolution in App-A.4 is *algebraic*,
not combinatorial: the §5 representative `γ` is a rational function of `Z` of **bounded
`Z`-degree** (Prop 5.5 gives `degreeX P ≤ 1`, i.e. the curve is linear in `Z`), so its
power-series numerator `αFromBeta` has a finite `Z`-degree and `αFromBeta t = 0` holds for
`t > T` *automatically*, by degree truncation.

## What this file provides

Because the *downstream* consumer
(`BetaToCurveCoeffPolys.tail_zero_of_betaRec_embedding_zero`
→ `subst_mk_eq_aeval_trunc_of_tail_zero`) genuinely needs the **infinite** tail
`∀ t, k ≤ t → αFromBeta … t = 0` (a power series equals its truncation only if *all* higher
coefficients vanish), we cannot simply weaken it to a finite range.  Instead we split the
tail vanishing into its two honest sources and recombine:

1. `tail_zero_of_finite_card_and_degree` — the **truncation lemma**: from
   * `mp`/`hcard` over the **finite** range `k ≤ t ≤ T` (the counting argument, genuinely
     dischargeable from a large fixed `matchingSet`), giving `αFromBeta t = 0` for `k ≤ t ≤ T`;
   * `htailDeg : ∀ t, T < t → αFromBeta … t = 0` — the **explicit** algebraic-degree datum
     (the bounded-`Z`-degree truncation of `γ`; this is genuine §5 data, *isolated as a
     hypothesis*, never `= goal`),
   conclude the full `∀ t, k ≤ t → αFromBeta … t = 0`.

2. `Section5StrictDataFin` — the corrected bundle, with the finite-range `mp`/`hcard` plus the
   degree datum `htailDeg`, and otherwise identical to `Section5StrictData`.

3. `curveCoeffPolys_of_section5DataFin` — re-derives the `CurveCoeffPolys` deliverable for the
   corrected bundle, routing through `tail_zero_of_finite_card_and_degree`.

4. `hcoeffPoly_witness_of_section5DataFin` — the front-door `∃ B` witness for the corrected
   bundle.

The point: with the corrected interface, `hcard` is **satisfiable** (the finite-range
counting bound *can* be discharged from `hlarge`), and the previously hidden
unbounded-in-`t` obligation is surfaced as the explicit, honest algebraic-degree hypothesis
`htailDeg`.

`#print axioms` of every theorem here is `[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A.2 (weight `Λ`), A.4 (recursion (A.1), Claims A.1/A.2).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory

namespace ArkLib

namespace HcardDischarge

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 1 — the finite-range counting branch gives the tail on `[k, T]`

The over-strong infinite-range `hcard`/`mp` are replaced by the **finite-range** versions
`k ≤ t ≤ T`.  The Lemma-A.1 counting bridge
(`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large`) is fired only for
`t` in that range, where a fixed large `matchingSet` genuinely dominates `weight(betaRec t)·d_H`.
This yields the tail vanishing on `[k, T]`. -/

omit [Fintype F] [DecidableEq F] in
/-- **Finite-range counting branch.**  From the ingredient-C matching data and the L9/L10 weight
bound over the *finite* range `k ≤ t ≤ T` (the honestly dischargeable counting bound), the
Hensel-lift coefficient `αFromBeta … t` vanishes for `k ≤ t ≤ T`.  This is `tail_zero_of_betaRec
_embedding_zero` restricted to the finite range — exactly the range over which the Lemma-A.1
counting argument is valid for a fixed `matchingSet`. -/
theorem tail_zero_on_finite_range (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    ∀ t, k ≤ t → t ≤ T → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t hkt htT
  have hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
    BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large
      x₀ R H hHyp Bcoeff t hH D hD (mpFin t hkt htT) (hcardFin t hkt htT)
  exact alphaFromBeta_eq_zero_of_embedding_zero x₀ R H hHyp Bcoeff hemb

/-! ## Step 2 — the truncation lemma: finite-range + degree datum ⟹ full tail

The downstream `subst_mk_eq_aeval_trunc_of_tail_zero` needs the **infinite** tail.  We obtain it
by combining the counting branch (range `[k, T]`) with the explicit algebraic-degree datum
`htailDeg` (range `(T, ∞)`).  This is purely the case split `t ≤ T ∨ T < t`; the genuine §5
content is isolated entirely in the hypothesis `htailDeg` (the bounded-`Z`-degree truncation of
`γ`), which is a hypothesis, NOT the goal. -/

omit [Fintype F] [DecidableEq F] in
/-- **The truncation lemma (the F5 repair).**  Pure recombination: if `αFromBeta` vanishes on the
counting range `[k, T]` and the degree datum `htailDeg` gives vanishing on `(T, ∞)`, then the full
tail `∀ t ≥ k, αFromBeta … t = 0` holds — exactly what the power-series-truncation consumer needs.

The `(T, ∞)` part is the genuine algebraic-degree argument (`γ` has bounded `Z`-degree, so its
numerator's coefficients vanish past the degree); it is supplied as the **explicit** hypothesis
`htailDeg`, never derived from the goal. -/
theorem tail_zero_of_range_and_degree
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {k T : ℕ}
    (hrange : ∀ t, k ≤ t → t ≤ T → αFromBeta x₀ R H hHyp Bcoeff t = 0)
    (htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t hkt
  rcases le_or_gt t T with htT | htT
  · exact hrange t hkt htT
  · exact htailDeg t htT

omit [Fintype F] [DecidableEq F] in
/-- **The composed truncation lemma (counting + degree ⟹ full tail).**  Bundles
`tail_zero_on_finite_range` with `tail_zero_of_range_and_degree`: the finite-range counting data
plus the algebraic-degree datum give the full infinite α-tail vanishing that
`BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` (via `subst_mk_eq_aeval_trunc_of_tail_zero`)
consumes.  This is the corrected replacement for the call into
`tail_zero_of_betaRec_embedding_zero` with the over-strong infinite-range `hcard`. -/
theorem tail_zero_of_finite_card_and_degree (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
  tail_zero_of_range_and_degree
    (tail_zero_on_finite_range x₀ R H hHyp Bcoeff hH D hD k T mpFin hcardFin)
    htailDeg

/-! ## Step 3 — the corrected bundle `Section5StrictDataFin`

Identical to `Section5StrictData` except that the over-strong infinite-range `mp`/`hcard` are
replaced by:
* a truncation index `T`,
* the finite-range `mpFin`/`hcardFin` (the genuinely dischargeable counting bound), and
* the explicit algebraic-degree datum `htailDeg` (the bounded-`Z`-degree truncation of `γ`).

All other fields are carried over verbatim. -/

/-- **The corrected §5 per-decoding extraction datum** (the satisfiable replacement for
`Section5StrictData`).  See the file header for the F5 satisfiability verdict.  The infinite-range
`hcard` is replaced by `T`/`hcardFin`/`htailDeg`. -/
structure Section5StrictDataFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- centre / curve data of [BCIKS20] §5. -/
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  root : (z : F) → rationalRoot (H_tilde' H) z
  /-- the Lemma-A.1 truncation index: the largest tail index for which the fixed `matchingSet`
  dominates `weight(betaRec t)·d_H`.  Replaces the (false) uniform-in-`t` largeness. -/
  T : ℕ
  /-- ingredient-C per-point matching data over the **finite** counting range `k ≤ t ≤ T`. -/
  mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  /-- the L9/L10 weight bound over the **finite** counting range `k ≤ t ≤ T` (the satisfiable
  form of `hcard`: a fixed large `matchingSet` *can* dominate the weight for `t ≤ T`). -/
  hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  /-- the **algebraic-degree datum**: beyond the truncation index `T`, the Hensel-lift coefficients
  vanish for the bounded-`Z`-degree reason (Prop 5.5: `γ` is linear in `Z`, hence its power-series
  numerator has finite degree).  This is the genuine §5 content that *replaces* the unsatisfiable
  unbounded-in-`t` counting obligation — isolated explicitly, never equal to the goal. -/
  htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0
  /-- validity of the BCIKS substitution `X ↦ X − x₀`. -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  /-- the Claim-5.9 substitution form of `γ` built from the genuine Hensel coefficients. -/
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  /-- the Prop-5.5 polynomial representative of `γ`. -/
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- the §5 specialisation bridge: at each good `z`, `P z` equals the linear representative at
      `Z = z` (per-point evaluation identity, NOT the per-coefficient conclusion). -/
  hPz : ∀ v₀ v₁ : F[X],
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

/-! ## Step 4 — re-derive the deliverable for the corrected bundle

We re-prove `curveCoeffPolys_of_betaRec`'s body for the corrected bundle.  The only change from
`curveCoeffPolys_of_section5Data` is that the α-tail vanishing now comes from
`tail_zero_of_finite_card_and_degree` (finite counting + degree datum) instead of the over-strong
infinite-range `hcard`.  Everything downstream of `htail` is unchanged §5 algebra. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The corrected §5 datum yields the per-coefficient curve-polynomial datum on the good set,
routing the α-tail vanishing through `tail_zero_of_finite_card_and_degree` (the F5-repaired,
satisfiable interface).  `betaRec` is genuinely consumed. -/
theorem curveCoeffPolys_of_section5DataFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P := by
  haveI := d.hIrr
  haveI := d.hPos
  -- The repaired tail: finite-range counting + algebraic-degree datum ⟹ full infinite tail.
  have htail : ∀ t, k ≤ t → BetaToCurveCoeffPolys.αFromBeta d.x₀ d.R d.H d.hHyp d.Bcoeff t = 0 :=
    tail_zero_of_finite_card_and_degree d.x₀ d.R d.H d.hHyp d.Bcoeff d.hH d.D d.hD k d.T
      d.mpFin d.hcardFin d.htailDeg
  -- Re-run the §5 algebra of `curveCoeffPolys_of_betaRec` from `htail` onwards.
  -- (Steps C–D of `curveCoeffPolys_of_betaRec`, verbatim, but with our repaired `htail`.)
  have htrunc :
      γ d.x₀ d.R d.H d.hHyp =
        Polynomial.aeval (Claim59Conditional.shiftSeries d.x₀ d.H)
          (PowerSeries.trunc k
            (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta d.x₀ d.R d.H d.hHyp d.Bcoeff))) := by
    rw [d.hγ]
    exact subst_mk_eq_aeval_trunc_of_tail_zero d.hsubst htail
  obtain ⟨v₀, v₁, hPpoly⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one d.hdegX
  have hlin :
      γ d.x₀ d.R d.H d.hHyp = polyToPowerSeries𝕃 d.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
    rw [← d.hrep, hPpoly]
  obtain ⟨hPeval, hd₀, hd₁⟩ := d.hPz v₀ v₁ hlin
  exact BetaToCurveCoeffPolys.curveCoeffPolys_of_linear_representative v₀ v₁ hd₀ hd₁ hPeval

omit [Nonempty ι] [DecidableEq ι] in
/-- The corrected §5 datum yields the bundled `hcoeffPoly` existential the front door consumes
(identical statement to `hcoeffPoly_witness_of_section5Data`, but from the satisfiable bundle). -/
theorem hcoeffPoly_witness_of_section5DataFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys u P
    (curveCoeffPolys_of_section5DataFin d)

/-! ## Step 5 — bridge: the original over-strong bundle refines into the corrected one

For completeness/back-compatibility: any `Section5StrictData` (the over-strong bundle) trivially
yields a `Section5StrictDataFin` (the satisfiable bundle) — choose any `T`, restrict `mp`/`hcard`
to `[k,T]`, and take `htailDeg` from the original infinite-range vanishing (which the original
bundle *does* prove, via `tail_zero_of_betaRec_embedding_zero`).  This shows the corrected
interface is **weaker** (hence strictly more honest): it asks for less.  The converse fails — that
is precisely the F5 finding. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The over-strong `Section5StrictData` refines into the satisfiable `Section5StrictDataFin`
(taking `T := k`, so the counting range is the single index `k` and `htailDeg` covers `t > k` from
the original infinite-range vanishing).  Demonstrates the corrected interface asks for strictly
less. -/
noncomputable def section5DataFin_of_section5Data {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  haveI := d.hIrr
  haveI := d.hPos
  -- the original bundle proves the full infinite tail
  have htailAll : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta d.x₀ d.R d.H d.hHyp d.Bcoeff t = 0 :=
    BetaToCurveCoeffPolys.tail_zero_of_betaRec_embedding_zero
      d.x₀ d.R d.H d.hHyp d.Bcoeff d.hH d.D d.hD k d.mp d.hcard
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    Bcoeff := d.Bcoeff, hH := d.hH, D := d.D, hD := d.hD, matchingSet := d.matchingSet,
    root := d.root, T := k,
    mpFin := fun t hkt _ => d.mp t hkt,
    hcardFin := fun t hkt _ => d.hcard t hkt,
    htailDeg := fun t htk => htailAll t (le_of_lt htk),
    hsubst := d.hsubst, hγ := d.hγ, Ppoly := d.Ppoly, hrep := d.hrep, hdegX := d.hdegX,
    hPz := d.hPz }

end HcardDischarge

end ArkLib

/-! ## Axiom audit — every declaration here must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.HcardDischarge.tail_zero_on_finite_range
#print axioms ArkLib.HcardDischarge.tail_zero_of_range_and_degree
#print axioms ArkLib.HcardDischarge.tail_zero_of_finite_card_and_degree
#print axioms ArkLib.HcardDischarge.curveCoeffPolys_of_section5DataFin
#print axioms ArkLib.HcardDischarge.hcoeffPoly_witness_of_section5DataFin
#print axioms ArkLib.HcardDischarge.section5DataFin_of_section5Data
