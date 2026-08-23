/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellStrictExtraction
import ArkLib.ToMathlib.LocalSeriesBaseRationalReading

/-!
# Issue #304 — fixing the most-common-cell interface direction

## The problem (precisely)

The landed producer `RawGS304.localSeriesDatumOn_of_cell` demands
`hcell : ∀ z ∈ good, z ∈ cell` — the good set INSIDE one incidence cell.  But the proven
combinatorial Claim 5.7 (`Claim57Pigeonhole.claim57_pigeonhole`) outputs the OPPOSITE
inclusion: one LARGE cell inside the (avoided sub-)good set, `T < |cell ∩ S₀|` with
`cell ⊆ S₀`.  The two shapes meet nowhere, so the §5 "pass to the most common cell"
step (BCIKS20 Steps 5–7) could not be expressed against the landed interface.

## The fix (this file)

Weaken the producer interface from the pinned good set to an arbitrary finset `S`:

* `LocalSeriesDatumOnSub k S P` — `FaithfulCurveExtraction.LocalSeriesDatumOn` with every
  per-`z` demand quantified over `z ∈ S` instead of `z ∈ RS_goodCoeffsCurve u δ`
  (note the pinned structure used `u, δ, domain, deg` ONLY through the good set, and `k`
  only through `hn`; so the sub-finset variant needs only `(k, S, P)`);
* round-trip welds `…Sub_of_localSeriesDatumOn` / `localSeriesDatumOn_of_…Sub_good`
  (the new interface is a conservative generalization) and the new freedom
  `LocalSeriesDatumOnSub.mono` (restriction to any sub-finset — impossible at the pinned
  interface, and exactly what "pass to the most common cell" needs);
* `localSeriesDatumOnSub_of_rawGS` — the raw-GS producer of `LocalSeriesProducer.lean`,
  re-targeted at `S` (all its `RawGS304` field welds were already `S`-generic);
* `localSeriesDatumOnSub_of_cell` — **the corrected cell weld**: take `S :=` the claim57
  incidence cell itself; cell MEMBERSHIP (not `good ⊆ cell`) supplies both per-`z` raw GS
  inputs via `cell_conditions_of_mem`;
* `exists_localSeriesDatumOnSub_of_pigeonhole_output` — the weld consuming
  `claim57_pigeonhole`'s ACTUAL per-cell output shape (`hshape` + `∃ c ∈ Index, T < |cell c|`),
  with the genuinely deep per-cell residuals isolated as named hypotheses.

## Downstream soundness (the counting only needs ≥-many points — verified)

The pinned consumers (`CurveFamilyData.hPz`, `KeystoneCapstone.CurveCoeffPolys`,
`StrictCoeffPolysResidual`) quantify over the WHOLE good set, but the underlying counting
chain in `Curves.lean` is already sub-finset-ready:
`decoded_family_coefficients_of_coeff_polys_core`,
`decoded_family_coefficients_assemble_codeword_curve`, and
`decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement` all work on an
arbitrary `S'` with ONLY the cardinality thresholds `|S'| > l + 1` and
`|S'| ≥ (|ι| + 1)·(l + 1)` — and they consume a SPECIFIC decoded family `P`, so a
`P`-dependent most-common cell is fine.  This file proves the full chain:

* `hPz_of_localSeriesDatumOnSub` — the per-`z` Hensel pin `P z = ∑ (z − x₀)^t • c t` on `S`
  (the `S`-generic re-assembly of `curveHenselDatum_of_truncatedLocalRoot_genuine_on` +
  `eval_identity_of_curveHensel`, all of whose per-`z` bricks were already good-set-free);
* `curveCoeffPolys_of_localSeriesDatumOnSub` / `coeffPolyWitness_of_localSeriesDatumOnSub` —
  the coefficient-interpolant extraction on `S` (via the already-finset-generic
  `curveCoeffPolys_of_curveFamily`);
* `jointAgreement_of_localSeriesDatumOnSub` — **the threshold capstone**: a sub-finset datum
  on ANY `S'` with `|S'| > l + 1` and `|S'| ≥ (|ι| + 1)·(l + 1)`, for a decoded family `P`
  on `S'`, already yields the §6 `jointAgreement` conclusion — so the weakening is sound
  end-to-end, and the most-common cell can replace the good set as soon as the pigeonhole
  threshold `T` is taken `≥ (|ι| + 1)·(l + 1)`;
* `jointAgreement_of_pigeonhole_cell` — the composed Steps-5–7 skeleton: claim57 per-cell
  output at threshold `T = (|ι| + 1)·(l + 1)` + per-cell analytic cargo ⟹ `jointAgreement`.

## Honest scope — the isolated deep residuals

NOT claimed (carried as named hypotheses, exactly as in the landed producer lane):

* `htrunc` (`TruncReadingOnSub`) — the §5 Claim-5.9/Prop-5.5 base-rational reading of the
  truncated local series, now demanded only on the cell; the `…_baseRational` adapters derive
  it from the lower-order base-rationality statement `αGenuine t = lift (c t)` plus tail
  vanishing, so raw `htrunc` is no longer primitive on that route;
* `hvanish` — the `αGenuine` tail vanishing (in-tree production lanes exist on the good set;
  the *statement* is `z`-free so it transfers verbatim);
* `hlc` — the monicization residual; `hsep`/`hRsep` — the S5 separable-specialization facts;
* `havoid` — cofinite `elimPoly (ξ)` avoidance (discriminant proven nonzero in-tree:
  `RawGS304.elimPoly_ξ_ne_zero`), now demanded only on the cell — strictly weaker than the
  landed good-set demand.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped BigOperators ENNReal ProbabilityTheory

namespace ArkLib

namespace Threshold304

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the threshold-quantified (sub-finset) producer interface -/

section Interface

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The sub-finset §5 analytic datum** — `FaithfulCurveExtraction.LocalSeriesDatumOn` with
the pinned good set `RS_goodCoeffsCurve u δ` replaced by an arbitrary carrier finset `S`.
Every per-`z` field is demanded at members of `S` only.  Instantiating
`S := RS_goodCoeffsCurve u δ` recovers the landed structure exactly
(`localSeriesDatumOnSub_of_localSeriesDatumOn` / `localSeriesDatumOn_of_localSeriesDatumOnSub_good`);
instantiating `S :=` a claim57 incidence cell is the §5 "pass to the most common cell". -/
structure LocalSeriesDatumOnSub (k : ℕ) (S : Finset F) (P : F → Polynomial F) : Type where
  /-- the expansion centre. -/
  x₀ : F
  /-- the GS interpolant data. -/
  R : F[X][X][Y]
  /-- the (monic) irreducible GS factor. -/
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  hξ : ξ x₀ R H hHyp ≠ 0
  hlc : H.leadingCoeff = 1
  hR : R.Separable
  /-- the number of curve coefficients (at most `k + 1`). -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- the membership-restricted rational-root family — now restricted to `S`. -/
  rootOn : (z : F) → z ∈ S → rationalRoot (H_tilde' H) z
  /-- per-`z` unit condition at members of `S`. -/
  hx : ∀ z (hz : z ∈ S), (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0
  /-- tail vanishing of the genuine Hensel coefficients from `n` on (`z`-free). -/
  hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0
  /-- the per-`z` base-rational reading on `S`. -/
  htrunc : ∀ z (hz : z ∈ S),
    (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
      = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t
  /-- the decoded-side GS matching-factor divisibility on `S`. -/
  hdvd : ∀ z (hz : z ∈ S),
    (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz))))
  /-- the decoded-side order-0 congruence on `S`. -/
  hcong : ∀ z (hz : z ∈ S),
    ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
        (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}

/-- **Restriction (the new freedom).**  A sub-finset datum restricts to any smaller carrier —
the operation the pinned interface could not express, and exactly what "pass to the most
common cell" performs (`good ⊇ cell`, not `good ⊆ cell`). -/
noncomputable def LocalSeriesDatumOnSub.mono {k : ℕ} {S S' : Finset F} {P : F → Polynomial F}
    (hsub : S' ⊆ S) (d : LocalSeriesDatumOnSub k S P) :
    LocalSeriesDatumOnSub k S' P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    hξ := d.hξ, hlc := d.hlc, hR := d.hR, n := d.n, hn := d.hn, c := d.c,
    rootOn := fun z hz => d.rootOn z (hsub hz),
    hx := fun z hz => d.hx z (hsub hz),
    hvanish := d.hvanish,
    htrunc := fun z hz => d.htrunc z (hsub hz),
    hdvd := fun z hz => d.hdvd z (hsub hz),
    hcong := fun z hz => d.hcong z (hsub hz) }

end Interface

/-! ## Part 2 — round trips with the pinned interface (conservative generalization) -/

section RoundTrip

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The pinned datum is the sub-finset datum at `S := RS_goodCoeffsCurve u δ`. -/
noncomputable def localSeriesDatumOnSub_of_localSeriesDatumOn
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    LocalSeriesDatumOnSub k
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    hξ := d.hξ, hlc := d.hlc, hR := d.hR, n := d.n, hn := d.hn, c := d.c,
    rootOn := d.rootOn, hx := d.hx, hvanish := d.hvanish, htrunc := d.htrunc,
    hdvd := d.hdvd, hcong := d.hcong }

/-- Conversely, a sub-finset datum at the full good set is the pinned datum. -/
noncomputable def localSeriesDatumOn_of_localSeriesDatumOnSub_good
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : LocalSeriesDatumOnSub k
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P) :
    FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    hξ := d.hξ, hlc := d.hlc, hR := d.hR, n := d.n, hn := d.hn, c := d.c,
    rootOn := d.rootOn, hx := d.hx, hvanish := d.hvanish, htrunc := d.htrunc,
    hdvd := d.hdvd, hcong := d.hcong }

end RoundTrip

/-! ## Part 3 — raw-GS production on an arbitrary carrier finset -/

section RawGSSub

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The §5 base-rational reading on a selected carrier.**
This is `RawGS304.TruncReadingOn` with the pinned good set replaced by an arbitrary finset `S`.
It is the deep Claim-5.9 / Prop.-5.5 residual needed by the corrected most-common-cell interface;
all other fields of `LocalSeriesDatumOnSub` below are derived from raw GS cell cargo. -/
def TruncReadingOnSub {S : Finset F} (P : F → Polynomial F)
    {H : F[X][Y]} [Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    {R : F[X][X][Y]} (hHyp : Hypotheses (0 : F) R H) (n : ℕ) (c : ℕ → F[X])
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval 0) H = 0) : Prop :=
  ∀ z (hz : z ∈ S)
    (hx : (π_z z (RawGS304.rootOnOfFiber hPos.out hfiber z hz)) (ξ 0 R H hHyp) ≠ 0),
    (PowerSeries.trunc n
        (localSeries hHyp z (RawGS304.rootOnOfFiber hPos.out hfiber z hz) hx) :
      Polynomial F) = ∑ t ∈ Finset.range n, (z - 0) ^ t • c t

omit [Fintype F] in
/-- **Selected-carrier Claim-5.9 from base-rationality.**
The raw `TruncReadingOnSub` input is derivable from the §5 base-rationality statement
`αGenuine t = lift (c t)` below `n`, plus tail vanishing from `n` on.  The resulting curve
coefficients are the transposed coefficients from `LocalSeriesBaseRationalReading`. -/
theorem truncReadingOnSub_of_baseRational {S : Finset F} {P : F → Polynomial F}
    {H : F[X][Y]} [hIrr : Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    {R : F[X][X][Y]} (hHyp : Hypotheses (0 : F) R H)
    (hlc : H.leadingCoeff = 1) {n N : ℕ} {c : ℕ → F[X]} (hnN : n ≤ N)
    (hdeg : ∀ t < n, (c t).natDegree < N)
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval 0) H = 0)
    (hbase : ∀ t < n, αGenuine H 0 R hHyp t = liftToFunctionField (H := H) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine H 0 R hHyp t = 0) :
    TruncReadingOnSub P hHyp N (transposedCurveCoeffs 0 n c) hfiber := by
  intro z hz hx
  exact htrunc_of_base_rational hHyp (Match304.ξ_ne_zero H 0 R hHyp) hlc z
    (RawGS304.rootOnOfFiber hPos.out hfiber z hz) hx hnN hdeg hbase hvanish

/-- **`LocalSeriesDatumOnSub` from raw GS output on an arbitrary carrier.**
This is the corrected most-common-cell producer: the raw factor/root/divisibility/avoidance
conditions are demanded only on `S`, not on the whole good set. The remaining analytic inputs are
the `z`-free tail vanishing and the selected-carrier Claim-5.9 residual
`TruncReadingOnSub`. -/
noncomputable def localSeriesDatumOnSub_of_rawGS
    {k : ℕ} {S : Finset F} {P : F → Polynomial F}
    {R : F[X][X][Y]} {H : F[X][Y]}
    [hIrr : Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses (0 : F) R H)
    (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} (hn : n < k + 2) (c : ℕ → F[X])
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval 0) H = 0)
    (hdvdRaw : ∀ z ∈ S,
      (Polynomial.X - Polynomial.C (P z)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (havoid : ∀ z ∈ S, (elimPoly hPos.out (ξ 0 R H hHyp)).eval z ≠ 0)
    (hvanish : ∀ t, n ≤ t → αGenuine H 0 R hHyp t = 0)
    (htrunc : TruncReadingOnSub P hHyp n c hfiber) :
    LocalSeriesDatumOnSub k S P :=
  { x₀ := 0, R := R, H := H, hIrr := hIrr, hPos := hPos, hHyp := hHyp,
    hξ := Match304.ξ_ne_zero H 0 R hHyp,
    hlc := hlc, hR := hR, n := n, hn := hn, c := c,
    rootOn := RawGS304.rootOnOfFiber hPos.out hfiber,
    hx := RawGS304.hx_of_elimPoly_avoidance hHyp havoid
      (RawGS304.rootOnOfFiber hPos.out hfiber),
    hvanish := hvanish,
    htrunc := fun z hz => htrunc z hz _,
    hdvd := fun z hz =>
      RawGS304.matching_dvd_loc_of_specialized_dvd_centred hHyp z _ _ (hdvdRaw z hz),
    hcong := fun _ hz => RawGS304.hcong_of_fiber_monic hHyp hlc hfiber hz }

/-- **`LocalSeriesDatumOnSub` from raw GS plus base-rationality.**
This is the `htrunc`-free selected-carrier producer: base-rationality below `n` derives the
Claim-5.9 reading at truncation length `N`; tail vanishing is then restricted from `n` to `N`
for the output datum. -/
noncomputable def localSeriesDatumOnSub_of_rawGS_baseRational
    {k : ℕ} {S : Finset F} {P : F → Polynomial F}
    {R : F[X][X][Y]} {H : F[X][Y]}
    [hIrr : Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses (0 : F) R H)
    (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n N : ℕ} (hN : N < k + 2) (hnN : n ≤ N) (c : ℕ → F[X])
    (hdeg : ∀ t < n, (c t).natDegree < N)
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval 0) H = 0)
    (hdvdRaw : ∀ z ∈ S,
      (Polynomial.X - Polynomial.C (P z)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (havoid : ∀ z ∈ S, (elimPoly hPos.out (ξ 0 R H hHyp)).eval z ≠ 0)
    (hbase : ∀ t < n, αGenuine H 0 R hHyp t = liftToFunctionField (H := H) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine H 0 R hHyp t = 0) :
    LocalSeriesDatumOnSub k S P :=
  localSeriesDatumOnSub_of_rawGS hHyp hlc hR hN (transposedCurveCoeffs 0 n c)
    hfiber hdvdRaw havoid
    (fun t ht => hvanish t (hnN.trans ht))
    (truncReadingOnSub_of_baseRational hHyp hlc hnN hdeg hfiber hbase hvanish)

/-- **The corrected cell weld.**
If the selected carrier `S` lies inside one Claim-5.7 incidence cell at the centre `0`, then cell
membership supplies the fiber equation and the specialized matching-factor divisibility needed by
`localSeriesDatumOnSub_of_rawGS`. This direction matches the pigeonhole output: a large cell
inside the good set is enough. -/
noncomputable def localSeriesDatumOnSub_of_cell
    {k : ℕ} {S : Finset F} {P : F → Polynomial F}
    {ι' : Type} {rep : ι' → (F[X])[X][Y]} {S₀ : Finset F} {cc : ι' × F[X][Y]}
    [hIrr : Fact (Irreducible cc.2)] [hPos : Fact (0 < cc.2.natDegree)]
    (hcell : ∀ z ∈ S, z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc)
    (hHyp : Hypotheses (0 : F) (rep cc.1) cc.2)
    (hlc : cc.2.leadingCoeff = 1) (hR : (rep cc.1).Separable)
    {n : ℕ} (hn : n < k + 2) (c : ℕ → F[X])
    (havoid : ∀ z ∈ S,
      (elimPoly hPos.out (ξ 0 (rep cc.1) cc.2 hHyp)).eval z ≠ 0)
    (hvanish : ∀ t, n ≤ t → αGenuine cc.2 0 (rep cc.1) hHyp t = 0)
    (htrunc : TruncReadingOnSub P hHyp n c
      (fun z hz => (RawGS304.cell_conditions_of_mem (hcell z hz)).2)) :
    LocalSeriesDatumOnSub k S P :=
  localSeriesDatumOnSub_of_rawGS hHyp hlc hR hn c
    (fun z hz => (RawGS304.cell_conditions_of_mem (hcell z hz)).2)
    (fun z hz => (RawGS304.cell_conditions_of_mem (hcell z hz)).1)
    havoid hvanish htrunc

/-- **The corrected cell weld from base-rationality.**
Cell membership supplies the raw GS facts, and base-rationality supplies the truncation reading;
the caller no longer has to provide `TruncReadingOnSub` directly. -/
noncomputable def localSeriesDatumOnSub_of_cell_baseRational
    {k : ℕ} {S : Finset F} {P : F → Polynomial F}
    {ι' : Type} {rep : ι' → (F[X])[X][Y]} {S₀ : Finset F} {cc : ι' × F[X][Y]}
    [hIrr : Fact (Irreducible cc.2)] [hPos : Fact (0 < cc.2.natDegree)]
    (hcell : ∀ z ∈ S, z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc)
    (hHyp : Hypotheses (0 : F) (rep cc.1) cc.2)
    (hlc : cc.2.leadingCoeff = 1) (hR : (rep cc.1).Separable)
    {n N : ℕ} (hN : N < k + 2) (hnN : n ≤ N) (c : ℕ → F[X])
    (hdeg : ∀ t < n, (c t).natDegree < N)
    (havoid : ∀ z ∈ S,
      (elimPoly hPos.out (ξ 0 (rep cc.1) cc.2 hHyp)).eval z ≠ 0)
    (hbase : ∀ t < n,
      αGenuine cc.2 0 (rep cc.1) hHyp t = liftToFunctionField (H := cc.2) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine cc.2 0 (rep cc.1) hHyp t = 0) :
    LocalSeriesDatumOnSub k S P :=
  localSeriesDatumOnSub_of_rawGS_baseRational hHyp hlc hR hN hnN c hdeg
    (fun z hz => (RawGS304.cell_conditions_of_mem (hcell z hz)).2)
    (fun z hz => (RawGS304.cell_conditions_of_mem (hcell z hz)).1)
    havoid hbase hvanish

/-- **Bundled analytic cargo on one Claim-5.7 cell.**
This is the exact per-cell producer surface left after the combinatorial pigeonhole:
the carrier is the incidence cell itself, and membership in that cell supplies the raw GS
fiber/divisibility facts.  The remaining fields are the genuine §5 analytic cargo
(`htrunc`, tail vanishing, monic/separable/avoidance data). -/
structure Claim57CellDatum (k : ℕ) (P : F → Polynomial F) : Type 2 where
  ι' : Type
  rep : ι' → (F[X])[X][Y]
  S₀ : Finset F
  cc : ι' × F[X][Y]
  hIrr : Fact (Irreducible cc.2)
  hPos : Fact (0 < cc.2.natDegree)
  hHyp : Hypotheses (0 : F) (rep cc.1) cc.2
  hlc : cc.2.leadingCoeff = 1
  hR : (rep cc.1).Separable
  n : ℕ
  hn : n < k + 2
  c : ℕ → F[X]
  havoid : (letI := hPos
    ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
      (elimPoly hPos.out (ξ 0 (rep cc.1) cc.2 hHyp)).eval z ≠ 0)
  hvanish : ∀ t, n ≤ t → αGenuine cc.2 0 (rep cc.1) hHyp t = 0
  htrunc : (letI := hIrr; letI := hPos
    TruncReadingOnSub (S := GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc)
      P hHyp n c
      (fun _ hz => (RawGS304.cell_conditions_of_mem (rep := rep) (x₀ := 0) (qz := P)
        (S := S₀) (c := cc) hz).2))

/-- The carrier finset of a bundled Claim-5.7 cell datum. -/
noncomputable def Claim57CellDatum.carrier {k : ℕ} {P : F → Polynomial F}
    (d : Claim57CellDatum k P) : Finset F :=
  GuruswamiSudan.OverRatFunc.Claim57.cell d.rep 0 P d.S₀ d.cc

/-- A bundled Claim-5.7 cell datum produces the sub-finset local-series datum on its carrier. -/
noncomputable def Claim57CellDatum.localSeriesDatumOnSub {k : ℕ} {P : F → Polynomial F}
    (d : Claim57CellDatum k P) :
    LocalSeriesDatumOnSub k d.carrier P := by
  letI := d.hIrr
  letI := d.hPos
  exact localSeriesDatumOnSub_of_cell (S := d.carrier) (P := P) (rep := d.rep) (S₀ := d.S₀)
    (cc := d.cc) (fun z hz => hz) d.hHyp d.hlc d.hR d.hn d.c d.havoid d.hvanish
    d.htrunc

/-- Build the bundled Claim57-cell datum from base-rationality, deriving `htrunc` internally. -/
noncomputable def Claim57CellDatum.of_baseRational {k : ℕ} {P : F → Polynomial F}
    {ι' : Type} {rep : ι' → (F[X])[X][Y]} {S₀ : Finset F} {cc : ι' × F[X][Y]}
    [hIrr : Fact (Irreducible cc.2)] [hPos : Fact (0 < cc.2.natDegree)]
    (hHyp : Hypotheses (0 : F) (rep cc.1) cc.2)
    (hlc : cc.2.leadingCoeff = 1) (hR : (rep cc.1).Separable)
    {n N : ℕ} (hN : N < k + 2) (hnN : n ≤ N) (c : ℕ → F[X])
    (hdeg : ∀ t < n, (c t).natDegree < N)
    (havoid : ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
      (elimPoly hPos.out (ξ 0 (rep cc.1) cc.2 hHyp)).eval z ≠ 0)
    (hbase : ∀ t < n,
      αGenuine cc.2 0 (rep cc.1) hHyp t = liftToFunctionField (H := cc.2) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine cc.2 0 (rep cc.1) hHyp t = 0) :
    Claim57CellDatum k P where
  ι' := ι'
  rep := rep
  S₀ := S₀
  cc := cc
  hIrr := hIrr
  hPos := hPos
  hHyp := hHyp
  hlc := hlc
  hR := hR
  n := N
  hn := hN
  c := transposedCurveCoeffs 0 n c
  havoid := havoid
  hvanish := fun t ht => hvanish t (hnN.trans ht)
  htrunc :=
    truncReadingOnSub_of_baseRational hHyp hlc hnN hdeg
      (fun _ hz => (RawGS304.cell_conditions_of_mem (rep := rep) (x₀ := 0) (qz := P)
        (S := S₀) (c := cc) hz).2)
      hbase hvanish

omit [Fintype F] in
/-- **The actual pigeonhole-output weld.**
Given an index set of Claim-5.7 cells, a pigeonhole-selected large cell, containment of every
indexed cell in the ambient good carrier, and analytic cargo on each indexed cell, select the
large carrier and expose it as a `LocalSeriesDatumOnSub`.

This is the shape emitted by `claim57_pigeonhole`: the large object is a cell *inside* the
good set, not a cell containing the whole good set. -/
theorem exists_localSeriesDatumOnSub_of_pigeonhole_output {k T : ℕ}
    {P : F → Polynomial F} {ι' : Type} {rep : ι' → (F[X])[X][Y]}
    {S₀ good : Finset F} {Index : Finset (ι' × F[X][Y])}
    (hlarge : ∃ cc ∈ Index,
      T < (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc).card)
    (hsub : ∀ cc ∈ Index, ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
      z ∈ good)
    (hdatum : ∀ cc ∈ Index,
      Nonempty (LocalSeriesDatumOnSub k
        (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc) P)) :
    ∃ S' : Finset F,
      T < S'.card ∧
        (∀ z ∈ S', z ∈ good) ∧
          Nonempty (LocalSeriesDatumOnSub k S' P) := by
  obtain ⟨cc, hcc, hcard⟩ := hlarge
  exact ⟨GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc, hcard,
    hsub cc hcc, hdatum cc hcc⟩

omit [Fintype F] in
/-- **Pigeonhole-output weld from base-rational per-index fields.**
This is the previous selection theorem with the cellwise `LocalSeriesDatumOnSub` cargo produced
internally by `localSeriesDatumOnSub_of_cell_baseRational`.  The remaining hypotheses are exactly
per-index analytic facts for the Claim57 cells: Hensel hypotheses, monicity/separability,
avoidance, base-rationality below `n`, degree bounds, and tail vanishing. -/
theorem exists_localSeriesDatumOnSub_of_pigeonhole_baseRational_output {k T : ℕ}
    {P : F → Polynomial F} {ι' : Type} {rep : ι' → (F[X])[X][Y]}
    {S₀ good : Finset F} {Index : Finset (ι' × F[X][Y])}
    (hlarge : ∃ cc ∈ Index,
      T < (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc).card)
    (hsub : ∀ cc ∈ Index, ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
      z ∈ good)
    (hIrr : ∀ cc ∈ Index, Irreducible cc.2)
    (hPos : ∀ cc ∈ Index, 0 < cc.2.natDegree)
    (hHyp : ∀ cc (hcc : cc ∈ Index),
      letI : Fact (Irreducible cc.2) := ⟨hIrr cc hcc⟩
      letI : Fact (0 < cc.2.natDegree) := ⟨hPos cc hcc⟩
      Hypotheses (0 : F) (rep cc.1) cc.2)
    (hlc : ∀ cc ∈ Index, cc.2.leadingCoeff = 1)
    (hR : ∀ cc ∈ Index, (rep cc.1).Separable)
    (n N : ι' × F[X][Y] → ℕ) (c : ι' × F[X][Y] → ℕ → F[X])
    (hN : ∀ cc ∈ Index, N cc < k + 2)
    (hnN : ∀ cc ∈ Index, n cc ≤ N cc)
    (hdeg : ∀ cc (_hcc : cc ∈ Index), ∀ t < n cc, (c cc t).natDegree < N cc)
    (havoid : ∀ cc (hcc : cc ∈ Index),
      letI : Fact (Irreducible cc.2) := ⟨hIrr cc hcc⟩
      letI : Fact (0 < cc.2.natDegree) := ⟨hPos cc hcc⟩
      ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
        (elimPoly (hPos cc hcc)
          (ξ 0 (rep cc.1) cc.2 (hHyp cc hcc))).eval z ≠ 0)
    (hbase : ∀ cc (hcc : cc ∈ Index),
      letI : Fact (Irreducible cc.2) := ⟨hIrr cc hcc⟩
      letI : Fact (0 < cc.2.natDegree) := ⟨hPos cc hcc⟩
      ∀ t < n cc,
        αGenuine cc.2 0 (rep cc.1) (hHyp cc hcc) t =
          liftToFunctionField (H := cc.2) (c cc t))
    (hvanish : ∀ cc (hcc : cc ∈ Index),
      letI : Fact (Irreducible cc.2) := ⟨hIrr cc hcc⟩
      letI : Fact (0 < cc.2.natDegree) := ⟨hPos cc hcc⟩
      ∀ t, n cc ≤ t → αGenuine cc.2 0 (rep cc.1) (hHyp cc hcc) t = 0) :
    ∃ S' : Finset F,
      T < S'.card ∧
        (∀ z ∈ S', z ∈ good) ∧
          Nonempty (LocalSeriesDatumOnSub k S' P) := by
  obtain ⟨cc, hcc, hcard⟩ := hlarge
  letI : Fact (Irreducible cc.2) := ⟨hIrr cc hcc⟩
  letI : Fact (0 < cc.2.natDegree) := ⟨hPos cc hcc⟩
  refine ⟨GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc, hcard,
    hsub cc hcc, ⟨?_⟩⟩
  exact localSeriesDatumOnSub_of_cell_baseRational
    (S := GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc)
    (P := P) (rep := rep) (S₀ := S₀) (cc := cc)
    (fun z hz => hz) (hHyp cc hcc) (hlc cc hcc) (hR cc hcc)
    (hN cc hcc) (hnN cc hcc) (c cc) (hdeg cc hcc)
    (havoid cc hcc) (hbase cc hcc) (hvanish cc hcc)

end RawGSSub

/-! ## Part 4 — sub-finset consumers: Hensel pinning and coefficient witnesses -/

section SubConsumers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **The per-`z` Hensel pin on an arbitrary carrier.**
A `LocalSeriesDatumOnSub` datum pins the decoded polynomial to the curve-family specialization
on every selected point `z ∈ S`. This is the pointwise Hensel uniqueness argument used by the
pinned good-set lane, but with the carrier kept arbitrary for the most-common-cell step. -/
theorem hPz_of_localSeriesDatumOnSub {k : ℕ} {S : Finset F} {P : F → Polynomial F}
    (d : LocalSeriesDatumOnSub k S P) :
    ∀ z ∈ S, P z = ∑ t ∈ Finset.range d.n, (z - d.x₀) ^ t • d.c t := by
  haveI := d.hIrr
  haveI := d.hPos
  intro z hz
  let f : Polynomial (PowerSeries F) :=
    (d.R.map (coeffHom_loc d.x₀ d.hHyp)).map
      (PowerSeries.map (π_hat_z d.hHyp z (d.rootOn z hz) (d.hx z hz)))
  let a₀ : PowerSeries F :=
    PowerSeries.C ((π_z z (d.rootOn z hz))
      (BCIKS20.HenselNumerator.βHensel d.H d.x₀ d.R d.hHyp 0))
  have hvanishAlpha : ∀ t, d.n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta d.x₀ d.R d.H d.hHyp
        (BetaRecGenuineBridge.BcoeffSigned d.H d.x₀ d.R) t = 0 := by
    intro t ht
    rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic
      d.x₀ d.R d.hHyp d.hlc t]
    exact d.hvanish t ht
  have hProot : f.IsRoot ((P z : F[X]) : PowerSeries F) :=
    Polynomial.dvd_iff_isRoot.mp (d.hdvd z hz)
  refine FaithfulCurveExtraction.eval_identity_of_curveHensel
    (P := P) (x₀ := d.x₀) (n := d.n) (c := d.c) (z := z) (f := f) (a₀ := a₀)
    hProot ?_ (d.hcong z hz) ?_ ?_
  · rw [← d.htrunc z hz]
    exact trunc_localSeries_isRoot_of_alphaFromBeta_vanishing d.hHyp d.hξ d.hlc z
      (d.rootOn z hz) (d.hx z hz) hvanishAlpha
  · rw [← d.htrunc z hz,
      ← powerSeries_eq_coe_trunc_of_tail_zero (fun t ht =>
        coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero d.hHyp d.hξ z (d.rootOn z hz)
          (d.hx z hz) t (hvanishAlpha t ht)),
      Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
      constantCoeff_localSeries d.hHyp z (d.rootOn z hz) (d.hx z hz),
      PowerSeries.constantCoeff_C, sub_self]
  · exact HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr f
      (specialized_separable_of_R_separable d.hHyp z (d.rootOn z hz) (d.hx z hz) d.hR)
      hProot (d.hcong z hz)

omit [Fintype F] in
/-- The sub-finset datum yields coefficient polynomials on its selected carrier. -/
theorem curveCoeffPolys_of_localSeriesDatumOnSub {k deg : ℕ} {S : Finset F}
    {P : F → Polynomial F} (d : LocalSeriesDatumOnSub k S P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg S P :=
  FaithfulCurveExtraction.curveCoeffPolys_of_curveFamily d.x₀ d.n d.c d.hn
    (hPz_of_localSeriesDatumOnSub d)

omit [Fintype F] in
/-- Bundled coefficient-polynomial witness on an arbitrary selected carrier. -/
theorem coeffPolyWitness_of_localSeriesDatumOnSub {k deg : ℕ} {S : Finset F}
    {P : F → Polynomial F} (d : LocalSeriesDatumOnSub k S P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  have hCurve := curveCoeffPolys_of_localSeriesDatumOnSub (deg := deg) d
  refine ⟨fun j => if h : j < deg then (hCurve j h).choose else 0, ?_, ?_⟩
  · intro j hj
    simp only [hj, dif_pos]
    exact (hCurve j hj).choose_spec.1
  · intro z hz j hj
    simp only [hj, dif_pos]
    exact (hCurve j hj).choose_spec.2 z hz

end SubConsumers

/-! ## Part 5 — a `P`-dependent selected carrier reaches joint agreement -/

section JointAgreement

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **Joint agreement from a `P`-dependent large selected carrier.**
The existing curve-counting bridge fixes a carrier before it chooses a decoded family. The
BCIKS20 most-common-cell step naturally goes the other way: choose a decoded family `P` on the
whole good set, then pass to a large cell depending on `P`. This front door internalizes that
order. For each full-good decoded family, it accepts a large subcarrier inside the good set and
a coefficient-polynomial witness on that subcarrier, then runs the same assembly and counting
proof to produce `jointAgreement`. -/
theorem jointAgreement_of_exists_sub_coeffPolyWitness {l deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (l + 2)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ S' : Finset F,
        S'.card > l + 1 ∧
          S'.card ≥ (Fintype.card ι + 1) * (l + 1) ∧
          (∀ z ∈ S',
            z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ) ∧
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < l + 2) ∧
              ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  obtain ⟨P, hdecodedGood⟩ :=
    exists_decoded_polynomial_family_of_subset_goodCoeffsCurve
      (k := l + 1) (deg := deg) (domain := domain) (δ := δ) u (fun z hz => hz)
  obtain ⟨S', hcard, hcard₁, hS', B, hBdeg, hcoeff⟩ := hInput P hdecodedGood
  obtain ⟨A, hAdeg, hPcoeff⟩ :=
    decoded_family_coefficients_of_coeff_polys_core
      (l := l) (deg := deg) (S' := S') (P := P) B
      hBdeg (fun z hz => (hdecodedGood z (hS' z hz)).1) hcoeff
  obtain ⟨v, hv, hPcurve⟩ :=
    decoded_family_coefficients_assemble_codeword_curve
      (deg := deg) (domain := domain) P A hAdeg hPcoeff
  exact decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hcard hcard₁ P (fun z hz => hdecodedGood z (hS' z hz)) hPcurve

omit [DecidableEq ι] in
/-- **Joint agreement from a `P`-dependent sub-finset local-series producer.**
For every decoded family on the whole good set, it is enough to produce a large selected carrier
inside the good set together with a `LocalSeriesDatumOnSub` on that carrier. The coefficient
witness is extracted by `coeffPolyWitness_of_localSeriesDatumOnSub`, and the preceding front door
does the counting. -/
theorem jointAgreement_of_exists_localSeriesDatumOnSub {l deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (l + 2)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ S' : Finset F,
        S'.card > l + 1 ∧
          S'.card ≥ (Fintype.card ι + 1) * (l + 1) ∧
          (∀ z ∈ S',
            z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ) ∧
          Nonempty (LocalSeriesDatumOnSub (l + 1) S' P)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  jointAgreement_of_exists_sub_coeffPolyWitness (domain := domain) (δ := δ) (u := u)
    (fun P hdecoded => by
      obtain ⟨S', hcard, hcard₁, hS', hd⟩ := hInput P hdecoded
      obtain ⟨d⟩ := hd
      obtain ⟨B, hBdeg, hcoeff⟩ :=
        coeffPolyWitness_of_localSeriesDatumOnSub (deg := deg) d
      exact ⟨S', hcard, hcard₁, hS', B, hBdeg, hcoeff⟩)

omit [DecidableEq ι] in
/-- **Joint agreement from a large Claim-5.7 cell with analytic cargo.**
This is the composed most-common-cell front door: for every decoded family on the full good set,
it is enough to select one large incidence cell inside that good set and provide the bundled
`Claim57CellDatum` on that cell.  The datum is converted to `LocalSeriesDatumOnSub`; coefficient
witnesses and the final counting step are then derived internally. -/
theorem jointAgreement_of_exists_claim57CellDatum {l deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (l + 2)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ d : Claim57CellDatum (l + 1) P,
        d.carrier.card > l + 1 ∧
          d.carrier.card ≥ (Fintype.card ι + 1) * (l + 1) ∧
          ∀ z ∈ d.carrier,
            z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  jointAgreement_of_exists_localSeriesDatumOnSub (domain := domain) (δ := δ) (u := u)
    (fun P hdecoded => by
      obtain ⟨d, hcard, hcard₁, hS⟩ := hInput P hdecoded
      exact ⟨d.carrier, hcard, hcard₁, hS, ⟨d.localSeriesDatumOnSub⟩⟩)

omit [DecidableEq ι] in
/-- Positive-`k` version of
`jointAgreement_of_exists_sub_coeffPolyWitness`, in the native residual shape
`u : Fin (k + 1) → ι → F`. -/
theorem jointAgreement_of_exists_sub_coeffPolyWitness_of_pos {k deg : ℕ} [NeZero deg]
    (hk : 0 < k)
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ S' : Finset F,
        S'.card > k ∧
          S'.card ≥ (Fintype.card ι + 1) * k ∧
          (∀ z ∈ S',
            z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  let l : ℕ := k - 1
  have hlk : l + 1 = k := by omega
  have hlen : l + 2 = k + 1 := by omega
  let u' : Fin (l + 2) → ι → F := fun i => u (finCongr hlen i)
  have hgood_eq :
      RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u' δ =
        RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ := by
    simpa [u', hlk] using
      (RS_goodCoeffsCurve_finCongr_core (F := F) (ι := ι)
        (k := l + 1) (k' := k) (deg := deg) (domain := domain) (δ := δ)
        (by omega : (l + 1) + 1 = k + 1) u)
  have hja' :
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u') := by
    refine jointAgreement_of_exists_sub_coeffPolyWitness
      (domain := domain) (δ := δ) (u := u') ?_
    intro P hdecoded
    have hdecoded_orig :
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ := by
      intro z hz
      have hz' :
          z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u' δ := by
        simpa [hgood_eq] using hz
      have hsum :
          (∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u' t) =
            ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t := by
        simpa [u'] using
          (curve_sum_reindex_equiv_core (F := F) (ι := ι) (e := finCongr hlen) z u
            (fun t : Fin (k + 1) => (t : ℕ)))
      exact ⟨(hdecoded z hz').1, by simpa [hsum] using (hdecoded z hz').2⟩
    obtain ⟨S', hcard, hcard₁, hS', B, hBdeg, hcoeff⟩ := hInput P hdecoded_orig
    refine ⟨S', ?_, ?_, ?_, B, ?_, hcoeff⟩
    · simpa [hlk] using hcard
    · simpa [hlk] using hcard₁
    · intro z hz
      simpa [hgood_eq] using hS' z hz
    · intro j hj
      simpa [hlen] using hBdeg j hj
  exact jointAgreement_reindex_equiv_core
    (F := F) (ι := ι) (C := ReedSolomon.code domain deg) (δ := δ)
    (W := u) (W' := u') (e := (finCongr hlen).symm)
    (by intro i x; simp [u'])
    hja'

omit [DecidableEq ι] in
/-- Positive-`k` native residual-shape front door from selected-carrier local-series data. -/
theorem jointAgreement_of_exists_localSeriesDatumOnSub_of_pos {k deg : ℕ} [NeZero deg]
    (hk : 0 < k)
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ S' : Finset F,
        S'.card > k ∧
          S'.card ≥ (Fintype.card ι + 1) * k ∧
          (∀ z ∈ S',
            z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
          Nonempty (LocalSeriesDatumOnSub k S' P)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  jointAgreement_of_exists_sub_coeffPolyWitness_of_pos (domain := domain) (δ := δ) (u := u)
    hk (fun P hdecoded => by
      obtain ⟨S', hcard, hcard₁, hS', hd⟩ := hInput P hdecoded
      obtain ⟨d⟩ := hd
      obtain ⟨B, hBdeg, hcoeff⟩ :=
        coeffPolyWitness_of_localSeriesDatumOnSub (deg := deg) d
      exact ⟨S', hcard, hcard₁, hS', B, hBdeg, hcoeff⟩)

omit [DecidableEq ι] in
/-- Positive-`k` native residual-shape front door from a large Claim-5.7 cell with analytic
cargo. -/
theorem jointAgreement_of_exists_claim57CellDatum_of_pos {k deg : ℕ} [NeZero deg]
    (hk : 0 < k)
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ d : Claim57CellDatum k P,
        d.carrier.card > k ∧
          d.carrier.card ≥ (Fintype.card ι + 1) * k ∧
          ∀ z ∈ d.carrier,
            z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  jointAgreement_of_exists_localSeriesDatumOnSub_of_pos (domain := domain) (δ := δ) (u := u)
    hk (fun P hdecoded => by
      obtain ⟨d, hcard, hcard₁, hS⟩ := hInput P hdecoded
      exact ⟨d.carrier, hcard, hcard₁, hS, ⟨d.localSeriesDatumOnSub⟩⟩)

omit [DecidableEq ι] in
/-- **Joint agreement directly from Claim-5.7 pigeonhole output.**
For every decoded family `P`, it is enough to provide the actual finite cell index output of
`claim57_pigeonhole`: a cell of size greater than `(card ι + 1) * k`, every indexed cell lying
inside the good set, and analytic cargo on each indexed cell.  The proof selects the large cell
and runs the sub-finset counting consumer. -/
theorem jointAgreement_of_pigeonhole_output_of_pos {k deg : ℕ} [NeZero deg]
    (hk : 0 < k)
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι}
    (hInput : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ (ι' : Type) (rep : ι' → (F[X])[X][Y]) (S₀ : Finset F)
        (Index : Finset (ι' × F[X][Y])),
        (∃ cc ∈ Index,
          (Fintype.card ι + 1) * k <
            (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc).card) ∧
          (∀ cc ∈ Index,
            ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
              z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
            (∀ cc ∈ Index,
              Nonempty (LocalSeriesDatumOnSub k
                (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc) P))) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  jointAgreement_of_exists_localSeriesDatumOnSub_of_pos (domain := domain) (δ := δ) (u := u)
    hk (fun P hdecoded => by
      obtain ⟨ι', rep, S₀, Index, hlarge, hsub, hdatum⟩ := hInput P hdecoded
      obtain ⟨S', hcard, hS, hd⟩ :=
        exists_localSeriesDatumOnSub_of_pigeonhole_output
          (k := k) (T := (Fintype.card ι + 1) * k) (P := P) (rep := rep)
          (S₀ := S₀)
          (good := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
          (Index := Index) hlarge hsub hdatum
      refine ⟨S', ?_, Nat.le_of_lt hcard, hS, hd⟩
      have hk_le : k ≤ (Fintype.card ι + 1) * k := by
        simpa [one_mul] using
          Nat.mul_le_mul_right k (Nat.succ_le_succ (Nat.zero_le (Fintype.card ι)))
      exact lt_of_le_of_lt hk_le hcard)

omit [DecidableEq ι] in
/-- **Correlated agreement from actual Claim-5.7 pigeonhole output plus an explicit boundary
branch.**  This is the same strict-branch route as
`correlatedAgreement_affine_curves_of_claim57CellDatum_and_boundary`, but phrased one layer
closer to `claim57_pigeonhole`: the strict input is an indexed cell family with a large selected
cell and cellwise `LocalSeriesDatumOnSub` cargo. -/
theorem correlatedAgreement_affine_curves_of_pigeonhole_output_and_boundary {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictPigeonhole : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ (ι' : Type) (rep : ι' → (F[X])[X][Y]) (S₀ : Finset F)
            (Index : Finset (ι' × F[X][Y])),
            (∃ cc ∈ Index,
              (Fintype.card ι + 1) * k <
                (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc).card) ∧
              (∀ cc ∈ Index,
                ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
                  z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
                (∀ cc ∈ Index,
                  Nonempty (LocalSeriesDatumOnSub k
                    (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc) P)))
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_list_decoding_obligations
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt
  exact jointAgreement_of_pigeonhole_output_of_pos
    (domain := domain) (δ := δ) (u := u) hk
    (fun P hP => hStrictPigeonhole hk u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- Strict-interior correlated agreement from actual Claim-5.7 pigeonhole output.  In the
strict range the boundary branch is unreachable. -/
theorem correlatedAgreement_affine_curves_of_strict_pigeonhole_output {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictPigeonhole : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ (ι' : Type) (rep : ι' → (F[X])[X][Y]) (S₀ : Finset F)
            (Index : Finset (ι' × F[X][Y])),
            (∃ cc ∈ Index,
              (Fintype.card ι + 1) * k <
                (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc).card) ∧
              (∀ cc ∈ Index,
                ∀ z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc,
                  z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
                (∀ cc ∈ Index,
                  Nonempty (LocalSeriesDatumOnSub k
                    (GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S₀ cc) P))) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_pigeonhole_output_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ.le
    (fun hk u hprob hJ _hsqrt => hStrictPigeonhole hk u hprob hJ)
    (fun _hk _u _hprob _hJ hnot => False.elim (hnot hδ))

omit [DecidableEq ι] in
/-- **Correlated agreement from Claim57-cell strict-branch cargo plus an explicit boundary
branch.**  This lifts the corrected most-common-cell interface directly to the BCIKS20 curve
keystone's `jointAgreement`-obligation entry point.  It does not assert whole-good-set
coefficient witnesses; it uses a large selected Claim57 cell for each decoded family. -/
theorem correlatedAgreement_affine_curves_of_claim57CellDatum_and_boundary {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCell : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ d : Claim57CellDatum k P,
            d.carrier.card > k ∧
              d.carrier.card ≥ (Fintype.card ι + 1) * k ∧
              ∀ z ∈ d.carrier,
                z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_list_decoding_obligations
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt
  exact jointAgreement_of_exists_claim57CellDatum_of_pos
    (domain := domain) (δ := δ) (u := u) hk
    (fun P hP => hStrictCell hk u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- Strict-interior correlated agreement from Claim57-cell analytic cargo alone.  In the
strict range the closed-boundary branch is unreachable. -/
theorem correlatedAgreement_affine_curves_of_strict_claim57CellDatum {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCell : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ d : Claim57CellDatum k P,
            d.carrier.card > k ∧
              d.carrier.card ≥ (Fintype.card ι + 1) * k ∧
              ∀ z ∈ d.carrier,
                z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_claim57CellDatum_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ.le
    (fun hk u hprob hJ _hsqrt => hStrictCell hk u hprob hJ)
    (fun _hk _u _hprob _hJ hnot => False.elim (hnot hδ))

/-- **SK1-to-threshold weld (#304).** If every decoded family admits a large selected
section-linked cell carrying the elementary strict-coefficient data, then
`jointAgreement_of_exists_sub_coeffPolyWitness_of_pos` already yields joint agreement.

This theorem deliberately does not select the cell: it only turns supplied cell data into the
sub-finset coefficient-polynomial witness expected by the downstream threshold theorem. -/
theorem jointAgreement_of_exists_cell_strictCoeffPolys_of_pos {n k deg : ℕ}
    [NeZero n] [NeZero deg] (hk : 0 < k)
    {domain : Fin n ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) (Fin n)}
    (hInput : ∀ P : F → F[X],
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ (E : Finset F) (R : (F[X])[X][Y]) (w : F[X][Y]) (Bw : ℕ)
        (T : Finset (Fin n)) (S : Fin n → Finset F),
        E.card > k ∧
          E.card ≥ (Fintype.card (Fin n) + 1) * k ∧
          (∀ z ∈ E,
            z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
          Irreducible R ∧
          (Polynomial.X - Polynomial.C w) ∣ R ∧
          (∀ i, (w.coeff i).natDegree ≤ Bw) ∧
          (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) ∧
          w.natDegree < T.card ∧
          (∀ t ∈ T, S t ⊆ E) ∧
          (∀ t ∈ T, max Bw k < (S t).card) ∧
          ∀ t ∈ T, ∀ z ∈ S t,
            (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  refine jointAgreement_of_exists_sub_coeffPolyWitness_of_pos
    (domain := domain) (δ := δ) (u := u) hk ?_
  intro P hdecoded
  obtain ⟨E, R, w, Bw, T, S, hEcard, hEthresh, hEgood, hRirr, hwdvd, hB, hdvdP,
    hT, hSE, hcard, hagree⟩ := hInput P hdecoded
  obtain ⟨B, hBdeg, hcoeff⟩ :=
    BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell
      (domain := domain) (u := u) (k := k)
      hRirr hwdvd (by omega : k + 1 - 1 ≤ k) hB E P hdvdP T hT S hSE hcard hagree
  exact ⟨E, hEcard, hEthresh, hEgood, B, (fun j _ => hBdeg j),
    fun z hz j _ => hcoeff z hz j⟩

end JointAgreement

end Threshold304

end ArkLib

/-! ## Axiom audit (Parts 1–2) -/
#print axioms ArkLib.Threshold304.LocalSeriesDatumOnSub
#print axioms ArkLib.Threshold304.LocalSeriesDatumOnSub.mono
#print axioms ArkLib.Threshold304.localSeriesDatumOnSub_of_localSeriesDatumOn
#print axioms ArkLib.Threshold304.localSeriesDatumOn_of_localSeriesDatumOnSub_good
#print axioms ArkLib.Threshold304.TruncReadingOnSub
#print axioms ArkLib.Threshold304.truncReadingOnSub_of_baseRational
#print axioms ArkLib.Threshold304.localSeriesDatumOnSub_of_rawGS
#print axioms ArkLib.Threshold304.localSeriesDatumOnSub_of_rawGS_baseRational
#print axioms ArkLib.Threshold304.localSeriesDatumOnSub_of_cell
#print axioms ArkLib.Threshold304.localSeriesDatumOnSub_of_cell_baseRational
#print axioms ArkLib.Threshold304.Claim57CellDatum
#print axioms ArkLib.Threshold304.Claim57CellDatum.carrier
#print axioms ArkLib.Threshold304.Claim57CellDatum.localSeriesDatumOnSub
#print axioms ArkLib.Threshold304.Claim57CellDatum.of_baseRational
#print axioms ArkLib.Threshold304.exists_localSeriesDatumOnSub_of_pigeonhole_output
#print axioms ArkLib.Threshold304.exists_localSeriesDatumOnSub_of_pigeonhole_baseRational_output
#print axioms ArkLib.Threshold304.hPz_of_localSeriesDatumOnSub
#print axioms ArkLib.Threshold304.curveCoeffPolys_of_localSeriesDatumOnSub
#print axioms ArkLib.Threshold304.coeffPolyWitness_of_localSeriesDatumOnSub
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_sub_coeffPolyWitness
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_localSeriesDatumOnSub
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_claim57CellDatum
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_sub_coeffPolyWitness_of_pos
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_localSeriesDatumOnSub_of_pos
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_claim57CellDatum_of_pos
#print axioms ArkLib.Threshold304.jointAgreement_of_pigeonhole_output_of_pos
#print axioms ArkLib.Threshold304.correlatedAgreement_affine_curves_of_pigeonhole_output_and_boundary
#print axioms ArkLib.Threshold304.correlatedAgreement_affine_curves_of_strict_pigeonhole_output
#print axioms ArkLib.Threshold304.correlatedAgreement_affine_curves_of_claim57CellDatum_and_boundary
#print axioms ArkLib.Threshold304.correlatedAgreement_affine_curves_of_strict_claim57CellDatum
#print axioms ArkLib.Threshold304.jointAgreement_of_exists_cell_strictCoeffPolys_of_pos
