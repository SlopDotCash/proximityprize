/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSGradedBundle
import ArkLib.ToMathlib.ConditionDiscProduct
import ArkLib.ToMathlib.CurveHenselDatumProducers
import ArkLib.ToMathlib.CurveFamilyZLinear
import ArkLib.ToMathlib.BetaTailDegreeVanishing

/-!
# Issue #304 — the end-to-end faithful frontier composition

**The single theorem** (`correlatedAgreement_affine_curves_of_faithful_frontier`): the §5
keystone goal `δ_ε_correlatedAgreementCurves` in the strict Johnson regime, from a per-`(u, P)`
producer of `FaithfulFrontierData` — one bundle whose fields are **only the named honest
residuals** of the round-1 harvest.  Every proven lane in between is composed here, so that
nothing provable remains in the hypothesis list.

## The composition chain (all PROVEN, in-tree)

| input (field)            | paper ingredient ([BCIKS20])           | supplying lane                                  | status |
|--------------------------|----------------------------------------|--------------------------------------------------|--------|
| `gb : GradedBundle`      | GS factor pair `(R, H)`, grading (iii)–(v) | `GSGradedBundle.GradedBundle.of_section5Inputs` | residual data (graph extraction proven; grading PROVEN) |
| `hres : MonicHighYResidual` | (i) monic `H`, (ii) `2 ≤ deg_Y R`    | `GSGradedBundle` (the A.4 monicization wall)     | named residual |
| `hRsep : R.Separable`    | §6.2 separable interpolant             | `CurveHenselDatumProducers` (unit derivative)    | named residual |
| `fB`,`hfBdeg`,`hfBdiscr`,`hfBne` | §6 separability discriminant source | `ConditionDiscProduct.conditionDiscs` slot 0 | named residual (genuine `fB` inputs) |
| `hbig`                   | the §6 field-size inequality           | `ConditionDiscProduct.matchingSet304_geometry_and_card` | named residual (ONE inequality) |
| `root`                   | per-place rational root supply         | `ConditionDiscProduct.RootSupplyOn` (not a disc condition) | named residual |
| `mpFin`                  | ingredient C per-point matching data on `[n, T]` | `BetaMatchingVanishes.MatchingPoint`     | named residual |
| `htailBeyond`            | Claim 5.8′ tail beyond the counting window | `BetaTailDegreeVanishing` (see `htailBeyond_of_lift_window`) | named residual / conditionally PROVEN |
| `hgoodDisc`              | good places avoid the discriminant bad locus | `ConditionDiscProduct.discMatchingSet`     | named residual |
| `htrunc`                 | §5 base-rationality reading of the local series | `TruncatedLocalRoot` / `LocalHenselSeries` | named residual |
| `hdvd`                   | GS matching-factor divisibility at `P z` | `MatchingFactorLift` cargo                      | named residual |
| `hcong`                  | order-0 congruence `P z ≡ π_z(β₀)` mod `X` | §6.2 approximation                           | named residual |

Composed PROVEN middleware (none of it appears in the hypothesis list):

* the §6 counting: `Match304.matchingSet304_geometry_and_card` (the product-discriminant
  matching set, its cardinality family in the exact `gradedCardBudget` shape) — from `hbig`;
* the graded weight collapse at the signed family:
  `GenuineMonicCapstone.hcardFin_of_graded_signed` — from the graded bundle + (i)–(ii);
* the genuine-coefficient window vanishing:
  `FaithfulCurveExtraction.αGenuine_eq_zero_on_range_of_matching_monic` (`αGenuine = 0` on
  `[n, T]`) — from `mpFin` + the counting;
* the per-place `ξ`-reading nonvanishing on the good set:
  `xiReading_ne_zero_of_mem_discMatchingSet` (NEW here) — from `hgoodDisc` + the `elimPoly ξ`
  condition disc (`Match304.π_z_ne_zero_of_elimPoly_eval_ne_zero`), with the global `ξ ≠ 0`
  from `Match304.ξ_ne_zero`;
* the per-`z` Hensel assembly at the constructed local series:
  `FaithfulCurveExtraction.curveHenselDatum_of_truncatedLocalRoot_genuine` →
  `curveFamilyData_of_curveHenselDatum` → the faithful `CurveFamilyData`;
* the keystone front door:
  `FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict`.

## The window parameterization (the degenerate-window caveat, handled honestly)

The matching machinery vanishes `αGenuine` on a **window** `[n, T]` (`n` = the curve length,
`T` = the counting top); the producer owes the tail only **beyond `T`** (`htailBeyond`).  The
recursion-route discharge `BetaTail.htail_of_window_of_lift` needs the **full initial segment**
`[1, T₀]` (the `[k, T]`-window propagation is FALSE — see `BetaTailDegreeVanishing`), and then
yields vanishing at *every* `t ≥ 1`, collapsing the curve to its constant term.  We therefore
do NOT force that route: the window is parameterized (`n`, `T` free), `htailBeyond` is the
named residual, and `htailBeyond_of_lift_window` is the PROVEN conditional discharge for
producers that do supply the full window `[1, T]` plus the lift identities and the lift-`X`
degree bound — with the degeneration documented, not hidden.

## The `Z`-linear lane front door (the `n + m < k + 2` budget split)

`correlatedAgreement_affine_curves_of_placeReading_frontier` is the keystone front door for the
Claim-5.9 two-series lane (`CurveFamilyZLinear`): a per-`(u, P)` producer of the place-reading
datum `CurvePlaceReading` plus branch rationality (`m` branch coefficients) under the split
budget `n + m < k + 2` reaches the same keystone through the proven reading convolution.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5, Claims 5.8/5.8′/5.9), §6.2, Appendix A.2/A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulFrontier

/-! ## Part 1 — the per-place `ξ`-reading from the condition-disc matching set -/

section Readings

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The `ξ`-reading nonvanishing at a place of the canonical matching set.**  Membership in
`discMatchingSet` makes the `elimPoly ξ` condition disc (slot 1 of `conditionDiscs`) nonzero at
`z`, hence (`π_z_ne_zero_of_elimPoly_eval_ne_zero`) the per-place reading of `ξ` is nonzero at
**every** rational root over `z` — exactly the `hx` input of the analytic curve-Hensel
producer. -/
theorem xiReading_ne_zero_of_mem_discMatchingSet
    {fB : F[X][Y]} {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hH : 0 < H.natDegree} {hHyp : Hypotheses x₀ R H} {z : F}
    (hz : z ∈ Match304.discMatchingSet Finset.univ
      (Match304.conditionDiscs fB x₀ R H hH hHyp))
    (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) (ξ x₀ R H hHyp) ≠ 0 :=
  Match304.π_z_ne_zero_of_elimPoly_eval_ne_zero hH _
    (by simpa using Match304.mem_discMatchingSet.mp hz 1 (Finset.mem_univ _)) root

end Readings

/-! ## Part 2 — the conditional tail discharge (the lift-window route, parameterized) -/

section TailWindow

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The PROVEN conditional discharge of the `htailBeyond` residual** — the
`BetaTailDegreeVanishing` recursion route.  If the producer supplies the per-point matching
data on the **full initial window** `[1, T]`, the lift-`X` degree bound `deg_X R ≤ T`, and the
per-`t` lift identities, then `αGenuine t = 0` for every `t > T` (indeed for every `t ≥ 1`):
the matching window `[1, T]` is closed by the counting chain
(`matchingSet304_geometry_and_card` → `hcardFin_of_graded_signed` →
`αGenuine_eq_zero_on_range_of_matching_monic`), and `BetaTail.αGenuine_tail_eq_zero_of_window_of_lift`
propagates it past `T` by the algebraic-degree argument.

**The honest caveat** (why this is a *conditional* discharge and not folded into the frontier
bundle): the full-window hypothesis kills every positive-order coefficient, degenerating the
curve `γ` to its constant term — it matches the *recentered* root (curve part subtracted) or
the degenerate `n = 1` window, per the analysis in `BetaTailDegreeVanishing`.  The frontier
bundle keeps the window `[n, T]` parameterized and the tail beyond `T` residual instead. -/
theorem htailBeyond_of_lift_window
    {x₀ : F} (gb : GSFactorData.GradedBundle (F := F) x₀)
    [Fact (Irreducible gb.H)] [Fact (0 < gb.H.natDegree)]
    (hres : GSFactorData.MonicHighYResidual gb.toBundle)
    {T : ℕ} (fB : F[X][Y])
    (hfBdeg : 0 < fB.natDegree) (hfBdiscr : fB.discr ≠ 0) (hfBne : fB ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY gb.R) gb.D gb.H.natDegree T
        + ∑ i, (Match304.conditionDiscs fB x₀ gb.R gb.H gb.hH gb.hHyp i).natDegree
        < Fintype.card F)
    {root : (z : F) → rationalRoot (H_tilde' gb.H) z}
    (mpFin1 : ∀ t, 1 ≤ t → t ≤ T →
      ∀ z ∈ Match304.discMatchingSet Finset.univ
          (Match304.conditionDiscs fB x₀ gb.R gb.H gb.hH gb.hHyp),
        BetaMatchingVanishes.MatchingPoint x₀ gb.R gb.H gb.hHyp
          (BetaRecGenuineBridge.BcoeffSigned gb.H x₀ gb.R) t z (root z))
    (hdX : ∀ j, (gb.R.coeff j).natDegree ≤ T)
    (hlift : ∀ t, S5Genuine.LiftIdentityAt gb.H x₀ gb.R gb.hHyp t) :
    ∀ t, T < t → αGenuine gb.H x₀ gb.R gb.hHyp t = 0 := by
  have hconcreteFin := (Match304.matchingSet304_geometry_and_card fB x₀ gb.R gb.H gb.hH
      gb.hHyp hfBdeg hfBdiscr hfBne (k := 1) hbig).2
  have hcardFin := GenuineMonicCapstone.hcardFin_of_graded_signed x₀ gb.R gb.H gb.hHyp
      gb.hD gb.hH hres.hmonic hres.hd2 gb.hdHD gb.hD_Rx0 gb.hR hconcreteFin
  have hwin := FaithfulCurveExtraction.αGenuine_eq_zero_on_range_of_matching_monic x₀ gb.R
      gb.hHyp hres.hmonic.leadingCoeff gb.hH gb.D gb.hD 1 T mpFin1 hcardFin
  intro t hTt
  exact BetaTail.αGenuine_tail_eq_zero_of_window_of_lift gb.H x₀ gb.R gb.hHyp hdX hlift
    hwin t (by omega)

end TailWindow

/-! ## Part 3 — the faithful frontier bundle -/

section Frontier

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The faithful frontier bundle for issue #304** — the per-`(u, P)` data whose fields are
exactly the named honest residuals of the round-1 harvest (see the file docstring table).
Everything provable between these fields and the §5 keystone is composed by
`curveFamilyData_of_faithfulFrontier`; nothing in this structure is the keystone goal in
disguise (each field is a recognized BCIKS20 §5/§6 ingredient with its own production lane,
and the per-`z` fields quantify only over the good set / the matching set). -/
structure FaithfulFrontierData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the expansion centre. -/
  x₀ : F
  /-- the graded GS-factor bundle (side conditions (iii)–(v) PROVEN by re-grading). -/
  gb : GSFactorData.GradedBundle (F := F) x₀
  /-- irreducibility instance (supplied by `gb.hIrr`). -/
  iIrr : Fact (Irreducible gb.H) := gb.hIrr
  /-- positivity instance (supplied by `gb.hPos`). -/
  iPos : Fact (0 < gb.H.natDegree) := gb.hPos
  /-- the GS-factor residual: (i) `H` monic, (ii) `2 ≤ deg_Y R` (the A.4 wall). -/
  hres : GSFactorData.MonicHighYResidual gb.toBundle
  /-- §6.2 separability of the GS factor (the unit-derivative source). -/
  hRsep : gb.R.Separable
  /-- the number of curve coefficients (at most `k + 1`: the GS degree budget). -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- the counting-window top. -/
  T : ℕ
  /-- the §6 separability-discriminant source (slot 0 of the condition discs;
  take `fB := H_tilde' gb.H` for the matching polynomial itself). -/
  fB : F[X][Y]
  hfBdeg : 0 < fB.natDegree
  hfBdiscr : fB.discr ≠ 0
  hfBne : fB ≠ 0
  /-- **the single §6 field-size inequality** (the whole counting side). -/
  hbig : gradedCardBudget (Bivariate.natDegreeY gb.R) gb.D gb.H.natDegree T
      + ∑ i, (Match304.conditionDiscs fB x₀ gb.R gb.H gb.hH gb.hHyp i).natDegree
      < Fintype.card F
  /-- the per-place rational-root supply (cf. `Match304.RootSupplyOn`: provably NOT a
  discriminant condition; supplied by the §5 decoded geometry). -/
  root : (z : F) → rationalRoot (H_tilde' gb.H) z
  /-- ingredient C: the per-point matching data on the counting window `[n, T]`, on the
  canonical condition-disc matching set, at the signed canonical family. -/
  mpFin : ∀ t, n ≤ t → t ≤ T →
    ∀ z ∈ Match304.discMatchingSet Finset.univ
        (Match304.conditionDiscs fB x₀ gb.R gb.H gb.hH gb.hHyp),
      BetaMatchingVanishes.MatchingPoint x₀ gb.R gb.H gb.hHyp
        (BetaRecGenuineBridge.BcoeffSigned gb.H x₀ gb.R) t z (root z)
  /-- the genuine-coefficient tail beyond the counting window (Claim 5.8′ content;
  conditionally PROVEN by `htailBeyond_of_lift_window` on the full-window/lift route). -/
  htailBeyond : ∀ t, T < t → αGenuine gb.H x₀ gb.R gb.hHyp t = 0
  /-- the good places avoid the discriminant bad locus (the §6 genericity input). -/
  hgoodDisc : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    z ∈ Match304.discMatchingSet Finset.univ
      (Match304.conditionDiscs fB x₀ gb.R gb.H gb.hH gb.hHyp)
  /-- the §5 base-rationality reading: the truncated local series IS the curve
  specialization at every good place. -/
  htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    (PowerSeries.trunc n (localSeries gb.hHyp z (root z)
        (xiReading_ne_zero_of_mem_discMatchingSet (hgoodDisc z hz) (root z))) : Polynomial F)
      = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t
  /-- the decoded-side GS cargo: the matching-factor divisibility at `↑(P z)`. -/
  hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
      ((gb.R.map (coeffHom_loc x₀ gb.hHyp)).map
        (PowerSeries.map (π_hat_z gb.hHyp z (root z)
          (xiReading_ne_zero_of_mem_discMatchingSet (hgoodDisc z hz) (root z)))))
  /-- the decoded-side order-0 congruence `P z ≡ π_z(βHensel 0)` mod `X`. -/
  hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
        (BCIKS20.HenselNumerator.βHensel gb.H x₀ gb.R gb.hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}

/-! ## Part 4 — the proven composition into the faithful curve-family datum -/

/-- **The frontier composition (everything provable, composed).**  From the frontier bundle:

1. the §6 counting (`matchingSet304_geometry_and_card` from `hbig`) feeds
2. the signed graded weight collapse (`hcardFin_of_graded_signed`, using the graded bundle's
   (iii)–(v) and the residual's (i)–(ii)), which with `mpFin` feeds
3. the genuine window vanishing (`αGenuine_eq_zero_on_range_of_matching_monic` on `[n, T]`),
   extended past `T` by `htailBeyond`, giving the full truncation tail; meanwhile
4. `hgoodDisc` + the `elimPoly ξ` condition disc give the per-place `ξ`-reading nonvanishing
   on the good set (`xiReading_ne_zero_of_mem_discMatchingSet`, with the global `ξ ≠ 0`
   PROVEN by `Match304.ξ_ne_zero`), so that
5. the analytic per-`z` assembly (`curveHenselDatum_of_truncatedLocalRoot_genuine`) discharges
   all seven curve-Hensel fields, and Hensel uniqueness pins `P z` to the curve
   (`curveFamilyData_of_curveHenselDatum`). -/
noncomputable def curveFamilyData_of_faithfulFrontier
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : FaithfulFrontierData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    FaithfulCurveExtraction.CurveFamilyData
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  haveI := d.iIrr
  haveI := d.iPos
  -- (1) the §6 counting in the exact graded shape
  have hconcreteFin := (Match304.matchingSet304_geometry_and_card d.fB d.x₀ d.gb.R d.gb.H
      d.gb.hH d.gb.hHyp d.hfBdeg d.hfBdiscr d.hfBne (k := d.n) d.hbig).2
  -- (2) the graded weight collapse at the signed canonical family
  have hcardFin := GenuineMonicCapstone.hcardFin_of_graded_signed d.x₀ d.gb.R d.gb.H
      d.gb.hHyp d.gb.hD d.gb.hH d.hres.hmonic d.hres.hd2 d.gb.hdHD d.gb.hD_Rx0 d.gb.hR
      hconcreteFin
  -- (3) genuine-coefficient vanishing on the counting window [n, T]
  have hwindow := FaithfulCurveExtraction.αGenuine_eq_zero_on_range_of_matching_monic d.x₀
      d.gb.R d.gb.hHyp d.hres.hmonic.leadingCoeff d.gb.hH d.gb.D d.gb.hD d.n d.T d.mpFin
      hcardFin
  -- (3′) the full truncation tail: window + beyond-window residual
  have hvanish : ∀ t, d.n ≤ t → αGenuine d.gb.H d.x₀ d.gb.R d.gb.hHyp t = 0 := fun t ht => by
    by_cases htT : t ≤ d.T
    · exact hwindow t ht htT
    · exact d.htailBeyond t (by omega)
  -- (4)+(5) the analytic per-`z` Hensel assembly and the curve pin
  FaithfulCurveExtraction.curveFamilyData_of_curveHenselDatum d.hn
    (FaithfulCurveExtraction.curveHenselDatum_of_truncatedLocalRoot_genuine d.gb.hHyp
      (Match304.ξ_ne_zero d.gb.H d.x₀ d.gb.R d.gb.hHyp) d.hres.hmonic.leadingCoeff d.hRsep
      d.root
      (fun z hz => xiReading_ne_zero_of_mem_discMatchingSet (d.hgoodDisc z hz) (d.root z))
      hvanish d.htrunc d.hdvd d.hcong)

/-! ## Part 5 — the keystone front doors -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` faithful-frontier producer.** -/
theorem strictCoeffPolysResidual_of_faithful_frontier
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        FaithfulFrontierData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData
    (curveFamilyData_of_faithfulFrontier (hInput hk u hprob hJ hsqrt P hP))

omit [DecidableEq ι] in
/-- **THE FRONTIER THEOREM.**  The §5 keystone goal `δ_ε_correlatedAgreementCurves` (strict
Johnson regime), from a per-`(u, P)` producer of the faithful frontier bundle — the hypothesis
list is exactly the named honest residuals of the round-1 harvest (see the docstring table);
every proven lane (graded re-grading, §6 condition-disc counting, signed weight collapse,
genuine window vanishing, per-place `ξ`-readings, the analytic Hensel assembly, Hensel
uniqueness, the faithful extraction) is composed away. -/
theorem correlatedAgreement_affine_curves_of_faithful_frontier
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        FaithfulFrontierData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ hsqrt P hP =>
      curveFamilyData_of_faithfulFrontier (hInput hk u hprob hJ hsqrt P hP))

/-- **The closed-radius frontier front door** (boundary branch via the packaged
`BoundaryCardResidual`). -/
theorem correlatedAgreement_affine_curves_of_faithful_frontier_closed
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        FaithfulFrontierData (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ hsqrt P hP =>
      curveFamilyData_of_faithfulFrontier (hInput hk u hprob hJ hsqrt P hP))
    hBoundaryCard

/-! ## Part 6 — the `Z`-linear lane front door (the `n + m < k + 2` budget split) -/

omit [DecidableEq ι] in
/-- **The place-reading frontier front door** (the Claim-5.9 two-series lane of
`CurveFamilyZLinear`): the keystone from a per-`(u, P)` producer of the place-reading datum
`CurvePlaceReading` (centre, `n` two-series coefficients, the per-`z` branch readings) plus
branch rationality (`m` branch coefficients) under the split budget `n + m < k + 2` — the
reading convolution (`curveFamilyData_of_placeReading`, PROVEN) does the rest. -/
theorem correlatedAgreement_affine_curves_of_placeReading_frontier
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Σ' (x₀ : F) (n m : ℕ) (c₀ c₁ : ℕ → F[X]) (b : ℕ → F) (_ : n + m < k + 2)
          (d : FaithfulCurveExtraction.CurvePlaceReading
            (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c₀ c₁),
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            d.r z = ∑ s ∈ Finset.range m, b s * (z - x₀) ^ s) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro hk u hprob hJ P hP
  obtain ⟨x₀, n, m, c₀, c₁, b, hnm, d, hbranch⟩ := hInput hk u hprob hJ hδ P hP
  exact FaithfulCurveExtraction.hcoeffPoly_witness_of_placeReading hnm d hbranch

end Frontier

end FaithfulFrontier

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulFrontier.xiReading_ne_zero_of_mem_discMatchingSet
#print axioms ArkLib.FaithfulFrontier.htailBeyond_of_lift_window
#print axioms ArkLib.FaithfulFrontier.FaithfulFrontierData
#print axioms ArkLib.FaithfulFrontier.curveFamilyData_of_faithfulFrontier
#print axioms ArkLib.FaithfulFrontier.strictCoeffPolysResidual_of_faithful_frontier
#print axioms ArkLib.FaithfulFrontier.correlatedAgreement_affine_curves_of_faithful_frontier
#print axioms ArkLib.FaithfulFrontier.correlatedAgreement_affine_curves_of_faithful_frontier_closed
#print axioms ArkLib.FaithfulFrontier.correlatedAgreement_affine_curves_of_placeReading_frontier
