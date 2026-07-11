/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ14BCIKS57Chunk2
import ArkLib.ToMathlib.GenuinePpolyConverter

/-!
# SYZ15 — the `T`-loaded interface repair for the BCIKS20 §5 branch handoff

## The obstruction (SYZ14 + issue #304 F6)

`Frontier/_SYZ14BCIKS57Chunk2.lean` reduced the [BCIKS20] Claim 5.7 per-cell package to a single
named branch residual `HenselBranchSupply`, whose γ-representative field is the *ground-line*
identity

  `hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp`.

`ToMathlib/GenuinePpolyConverter.lean` (`not_hrepG_of_two_le_natDegree`, FINDING F6) proves this
equation is **unsatisfiable for `2 ≤ H.natDegree`**: `coeff 0 (polyToPowerSeries𝕃 H Ppoly)` lives
on the ground `F[Z]`-line, while `coeff 0 (gammaGenuine) = α₀ = T/W` is off it. So the *literal*
`HenselBranchSupply` — and hence `PlaceCurveSupply`, `DiscLocusCellData`, the whole disc-locus
package — is vacuous at every curve of interest (`d_H = 2` is the in-tree monic-quadratic regime).

## Where `hrepG` is actually consumed (the trace)

Following the field down the assembly:
`DiscLocusCellData.hrepG` → `CellPackage.ofSurfaceRootDiscLocus` → `.ofSurfaceRootShared` →
`.ofSurfaceRoot`, and there it is used **exactly once**, to build the `htail` leg via

  `BCIKS20.Claim510SlicedComposition.gammaGenuine_eq_trunc_of_decoded_sliced … hrepG …`

which in turn calls `GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc … hrepG …`.
Every other appearance of `Ppoly` is the *numeric* budget `Ppoly.natDegree` in `hbig`.

**The converter already supplies the satisfiable replacement** for that single consumer:
`GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected`, which takes the T-loaded
`hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine` and the tail index `max (deg P₀) (deg P₁)`.

## What this file delivers (the shallowest correct repair)

1. **`gammaGenuine_eq_trunc_of_decoded_sliced_T`** — the T-loaded twin of the sliced truncation
   capstone (core repair; proved by routing `hvanish_of_decoded_sliced` at `max (deg P₀)(deg P₁)`
   into the corrected converter capstone).
2. **`CellPackage.ofSurfaceRootT`** — the T-loaded smart constructor: a genuine `CellPackage`
   from T-loaded branch data. Byte-for-byte `ofSurfaceRoot` except the `htail` leg goes through
   (1) and `hbig` budgets on `max (deg P₀)(deg P₁)`. This is the point where satisfiability is
   restored.
3. **`DiscLocusCellDataT`** + **`CellPackage.ofDiscLocusDataT`** — the T-loaded twin of the SYZ8
   disc-locus cell data and its rebuild into a full `CellPackage`.
4. **`CellPackageSupplyDiscLocusT`** + **`cellPackageSupply_of_discLocusT`** — the T-loaded supply
   Prop and its reduction to the named `CellPackageSupply` residual, re-basing the whole Johnson
   floor lane on the **satisfiable** branch data.
5. **Non-vacuity** (`branch_field_gap_at_monic_quadratic`): at a monic quadratic curve
   (`d_H = 2`) the *ground* branch field is empty (F6) while the *T*-loaded field is inhabited
   (converter Claim 5.9 closure) given the truncation identity — the repaired field is provably
   NOT subject to the SYZ14 obstruction.
6. **`HenselBranchSupplyT`** + **`discLocusCellDataT_of_henselBranchT`** — the T-loaded branch
   residual and its derived-root assembly into `DiscLocusCellDataT` (the `root` section derived
   via `DecodedRootSupply.rootDecoded`, as in SYZ14).

## Honest residual

The SYZ11–13 *carrier* structures (`PlaceCurveSupply`, `GradedYRootSupply`, `DiscBudgetSupply`,
`MatchingFoldSupply`, `HeavyPinSupply`) still bake in the ground `(Ppoly, hrepG)` pair as a
pass-through field; none of them *use* it semantically. Producing their `(P₀, P₁, hrepT)`
twins is a purely mechanical field rename (no new mathematics), tracked here as the named
`SYZ11-13 T-carrier rename` residual. `discLocusCellDataT_of_henselBranchT` therefore assembles
`DiscLocusCellDataT` directly from the branch residual plus the C4/C5/C6 numeric data, bypassing
those pass-through carriers rather than re-deriving all five twins.

Axiom target: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal ENNReal
open ArkLib

namespace BCIKS20.CellPencilJohnson.SYZ15

/-! ## 1. The core repair: the T-loaded sliced truncation capstone -/

section Capstone

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The `T`-loaded sliced truncation capstone.**  Verbatim
`Claim510SlicedComposition.gammaGenuine_eq_trunc_of_decoded_sliced` except the F6-unsatisfiable
ground representative `hrepG` is replaced by the **satisfiable** T-loaded representative
`hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine`, and the tail budget `Ppoly.natDegree` by
`max (deg P₀) (deg P₁)`.  Proved by feeding `hvanish_of_decoded_sliced` at that tail index into
`GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected`. -/
theorem gammaGenuine_eq_trunc_of_decoded_sliced_T {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z, ∀ hz : z ∈ matchingSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
          (max P₀.natDegree P₁.natDegree)
        + disc.natDegree < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k
            (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H)) :=
  ArkLib.GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH
    hmonic hd2 hdHD hD_Rx0 hRgrade hrepT
    (BCIKS20.Claim510SlicedComposition.hvanish_of_decoded_sliced hHyp hξ hmonic.leadingCoeff
      root hx hdeg hdvd hbase hsepT (max P₀.natDegree P₁.natDegree))
    hdisc hcover hbig

end Capstone

/-! ## 2. The T-loaded `CellPackage` smart constructor -/

variable {F₀ : Type} [Field F₀]

/-- **The T-loaded smart constructor for `CellPackage`.**  Byte-for-byte
`CellPackage.ofSurfaceRoot` (`Hab25JohnsonPackageSupply.lean`), except the F6-unsatisfiable
ground representative field `hrepG` is replaced by the satisfiable T-loaded `hrepT`, the tail
budget `Ppoly.natDegree` by `max (deg P₀) (deg P₁)`, and the derived `htail` leg routes through
`gammaGenuine_eq_trunc_of_decoded_sliced_T`.  Every other field is identical. -/
noncomputable def CellPackage.ofSurfaceRootT [Fintype F₀] [DecidableEq F₀] {n : ℕ}
    [NeZero n] {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F₀[X][Y]}
    (hrepT : ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F₀) → rationalRoot (H_tilde' H) z)
    {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {truncSet : Finset F₀}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z ∈ truncSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {disc : F₀[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F₀, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
          (max P₀.natDegree P₁.natDegree)
        + disc.natDegree < Fintype.card F₀)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    (matchingSet : Fin n → Finset F₀)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hbase₀ : ∀ z ∈ S₀, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsep₀ : ∀ z ∈ S₀,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    CellPackage domain k δ u R H where
  x₀ := x₀
  hHyp := hHyp
  hmonic := hmonic
  htail := BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc H hHyp
    (gammaGenuine_eq_trunc_of_decoded_sliced_T hHyp
      (BCIKS20.Claim510AgreementSupply.xi_ne_zero_of_monic hHyp hmonic.leadingCoeff)
      hD (Fact.out) hmonic hd2 hdHD hD_Rx0 hRgrade hrepT root
      (fun z _ => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
        hmonic.leadingCoeff z (root z))
      hwdeg hwdvd hbaseT (fun z hz => hsepT z hz) hdisc hcover hbig)
  e := e
  he := he
  u₀ := u₀
  u₁ := u₁
  D := D
  hD := hD
  matchingSet := matchingSet
  root := root
  w := w
  hwdeg := hwdeg
  hwdvd := hwdvd
  hbaseA := hbaseA
  hsepA := hsepA
  hfold := hfold
  W := BCIKS20.Claim510Supply.killBudget n D H.natDegree (Bivariate.natDegreeY R) xw
  hweight := fun j => BCIKS20.Claim510Supply.weight_killTarget_le H x₀ R hHyp hD
    (Fact.out) hmonic hd2 hdHD hD_Rx0 hRgrade hξw n (e j) (u₀ j) (u₁ j)
  hcard := hcard
  S₀ := S₀
  hbase₀ := hbase₀
  hsep₀ := hsep₀
  Bw := Bw
  hBw := hBw
  hS₀ := hS₀

/-! ## 3. The T-loaded disc-locus cell data and its rebuild -/

/-- **The T-loaded disc-locus per-cell data.**  The `DiscLocusCellData` twin (SYZ8), with the
ground representative pair `(Ppoly, hrepG)` replaced by the T-loaded pair `(P₀, P₁, hrepT)` and
the budget `hbig` reading `max (deg P₀) (deg P₁)`.  Unlike its ground counterpart, this structure
is **inhabitable** at every monic curve of interest (its representative field is satisfiable at
`d_H = 2`; see `branch_field_gap_at_monic_quadratic`). -/
structure DiscLocusCellDataT [Fintype F₀] [DecidableEq F₀] {n : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0) (u : WordStack F₀ (Fin 2) (Fin n))
    (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : Type where
  x₀ : F₀
  hHyp : Hypotheses x₀ R H
  hmonic : H.Monic
  D : ℕ
  hD : Bivariate.totalDegree H ≤ D
  hd2 : 2 ≤ Bivariate.natDegreeY R
  hdHD : H.natDegree ≤ D
  hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)
  hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j
  P₀ : F₀[X][Y]
  P₁ : F₀[X][Y]
  hrepT : ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
    = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
  root : (z : F₀) → rationalRoot (H_tilde' H) z
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R
  disc : F₀[X]
  hdisc : disc ≠ 0
  hbaseT : ∀ z : F₀, disc.eval z ≠ 0 → (w.eval (Polynomial.C x₀)).eval z = (root z).1
  hsepT : ∀ z : F₀, disc.eval z ≠ 0 →
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z (root z)
        (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
          hmonic.leadingCoeff z (root z))))).Separable
  hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree (max P₀.natDegree P₁.natDegree)
      + disc.natDegree < Fintype.card F₀
  e : Fin n → F₀
  he : Function.Injective e
  u₀ : Fin n → F₀
  u₁ : Fin n → F₀
  matchingSet : Fin n → Finset F₀
  hmatchSub : ∀ j, ∀ z ∈ matchingSet j, disc.eval z ≠ 0
  hfold : ∀ j, ∀ z ∈ matchingSet j,
    (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j
  xw : ℕ
  hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
    (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ)
  hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
      (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card
  S₀ : Finset F₀
  hS₀sub : ∀ z ∈ S₀, disc.eval z ≠ 0
  Bw : ℕ
  hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw
  hS₀ : max Bw 1 < S₀.card

/-- **Rebuild a full `CellPackage` from T-loaded disc-locus data.**  The T-loaded analogue of
`CellPackage.ofDiscLocusData`: pin the truncation set to the disc non-vanishing locus (discharging
the cover leg by `Finset.mem_filter`), and route through `CellPackage.ofSurfaceRootT`.  The four
base/separability legs are derived from the single disc-locus certificates by membership
monotonicity. -/
noncomputable def CellPackage.ofDiscLocusDataT [Fintype F₀] [DecidableEq F₀] {n : ℕ}
    [NeZero n] {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (d : DiscLocusCellDataT domain k δ u R H) :
    CellPackage domain k δ u R H :=
  CellPackage.ofSurfaceRootT (truncSet := Finset.univ.filter (fun z => d.disc.eval z ≠ 0))
    d.x₀ d.hHyp d.hmonic d.hD d.hd2 d.hdHD d.hD_Rx0 d.hRgrade d.hrepT d.root d.hwdeg d.hwdvd
    (fun z hz => d.hbaseT z (Finset.mem_filter.mp hz).2)
    (fun z hz => d.hsepT z (Finset.mem_filter.mp hz).2)
    d.hdisc
    (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩)
    d.hbig
    d.e d.he d.u₀ d.u₁ d.matchingSet
    (fun j z hz => d.hbaseT z (d.hmatchSub j z hz))
    (fun j z hz => d.hsepT z (d.hmatchSub j z hz))
    d.hfold d.hξw d.hcard d.S₀
    (fun z hz => d.hbaseT z (d.hS₀sub z hz))
    (fun z hz => d.hsepT z (d.hS₀sub z hz))
    d.hBw d.hS₀

/-! ## 4. The T-loaded supply Prop and its reduction to the named residual -/

/-- **The T-loaded disc-locus supply Prop.**  Identical to `CellPackageSupplyDiscLocus` (SYZ8)
but with the per-cell obligation carried by the **satisfiable** `DiscLocusCellDataT`. -/
def CellPackageSupplyDiscLocusT [Fintype F₀] [DecidableEq F₀] {n : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0) (T : ℕ) : Prop :=
  ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y]) (E : Finset F₀)
    (P : F₀ → F₀[X]),
    Irreducible R →
    (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
    (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
    E.card ≤ T ∨
    ∃ (H : F₀[X][Y]) (h1 : Fact (Irreducible H)) (h2 : Fact (0 < H.natDegree)),
      haveI := h1; haveI := h2
      Nonempty (DiscLocusCellDataT domain k δ u R H)

/-- **The reduction.**  T-loaded disc-locus supply ⟹ the named `CellPackageSupply` residual, by
rebuilding each cell's package with `CellPackage.ofDiscLocusDataT`.  This lets every consumer of
`CellPackageSupply` (the Johnson floor jump, `JohnsonDischargeStatement`, …) be re-based on the
strictly-smaller **and satisfiable** T-loaded form. -/
theorem cellPackageSupply_of_discLocusT [Fintype F₀] [DecidableEq F₀]
    {n k : ℕ} [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0} {T : ℕ}
    (h : CellPackageSupplyDiscLocusT domain k δ T) :
    CellPackageSupply domain k δ T := by
  intro u R E P hRirr hdec hdvdR
  rcases h u R E P hRirr hdec hdvdR with hsmall | ⟨H, h1, h2, hdata⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨H, h1, h2, hdata.map (fun d => CellPackage.ofDiscLocusDataT d)⟩

/-! ## 5. Non-vacuity: the repaired field escapes the SYZ14 obstruction -/

section NonVacuity

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Non-vacuity of the repaired branch field.**  At a monic quadratic curve (`d_H = 2`, the
in-tree regime), given the truncation identity `γ = trunc k γ` (the Claim 5.8 counting content):

* the **ground** representative field is EMPTY — no `Ppoly` satisfies
  `polyToPowerSeries𝕃 H Ppoly = gammaGenuine` (F6, `not_hrepG_of_two_le_natDegree`);
* the **T-loaded** representative field is INHABITED — a pair `(P₀, P₁)` with
  `polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine` and finite coefficient support exists
  (`exists_corrected_representative_of_monic_natDegree_le_two`).

So `DiscLocusCellDataT.hrepT` is provably not subject to the SYZ14 obstruction that empties
`DiscLocusCellData.hrepG`. -/
theorem branch_field_gap_at_monic_quadratic (hd2 : H.natDegree = 2)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic)
    {k : ℕ}
    (htrunc : ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k
            (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H))) :
    (¬ ∃ Ppoly : F[X][Y],
        polyToPowerSeries𝕃 H Ppoly
          = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
      ∧ (∃ P₀ P₁ : F[X][Y],
        ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
          = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
        ∧ (∀ t, k ≤ t → P₀.coeff t = 0) ∧ (∀ t, k ≤ t → P₁.coeff t = 0)) := by
  refine ⟨ArkLib.GenuinePpolyConverter.hrepG_unsat_of_two_le_natDegree H (by omega) hHyp, ?_⟩
  exact ArkLib.GenuinePpolyConverter.exists_corrected_representative_of_monic_natDegree_le_two
    H hHyp hmonic.leadingCoeff (by omega) htrunc

end NonVacuity

/-! ## 6. The T-loaded branch residual and its assembly into `DiscLocusCellDataT` -/

variable {n : ℕ} [NeZero n]

/-- **The T-loaded Hensel-branch supply** (the SYZ14 `HenselBranchSupply` twin).  The
genuinely-open [BCIKS20] §5 branch data, with the ground representative field `(Ppoly, hrepG)`
replaced by the **satisfiable** T-loaded pair `(P₀, P₁, hrepT)`.  Every other field is verbatim
`HenselBranchSupply`. -/
structure HenselBranchSupplyT [Fintype F₀] [DecidableEq F₀]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) : Type where
  G : F₀[X][Y]
  hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R
  hbranch : ∀ z : F₀,
    Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0
  P₀ : F₀[X][Y]
  P₁ : F₀[X][Y]
  hrepT : ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
    = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp

/-- **The T-loaded branch assembly** (the SYZ14 `discLocusCellData_of_henselBranch` twin).  From
the base facts, a `HenselBranchSupplyT`, and the C4/C5/C6 numeric disc-budget / matching-fold /
heavy-pin data (supplied here as explicit typed hypotheses, bypassing the ground-representative
pass-through carriers of SYZ11–13), assemble `DiscLocusCellDataT`.  The per-`z` rational-root
section `root` is **derived** via `DecodedRootSupply.rootDecoded`, exactly as in SYZ14. -/
noncomputable def discLocusCellDataT_of_henselBranchT [Fintype F₀] [DecidableEq F₀]
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    (hb : HenselBranchSupplyT domain k δ u R H x₀ hHyp)
    (D : ℕ) (hD : Bivariate.totalDegree H ≤ D) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (disc : F₀[X]) (hdisc : disc ≠ 0)
    (hsepT : ∀ z : F₀, disc.eval z ≠ 0 →
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z
          (ArkLib.DecodedRootSupply.rootDecoded (Fact.out) hb.hsplit hb.hwdvd z (hb.hbranch z))
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z
            (ArkLib.DecodedRootSupply.rootDecoded (Fact.out) hb.hsplit hb.hwdvd z
              (hb.hbranch z)))))).Separable)
    (hbaseT : ∀ z : F₀, disc.eval z ≠ 0 →
      (hb.w.eval (Polynomial.C x₀)).eval z
        = (ArkLib.DecodedRootSupply.rootDecoded (Fact.out) hb.hsplit hb.hwdvd z (hb.hbranch z)).1)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
          (max hb.P₀.natDegree hb.P₁.natDegree)
        + disc.natDegree < Fintype.card F₀)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    (matchingSet : Fin n → Finset F₀)
    (hmatchSub : ∀ j, ∀ z ∈ matchingSet j, disc.eval z ≠ 0)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (hb.w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    (xw : ℕ)
    (hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hS₀sub : ∀ z ∈ S₀, disc.eval z ≠ 0)
    (Bw : ℕ) (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) hb.w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    DiscLocusCellDataT domain k δ u R H where
  x₀ := x₀
  hHyp := hHyp
  hmonic := hmonic
  D := D
  hD := hD
  hd2 := hd2
  hdHD := hdHD
  hD_Rx0 := hD_Rx0
  hRgrade := hRgrade
  P₀ := hb.P₀
  P₁ := hb.P₁
  hrepT := hb.hrepT
  root := fun z =>
    ArkLib.DecodedRootSupply.rootDecoded (Fact.out) hb.hsplit hb.hwdvd z (hb.hbranch z)
  w := hb.w
  hwdeg := hb.hwdeg
  hwdvd := hb.hwdvd
  disc := disc
  hdisc := hdisc
  hbaseT := hbaseT
  hsepT := hsepT
  hbig := hbig
  e := e
  he := he
  u₀ := u₀
  u₁ := u₁
  matchingSet := matchingSet
  hmatchSub := hmatchSub
  hfold := hfold
  xw := xw
  hξw := hξw
  hcard := hcard
  S₀ := S₀
  hS₀sub := hS₀sub
  Bw := Bw
  hBw := hBw
  hS₀ := hS₀

end BCIKS20.CellPencilJohnson.SYZ15

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ15.gammaGenuine_eq_trunc_of_decoded_sliced_T
#print axioms BCIKS20.CellPencilJohnson.SYZ15.CellPackage.ofSurfaceRootT
#print axioms BCIKS20.CellPencilJohnson.SYZ15.CellPackage.ofDiscLocusDataT
#print axioms BCIKS20.CellPencilJohnson.SYZ15.cellPackageSupply_of_discLocusT
#print axioms BCIKS20.CellPencilJohnson.SYZ15.branch_field_gap_at_monic_quadratic
#print axioms BCIKS20.CellPencilJohnson.SYZ15.discLocusCellDataT_of_henselBranchT
