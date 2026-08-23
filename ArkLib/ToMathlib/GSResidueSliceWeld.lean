/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceMappedSeparability
import ArkLib.ToMathlib.GSSurfaceRadicalSupply

/-!
# Issues #301/#302/#304 — the residue computation: the per-place residue IS the centre slice

**The named residue computation** welding `MappedSliceSeparability.of_residue`
(`GSSurfaceMappedSeparability.lean`) to the good-centre counting
(`GSSurfaceRadicalSupply.lean`).

## The computation (§1)

At each place `(z, root)` with `π_z(ξ) ≠ 0`, the residue (constant-term image in `F[Y]`) of
the doubly-mapped matching polynomial is computed *exactly*:

  `((R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map π̂_z)) mod X
     = (Bivariate.evalX (C x₀) R).map (evalRingHom z)`

(`residue_mapped_eq_slice`): the residue is the **`(x₀, z)`-slice of the surface** — the
centre slice `R(x₀, Z, Y)` further specialized at `Z := z`.  Coefficientwise this is
`constantCoeff ∘ π̂_z ∘ coeffHom_loc = eval z ∘ eval (C x₀)` (Taylor recentering reads its
constant term at the centre, `locLift` lands in `Y`-constants of `𝒪 H`, and `π_z` on
`Y`-constants is evaluation at `z` — `π_z_mk` + `evalEval_C`).  In particular the residue is
**independent of the chosen `root`** over `z`.

## The weld (§2–§3)

Two structural consequences, both *forced* by the computation:

1. **Residue separability is already in `hHyp`**: `Hypotheses.separable_evalX` is
   `(evalX (C x₀) R).Separable` over `F[Z]` — a Bézout identity that maps along
   `evalRingHom z` — so the residue polynomial is separable over the field `F` at **every**
   place.  The open content of `MappedSliceSeparability.of_residue` therefore collapses to
   its *degree-preservation* legs alone.
2. **Degree preservation = leading-coefficient avoidance**: the residue has the full
   `Y`-degree of `R` exactly when (a) the centre slice preserves it
   (`hcdeg : (evalX (C x₀) R).natDegree = R.natDegree` — the good-centre counting leg,
   `GSSurfaceRadicalSupply.slice_natDegree_eq_of_leadingCoeff_eval_ne` /
   `exists_good_centre_slice_discr_ne_zero`) and (b) `z` avoids the roots of the slice's
   `Y`-leading coefficient `(evalX (C x₀) R).leadingCoeff = G.leadingCoeff ∈ F[Z]` (monic
   `H`).  A degree squeeze (`map` never raises degree, the residue attains `R.natDegree`)
   then forces every intermediate degree to agree, and
   `separable_of_powerSeries_residue` fires (`mapped_separable_of_slice_natDegree`).

So `MappedSliceSeparability` is **produced** (not hypothesized): everywhere when the slice
leading coefficient has no roots (`mappedSliceSeparability_of_slice_leadingCoeff`), and on
the avoidance locus of `G.leadingCoeff` in general
(`MappedSliceSeparabilityOn`, `mappedSliceSeparabilityOn_of_slice_leadingCoeff`).

## The welded capstones (§4–§5)

The decoded-capstone chain only ever consumes the separability at places `z` in the
matching set, so the chain is re-proved with the set-restricted hypothesis
(`hvanish_of_decoded_roots_residue` → `gammaGenuine_eq_trunc_of_decoded_roots_residue`),
and the global capstone folds the leading-coefficient factor into the branch/ξ certificate:

* `gammaGenuine_eq_trunc_global_residue` — **no separability hypothesis beyond `hHyp`
  itself**: the matching set is the nonvanishing locus of
  `branchCert · xiCert · G.leadingCoeff`, the budget gains `G.leadingCoeff.natDegree`
  (bounded by the sloped interpolant budgets), and the per-place separability is
  manufactured from `hHyp.separable_evalX` via the residue computation.
* `gammaGenuine_eq_trunc_of_surface_residue` — the `GSSurfaceSupply` §5 shape
  (`G := cofactor hHyp`); `gammaGenuine_eq_trunc_of_surface_residue'` derives the centre
  degree-preservation leg from the counted condition
  `R.leadingCoeff.eval (C x₀) ≠ 0` (Schwartz–Zippel bad-centre count
  `c56_evalC_bad_set_card_le`).

Net effect on the open-node ledger: Node B's relocated open content (per-place residue
separability) is **closed** — it was contained in `hHyp` all along, and the residue
computation is what exposes it.  What the capstone now consumes beyond `hHyp` is purely
counted/numeric: centre degree preservation + the enlarged avoidance budget.

## References
* [BCIKS20] §5–§6, Appendix A; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace MappedSeparability

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## §1 — THE NAMED RESIDUE COMPUTATION -/

/-- **The coefficientwise residue computation**: on the interpolant's coefficient ring, the
composite `constantCoeff ∘ π̂_z ∘ coeffHom_loc` is evaluation at `(x₀, z)`:
the Taylor recentering contributes its constant term `q ↦ q.eval (C x₀)` (`taylor_coeff_zero`),
`locLift` lands in the `Y`-constants of `𝒪 H`, and `π_z` on `Y`-constants is evaluation at
`z` (`π_z_mk` + `evalEval_C`).  Note the result does not depend on `root`. -/
theorem constantCoeff_mapped_eq_slice_eval {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (q : F[X][X]) :
    PowerSeries.constantCoeff (R := F)
        (PowerSeries.map (π_hat_z hHyp z root hx) (coeffHom_loc x₀ hHyp q))
      = (q.eval (Polynomial.C x₀)).eval z := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    coeff_coeffHom_loc, Polynomial.taylor_coeff_zero]
  have h1 : locLift hHyp (q.eval (Polynomial.C x₀))
      = algebraMap (𝒪 H) (Localization.Away (ξ x₀ R H hHyp))
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (Polynomial.C (q.eval (Polynomial.C x₀)))) := rfl
  rw [h1, π_hat_z_comp, π_z_mk, Polynomial.evalEval_C]

/-- **THE NAMED RESIDUE COMPUTATION** (critical-path item (1) of the Nodes-A+B landing):
the residue `mod X` of the doubly-mapped matching polynomial at the place `(z, root)` is
**the `(x₀, z)`-slice of the surface**:

  `((R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map π̂_z)).map constantCoeff
     = (Bivariate.evalX (C x₀) R).map (evalRingHom z)`.

This is the exact polynomial the good-centre counting controls — the weld between
`MappedSliceSeparability.of_residue` and `GSSurfaceRadicalSupply`. -/
theorem residue_mapped_eq_slice {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).map (PowerSeries.constantCoeff (R := F))
      = (Bivariate.evalX (Polynomial.C x₀) R).map (Polynomial.evalRingHom z) := by
  rw [Bivariate.evalX_eq_map]
  ext n
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  exact constantCoeff_mapped_eq_slice_eval hHyp z root hx (R.coeff n)

/-! ## §2 — the per-place separability producer

The two inputs of `separable_of_powerSeries_residue` are discharged as follows.

* *Residue separability*: already contained in `hHyp` — `Hypotheses.separable_evalX` is a
  Bézout identity over `F[Z]`, which maps along `evalRingHom z` to the residue slice.
* *Degree preservation*: a squeeze.  `Polynomial.map` never raises `natDegree`, and by the
  residue computation the residue equals the slice; so if the slice attains the full
  `Y`-degree of `R`, every intermediate degree is pinned to it. -/

/-- **Per-place separability of the mapped matching polynomial from the slice degree
alone.**  Residue separability is free from `hHyp.separable_evalX`; the degree-preservation
squeeze pins `natDegree` of the mapped polynomial and its residue to `R.natDegree`; Lemma 2′
(`separable_of_powerSeries_residue`) does the rest. -/
theorem mapped_separable_of_slice_natDegree {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hRdeg : 0 < R.natDegree)
    (hslice : ((Bivariate.evalX (Polynomial.C x₀) R).map
        (Polynomial.evalRingHom z)).natDegree = R.natDegree) :
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable := by
  set f : Polynomial (PowerSeries F) :=
    (R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx)) with hf
  have hres : f.map (PowerSeries.constantCoeff (R := F))
      = (Bivariate.evalX (Polynomial.C x₀) R).map (Polynomial.evalRingHom z) :=
    residue_mapped_eq_slice hHyp z root hx
  have h1 : f.natDegree ≤ R.natDegree :=
    le_trans Polynomial.natDegree_map_le Polynomial.natDegree_map_le
  have h3 : (f.map (PowerSeries.constantCoeff (R := F))).natDegree = R.natDegree := by
    rw [hres, hslice]
  have hfdeg : f.natDegree = R.natDegree :=
    le_antisymm h1 (h3 ▸ Polynomial.natDegree_map_le)
  refine separable_of_powerSeries_residue ?_ ?_ ?_
  · rw [hfdeg]; exact hRdeg
  · rw [h3, hfdeg]
  · rw [hres]
    exact hHyp.separable_evalX.map

/-! ## §3 — the produced `MappedSliceSeparability` (full and set-restricted) -/

/-- **The full `MappedSliceSeparability`, PRODUCED** (no longer a hypothesis), in the regime
where the slice leading coefficient has no `F`-roots (e.g. the slice is monic in `Y`, or its
leading coefficient is a nonzero constant): the centre degree-preservation leg `hcdeg` plus
rootlessness give the slice degree at every `z`, and §2 fires.  This feeds the *existing*
`gammaGenuine_eq_trunc_of_surface_mapped` unchanged. -/
theorem mappedSliceSeparability_of_slice_leadingCoeff {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hRdeg : 0 < R.natDegree)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    (hlc : ∀ z : F, (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff.eval z ≠ 0) :
    MappedSliceSeparability hHyp := by
  intro z root hx
  refine mapped_separable_of_slice_natDegree hHyp z root hx hRdeg ?_
  have hlcz : (Polynomial.evalRingHom z)
      (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff ≠ 0 := by
    simpa [Polynomial.coe_evalRingHom] using hlc z
  rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlcz, hcdeg]

/-- The set-restricted per-place separability hypothesis — the exact amount the decoded
chain consumes (it only ever reads places `z` in the matching set). -/
def MappedSliceSeparabilityOn {x₀ : F} {R : F[X][X][Y]} (S : Finset F)
    (hHyp : Hypotheses x₀ R H) : Prop :=
  ∀ z ∈ S, ∀ (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0),
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable

/-- The full hypothesis restricts to any set. -/
theorem MappedSliceSeparabilityOn.of_full {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H} (h : MappedSliceSeparability hHyp) (S : Finset F) :
    MappedSliceSeparabilityOn S hHyp :=
  fun z _ root hx => h z root hx

/-- **The set-restricted producer on the leading-coefficient avoidance locus** — the general
form of the weld: at every `z` avoiding the roots of the slice's `Y`-leading coefficient,
the place is separable.  The bad `z` are at most `(evalX (C x₀) R).leadingCoeff.natDegree`
many — the factor the welded capstone folds into its certificate budget. -/
theorem mappedSliceSeparabilityOn_of_slice_leadingCoeff {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hRdeg : 0 < R.natDegree)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    {S : Finset F}
    (hS : ∀ z ∈ S, (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff.eval z ≠ 0) :
    MappedSliceSeparabilityOn S hHyp := by
  intro z hz root hx
  refine mapped_separable_of_slice_natDegree hHyp z root hx hRdeg ?_
  have hlcz : (Polynomial.evalRingHom z)
      (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff ≠ 0 := by
    simpa [Polynomial.coe_evalRingHom] using hS z hz
  rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlcz, hcdeg]

/-! ## §4 — the decoded chain on the set-restricted hypothesis -/

/-- Per-place `MatchingPoint` from decoded data, taking the separability fact directly
(the building block freeing the chain from the global `∀ z` hypothesis). -/
noncomputable def matchingPoint_of_decoded_at {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsep : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) (hkt : k ≤ t) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries_dvd hHyp hξ hlc z root hx
    (DecodedProximateRoot.aPDecoded hHyp z root hx w)
    (DecodedProximateRoot.aPDecoded_dvd hHyp z root hx hdvd)
    (DecodedProximateRoot.aPDecoded_cong hHyp z root hx hbase)
    hsep
    t (DecodedProximateRoot.coeff_aPDecoded_eq_zero hHyp z root hx
      (lt_of_lt_of_le hdeg hkt))

/-- `hvanish_of_decoded_roots_mapped` with the separability needed only **on the matching
set** — the exact consumption shape, enabling the certificate-folded capstone below. -/
theorem hvanish_of_decoded_roots_residue {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G : F[X][Y]} {k : ℕ}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hsepOn : MappedSliceSeparabilityOn matchingSet hHyp) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t) = 0 := by
  intro t hkt _ z hz
  refine ⟨DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz), ?_⟩
  rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t]
  exact (matchingPoint_of_decoded_at hHyp hξ hlc z
    (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)) (hx z hz)
    hdeg hdvd
    (DecodedRootSupply.rootDecoded_val_monic (Fact.out) hlc hsplit hdvd z (hbranch z hz))
    (hsepOn z hz _ (hx z hz)) t hkt).pi_z_eq_zero

section Capstones

variable [Fintype F] [DecidableEq F]

/-- `gammaGenuine_eq_trunc_of_decoded_roots_mapped` with the separability needed only on
the matching set. -/
theorem gammaGenuine_eq_trunc_of_decoded_roots_residue {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F} {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hsepOn : MappedSliceSeparabilityOn matchingSet hHyp)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH hmonic
    hd2 hdHD hD_Rx0 hRgrade hrepT
    (hvanish_of_decoded_roots_residue hHyp hξ hmonic.leadingCoeff hsplit hdeg hdvd
      hbranch hsepOn (max P₀.natDegree P₁.natDegree) hx)
    hdisc hcover hbig

/-! ## §5 — the welded global capstones: separability fully manufactured from `hHyp` -/

/-- **THE WELDED GLOBAL CAPSTONE**: `gammaGenuine_eq_trunc_global_mapped` with the
separability hypothesis **eliminated** — manufactured from `hHyp.separable_evalX` via the
residue computation.  The matching set is the nonvanishing locus of
`branchCert · xiCert · G.leadingCoeff` (the avoidance polynomial gains the slice
leading-coefficient factor; the budget gains its degree), and the only new structural
hypothesis is the counted good-centre leg `hcdeg` (degree preservation at the centre). -/
theorem gammaGenuine_eq_trunc_global_residue {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + ((G.eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))
            * G.leadingCoeff).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  classical
  set vC : F[X] := w.eval (Polynomial.C x₀) with hvC
  set dBr : F[X] := G.eval vC with hdBr
  set dXi : F[X] := (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval vC with hdXi
  set dLc : F[X] := G.leadingCoeff with hdLc
  have hG0 : G ≠ 0 := fun h0 => hbr (by rw [hdBr, h0, Polynomial.eval_zero])
  have hLc0 : dLc ≠ 0 := by
    rw [hdLc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hG0
  have hdisc : dBr * dXi * dLc ≠ 0 := mul_ne_zero (mul_ne_zero hbr hxi) hLc0
  set ms : Finset F := BranchCertificates.nonvanishingLocus (dBr * dXi * dLc) with hms
  have hbranch : ∀ z ∈ ms, Polynomial.evalEval z (vC.eval z) G ≠ 0 := by
    intro z hz
    have h := (BranchCertificates.mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul, Polynomial.eval_mul] at h
    have hBr : dBr.eval z ≠ 0 := fun h0 => h (by rw [h0, zero_mul, zero_mul])
    rw [hdBr] at hBr
    rw [← BranchCertificates.branchCert_eval G w x₀ z]
    exact hBr
  have hx : ∀ z (hz : z ∈ ms),
      (π_z z (DecodedRootSupply.rootDecoded hH hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0 := by
    intro z hz
    have h := (BranchCertificates.mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul, Polynomial.eval_mul] at h
    have hXi : dXi.eval z ≠ 0 := fun h0 => h (by rw [h0, mul_zero, zero_mul])
    rw [BranchCertificates.xiCert_eval_monic hH hmonic.leadingCoeff hsplit hdvd z
      (hbranch z hz)]
    rw [hdXi] at hXi
    exact hXi
  have hRdeg : 0 < R.natDegree := lt_of_lt_of_le Nat.zero_lt_two hd2
  have hsepOn : MappedSliceSeparabilityOn ms hHyp := by
    refine mappedSliceSeparabilityOn_of_slice_leadingCoeff hHyp hRdeg hcdeg ?_
    intro z hz
    have h := (BranchCertificates.mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul] at h
    have hLcz : dLc.eval z ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    have hRxlc : (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff = G.leadingCoeff := by
      rw [hsplit, Polynomial.leadingCoeff_mul, hmonic.leadingCoeff, one_mul]
    rw [hRxlc, ← hdLc]
    exact hLcz
  exact gammaGenuine_eq_trunc_of_decoded_roots_residue hHyp hξ hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepT hsplit hdeg hdvd hbranch hsepOn hx hdisc
    (fun z hz => (BranchCertificates.mem_nonvanishingLocus).mpr hz) hbig

/-- **The `GSSurfaceSupply` §5 shape of the welded capstone** (`G := cofactor hHyp`,
`hsplit` eliminated): the deepest consumer, with **no separability input beyond `hHyp`
itself** — Node B's relocated open content is closed by the residue computation. -/
theorem gammaGenuine_eq_trunc_of_surface_residue {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    (hbr : (GSSurfaceSupply.cofactor hHyp).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + (((GSSurfaceSupply.cofactor hHyp).eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))
            * (GSSurfaceSupply.cofactor hHyp).leadingCoeff).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  gammaGenuine_eq_trunc_global_residue hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hrepT
    (GSSurfaceSupply.cofactor_spec hHyp) hdeg hdvd hcdeg hbr hxi hbig

/-- The §5 welded capstone with the centre degree-preservation leg `hcdeg` derived from the
**counted** condition `R.leadingCoeff.eval (C x₀) ≠ 0` (bad centres ≤
`deg (R.leadingCoeff|_{z})` by `c56_evalC_bad_set_card_le` — the
`exists_good_centre_slice_discr_ne_zero` supply shape). -/
theorem gammaGenuine_eq_trunc_of_surface_residue' {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hlcx : R.leadingCoeff.eval (Polynomial.C x₀) ≠ 0)
    (hbr : (GSSurfaceSupply.cofactor hHyp).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + (((GSSurfaceSupply.cofactor hHyp).eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))
            * (GSSurfaceSupply.cofactor hHyp).leadingCoeff).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  gammaGenuine_eq_trunc_of_surface_residue hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
    hrepT hdeg hdvd
    (GSSurfaceRadicalSupply.slice_natDegree_eq_of_leadingCoeff_eval_ne hlcx)
    hbr hxi hbig

end Capstones

end MappedSeparability

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.MappedSeparability.constantCoeff_mapped_eq_slice_eval
#print axioms ArkLib.MappedSeparability.residue_mapped_eq_slice
#print axioms ArkLib.MappedSeparability.mapped_separable_of_slice_natDegree
#print axioms ArkLib.MappedSeparability.mappedSliceSeparability_of_slice_leadingCoeff
#print axioms ArkLib.MappedSeparability.MappedSliceSeparabilityOn
#print axioms ArkLib.MappedSeparability.MappedSliceSeparabilityOn.of_full
#print axioms ArkLib.MappedSeparability.mappedSliceSeparabilityOn_of_slice_leadingCoeff
#print axioms ArkLib.MappedSeparability.matchingPoint_of_decoded_at
#print axioms ArkLib.MappedSeparability.hvanish_of_decoded_roots_residue
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_of_decoded_roots_residue
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_global_residue
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_of_surface_residue
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_of_surface_residue'
