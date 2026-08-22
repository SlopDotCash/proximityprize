/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ15TLoadedInterfaceRepair
import ArkLib.ToMathlib.BetaTailDegreeVanishing

/-!
# SYZ16 — the Claim 5.8 truncation identity `γ = trunc k γ`, attacked at its root

## The object

The whole T-loaded §5 branch handoff of SYZ15 (`_SYZ15TLoadedInterfaceRepair.lean`) — and its
non-vacuity witness `branch_field_gap_at_monic_quadratic` — takes as an *external hypothesis* the
[BCIKS20] **Claim 5.8 truncation identity**

  `htrunc : gammaGenuine x₀ R H hHyp = ↑(PowerSeries.trunc k (gammaGenuine …))`.

Coefficient-wise this is exactly `αGenuine t = 0` for all `t ≥ k`: the genuine Y-root branch
series is a *polynomial* (its tail vanishes). This file determines **why** that holds and how far
in-tree machinery carries it.

## The mathematical reason (found)

`ToMathlib/BetaTailDegreeVanishing.lean` exhibits the actual mechanism. The genuine branch
coefficients obey the `(A.1)` Hensel recursion `βHensel_succ`, whose structure constants
`B_{i₁,λ}` are built from the `i₁`-th **lift-`X` Hasse derivative** of `R`
(`hasseDerivX i₁`). That derivative annihilates every `Y`-coefficient of `X`-degree `< i₁`
(`B_coeff_eq_zero_of_natDegree_coeff_lt`). Consequently the recursion is *degree-bounded on the
`X`-layer by `deg_X R`*: it is **not** the expansion of an infinite algebraic branch. Concretely
(`βHensel_eq_zero_of_initial_window`): once the branch coefficients vanish on the full initial
segment `[1, T₀]` with `T₀ ≥ deg_X R`, every successor order `> T₀` collapses to an
empty-partition Hasse coefficient of order `> deg_X R`, which vanishes by degree. This is the
in-tree face of "the fold only sees finitely many coefficients": the genuine γ-series is a
polynomial because the numerator recursion is `X`-Hasse-degree bounded.

## What is genuinely provable ab initio, and the honest wall

* **Reduction (largest honest piece).** The truncation identity `γ = trunc k γ` reduces, over the
  finite counting range, to a single *tail-degree datum* `htailDeg : ∀ t, T < t → αGenuine t = 0`
  ("γ is a polynomial of degree `≤ T`"), packaged here as the named residual
  `GammaGenuineTailPolynomial`. Composing `GenuineTruncationFin.SβLargeAtFin_of_graded_disc`
  (the §6 discriminant counting → largeness on `[k, T]`) with
  `GenuineTruncationFin.claim58prime_genuine_fin_of_monic` gives
  `gammaGenuine_eq_trunc_of_graded_disc_tail`: **all** of Claim 5.8 *except* the tail datum is
  discharged from finite geometric data, with no representative anywhere.

* **Ab-initio producer (the mechanism, decoded / full-window regime).**
  `gammaGenuineTailPolynomial_of_initial_window` proves the tail datum with **no representative
  and no assumed truncation**, purely from the recursion degree bound: the `X`-degree budget
  `deg_X R ≤ T₀`, the `(P2)` lift identity, and vanishing of `αGenuine` on the full initial
  segment `[1, T₀]`. This is the honest ab-initio truncation identity — but it settles only the
  regime where the branch is *constant past its window* (the window-collapse / decoded case): the
  naive `[k,T] → T+1` window propagation is **false** (`BetaTailDegreeVanishing`, recorded), so
  the pure `(A.1)`-recursion degree argument reaches only the full-window-collapse case.

* **The wall (the residual, named).** For a branch with a genuinely nonzero window coefficient the
  tail datum `GammaGenuineTailPolynomial` is *equivalent* (monic `d_H ≤ 2`, via the converter of
  `GenuinePpolyConverter`) to the corrected representative `hrepT` itself — so it cannot be
  produced ab initio without the algebraicity / `X`-degree-budget (#138) content. Claim 5.8 in
  its non-degenerate form is therefore isolated here to the single minimal Prop
  `GammaGenuineTailPolynomial`, with every geometric reduction around it discharged.

## Wiring into SYZ15

`branch_field_gap_of_graded_disc_tail` re-derives the SYZ15 non-vacuity witness with the raw
`htrunc` hypothesis **removed**: it now consumes finite geometric data plus the minimal tail
residual and produces `htrunc` internally via `gammaGenuine_eq_trunc_of_graded_disc_tail`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5.2 (Claims 5.8/5.8′, Prop 5.5), Appendix A (Lemma A.1 recursion, `X`-Hasse structure).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine
open ArkLib

namespace BCIKS20.CellPencilJohnson.SYZ16

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## 1. The minimal named residual: "the genuine γ-series is a polynomial" -/

/-- **The Claim 5.8 tail-degree datum** — the minimal residual isolated by SYZ16.  It says the
genuine Y-root branch series `gammaGenuine` is a *polynomial of degree `≤ T`*: `αGenuine t = 0`
for every `t > T`.  Equivalently (`PowerSeries` reading) its tail past `T` vanishes.  This is the
irreducible counting/algebraicity content of [BCIKS20] Claim 5.8; every *other* ingredient of the
truncation identity is discharged from finite geometric data below. -/
def GammaGenuineTailPolynomial (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (T : ℕ) : Prop :=
  ∀ t, T < t → αGenuine H x₀ R hHyp t = 0

/-! ## 2. The reduction: geometric data + tail datum ⟹ the truncation identity -/

section Reduction

variable [Fintype F] [DecidableEq F]

/-- **The truncation identity from finite geometric data + the tail residual.**  Byte-for-byte the
finite geometric inputs of `GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc`, but with
the F6-unsatisfiable ground representative `hrepG` **replaced** by the honest minimal residual
`GammaGenuineTailPolynomial` (the tail-degree datum).  Proved by composing the §6-counting
largeness supply `SβLargeAtFin_of_graded_disc` with `claim58prime_genuine_fin_of_monic`.  No
representative — ground *or* T-loaded — appears; the only non-geometric input is the polynomiality
of the branch. -/
theorem gammaGenuine_eq_trunc_of_graded_disc_tail {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (htail : GammaGenuineTailPolynomial x₀ R hHyp T)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T
        + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.claim58prime_genuine_fin_of_monic H hHyp hmonic.leadingCoeff
    (GenuineTruncationFin.SβLargeAtFin_of_graded_disc H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR
      hvanish hdisc hcover hbig)
    htail

end Reduction

/-! ## 3. The ab-initio producer (the mechanism): full-window collapse via the `(A.1)` recursion -/

/-- **The tail datum from the recursion degree bound (ab initio).**  The genuine branch is a
polynomial whenever the `(A.1)` numerator recursion collapses: given the lift-`X` degree budget
`deg_X R ≤ T₀`, the `(P2)` lift identity at every order, and vanishing of `αGenuine` on the
**full** initial segment `[1, T₀]`, every coefficient past `T₀` vanishes
(`BCIKS20.HenselNumerator.BetaTail.αGenuine_tail_eq_zero_of_window_of_lift`).  This is the honest
ab-initio face of Claim 5.8 — **no** representative, **no** assumed truncation — but it reaches
only the window-collapse (decoded / constant-past-window) regime, since the naive `[k,T]→T+1`
window propagation is false. -/
theorem gammaGenuineTailPolynomial_of_initial_window {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {T₀ : ℕ}
    (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hlift : ∀ t, S5Genuine.LiftIdentityAt H x₀ R hHyp t)
    (hwin : ∀ l, 1 ≤ l → l ≤ T₀ → αGenuine H x₀ R hHyp l = 0) :
    GammaGenuineTailPolynomial x₀ R hHyp T₀ :=
  fun t ht =>
    BCIKS20.HenselNumerator.BetaTail.αGenuine_tail_eq_zero_of_window_of_lift H x₀ R hHyp
      hdX hlift hwin t (by omega)

/-! ## 4. The wall: the tail datum from the corrected representative (the equivalence direction) -/

/-- **The tail datum from a corrected representative.**  If the T-loaded representative `hrepT`
exists, the branch is a polynomial of degree `≤ max (deg P₀) (deg P₁)`
(`GenuinePpolyConverter.htailDeg_genuine_of_corrected_representative`).  Together with the converter
(`exists_corrected_representative_of_monic_natDegree_le_two`, which builds `hrepT` back out of the
truncation identity), this shows that at monic `d_H ≤ 2` the residual
`GammaGenuineTailPolynomial` is *equivalent* to the representative — the wall the ab-initio route
of §3 cannot cross for a non-degenerate window. -/
theorem gammaGenuineTailPolynomial_of_corrected_representative {x₀ : F} {R : F[X][X][Y]}
    {hHyp : ClaimA2.Hypotheses x₀ R H} {P₀ P₁ : F[X][Y]}
    (hrepT : ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
      = gammaGenuine x₀ R H hHyp) :
    GammaGenuineTailPolynomial x₀ R hHyp (max P₀.natDegree P₁.natDegree) :=
  fun t ht =>
    ArkLib.GenuinePpolyConverter.htailDeg_genuine_of_corrected_representative H hrepT t ht

/-! ## 5. Wiring into SYZ15: the non-vacuity witness with `htrunc` removed -/

section Wiring

variable [Fintype F] [DecidableEq F]
variable (H) in
/-- **SYZ15 non-vacuity, with the raw `htrunc` hypothesis discharged.**  The SYZ15 witness
`branch_field_gap_at_monic_quadratic` assumed the Claim 5.8 truncation identity outright.  Here,
at a monic quadratic curve, we *derive* it from finite geometric data plus the minimal tail
residual `GammaGenuineTailPolynomial` (via `gammaGenuine_eq_trunc_of_graded_disc_tail`), then feed
it to the SYZ15 witness.  Result: the ground representative field is EMPTY (F6) while the T-loaded
field is INHABITED — the repaired §5 branch field escapes the SYZ14 obstruction, conditioned now
only on the honest polynomiality residual, not on a bare truncation. -/
theorem branch_field_gap_of_graded_disc_tail
    (hdegH : H.natDegree = 2) {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (htail : GammaGenuineTailPolynomial x₀ R hHyp T)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T
        + disc.natDegree < Fintype.card F) :
    (¬ ∃ Ppoly : F[X][Y],
        polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
      ∧ (∃ P₀ P₁ : F[X][Y],
        ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp
        ∧ (∀ t, k ≤ t → P₀.coeff t = 0) ∧ (∀ t, k ≤ t → P₁.coeff t = 0)) :=
  BCIKS20.CellPencilJohnson.SYZ15.branch_field_gap_at_monic_quadratic H hdegH hHyp hmonic
    (gammaGenuine_eq_trunc_of_graded_disc_tail hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR
      htail hvanish hdisc hcover hbig)

end Wiring

end BCIKS20.CellPencilJohnson.SYZ16

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ16.gammaGenuine_eq_trunc_of_graded_disc_tail
#print axioms BCIKS20.CellPencilJohnson.SYZ16.gammaGenuineTailPolynomial_of_initial_window
#print axioms BCIKS20.CellPencilJohnson.SYZ16.gammaGenuineTailPolynomial_of_corrected_representative
#print axioms BCIKS20.CellPencilJohnson.SYZ16.branch_field_gap_of_graded_disc_tail
