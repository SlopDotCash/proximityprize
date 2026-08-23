/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MpProducer
import ArkLib.ToMathlib.HenselDatumProducer
import ArkLib.ToMathlib.MatchingExtractor

/-!
# Matching Geometry and Finite-Range Pointwise Supply

This module formalizes the construction of the matching point family (`mpFin`) for the
finite-range proximity gap bundle `BetaCurveInputFin`. We extract the per-place geometry
independent of the truncation index $t$, showing that a single coordinate place geometry
serves every index in the range $[k, T]$.

## Mathematical Context

Let $F$ be a field and $H \in F[X][Y]$ be an irreducible polynomial defining the algebraic curve.
For each matching place $z \in F$ and specialization root, the local geometry of the Hensel lift
is captured by the `PlaceGeometry` structure. This packages:
1. The matching polynomial $f_z(Y) \in F[[X]][Y]$.
2. The specialized power series $a_\beta = \pi_z(\gamma)$ and the proximate root $a_P = P_z$.
3. The common root approximation $a_0 = \alpha_0$.
4. Pointwise root memberships and congruences modulo $X$.
5. Separability of the matching polynomial.

We show that:
* Under the separability condition, the derivative $f_z'(a_0)$ is a unit. This discharges
  the unit-derivative obligation of the matching point family from the algebraic properties
  of the curve.
* A single place geometry configuration can be reused at every index $t \in [k, T]$ in the
  finite range, requiring only the pointwise specialized coefficient readings (`BridgeData`)
  to vary with $t$.
* If the root membership is supplied as factor divisibility $(Y - a_P) \mid f_z$ (e.g. from
  the Guruswami-Sudan factor), it is converted to the root membership condition.

## Key Formalizations
* `PlaceGeometry`: Packages the $t$-uniform coordinate place geometry.
* `BridgeData`: Packages the specialized coefficient readings at the truncation index $t$
  and place $z$.
* `mkMatchingPoint_of_graph_vanishing`: Constructs the matching point instance from place
  geometry and bridging data.
* `mpFin_of_close_word`: Threads the place geometry family over the finite counting range
  $[k, T]$.
* `placeGeometry_of_matchingDvd`: Constructor for `PlaceGeometry` when root membership is
  supplied as factor divisibility.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon
  Codes*, eprint 2020.
-/

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open PowerSeries

namespace ArkLib

namespace MpFinSupply

variable {F : Type} [Field F]

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-! ### Coordinate Place Geometry -/

/-- Packages the $t$-uniform matching-place geometry at a single coordinate $z$. -/
structure PlaceGeometry (z : F) : Type where
  /-- The matching polynomial $f_z \in (F[[X]])[Y]$. -/
  f : Polynomial (PowerSeries F)
  /-- The power-series specialisation $a_\beta = \pi_z(\gamma)$ at $z$. -/
  aβ : PowerSeries F
  /-- The proximate-root power series $a_P = P_z$. -/
  aP : PowerSeries F
  /-- The common degree-0 simple approximation $a_0 = \alpha_0 \pmod X$. -/
  a₀ : PowerSeries F
  /-- Proof that $a_\beta$ is a root of $f$. -/
  haβ_root : f.IsRoot aβ
  /-- Proof that $a_P$ is a root of $f$. -/
  haP_root : f.IsRoot aP
  /-- Proof that $a_\beta \equiv a_0 \pmod X$. -/
  haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- Proof that $a_P \equiv a_0 \pmod X$. -/
  haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- Proof that $f$ is separable. -/
  hsep : f.Separable

/-- Derives the unit derivative property at the approximate root from the separability condition. -/
theorem PlaceGeometry.hderiv {z : F} (g : PlaceGeometry (F := F) z) :
    IsUnit (g.f.derivative.eval g.a₀) :=
  HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr
    g.f g.hsep g.haβ_root g.haβ_cong

/-! ### Pointwise Specialized Bridging Facts -/

/-- Packages the specialized coefficient readings at the truncation index $t$ and coordinate $z$. -/
structure BridgeData (t : ℕ) (z : F) (root : rationalRoot (H_tilde' H) z)
    (aβ aP : PowerSeries F) : Type where
  /-- The $\pi_z$-specialised $\alpha_t$-identity exponents. -/
  w : F
  /-- The $\pi_z$-specialised $\alpha_t$-identity exponent base for $\xi$. -/
  x : F
  /-- The $W$-power exponent ($a = t + 1$). -/
  a : ℕ
  /-- The $\xi$-power exponent ($e = e_t$). -/
  e : ℕ
  /-- The $\pi_z$-specialised $\alpha_t$-identity coefficient reading. -/
  hαβ : PowerSeries.coeff t aβ =
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e)
  /-- Proof that $w = \pi_z(W) \neq 0$. -/
  hw : w ≠ 0
  /-- Proof that $x = \pi_z(\xi) \neq 0$. -/
  hx : x ≠ 0
  /-- Proof that the proximate root vanishes at index $t$. -/
  haP_coeff : PowerSeries.coeff t aP = 0

/-! ### Pointwise Matching Point Constructor -/

/-- Constructs a `MatchingPoint` instance by combining place geometry and bridging data. -/
def mkMatchingPoint_of_graph_vanishing {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    (g : PlaceGeometry (F := F) z)
    (bd : BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root g.aβ g.aP) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root :=
  MpProducer.mkMatchingPoint
    (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff) (t := t) (z := z) (root := root)
    g.f g.aβ g.aP g.a₀ g.haβ_root g.haP_root g.haβ_cong g.haP_cong g.hderiv
    bd.hαβ bd.hw bd.hx bd.haP_coeff

/-- Firing Hensel uniqueness and coefficient extraction yields the matching vanishing condition. -/
theorem mkMatchingPoint_of_graph_vanishing_pi_z_eq_zero
    {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    (g : PlaceGeometry (F := F) z)
    (bd : BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root g.aβ g.aP) :
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  (mkMatchingPoint_of_graph_vanishing g bd).pi_z_eq_zero

/-! ### Finite-Range Matching Point Assembly -/

/-- Constructs the finite-range matching point family from place geometry and bridging data
producers. -/
def mpFin_of_close_word {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (geom : (z : F) → z ∈ matchingSet → PlaceGeometry (F := F) z)
    (bridge : ∀ t, k ≤ t → t ≤ T → ∀ z, (hz : z ∈ matchingSet) →
      BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        t z (root z) (geom z hz).aβ (geom z hz).aP) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  fun t hkt htT z hz =>
    mkMatchingPoint_of_graph_vanishing (geom z hz) (bridge t hkt htT z hz)

/-! ### Root Membership from Factor Divisibility -/

/-- Constructs a `PlaceGeometry` instance when the root condition is supplied as a factor
divisibility. -/
def placeGeometry_of_matchingDvd {z : F}
    (f : Polynomial (PowerSeries F)) (aβ aP a₀ : PowerSeries F)
    (haβ_root : f.IsRoot aβ)
    (haP_dvd : (Polynomial.X - Polynomial.C aP) ∣ f)
    (haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : f.Separable) :
    PlaceGeometry (F := F) z where
  f := f
  aβ := aβ
  aP := aP
  a₀ := a₀
  haβ_root := haβ_root
  haP_root := (Polynomial.dvd_iff_isRoot).mp haP_dvd
  haβ_cong := haβ_cong
  haP_cong := haP_cong
  hsep := hsep

/-- Constructs the finite-range matching point family when root conditions are supplied as
factor divisibility statements. -/
def mpFin_of_graph_vanishing_dvd {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ aP a₀ : (z : F) → PowerSeries F)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_dvd : ∀ z ∈ matchingSet, (Polynomial.X - Polynomial.C (aP z)) ∣ f z)
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet, aP z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (bridge : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet →
      BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        t z (root z) (aβ z) (aP z)) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  mpFin_of_close_word
    (geom := fun z hz =>
      placeGeometry_of_matchingDvd (z := z) (f z) (aβ z) (aP z) (a₀ z)
        (haβ_root z hz) (haP_dvd z hz) (haβ_cong z hz) (haP_cong z hz) (hsep z hz))
    (bridge := bridge)

end MpFinSupply

end ArkLib

/-! ## Axiom audit — every declaration here must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.MpFinSupply.PlaceGeometry.hderiv
#print axioms ArkLib.MpFinSupply.mkMatchingPoint_of_graph_vanishing
#print axioms ArkLib.MpFinSupply.mkMatchingPoint_of_graph_vanishing_pi_z_eq_zero
#print axioms ArkLib.MpFinSupply.mpFin_of_close_word
#print axioms ArkLib.MpFinSupply.placeGeometry_of_matchingDvd
#print axioms ArkLib.MpFinSupply.mpFin_of_graph_vanishing_dvd
