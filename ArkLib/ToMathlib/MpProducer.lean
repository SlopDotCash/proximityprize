/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.CoeffExtract

/-!
# Producing the per-point `MatchingPoint` datum — the `mpFin` field of `Section5StrictDataFin`

The corrected §5 bundle `HcardDischarge.Section5StrictDataFin`
(`ArkLib/ToMathlib/HcardDischarge.lean`) carries, over the *finite* counting range `k ≤ t ≤ T`,
the per-point matching datum

```
mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
  BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
```

i.e. for each tail index `t` in the counting range and each geometric matching point
`z ∈ matchingSet`, a `BetaMatchingVanishes.MatchingPoint` bundle.  This file provides the
**constructor** for that bundle.

## What `MatchingPoint` needs (read `BetaMatchingVanishes.lean`)

`MatchingPoint x₀ R H hHyp Bcoeff t z root` bundles power-series-level Hensel data at the
point `z` (intended readings in parentheses; none is enforced by the structure):

* `f : (F⟦X⟧)[Y]` (the matching polynomial `f_z`, the §5 specialization `R(X, ·, Z)` recentred at
  the matching coordinate `x₀`);
* `aβ`, `aP : F⟦X⟧` (the specialization `π_z(γ)` of the Hensel series, and the proximate root
  `P_z` of ingredient B);
* `a₀ : F⟦X⟧` (the common degree-0 simple approximation `α₀ mod (X−x₀)`);
* `haβ_root`, `haP_root` — both are roots of `f`;
* `haβ_cong`, `haP_cong` — both reduce mod `(X−x₀)` to `a₀`;
* `hderiv` — `f'(a₀)` is a unit (intended source: separability of `R`);
* `coeffExtract` — the implication `aβ = aP → (π_z z root) (betaRec … t) = 0`.

In the intended instantiation the first nine fields (`f`, `aβ`, `aP`, `a₀`, the two `IsRoot`, the
two `(X−x₀)`-congruences, the unit-derivative) are the §5 root geometry at `z`: the GS factor `H`
specialized at `z` carries the decoded root `P_z`, and the matching polynomial's root structure +
separability supply the four congruence/root facts and the unit-derivative that Hensel uniqueness
(`hensel_root_unique`, `HenselUniqueness.lean`) consumes.  **`mkMatchingPoint` does not enforce
that reading**: it accepts arbitrary `f`, `aβ`, `aP`, `a₀` with the stated properties, and nothing
in its signature, nor in `mpFin_of_pointwise`, links these series to `R`, to the decoder or to the
β-series.  They are therefore not "the genuine irreducible geometric obligations" in any checked
sense; they are interface inputs.

The tenth field, `coeffExtract`, is filled by `BetaMatchingVanishes.MatchingPoint.mk_coeffExtract`
(`CoeffExtract.lean`) from the π_z-specialized bridging facts

* `hαβ` — the coefficient reading `coeff t aβ = (π_z z root) (betaRec … t) / (w ^ a * x ^ e)`
  (intended: the L12 relation `α_t = embedding(betaRec … t) / (W^{t+1} ξ^{e_t})`, π_z-imaged);
* `haP_coeff` — `coeff t aP = 0`;
* `hw`, `hx` — `w ≠ 0`, `x ≠ 0` (intended: `w = π_z(W)`, `x = π_z(ξ)`).

Reading off the `(X−x₀)^t` coefficient of the Hensel equality `aβ = aP` yields the scalar
vanishing; that implication is pure coefficient extraction + field algebra and holds
unconditionally.  But with `aβ` unconstrained, `hαβ` is itself an assumption about `betaRec`, and
the inputs of `mkMatchingPoint` are **jointly equivalent to its conclusion**: if
`(π_z z root) (betaRec … t) = 0`, then `f := Polynomial.X`, `aβ = aP = a₀ := 0`, `w = x := 1`,
`a = e := 0` satisfy every input (`hαβ` reads `0 = 0 / 1`).  This is the same interface equivalence
as `BetaMatchingVanishes.MatchingPoint.nonempty_iff_pi_z_eq_zero`; the constructor packages the
abstract bundle and does not independently produce the claimed geometry.  Geometry enters only
through constructors that pin `f`, `aβ` and the bridge data to the actual objects, e.g.
`matchingPoint_of_localSeries` (`MatchingPointFromLocalSeries.lean`), whose remaining inputs must be
evaluated separately.

## What this file delivers

* `mkMatchingPoint` — the constructor: from the nine root/congruence/derivative inputs together
  with the four π_z-specialized bridging facts for `coeffExtract`, it produces a
  `BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root`.  The `coeffExtract` field
  is filled by `MatchingPoint.mk_coeffExtract`; the other nine are explicit (unconstrained) inputs.
* `mkMatchingPoint_pi_z_eq_zero` — sanity: the constructed bundle fires
  `MatchingPoint.pi_z_eq_zero`, giving `(π_z z root) (betaRec … t) = 0`.
* `mpFin_of_pointwise` — packaging into exactly the `mpFin`-field shape: a pointwise/finite-range
  family of the per-`z` bundles assembles into
  `∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint …` (the identity function).

The per-`z` inputs are explicit hypotheses; producing them for the actual decoder and β-series
remains open here, and the abstract inputs are as strong as the vanishing they yield.

Everything is kernel-clean (`#print axioms` at the bottom; only
`propext / Classical.choice / Quot.sound`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, Appendix A.2 / A.4 (the `W`-power numerator recursion (A.1), §5.2.6 matching geometry).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open PowerSeries

namespace ArkLib

namespace MpProducer

variable {F : Type} [Field F]

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {t : ℕ}
    {z : F} {root : rationalRoot (H_tilde' H) z}

/-! ## The per-point constructor

`mkMatchingPoint` assembles a `BetaMatchingVanishes.MatchingPoint` from:

* the Hensel inputs `f`, `aβ`, `aP`, `a₀`, the two `IsRoot` facts, the two `(X−x₀)`-congruences,
  and the unit-derivative (explicit per-`z` hypotheses, exactly the inputs of
  `hensel_root_unique`; intended to be the §5 root geometry at `z`, but not tied to it); and
* the four π_z-specialized bridging facts `hαβ`/`haP_coeff`/`hw`/`hx`, from which the
  `coeffExtract` field is derived by `MatchingPoint.mk_coeffExtract`.

Only `coeffExtract` is reconstructed from other inputs; since `aβ` is unconstrained, `hαβ` carries
the `betaRec` content, and the inputs jointly are equivalent to the conclusion (see the module
docstring).
-/

/-- **The `MatchingPoint` constructor.**

From Hensel inputs (a polynomial `f`, two roots `aβ`, `aP`, an approximation `a₀`, the
root/congruence/unit facts — exactly what `hensel_root_unique` consumes, with no link to the actual
decoder or β-series) together with the π_z-specialized bridging facts (`hαβ`/`haP_coeff`/`hw`/`hx`),
produce a `BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root`.

The `coeffExtract` field is filled via `BetaMatchingVanishes.MatchingPoint.mk_coeffExtract`
(`CoeffExtract.lean`); every other field is one of the explicit inputs.  The inputs are satisfiable
exactly when `(π_z z root) (betaRec … t) = 0` (e.g. by `f := Polynomial.X`, all series `0`,
`w = x := 1`, `a = e := 0`), so this constructor is interface plumbing, not a producer of
geometry. -/
def mkMatchingPoint
    -- §5 root geometry at `z` (the isolated explicit per-point hypotheses):
    (f : Polynomial (PowerSeries F)) (aβ aP a₀ : PowerSeries F)
    (haβ_root : f.IsRoot aβ) (haP_root : f.IsRoot aP)
    (haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hderiv : IsUnit (f.derivative.eval a₀))
    -- π_z-specialized bridging facts (for the in-tree `coeffExtract` discharge):
    {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP_coeff : PowerSeries.coeff t aP = 0) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root where
  f := f
  aβ := aβ
  aP := aP
  a₀ := a₀
  haβ_root := haβ_root
  haP_root := haP_root
  haβ_cong := haβ_cong
  haP_cong := haP_cong
  hderiv := hderiv
  -- the only field reconstructed from other inputs: the `(X−x₀)^t` coefficient extraction.
  coeffExtract :=
    BetaMatchingVanishes.MatchingPoint.mk_coeffExtract hαβ hw hx haP_coeff

/-- **Sanity: the constructed bundle yields the per-point conclusion.**  Firing
`BetaMatchingVanishes.MatchingPoint.pi_z_eq_zero` on `mkMatchingPoint` (Hensel uniqueness +
the in-tree `coeffExtract`) gives the geometric matching vanishing
`(π_z z root)(betaRec … t) = 0`. -/
theorem mkMatchingPoint_pi_z_eq_zero
    (f : Polynomial (PowerSeries F)) (aβ aP a₀ : PowerSeries F)
    (haβ_root : f.IsRoot aβ) (haP_root : f.IsRoot aP)
    (haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hderiv : IsUnit (f.derivative.eval a₀))
    {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP_coeff : PowerSeries.coeff t aP = 0) :
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  (mkMatchingPoint f aβ aP a₀ haβ_root haP_root haβ_cong haP_cong hderiv
    hαβ hw hx haP_coeff).pi_z_eq_zero

end MpProducer

/-! ## Packaging into the `mpFin`-field shape

`Section5StrictDataFin.mpFin` is a *family*:
`∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint x₀ R H hHyp Bcoeff t z (root z)`.

Given a pointwise producer — a function returning, for every `(t, z)` in the finite range, a
per-point `MatchingPoint` bundle — we assemble exactly that family.  In the intended instantiation
the pointwise producer is the §5 / L13 deliverable (the decoder yields the per-`z` root geometry at
each tail index), but nothing here links the bundles to the decoder or the β-series: the lemma is
the identity function on the family, and each abstract bundle is equivalent to its per-point
vanishing (`BetaMatchingVanishes.MatchingPoint.nonempty_iff_pi_z_eq_zero`). -/

namespace MpProducer

variable {F : Type} [Field F]
variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-- **Assemble the `mpFin` family from a pointwise producer.**  If for every tail index `t` in the
counting range `k ≤ t ≤ T` and every matching point `z ∈ matchingSet` a
`MatchingPoint x₀ R H hHyp Bcoeff t z (root z)` is supplied (the pointwise producer `point`;
intended to come from the §5 geometry), then the finite-range family in the exact shape of
`Section5StrictDataFin.mpFin` holds.  This is the identity on the family; it adds no geometry. -/
def mpFin_of_pointwise
    {k T : ℕ} {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (point : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  point

end MpProducer

end ArkLib

/-! ## Axiom audit — every declaration here must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.MpProducer.mkMatchingPoint
#print axioms ArkLib.MpProducer.mkMatchingPoint_pi_z_eq_zero
#print axioms ArkLib.MpProducer.mpFin_of_pointwise
