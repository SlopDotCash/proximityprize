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

`MatchingPoint x₀ R H hHyp Bcoeff t z root` bundles the power-series-level Hensel data at the
matching point `z`:

* `f : (F⟦X⟧)[Y]` — the matching polynomial `f_z` (the §5 specialization `R(X, ·, Z)` recentred at
  the matching coordinate `x₀`);
* `aβ`, `aP : F⟦X⟧` — the specialization `π_z(γ)` of `betaRec … t`, and the proximate root `P_z`
  (ingredient B);
* `a₀ : F⟦X⟧` — the common degree-0 simple approximation `α₀ mod (X−x₀)`;
* `haβ_root`, `haP_root` — both are roots of `f`;
* `haβ_cong`, `haP_cong` — both reduce mod `(X−x₀)` to `a₀`;
* `hderiv` — separability of `R`: `f'(a₀)` is a unit;
* `coeffExtract` — the residual `(X−x₀)^t` coefficient extraction
  `aβ = aP → (π_z z root) (betaRec … t) = 0`.

The first nine fields (`f`, `aβ`, `aP`, `a₀`, the two `IsRoot`, the two `(X−x₀)`-congruences, the
unit-derivative) are the **genuine §5 root geometry at `z`**: the GS factor `H` specialized at `z`
carries the decoded root `P_z`, and the matching polynomial's root structure + separability
(from `Hypotheses`) supply exactly the four congruence/root facts and the unit-derivative that
Hensel uniqueness (`hensel_root_unique`, `HenselUniqueness.lean`) consumes.  Per the brick spec we
**isolate these as the smallest explicit per-point hypotheses** (they are *not* the goal — the goal
is the bundled `MatchingPoint`; these are the per-`z` root-membership / congruence / separability
facts the §5 decoder provides, in the very shape `hensel_root_unique` takes, never a `sorry`).

The tenth field, `coeffExtract`, is **discharged in tree**: it is produced by
`BetaMatchingVanishes.MatchingPoint.mk_coeffExtract` (`CoeffExtract.lean`) from the strictly smaller
π_z-specialized bridging facts

* `hαβ` — the π_z-specialized `α_t`-identity:
  `coeff t aβ = (π_z z root) (betaRec … t) / (w ^ a * x ^ e)`
  (the L12 relation `α_t = embedding(betaRec … t) / (W^{t+1} ξ^{e_t})`, π_z-imaged);
* `haP_coeff` — the proximate root reads zero at index `t`: `coeff t aP = 0`;
* `hw`, `hx` — `w = π_z(W) ≠ 0`, `x = π_z(ξ) ≠ 0`.

Reading off the `(X−x₀)^t` coefficient of the Hensel equality `aβ = aP` (App-A §5.2.6 + the L12
identity) yields the scalar vanishing — this is pure coefficient extraction + field algebra, and it
is the only field reconstructed from in-tree facts rather than assumed.

## What this file delivers

* `mkMatchingPoint` — the constructor: from the genuine §5 per-`z` Hensel geometry (the nine
  isolated root/congruence/derivative facts) together with the four π_z-specialized bridging facts
  for `coeffExtract`, it produces a
  `BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root`.  The `coeffExtract` field
  is filled by `MatchingPoint.mk_coeffExtract` (in-tree); the other nine are
  the isolated explicit inputs.
* `mkMatchingPoint_pi_z_eq_zero` — sanity: the constructed bundle fires
  `MatchingPoint.pi_z_eq_zero`, giving `(π_z z root) (betaRec … t) = 0`.
* `mpFin_of_pointwise` — packaging into exactly the `mpFin`-field shape: a pointwise/finite-range
  family of the per-`z` data assembles into
  `∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint …`.

The genuine, irreducible per-`z` datum is isolated as the smallest explicit hypotheses (the §5
root-membership/congruence/separability geometry — *not* the goal); everything mechanically
derivable (`coeffExtract`) is discharged in tree.

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

* the §5 root geometry at `z` — `f`, `aβ`, `aP`, `a₀`, the two `IsRoot` facts, the two
  `(X−x₀)`-congruences, and the unit-derivative (these are the isolated explicit per-`z`
  hypotheses, exactly the inputs of `hensel_root_unique`); and
* the four π_z-specialized bridging facts `hαβ`/`haP_coeff`/`hw`/`hx`, from which the residual
  `coeffExtract` field is discharged **in tree** by `MatchingPoint.mk_coeffExtract`.

Only `coeffExtract` is reconstructed from in-tree facts; the rest are the genuine isolated §5 data.
-/

/-- **The `MatchingPoint` constructor.**

From the genuine §5 per-`z` Hensel geometry (the matching polynomial `f`, the two roots `aβ`, `aP`,
the approximation `a₀`, the root/congruence/unit facts — the isolated smallest explicit inputs,
exactly what `hensel_root_unique` consumes) together with the π_z-specialized bridging facts
(`hαβ`/`haP_coeff`/`hw`/`hx`), produce a `BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z
root`.

The `coeffExtract` field is filled in tree via `BetaMatchingVanishes.MatchingPoint.mk_coeffExtract`
(`CoeffExtract.lean`); every other field is one of the isolated explicit §5 inputs. -/
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
  -- the only field reconstructed from in-tree facts: the `(X−x₀)^t` coefficient extraction.
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

Given a pointwise producer — a function returning, for every `(t, z)` in the finite range, the
genuine §5 per-point Hensel datum — we assemble exactly that family.  The pointwise producer is the
honest §5 / L13 deliverable (the decoder yields the per-`z` root geometry at each tail index); this
lemma is the trivial currying that drops it into the bundle field. -/

namespace MpProducer

variable {F : Type} [Field F]
variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-- **Assemble the `mpFin` family from a pointwise producer.**  If for every tail index `t` in the
counting range `k ≤ t ≤ T` and every matching point `z ∈ matchingSet` the §5 geometry supplies a
`MatchingPoint x₀ R H hHyp Bcoeff t z (root z)` (the pointwise producer `point`), then the
finite-range family in the exact shape of `Section5StrictDataFin.mpFin` holds. -/
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
