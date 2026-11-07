/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BetaRecursion
import ArkLib.ToMathlib.IngredientCBridge
import ArkLib.ToMathlib.HenselUniqueness

/-!
# `betaRec` and `MatchingVanishes` via the abstract `MatchingPoint` interface (brick L12 → L14)

This file connects the **β-recursion** of brick L7 (`ArkLib.betaRec`, the genuine BCIKS20 Appendix
A.4 (A.1) Hensel-lift numerator recursion) to the **ingredient-C converse bridge** property of brick
L14 (`ArkLib.IngredientC.MatchingVanishes`) through an abstract per-point interface
(`MatchingPoint`).  It does **not** prove that `betaRec` satisfies `MatchingVanishes`: the
per-point interface is logically equivalent to that conclusion (see "What this file delivers").

## The goal (L12/L14 keystone)

`MatchingVanishes matchingSet root β` (from `IngredientCBridge.lean`) is the per-point requirement
```
MatchingVanishes matchingSet root β  :=  ∀ z ∈ matchingSet, π_z z (root z) β = 0
```
i.e. for every geometric matching point `z`, the rational specialization `π_z` of `β` vanishes.
Once
this holds for `β := betaRec … t` with a matching set larger than the L9 weight bound `Λ·d`, brick
L14 (`embedding_eq_zero_of_matchingSet_large`) fires and we get `embedding(betaRec … t) = 0`, which
is the engine of Claims 5.8–5.11.

## How `betaRec`'s specialization is meant to vanish (App-A §5.2.6, the intended argument)

For a fixed matching point `z` the §5 geometry produces, over the power-series ring `F⟦X⟧` (centred
at
the matching coordinate `x₀`), a *matching polynomial* `f_z` (the specialization `R(X, ·, Z)`) and a
*proximate root* power series `P_z` (the GS-factor approximate root, ingredient B).  The Hensel-lift
coefficients `α_t` assemble into the power series `γ`, whose specialization `π_z(γ)` is **another
root** of `f_z`.  Both `P_z` and `π_z(γ)` reduce mod `(X−x₀)` to the common degree-0 simple
approximation `a₀` (`α₀`), at which `f_z'(a₀)` is a unit (separability of `R`).  Hensel uniqueness
(`hensel_root_unique`, brick L15, exposed by L14 as `specialization_eq_proximate_root_of_hensel`)
therefore forces
```
π_z(γ)  =  P_z      (the equality "π_z(γ) = P_z" of App-A §5.2.6).
```
Reading off the `(X−x₀)^t` coefficient gives `π_z(α_t) = 0`, hence — via the L12 identity
`α_t = embedding(β_rec … t) / (W^{t+1} ξ^{e_t})` and `π_z(W), π_z(ξ) ≠ 0` — `π_z(β_rec … t) = 0`.

## What this file delivers — and what it does not

The intended argument has two substantive steps: (i) the power-series **root equality**
`π_z(γ) = P_z` (an instance of `hensel_root_unique`), and (ii) the `(X−x₀)^t` **coefficient
extraction** carrying that equality down to the scalar fact `π_z z (root z) (betaRec … t) = 0`.
Neither step is carried out here for the actual objects.  `MatchingPoint` (below) is an
**abstract interface**: its data fields `f`, `aβ`, `aP`, `a₀` are arbitrary, and no field ties them
to `R`, to the β-recursion, to the place `z`/`root`, or to a decoded polynomial.  The only link to
`betaRec` is the field `coeffExtract : aβ = aP → π_z z root (betaRec … t) = 0`.

Consequently **a `MatchingPoint … t z root` exists iff `π_z z root (betaRec … t) = 0`**
(`MatchingPoint.nonempty_iff_pi_z_eq_zero`).  One direction is `MatchingPoint.pi_z_eq_zero`;
conversely `MatchingPoint.ofPiZEqZero` builds a bundle from the conclusion alone out of dummy data
(`f := Polynomial.X`, `aβ = aP = a₀ := 0`, and a `coeffExtract` that ignores its argument).
Likewise a section of bundles over `matchingSet` is equivalent to
`MatchingVanishes matchingSet root (betaRec … t)` itself (`betaRec_matchingVanishes_iff`).  So the
remaining obligation is exactly that scalar vanishing: an abstract `MatchingPoint` producer is
neither easier than proving it nor evidence that the analytic production has been localized or
solved.  Mathematical content enters only through a proof of the vanishing itself or through
constructors that pin the fields to the actual objects — e.g. `matchingPoint_of_localSeries`
(`MatchingPointFromLocalSeries.lean`), which fixes `f` to the specialized surface and `aβ` to the
constructed local series and derives the coefficient reading from a proved identity — and such
constructors must be judged on their own remaining inputs.  The generic Hensel uniqueness used
here (`hensel_root_unique`, `HenselUniqueness.lean`, exposed as
`IngredientC.specialization_eq_proximate_root_of_hensel`) is an independent, reusable result and
does not depend on this interface.

* `MatchingPoint t z` — the abstract per-point interface: a polynomial `f` and power series `aβ`,
  `aP`, `a₀` (intended readings, none enforced: the matching polynomial `f_z`, the specialization
  of the Hensel series, the proximate root `P_z`, the common approximation `α₀`), the two `IsRoot`
  and two congruence facts and the unit-derivative fact (the hypotheses of `hensel_root_unique`),
  and the field `coeffExtract`.
* `MatchingPoint.pi_z_eq_zero` — the per-point conclusion `π_z z root (betaRec … t) = 0`, obtained
  by firing `hensel_root_unique` (`aβ = aP`) and feeding the equality to `coeffExtract`.
* `MatchingPoint.ofPiZEqZero` / `MatchingPoint.nonempty_iff_pi_z_eq_zero` — the converse
  construction and the resulting interface equivalence.
* `betaRec_matchingVanishes` — a section `mp : ∀ z ∈ matchingSet, MatchingPoint …` yields
  `MatchingVanishes matchingSet root (betaRec … t)`; `betaRec_matchingVanishes_iff` records that
  the two are equivalent, so this is a repackaging, not a reduction to weaker hypotheses.
* `betaRec_embedding_eq_zero_of_matchingSet_large` — the L14-composed corollary: with the per-point
  bundles *and* the L9 weight bound (`#matchingSet > Λ·d`), `embedding(betaRec … t) = 0`.  Its
  per-point input is equivalent to `MatchingVanishes … (betaRec … t)`, so this is Claim 5.8's
  conclusion *conditional on* that vanishing, not a discharge of it.

Everything is kernel-clean (`#print axioms` at the bottom; only `propext / Classical.choice /
Quot.sound`).
-/

set_option linter.style.longLine false


open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace BetaMatchingVanishes

variable {F : Type} [Field F]

/-! ### The per-point matching interface

For a fixed point `z` (carrying its rational-root section `root`) and a fixed recursion index `t`,
`MatchingPoint` has the *shape* of what the §5 geometry + the recursion are meant to provide at
that point, in the form Hensel uniqueness consumes.  The descriptions below are the **intended
readings**; none of them is enforced by the structure:

* `f` — intended: the matching polynomial `f_z : (F⟦X⟧)[Y]` (the §5 specialization `R(X, ·, Z)`
  recentred at the matching coordinate);
* `aβ` — intended: the power-series specialization of the Hensel series at `z` (whose
  `(X−x₀)^t` coefficient is `π_z(α_t)`-related), and `aP` — intended: the proximate-root power
  series `P_z`;
* the four congruence/root facts and the unit-derivative (separability) fact — exactly the
  hypotheses of `hensel_root_unique`, but about the supplied series, whatever they are;
* `coeffExtract` — the only field mentioning `betaRec`: an implication
  `aβ = aP → π_z z root (betaRec … t) = 0`.  Since the Hensel fields force `aβ = aP`, this field
  must in effect already contain the conclusion, and with `aβ`, `aP` unconstrained it can simply
  *be* the conclusion (`MatchingPoint.ofPiZEqZero`).  In the intended instantiation it is the
  `(X−x₀)^t` coefficient extraction (App-A §5.2.6 + the L12 identity), which
  `MatchingPoint.mk_coeffExtract` (`CoeffExtract.lean`) derives from a coefficient-reading
  identity `hαβ` — itself an unconstrained assumption about `betaRec` unless `aβ` is pinned to the
  actual series.
-/

/-- **Abstract per-point matching interface** for `betaRec … t` at the point `z`.

Bundles power-series-level Hensel data (a polynomial `f`, two roots `aβ`, `aP`, an approximation
`a₀`, the root/congruence/unit facts) together with the implication `coeffExtract` from the Hensel
equality `aβ = aP` to the scalar conclusion `π_z z root (betaRec … t) = 0`.

The data fields are **unconstrained**: nothing ties `f`, `aβ`, `aP`, `a₀` to `R`, the β-recursion,
`z`/`root` or a decoded polynomial, so the bundle exists iff its conclusion holds
(`MatchingPoint.nonempty_iff_pi_z_eq_zero`, via the dummy-data constructor
`MatchingPoint.ofPiZEqZero`).  The field docstrings give the *intended* readings only. -/
structure MatchingPoint (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    (z : F) (root : rationalRoot (H_tilde' H) z) where
  /-- Intended reading: the matching polynomial `f_z : (F⟦X⟧)[Y]` (the §5 specialization
  `R(X, ·, Z)`).  Unconstrained here: any polynomial is accepted. -/
  f : Polynomial (PowerSeries F)
  /-- Intended reading: the power-series specialization `π_z(γ)` at `z` of the Hensel series
  attached to `betaRec`.  Unconstrained here. -/
  aβ : PowerSeries F
  /-- Intended reading: the proximate-root power series `P_z` (ingredient B).  Unconstrained
  here. -/
  aP : PowerSeries F
  /-- Intended reading: the common degree-0 simple approximation `a₀ = α₀` mod `(X−x₀)`.
  Unconstrained here. -/
  a₀ : PowerSeries F
  /-- `aβ` is a root of `f` (intended: `π_z(γ)` is a root of the matching polynomial). -/
  haβ_root : f.IsRoot aβ
  /-- `aP` is a root of `f` (intended: the proximate root `P_z` is a root of the matching
  polynomial). -/
  haP_root : f.IsRoot aP
  /-- `aβ` reduces mod `(X−x₀)` to the approximation `a₀`. -/
  haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- `aP` reduces mod `(X−x₀)` to the approximation `a₀`. -/
  haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- The simple-root derivative `f'(a₀)` is a unit (intended source: separability of `R`). -/
  hderiv : IsUnit (f.derivative.eval a₀)
  /-- **The only field mentioning `betaRec`.**  Once Hensel uniqueness pins `aβ = aP`, this
  implication yields the scalar vanishing.  Intended instantiation: the `(X−x₀)^t`-coefficient
  reading (App-A §5.2.6 + the L12 identity `α_t = embedding(β_rec … t) / (W^{t+1} ξ^{e_t})`, using
  `π_z(W), π_z(ξ) ≠ 0`).  Because `aβ`, `aP` are unconstrained, this field can also be the bare
  conclusion (`MatchingPoint.ofPiZEqZero`); it is the target supplied as a hypothesis, not an
  independent construction of the coefficient-extraction fact. -/
  coeffExtract : aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0

namespace MatchingPoint

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {t : ℕ}
    {z : F} {root : rationalRoot (H_tilde' H) z}

/-- **Hensel uniqueness for the bundled data.**  The two supplied roots agree: `mp.aβ = mp.aP`,
directly from `hensel_root_unique` (exposed by L14 as `specialization_eq_proximate_root_of_hensel`):
both are roots of `f`, both congruent mod `(X−x₀)` to the approximation `a₀` at which `f'(a₀)` is a
unit.  Under the intended reading of the fields this is the equality "π_z(γ) = P_z" of
App-A §5.2.6; for an abstract bundle it is only an equality of the two supplied series. -/
theorem specialization_eq_proximate_root
    (mp : MatchingPoint x₀ R H hHyp Bcoeff t z root) :
    mp.aβ = mp.aP :=
  ArkLib.IngredientC.specialization_eq_proximate_root_of_hensel
    mp.f mp.haβ_root mp.haP_root mp.haβ_cong mp.haP_cong mp.hderiv

/-- **The per-point conclusion.**  At the point `z`, the specialization `π_z` of `betaRec … t`
vanishes.  Routes Hensel uniqueness (`specialization_eq_proximate_root`, i.e.
`hensel_root_unique`) into the field `coeffExtract`.  With `ofPiZEqZero` this shows that the
bundle is equivalent to this conclusion (`nonempty_iff_pi_z_eq_zero`). -/
theorem pi_z_eq_zero
    (mp : MatchingPoint x₀ R H hHyp Bcoeff t z root) :
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  mp.coeffExtract mp.specialization_eq_proximate_root

/-- **Converse construction: the bundle from its conclusion alone.**  The data fields of
`MatchingPoint` are unconstrained, so the scalar vanishing suffices to build one from dummy data:
`f := Polynomial.X` and `aβ = aP = a₀ := 0` satisfy every root, congruence and unit-derivative
field, and `coeffExtract` ignores its argument and returns the supplied conclusion.  Hence an
abstract `MatchingPoint` is exactly as strong as its target and is no evidence of analytic
production. -/
noncomputable def ofPiZEqZero (h : (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0) :
    MatchingPoint x₀ R H hHyp Bcoeff t z root where
  f := Polynomial.X
  aβ := 0
  aP := 0
  a₀ := 0
  haβ_root := by simp
  haP_root := by simp
  haβ_cong := by simp
  haP_cong := by simp
  hderiv := by simp
  coeffExtract := fun _ => h

/-- **Interface equivalence.**  A `MatchingPoint … t z root` exists iff the scalar vanishing
`π_z z root (betaRec … t) = 0` holds: forward by `pi_z_eq_zero`, backward by `ofPiZEqZero`. -/
theorem nonempty_iff_pi_z_eq_zero :
    Nonempty (MatchingPoint x₀ R H hHyp Bcoeff t z root) ↔
      (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  ⟨fun ⟨mp⟩ => mp.pi_z_eq_zero, fun h => ⟨ofPiZEqZero h⟩⟩

end MatchingPoint

/-! ### From a section of bundles to `MatchingVanishes`

A per-point section `mp : ∀ z ∈ matchingSet, MatchingPoint …` (in the intended instantiation, the
§5 geometry's output point by point) yields the ingredient-C property
`MatchingVanishes matchingSet root (betaRec … t)`.  Each point is discharged by
`MatchingPoint.pi_z_eq_zero` (Hensel uniqueness + `coeffExtract`).  Because each bundle is
equivalent to its conclusion, the section is equivalent to `MatchingVanishes` itself
(`betaRec_matchingVanishes_iff`).
-/

/-- **L12 → L14 keystone (repackaging).**  Given a `MatchingPoint` at every point of
`matchingSet`, the recursion `betaRec … t` satisfies the ingredient-C property `MatchingVanishes`:
its specialization `π_z` vanishes at every point of `matchingSet`.

This is **not** a reduction of `MatchingVanishes (betaRec … t)` to weaker hypotheses: a section of
abstract bundles is equivalent to `MatchingVanishes` (`betaRec_matchingVanishes_iff`), so the
remaining obligation is the vanishing itself, to be established by a construction that ties the
bundle fields to the actual objects.  Combined with L9's weight bound, L14 then fires (see
`betaRec_embedding_eq_zero_of_matchingSet_large`). -/
theorem betaRec_matchingVanishes (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ z ∈ matchingSet, MatchingPoint x₀ R H hHyp Bcoeff t z (root z)) :
    ArkLib.IngredientC.MatchingVanishes matchingSet root (betaRec x₀ R H hHyp Bcoeff t) :=
  fun z hz => (mp z hz).pi_z_eq_zero

/-- **A section of bundles is equivalent to `MatchingVanishes`.**  By
`MatchingPoint.nonempty_iff_pi_z_eq_zero` pointwise, a `MatchingPoint` exists at every point of
`matchingSet` iff `MatchingVanishes matchingSet root (betaRec … t)` holds, so
`betaRec_matchingVanishes` does not weaken the obligation. -/
theorem betaRec_matchingVanishes_iff (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z) :
    (∀ z ∈ matchingSet, Nonempty (MatchingPoint x₀ R H hHyp Bcoeff t z (root z))) ↔
      ArkLib.IngredientC.MatchingVanishes matchingSet root (betaRec x₀ R H hHyp Bcoeff t) :=
  ⟨fun h z hz => MatchingPoint.nonempty_iff_pi_z_eq_zero.mp (h z hz),
    fun h z hz => ⟨MatchingPoint.ofPiZEqZero (h z hz)⟩⟩

/-! ### The L14-composed corollary (Claim 5.8's conclusion for `betaRec`, conditional)

With the per-point bundles *and* the L9 weight bound `#matchingSet > Λ·d`, the verified L14
deliverable `IngredientC.embedding_eq_zero_of_matchingSet_large` fires on `betaRec … t`, giving
`embedding(betaRec … t) = 0` — the engine of Claims 5.8–5.11.  The per-point input is equivalent
to `MatchingVanishes … (betaRec … t)`, which therefore remains an open input. -/

/-- **Claim 5.8's `Lemma_A_1` conclusion for `betaRec`, conditional on the per-point bundles.**

Given `MatchingPoint` bundles at every point of `matchingSet` and the L9 weight bound
`#matchingSet > weight_Λ_over_𝒪 (betaRec … t) D * H.natDegree`, we conclude
`embeddingOf𝒪Into𝕃 H (betaRec … t) = 0`.

This composes `betaRec_matchingVanishes` with the verified converse-bridge deliverable
`IngredientC.embedding_eq_zero_of_matchingSet_large` (which routes through `Lemma_A_1`'s counting
step).  It is the `embedding(β R t) = 0` conclusion that drives Claims 5.8–5.11, **conditional on**
its inputs: the per-point bundles (equivalent to `MatchingVanishes … (betaRec … t)`, see
`betaRec_matchingVanishes_iff`) and the `Λ·d` largeness.  It does not discharge either input. -/
theorem betaRec_embedding_eq_zero_of_matchingSet_large (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ z ∈ matchingSet, MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  ArkLib.IngredientC.embedding_eq_zero_of_matchingSet_large hH
    (betaRec x₀ R H hHyp Bcoeff t) D hD
    (betaRec_matchingVanishes x₀ R H hHyp Bcoeff t mp) hcard

end BetaMatchingVanishes

end ArkLib

-- Axiom audit: every claimed-done declaration must rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.BetaMatchingVanishes.MatchingPoint.specialization_eq_proximate_root
#print axioms ArkLib.BetaMatchingVanishes.MatchingPoint.pi_z_eq_zero
#print axioms ArkLib.BetaMatchingVanishes.MatchingPoint.ofPiZEqZero
#print axioms ArkLib.BetaMatchingVanishes.MatchingPoint.nonempty_iff_pi_z_eq_zero
#print axioms ArkLib.BetaMatchingVanishes.betaRec_matchingVanishes
#print axioms ArkLib.BetaMatchingVanishes.betaRec_matchingVanishes_iff
#print axioms ArkLib.BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large
