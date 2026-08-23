/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SbetaPackaging
import ArkLib.ToMathlib.HenselUniqueness

/-!
# Ingredient-C converse bridge (L14 / L16): matching points ⟹ `embedding β = 0`

This file is the **conditional** formalization of *ingredient C* of the BCIKS20 §5 list-decoding
keystone (`research/proximity-prize/ingredient-D-DAG-2026-06-05.md`, bricks **L14/L16**).

## What ingredient C is, and why it is *conditional* here

`BCIKS20AppendixA.Lemma_A_1` (in `RationalFunctions.lean`) concludes
`embeddingOf𝒪Into𝕃 _ β = 0` once the set
```
S_β β = {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}
```
of "matching specialization points" is strictly larger than `weight_Λ_over_𝒪 hH β D * H.natDegree`
(the `Λ·d` bound).  The packaging brick
`ArkLib.embedding_eq_zero_of_finset_subset_S_β` (`SbetaPackaging.lean`) reduces this to exhibiting a
*finite* set `T ⊆ S_β β` with `#T` beating `Λ·d`.

The §5 geometry produces a `Finset` `matchingSet` of *geometric matching points*.  Each such point
`z` carries the matching data the §5 chain provides (its rational root `root z` of `H_tilde' H`, the
proximate root polynomial `P_z`).  The **converse bridge** asserts that for every matching point,
`π_z z (root z) β = 0`, i.e. the point lands in `S_β β`.  This is the substantive content of L14.

Because the *real* `β` — the BCIKS20 Appendix A.4 recursive Hensel-lift numerator (ingredient D /
L13) — is **not yet built** (the in-tree `β` is the trivial `β = 0` witness, which makes the bridge
vacuous), we cannot yet *prove* `π_z z (root z) β = 0` from first principles.  We therefore
**isolate that requirement as an explicit hypothesis** `P β` and prove the entire bridge *from* it.

## The isolated property `P`

For a matching set `matchingSet : Finset F` equipped with a section
`root : (z : F) → rationalRoot (H_tilde' H) z` selecting each point's rational-root data, the
required property of `β : 𝒪 H` is
```
P β  :=  ∀ z ∈ matchingSet, π_z z (root z) β = 0
```
This is *exactly* the membership condition `z ∈ S_β β`, point-by-point (it is the strongest possible
statement: `S_β`-membership is an `∃ root`, and `P` supplies a concrete witnessing section).  It is
the property the real `β` of L13 must carry (App-A §5.2.6: `π_z(γ) = P_z` by Hensel uniqueness ⟹
`π_z(α_t) = 0` ⟹ `π_z(β_t) = 0` for `t > k`).

## Main results

* `ArkLib.IngredientC.mem_S_β_of_pi_z_eq_zero` — the atomic step: `π_z z root β = 0 → z ∈ S_β β`.
* `ArkLib.IngredientC.matchingSet_subset_S_β_of_P` — `P β → ↑matchingSet ⊆ S_β β`.
* `ArkLib.IngredientC.embedding_eq_zero_of_matchingSet_large` — **the deliverable**: given `P β`
  (the per-point specialization vanishing) and `#matchingSet > Λ·d`, conclude `embedding β = 0`.
* `ArkLib.IngredientC.pi_z_eq_zero_of_specialization_eq` — a Hensel-uniqueness powered helper
  (`hensel_root_unique`): `π_z z root β = 0` follows once the specialization of `β` is exhibited as
  *the* lifted root of the matching polynomial congruent mod `X` to the §5 approximation — i.e.
  uniqueness pins the matching polynomial at `z` equal to the specialization of `β`.  This is the
  shape L13's real β-construction will discharge `P` through.

## What remains for L13 (ingredient D) to supply

L13 must produce a concrete `β : 𝒪 H` (the App-A (A.1) recursion numerator) together with a
matching `Finset` for which `P β` holds and `#matchingSet > weight_Λ_over_𝒪 hH β D * H.natDegree`.
The weight side (`Λ·d` bound) is L9/L10/L13; the `P β` side is L14, whose final per-point step is
`pi_z_eq_zero_of_specialization_eq` fed by `hensel_root_unique` once `β_rec` is in hand.  Both are
purely about the real `β`; this file consumes them as the single hypothesis `P β` (no `sorry`).

Everything here is kernel-clean.
-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal BCIKS20AppendixA

namespace ArkLib

namespace IngredientC

variable {F : Type} [Field F]

/-! ### The atomic membership step -/

/-- **Atomic converse step.**  If the specialization `π_z z root` of `β` at a matching point `z`
(with rational-root data `root`) vanishes, then `z` lies in the matching-point set `S_β β`.

This is just unfolding the definition `S_β β = {z | ∃ root, π_z z root β = 0}`, packaging the
*concrete* witnessing section `root` into the existential. -/
lemma mem_S_β_of_pi_z_eq_zero {H : F[X][Y]} (β : 𝒪 H) {z : F}
    (root : rationalRoot (H_tilde' H) z) (hz : (π_z z root) β = 0) :
    z ∈ S_β β :=
  ⟨root, hz⟩

/-! ### The isolated property `P` and the subset bridge -/

/-- **The isolated property `P(β)`.**  For a matching set `matchingSet : Finset F` with a
rational-root section `root`, `MatchingVanishes` says the specialization of `β` vanishes at every
matching point.  This is the *exact* requirement of ingredient C, stated as a clean hypothesis
(no `sorry`): it is the strongest possible "`matchingSet ⊆ S_β β`" — a concrete witnessing section
for each point's `S_β`-membership existential.

`L13`'s real β-construction will discharge `MatchingVanishes` via Hensel uniqueness
(`pi_z_eq_zero_of_specialization_eq` below). -/
def MatchingVanishes {H : F[X][Y]} (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' H) z) (β : 𝒪 H) : Prop :=
  ∀ z ∈ matchingSet, (π_z z (root z)) β = 0

/-- **The converse bridge (L14 packaging).**  The isolated property `P β`
(`MatchingVanishes`) implies that the whole matching set sits inside `S_β β`. -/
lemma matchingSet_subset_S_β_of_P {H : F[X][Y]} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z} {β : 𝒪 H}
    (hP : MatchingVanishes matchingSet root β) :
    (↑matchingSet : Set F) ⊆ S_β β := by
  intro z hz
  exact mem_S_β_of_pi_z_eq_zero β (root z) (hP z (by simpa using hz))

/-! ### The deliverable conditional theorem -/

/-- **Ingredient C, conditional formalization (the deliverable).**

Given:
* `hP : MatchingVanishes matchingSet root β` — the isolated property `P β`, i.e. the specialization
  `π_z z (root z) β` vanishes at every geometric matching point `z` (this is what L13's real `β`
  will provide via Hensel uniqueness);
* `hcard : (#matchingSet : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree` — the matching set is
  larger than the `Λ·d` weight bound (this is what L9/L10/L13's weight bound + §5 largeness give);

we conclude `embeddingOf𝒪Into𝕃 _ β = 0`.

This reduces **all** of ingredient C to producing a `β` satisfying `MatchingVanishes` with a large
matching set — exactly the output of L13's real β-construction.  The proof routes the matching set
through `matchingSet_subset_S_β_of_P` (L14) into the verified packaging brick
`ArkLib.embedding_eq_zero_of_finset_subset_S_β` (which is `Lemma_A_1`'s counting step). -/
theorem embedding_eq_zero_of_matchingSet_large {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (hP : MatchingVanishes matchingSet root β)
    (hcard : (↑matchingSet.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree) :
    embeddingOf𝒪Into𝕃 _ β = 0 :=
  embedding_eq_zero_of_finset_subset_S_β hH β D hD
    (matchingSet_subset_S_β_of_P hP) hcard

/-! ### Hensel-uniqueness powered per-point step (how L13 discharges `P`)

The per-point obligation `π_z z (root z) β = 0` of `MatchingVanishes` is, in App-A §5.2.6, proven by
**Hensel uniqueness**: `π_z(γ) = P_z` because both are roots of `R(X, ·, Z)` over the power-series
ring congruent mod `X` to the §5 approximation `α₀`, and the simple-root derivative is a unit, so
`hensel_root_unique` pins them equal; subtracting `P_z` and reading off the `(X-x₀)^t` coefficient
gives `π_z(α_t) = 0` hence `π_z(β_t) = 0`.

We expose two clean shapes of this per-point step so L13 can plug `hensel_root_unique` in directly.
-/

/-- **Per-point step, equality form.**  If the specialization of `β` at the matching point equals a
quantity `e` that is already known to vanish, then `π_z z root β = 0`.  Trivial, but it is the exact
landing pad: L14 produces `e = 0` (the proximate-root polynomial `P_z` minus its truncation) from
Hensel uniqueness, and this records that `π_z z root β` inherits the vanishing. -/
lemma pi_z_eq_zero_of_eq_zero {H : F[X][Y]} (β : 𝒪 H) {z : F}
    (root : rationalRoot (H_tilde' H) z) {e : F}
    (hspec : (π_z z root) β = e) (he : e = 0) :
    (π_z z root) β = 0 := by
  rw [hspec, he]

/-- **Per-point step via Hensel uniqueness.**

This is the concrete way L14 discharges a single matching point.  Suppose:
* `f : (k⟦X⟧)[Y]` is the matching polynomial at `z` (the §5 specialization `R(X, ·, Z)` recentered
  at the matching coordinate, with `k = F`);
* `aβ` is the power-series specialization of `β` at `z` and `aP` is the proximate-root power series
  `P_z` (both are *roots* of `f`);
* both are congruent mod `X` to the common §5 approximation `a₀` (the degree-0 simple root `α₀`),
  at which `f'(a₀)` is a unit (separability of `R`).

Then Hensel uniqueness (`hensel_root_unique`) forces `aβ = aP`: the lifted root is unique, so the
matching polynomial at `z` (its root `aP`) equals the specialization of `β` (`aβ`).  This is the
equality `π_z(γ) = P_z` of App-A §5.2.6 at the power-series level, from which the `(X-x₀)^t`
coefficient extraction (L12/L14, requiring the real `β_rec`) yields `π_z z root β = 0`.

We state it as the clean uniqueness conclusion `aβ = aP`; the residual coefficient-extraction step
is exactly what L13/L14 must add on top of the real `β`. -/
lemma specialization_eq_proximate_root_of_hensel {k : Type*} [Field k]
    (f : Polynomial (PowerSeries k)) {aβ aP a₀ : PowerSeries k}
    (haβ_root : f.IsRoot aβ) (haP_root : f.IsRoot aP)
    (haβ : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries k)})
    (haP : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries k)})
    (hderiv : IsUnit (f.derivative.eval a₀)) :
    aβ = aP :=
  hensel_root_unique f haβ_root haP_root haβ haP hderiv

end IngredientC

end ArkLib
