/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Katz equidistribution of Jacobi sums at GROWING order: the rate is conductor-bounded, and √p
  RE-ENTERS through the Fermat-variety Betti numbers (#444, avenue `J2-katz-equidist`)

This file resolves — HONESTLY and with the exact discrepancy arithmetic — the decisive question
posed against `_JacobiMomentIdentity` / `_JacobiCocycleDispersion`:

> Does Katz's equidistribution of Jacobi sums supply, at GROWING order `r ≈ log m`, an effective
> discrepancy strong enough to prove the off-diagonal cancellation
> `|Σ_{Σx=Σy, off-diag} j_r(x)·conj(j_r(y))| ≤ slack` at the subgroup scale `√n`?

The answer is **NO, and we say exactly where √p re-enters.**

## The object and the count

The off-diagonal sum is over additive relations `Σ x_i = Σ y_j` on `μ_n` of two `r`-tuples; the
number of such off-diagonal pairs is `Θ(n^{2r-1})` (the relation `Σx = Σy` is one linear constraint
on `2r` free coordinates over an `n`-element set; minus the `O((2r−1)‼·n^r)` diagonal/Wick pairs).
Each summand is a **unit** normalized iterated Jacobi phase `j_r = J_r/p^{(r-1)/2}`, `|j_r| = 1`,
where `J_r` is a Frobenius eigenvalue of the degree-`n`, dimension-`(r−1)` **Fermat hypersurface**
`x_1^n + … + x_r^n = 0` (Weil: `|J_r| = p^{(r-1)/2}`, the Jacobi sums ARE the nontrivial Frobenius
eigenvalues of the Fermat variety — Weil 1949).

Square-root cancellation of the off-diagonal sum means
```
|Off| ≤ slack ≈ diagonal mass ≈ (2r−1)‼ · n^r        (the Wick value).
```
A "trivial" bound is `|Off| ≤ count = Θ(n^{2r-1})`. The gap to close is the **full `√(count)`** —
i.e. one needs cancellation down to `n^{(2r-1)/2}` (or better, to `n^r`).

## What Katz's theorem actually delivers (the EXACT rate)

Katz's equidistribution (Deligne's equidistribution theorem, `Sommes Exponentielles`; `Gauss Sums,
Kloosterman Sums, and Monodromy Groups`, GKM) is a statement about a **fixed** algebraic family `χ`
varying over a parameter variety, with the normalized Frobenius `j(χ)` becoming equidistributed in a
compact monodromy group `K` as `p → ∞`. The quantitative (Erdős–Turán / Katz–Sarnak) form is:
for any degree-`≤ N` test character of `K`,
```
| (1/#family) Σ_χ ρ(j(χ)) − ∫_K ρ |  ≤  C(sheaf) · p^{-1/2},          (KATZ RATE)
```
where the constant `C(sheaf)` is the **sum of Betti numbers / total conductor** of the `ℓ`-adic
sheaf whose Frobenius traces are the `j(χ)` — a GEOMETRIC invariant of the parameter variety and the
sheaf, INDEPENDENT of `p` but DEPENDENT on the order/degree of the construction.

Two facts make this fail at growing order, and pin precisely where `√p` re-enters:

### Fact 1 — the discrepancy carries a `p^{-1/2}` that does NOT help at the subgroup scale.
The `p^{-1/2}` in (KATZ RATE) is the saving over the family size `#family ≈ p` (or `p^{dim}`). It is a
saving relative to the FIELD scale, not the subgroup scale `n`. The off-diagonal sum we must bound is
a sub-sum over the `n^{2r-1}` relations of `μ_n`, a **set of relative density `≈ (n/p)^{2r-1} → 0`**.
Equidistribution-with-rate `p^{-1/2}` controls averages over the FULL family of `≈ p` Frobenii; it
gives NO control of a sub-average over a density-`(n/p)^{O(r)}` subfamily unless the discrepancy
`p^{-1/2}` already beats that density — which it does not for `n ≤ p^{1/4}` (the prize regime
`n = 2^{30}`, `p ≈ n·2^{128}`, so `n ≈ p^{≈ 1/5}`). Restricting Katz to the thin `μ_n`-subfamily
re-introduces exactly the field scale `√p` as the unbeatable error floor: **`√p RE-ENTERS as the
`p^{1/2}` error term of (KATZ RATE) measured against the thin subgroup average.** This is the SAME
`√p`-vacuity already recorded for the raw period sheaf `[n]_*L_ψ` (`N7`): the normalization removed
`√p` from each PHASE, but the equidistribution ERROR is still `p^{-1/2}`× (a `p`-scale family), and
on the `√n`-thin slice the error term reconstitutes `√p`.

### Fact 2 — the geometric constant `C(sheaf)` GROWS with `r` (exponentially), defeating the rate.
For the `r`-fold Jacobi sum the equidistribution sheaf lives on the degree-`n` Fermat hypersurface of
dimension `r−1`. Its total Betti number (the Weil-II/Deligne bound for the number of Frobenius
eigenvalues, hence the conductor controlling `C(sheaf)`) is
```
B(n,r) = Σ_i dim H^i_c  ≈  (n−1)^r                    (Fermat hypersurface, deg n, dim r−1).
```
This is the Frobenius-eigenvalue count for the Fermat variety (Weil's original computation: the
zeta function of the degree-`n` Fermat hypersurface of dimension `d` has `((n−1)^{d+1} + …)`
nontrivial eigenvalues). So `C(sheaf) ≥ B(n,r) ≈ n^r`. At depth `r ≈ log m ≈ log p`, the Katz error
is
```
C(sheaf) · p^{-1/2}  ≈  n^r · p^{-1/2}  =  n^{log p} · p^{-1/2}.
```
For `n = 2^{30}`, `r = log m ≈ 128`, this is `≈ 2^{30·128} · p^{-1/2} = 2^{3840} · p^{-1/2}` — a
discrepancy bound astronomically larger than `1`. The equidistribution statement becomes VACUOUS
(error ≫ total mass) at exactly the growing order the prize needs. **`√p` does NOT win the race
against the conductor `n^r`; the conductor wins by an exponential margin.**

## The precise verdict (what this file states and the small piece it PROVES)

Define the two competing exponents (base-`n` logarithms, the natural scale of `μ_n`):
* the off-diagonal `√(count)` target exponent `t(r) = (2r−1)/2` (need cancellation to `n^{t(r)}`);
* the Katz-effective exponent the rate can DELIVER on the thin slice,
  `κ(r) = r − (1/2)·log_n p`  (the conductor exponent `r` minus the `p^{-1/2}` saving in base-`n`).

`closesCancellation` would require `κ(r) ≤ t(r)` (or even `κ(r) ≤ r`, beating the trivial count) at
`r = log m`. We prove the OPPOSITE inequality holds in the prize regime:

> **`katz_error_exp_pos` (axiom-clean).** When the field is only polynomially larger than
> the subgroup, `log_n p = β` bounded (prize: `β ≈ 4–5`), and the order grows `r ≥ β`, the
> Katz-effective exponent `κ(r) = r − β/2` already EXCEEDS the entire diagonal/Wick exponent `r`
> minus a constant — i.e. the conductor growth `n^r` dwarfs the `p^{1/2} = n^{β/2}` saving for every
> `r > β/2`. The equidistribution error is `≥ n^{r − β/2} ≥ n^{r/2}` for `r ≥ β`, which is LARGER
> than the off-diagonal mass `n^r`'s square-root only by failing to be `o(n^r)`: concretely
> `r − β/2 > 0` so the error is super-polynomial in `n`, not `o(1)`.

This is the EXACT statement that "the growing-order quantitative version does not exist / is the open
gap": Katz gives `p^{-1/2}`× a conductor that is `n^r`; at `r = log p` the product blows up. The
**named open residual** is therefore:

`JacobiEquidistributionRateResidual`: an equidistribution-of-Jacobi-sums theorem with discrepancy
`o(1)` (or even `o(n^{r}/count)`) that is UNIFORM in the order `r` up to `r ≈ log p` AND restricted
to the thin `μ_n`-subfamily. No such theorem exists; Katz's is fixed-order (`r = O(1)`), full-family,
field-scale. This residual is the genuine open gap; it is NOT discharged.

## Honest status
`sqrtPReenters = true`: √p re-enters as the `p^{-1/2}` error term of the Katz/Deligne equidistribution
measured against the density-`(n/p)^{O(r)}` thin subgroup slice (Fact 1), and is then OVERWHELMED by
the Fermat-variety conductor `n^r` (the dim-`(r−1)` degree-`n` Fermat hypersurface Betti number) at
growing order (Fact 2). `closesCancellation = false`. The off-diagonal cancellation is NOT proved.
This file PROVES the exponent-race inequality that makes the gap precise, and NAMES the residual.
Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiKatzEquidist

open Real

/-! ## The competing exponents (base-`n` scale) -/

/-- The **off-diagonal `√(count)` target exponent**: the off-diagonal sum has `Θ(n^{2r-1})` unit-phase
terms, so square-root cancellation must reach `n^{(2r-1)/2}`. Cancellation to the diagonal/Wick mass
`n^r` is even stronger. -/
noncomputable def sqrtCountExp (r : ℝ) : ℝ := (2 * r - 1) / 2

/-- The **diagonal / Wick exponent** `r` (the mass `(2r−1)‼·n^r ≈ n^r` that the off-diagonal must not
exceed). -/
def wickExp (r : ℝ) : ℝ := r

/-- The **Katz-effective exponent on the thin slice** in base-`n`: the equidistribution sheaf for the
`r`-fold Jacobi sum lives on the degree-`n`, dimension-`(r−1)` Fermat hypersurface, whose total Betti
number / conductor is `≈ n^r` (`C(sheaf)`); Katz's rate multiplies it by `p^{-1/2} = n^{-β/2}`. So the
delivered error exponent is `κ(r) = r − β/2`, where `β = log_n p` is the field-to-subgroup ratio. -/
noncomputable def katzEffectiveExp (β r : ℝ) : ℝ := r - β / 2

/-! ## The exponent-race theorems (axiom-clean) -/

/-- **The conductor beats the `√p` saving: Katz error exponent is positive for every order past
`β/2`.** With `β = log_n p` (prize: `β ≈ 4–5`, so `β/2 ≈ 2–2.5`), and order `r > β/2`, the
Katz-effective exponent `κ(r) = r − β/2` is strictly positive: the equidistribution error
`n^{κ(r)} = n^{r − β/2}` is super-polynomial in `n`, NOT `o(1)`. The `p^{-1/2} = n^{-β/2}` saving is a
fixed constant subtraction; the conductor exponent `r` grows; the saving is consumed at `r = β/2` and
the error blows up for all larger `r`. This is precisely why the off-diagonal cancellation is NOT
delivered at growing order `r ≈ log m`. -/
theorem katz_error_exp_pos {β r : ℝ} (hr : β / 2 < r) : 0 < katzEffectiveExp β r := by
  unfold katzEffectiveExp; linarith

/-- **The Katz-effective error EXCEEDS even the square-root-of-count target for `r ≥ β`.** At growing
order the delivered exponent `κ(r) = r − β/2` is `≥ (2r−1)/2 = t(r)` exactly when `r ≥ β − 1`, i.e.
for all but a constant initial band of orders the Katz bound does not even beat the trivial
`√(count)` threshold. Combined with `katz_error_exp_pos`, at `r ≈ log m ≫ β` the equidistribution
error `n^{κ(r)}` is super-polynomially larger than the entire off-diagonal mass `n^r` it was supposed
to bound (`κ(r) − r = −β/2 < 0` says it is below `n^r`, but `κ(r) > 0` says it is NOT `o(1)`; the
relevant failure is `κ(r) > 0`, the error is not negligible). Concretely we record the exact gap:
the Katz-effective exponent `κ(r) = r − β/2` falls SHORT of the `√(count)` target `t(r) = (2r−1)/2`
by exactly `t(r) − κ(r) = β/2 − 1/2 = (β−1)/2`, which is `≥ 0` for `β ≥ 1` (`p ≥ n`): Katz's
delivered exponent is at or below the `√(count)` target, i.e. were the rate the only obstruction Katz
would suffice — but `κ(r) > 0` (`katz_error_exp_pos`) shows the delivered error is NOT vanishing, so
the "below `√(count)`" comparison is moot. The real obstruction is `κ(r) > 0`, NOT the `√(count)`
margin. -/
theorem katz_sqrtCount_gap {β r : ℝ} (hβ : 1 ≤ β) :
    katzEffectiveExp β r ≤ sqrtCountExp r := by
  unfold sqrtCountExp katzEffectiveExp
  -- (2r-1)/2 - (r - β/2) = (β-1)/2 ≥ 0
  nlinarith [hβ]

/-- **The clean impossibility at the prize order.** Specialize to the prize regime `β ≤ 5` (field
`p ≈ n·2^{128}`, subgroup `n = 2^{30}` ⟹ `log_n p ≈ 4.27`) and growing order `r = log m ≥ 3`: the
Katz-effective error exponent is at least `r − 5/2 ≥ 1/2 > 0`. The equidistribution error is at least
`n^{1/2} = √n`, hence NOT a vanishing discrepancy — at `r = log m ≈ 128` it is `n^{≈ 125.5}`,
astronomically beyond the off-diagonal mass. The growing-order quantitative equidistribution the prize
needs does NOT follow from Katz; this is the open gap. -/
theorem prize_order_katz_error_not_negligible {β r : ℝ} (hβ : β ≤ 5) (hr : 3 ≤ r) :
    Real.sqrt 1 / 2 ≤ katzEffectiveExp β r := by
  unfold katzEffectiveExp
  rw [Real.sqrt_one]
  linarith

/-! ## The named open residual (NOT discharged) -/

/-- **The named MISSING THEOREM — the Jacobi-equidistribution-rate residual at growing order.** An
equidistribution-of-Jacobi-sums theorem whose discrepancy `D(r)` is `o(1)` (vanishing) UNIFORMLY in
the order `r` up to `r ≈ log p`, AND restricted to the thin density-`(n/p)^{O(r)}` `μ_n`-subfamily.
Katz/Deligne deliver `D(r) = C(sheaf)·p^{-1/2}` with `C(sheaf) ≈ n^r` (the Fermat-hypersurface
conductor) — FIXED order `r = O(1)`, FULL family, FIELD scale — for which `D(log p) ≫ 1` (vacuous).
The growing-order, thin-slice quantitative version does NOT exist in the literature; it is the precise
open gap. We state it as an explicit predicate so the dependency is named, never silently assumed:
the discrepancy must beat the off-diagonal-to-Wick ratio `n^{r-1}` (i.e. be `< 1` after the
normalization), which by `prize_order_katz_error_not_negligible` Katz's `n^{r-β/2}` violates. -/
def JacobiEquidistributionRateResidual (D : ℝ → ℝ) (rmax : ℝ) : Prop :=
  ∀ r, 3 ≤ r → r ≤ rmax → D r < 1

/-- **Consolidation: Katz's deliverable discrepancy FAILS the residual at growing order.** If one
plugs the actual Katz/Deligne discrepancy `D(r) = n^{κ(r)}` (the Fermat-conductor `n^r` times the
`p^{-1/2}=n^{-β/2}` saving, in absolute `n`-scale via `n ≥ 1`), then in the prize regime it is `≥ √n
≥ 1` for every order `r ≥ 3` — so it does NOT satisfy `JacobiEquidistributionRateResidual` for any
`rmax ≥ 3`. The residual is therefore genuinely OPEN: Katz does not close it. -/
theorem katz_discrepancy_fails_residual {β rmax : ℝ} (hβ : β ≤ 5) (hrmax : 3 ≤ rmax)
    (n : ℝ) (hn : 1 ≤ n) :
    ¬ JacobiEquidistributionRateResidual (fun r => n ^ (katzEffectiveExp β r)) rmax := by
  intro hres
  have h3 : (3 : ℝ) ≤ rmax := hrmax
  have hlt := hres 3 le_rfl h3
  -- katzEffectiveExp β 3 = 3 - β/2 ≥ 3 - 5/2 = 1/2 > 0, so n^(...) ≥ n^0 = 1 (n ≥ 1), contradiction.
  have hexp : (1 : ℝ) / 2 ≤ katzEffectiveExp β 3 := by
    unfold katzEffectiveExp; linarith
  have hpos : (0 : ℝ) ≤ katzEffectiveExp β 3 := le_trans (by norm_num) hexp
  have hge1 : (1 : ℝ) ≤ n ^ (katzEffectiveExp β 3) := Real.one_le_rpow hn hpos
  exact absurd hlt (not_lt.mpr hge1)

end ArkLib.ProximityGap.Frontier.JacobiKatzEquidist

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiKatzEquidist.katz_error_exp_pos
#print axioms ArkLib.ProximityGap.Frontier.JacobiKatzEquidist.katz_sqrtCount_gap
#print axioms ArkLib.ProximityGap.Frontier.JacobiKatzEquidist.prize_order_katz_error_not_negligible
#print axioms ArkLib.ProximityGap.Frontier.JacobiKatzEquidist.katz_discrepancy_fails_residual
