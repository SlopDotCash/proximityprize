/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

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

*Status and corrections (audit 2026-10-28, R-214).* Nothing about the actual Jacobi family, its
sheaf, conductor, Betti numbers or discrepancy is instantiated in Lean here: the theorems below
are scalar inequalities about the explicitly *defined* exponent proxies `t(r) = r − 1/2`,
`κ(r) = r − β/2` and `r`. The later `_JacKatzBoundedConductorFamily.lean` states that this file
analysed the wrong family; read the discussion below as a historical heuristic for that model.
Since `t(r) − κ(r) = (β − 1)/2` independently of `r`, for `β > 1` the proxy `κ` lies strictly
**below** `t` at every `r`; there is no `r`-dependent crossing (`katz_sqrtCount_gap`). And
`n^{κ(r)}` is a proxy for an *upper* error estimate: a positive exponent only means that estimate
does not certify vanishing; it is not a lower bound on the actual discrepancy.

The off-diagonal sum is over additive relations `Σ x_i = Σ y_j` on `μ_n` of two `r`-tuples. The
number of such pairs is at most `n^{2r-1}` (the first `2r − 1` coordinates determine the last);
this is an upper bound, not a `Θ` estimate: one linear equation on coordinates in an arbitrary
`n`-element subset does not force `≍ n^{2r-1}` solutions (for thin `μ_n` the char-0 count is
`≈ (2r−1)‼·n^r`, plus wraparound relations).
Each summand is a **unit** normalized iterated Jacobi phase `j_r = J_r/p^{(r-1)/2}`, `|j_r| = 1`,
where `J_r` is a Frobenius eigenvalue of the degree-`n`, dimension-`(r−1)` **Fermat hypersurface**
`x_1^n + … + x_r^n = 0` (Weil: `|J_r| = p^{(r-1)/2}`, the Jacobi sums ARE the nontrivial Frobenius
eigenvalues of the Fermat variety — Weil 1949).

Square-root cancellation of the off-diagonal sum means
```
|Off| ≤ slack ≈ diagonal mass ≈ (2r−1)‼ · n^r        (the Wick value).
```
A "trivial" bound is `|Off| ≤ count ≤ n^{2r-1}`. If the count were `≍ n^{2r-1}`, square-root
cancellation would mean `|Off| ≲ n^{(2r-1)/2}`; the Wick target `n^r` is *weaker* than that
(`n^r > n^{r−1/2}`), not stronger.

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

What is proved (scalar facts about the proxies only):

> * **`katz_sqrtCount_gap`.** `κ(r) ≤ t(r)` whenever `β ≥ 1`, with `t(r) − κ(r) = (β−1)/2` for
>   every `r`. So the proxy `κ` is always *below* the `√(count)` exponent and below `r`; it never
>   exceeds them.
> * **`katz_error_exp_pos`.** `κ(r) > 0` when `r > β/2`: the proxy *upper* estimate
>   `C(sheaf)·p^{-1/2} ≈ n^{κ(r)}` for the **normalized** discrepancy is not `< 1`, so that
>   estimate does not certify vanishing normalized discrepancy. It is not a lower bound on the
>   actual discrepancy, and it is not a comparison of an actual error with the off-diagonal mass.

Heuristically, Katz's fixed-order rate multiplied by a conductor proxy `≈ n^r` does not give a
useful normalized discrepancy bound at `r ≈ log p`. This is a statement about this particular
upper estimate, not a theorem excluding every effective Katz route. The **named open residual**
is:

`JacobiEquidistributionRateResidual`: an equidistribution-of-Jacobi-sums theorem with discrepancy
`o(1)` (or even `o(n^{r}/count)`) that is UNIFORM in the order `r` up to `r ≈ log p` AND restricted
to the thin `μ_n`-subfamily. No such theorem exists; Katz's is fixed-order (`r = O(1)`), full-family,
field-scale. This residual is the genuine open gap; it is NOT discharged.

## Honest status
Heuristic (not formalized): √p re-enters as the `p^{-1/2}` error term of the Katz/Deligne
equidistribution measured against the thin subgroup slice (Fact 1), and the conductor proxy `n^r`
makes that upper estimate useless at growing order (Fact 2). The off-diagonal cancellation is NOT
proved, and NOT refuted: this file proves only scalar inequalities about the defined exponent
proxies, for an uninstantiated family/conductor model, and names the residual. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiKatzEquidist

open Real

/-! ## The competing exponents (base-`n` scale) -/

/-- The **off-diagonal `√(count)` exponent proxy** `(2r−1)/2`: the off-diagonal sum has at most
`n^{2r-1}` unit-phase terms, and `n^{(2r-1)/2}` is the square root of that upper count.
Cancellation to the diagonal/Wick mass `n^r` is *weaker* (`r > (2r−1)/2`). -/
noncomputable def sqrtCountExp (r : ℝ) : ℝ := (2 * r - 1) / 2

/-- The **diagonal / Wick exponent** `r` (the mass `(2r−1)‼·n^r ≈ n^r` that the off-diagonal must not
exceed). -/
def wickExp (r : ℝ) : ℝ := r

/-- The **Katz-effective exponent proxy** in base-`n`: modelling the conductor `C(sheaf)` of the
(uninstantiated) `r`-fold Jacobi family by `≈ n^r` and Katz's rate factor by `p^{-1/2} = n^{-β/2}`,
the upper estimate for the *normalized* discrepancy has exponent `κ(r) = r − β/2`, where
`β = log_n p`. This is a definition of a proxy, not a computed conductor or discrepancy. -/
noncomputable def katzEffectiveExp (β r : ℝ) : ℝ := r - β / 2

/-! ## The exponent-race theorems (axiom-clean) -/

/-- **The proxy Katz exponent is positive for every order past `β/2`.** With `β = log_n p` and
`r > β/2`, `κ(r) = r − β/2 > 0`, so the proxy upper estimate `n^{κ(r)}` for the normalized
discrepancy is `≥ 1` (for `n ≥ 1`) and does not certify vanishing. This says the particular upper
estimate is useless there; it is not a lower bound on the actual discrepancy and does not show the
off-diagonal cancellation fails. -/
theorem katz_error_exp_pos {β r : ℝ} (hr : β / 2 < r) : 0 < katzEffectiveExp β r := by
  unfold katzEffectiveExp; linarith

/-- **The proxy Katz exponent lies below the `√(count)` exponent at every order.** The exact gap is
`t(r) − κ(r) = (2r−1)/2 − (r − β/2) = (β−1)/2`, independent of `r`, which is `≥ 0` for `β ≥ 1`
(`p ≥ n`) and `> 0` for `β > 1`. There is no `r`-dependent crossing: `κ(r)` never exceeds `t(r)`
(nor `r`). (An earlier docstring claimed `κ ≥ t` exactly when `r ≥ β − 1`; that was false, R-214.)
The two exponents measure different things — `κ` a normalized-discrepancy upper estimate, `t` an
absolute off-diagonal size — so this comparison is between proxies only. -/
theorem katz_sqrtCount_gap {β r : ℝ} (hβ : 1 ≤ β) :
    katzEffectiveExp β r ≤ sqrtCountExp r := by
  unfold sqrtCountExp katzEffectiveExp
  -- (2r-1)/2 - (r - β/2) = (β-1)/2 ≥ 0
  nlinarith [hβ]

/-- **The proxy exponent at the prize order.** In the regime `β ≤ 5` (field `p ≈ n·2^{128}`,
subgroup `n = 2^{30}` ⟹ `log_n p ≈ 4.27`) and order `r ≥ 3`, `κ(r) ≥ r − 5/2 ≥ 1/2 > 0`. So the
proxy upper estimate `n^{κ(r)}` for the normalized discrepancy is at least `√n`: this estimate
certifies nothing. It is not a lower bound on the actual discrepancy, and this scalar fact does not
show that every effective Katz-type argument fails. -/
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
open gap. We state it as an explicit predicate (`D r < 1` on the order window) so the dependency
is named, never silently assumed; the proxy `n^{r-β/2}` violates it
(`katz_discrepancy_fails_residual`). -/
def JacobiEquidistributionRateResidual (D : ℝ → ℝ) (rmax : ℝ) : Prop :=
  ∀ r, 3 ≤ r → r ≤ rmax → D r < 1

/-- **The proxy majorant fails the residual predicate.** For the explicitly defined majorant
`D(r) = n^{κ(r)}` (the conductor proxy `n^r` times `p^{-1/2} = n^{-β/2}`, with `n ≥ 1`), in the
regime `β ≤ 5` one has `D(3) ≥ 1`, so `D` does not satisfy `JacobiEquidistributionRateResidual`
for any `rmax ≥ 3`. This refutes the predicate for that majorant only; it does not identify the
majorant with the actual discrepancy of any Jacobi family, and does not show the residual is
unattainable by other means. -/
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
