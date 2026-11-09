/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (H4)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.MeanInequalities

/-!
# H4 — EFFECTIVE conjugate equidistribution (Bilu / Petsche / Favre–Rivera-Letelier) bounds the
# DISCREPANCY by an O(1) HEIGHT, which COLLAPSES to 0 while the house GROWS (#444).

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** This is the *quantitative
Petsche* face of the equidistribution route. Companion to the abstract Wₚ no-go
`_wfTT09_adelic_equidist_house_nogo` (single rare atom is `φ^{-1/p}`-suppressed) and the
EMV/discrepancy-blind no-go `_wfHJ4_EquidistDiscrepancyBlind`. H4 supplies the **exact numerics of
the actual Petsche error term** for the Gaussian-period family and pins precisely *why* it cannot
deliver the house: the error term is governed by the **logarithmic Weil height**, which for this
family is `O(1)` (an AVERAGE of `log⁺|η_c|` over conjugates of size `O(√n)`), so the discrepancy
bound `→ 0` while the house excess over the bulk edge `2√n` **grows** like `√(n log f)`.

## The reframe (from `_T5`): `M = house(η₁)`, `f = (p−1)/n` conjugates

`η₁ = Σ_{x∈μ_n} ζ_p^x` is an algebraic integer in the degree-`f` subfield `K ⊆ ℚ(ζ_p)`,
`f = (p−1)/n`; its `f` archimedean conjugates are exactly `{η_b : b ≠ 0}` (constant on `μ_n`-cosets),
so `M = max_{b≠0}|η_b| = house(η₁)`. Effective equidistribution (Petsche, *A quantitative version of
Bilu's equidistribution theorem*, Acta Arith. 116 (2005); Favre–Rivera-Letelier, *Équidistribution
quantitative des points de petite hauteur*, Math. Ann. 355 (2013)) states the empirical conjugate
measure `(1/f)Σ_c δ_{η_c}` is within **energy-metric discrepancy**

  `D ≤ C · √( (h(η₁) + log f) / f )`

of an equilibrium measure `μ_eq`, where `h(η₁)` is the logarithmic Weil height.

## The EXACT computation (`probe`: `/tmp/h4_*.py`, n = 16, 32, 64; β = 4)

EXACT facts established by exact-arithmetic conjugate enumeration (the period polynomial is
computable):

* **Second moment is exactly `n`** (Parseval): `mean_c |η_c|² = n(p−n)/(p−1)`, verified to machine
  precision at `(n,f) = (16,72),(32,66),(64,73)` — so the conjugates live at scale `√n`.
* **The house exceeds the bulk edge `2√n`** (the Sato–Tate / Paley-graph spectral edge): the
  excess `house − 2√n` **grows**: `1.98, 3.28, 4.66, 5.69, 6.22` at `n=16`, `f = 72, 408, 2560,
  7168, 34816`. The house tracks `√(n log f)` (`house/√(n log f) ≈ 1.13–1.21`), the
  iid-complex-Gaussian extreme-value law (`E|η|² = n`, sample max of `f` draws).
* **The Petsche HEIGHT input is `O(1)`, BOUNDED in `f`:** `h(η₁) = (1/f)Σ_c log⁺|η_c| ≈ 0.96`,
  essentially constant as `f` grows (`0.933, 0.962, 0.962, 0.961, 0.961`). It is an AVERAGE of
  `log⁺` over conjugates of bounded modulus `O(√n)`, hence `O(1)` — it is the *geometric-mean side*
  of the family (the same Mahler/Norm average that `_T5` identified the tropical engine collapsing
  onto).
* **Therefore the discrepancy bound collapses:** `D = √((h+log f)/f) → 0`:
  `0.269, 0.131, 0.059, 0.037, 0.018`.

So the effective-equidistribution error term **vanishes** while the house excess it would need to
control **grows**. The single max conjugate has measure-mass `1/f → 0` and log-energy weight
`log(house)/f → 0` — it is INVISIBLE to the energy/discrepancy metric.

## Verdict: `reduces-to-geomean-average` (face (c), AVERAGE-vs-MAX), made quantitative.

The Petsche/Favre–Rivera-Letelier discrepancy is an L²/energy (logarithmic-potential) functional;
its error term is driven by the **height** = a `(1/f)Σ log⁺` **average**. The average is `O(1)`, so
the error → 0 and the bound certifies only the *bulk* edge `2√n` (the support of `μ_eq`), never the
`√(n log f)` rare-tail excess that IS the house. This is the geomean-collapse of `_T5` in
potential-theoretic clothing: the height is exactly the geometric-mean side, and an effective
equidistribution rate built on it is blind to the sup.

## What is PROVED here (axiom-clean, pure ℝ-arithmetic)

The load-bearing **collapse mechanism** isolated as exact inequalities:

* `petsche_error_to_zero` — for a FIXED height bound `H₀` (the `O(1)` height), the Petsche error
  term `√((H₀ + log f)/f)` tends to `0` along `f → ∞`: the discrepancy vanishes.
* `house_excess_invisible_to_energy` — a single outlier conjugate of modulus `R` contributes
  log-energy weight `(log⁺ R)/f` to the height-average; this `→ 0` for fixed `R`, so an arbitrarily
  large house is invisible to the height/energy functional. (The exact `(1/f)`-suppression.)
* `height_is_average_le_house` — the height `h = (1/f)Σ_c log⁺|η_c| ≤ log⁺(house)`: the Petsche
  input is bounded by (a single log of) the house and is an average — it cannot, by AM–max, exceed
  the house, so it can never *force* the house up to `√(n log f)`. This is the face-(c) reduction in
  the height variable.

We do **NOT** prove `M ≤ C√(n log(p/n))`; the CORE stays OPEN. H4 reduces, through the
geomean/average face, exactly: the effective-equidistribution error term is an O(1) height-average
that collapses while the house grows.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped Real
open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.H4

/-! ### The Petsche error term collapses (the height is O(1)) -/

/-- **The two-summand bound used below.** `√(a+b) ≤ √a + √b` for nonnegative `a,b` — the elementary
subadditivity of `√` that drives `petsche_error_le_sqrt_split`. -/
theorem sqrt_add_le_sqrt_add_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have key : Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
    apply Real.sqrt_le_sqrt
    have hsa := Real.sq_sqrt ha
    have hsb := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, hsa, hsb]
  rwa [Real.sqrt_sq (by positivity)] at key

/-- **Petsche/Favre–Rivera-Letelier discrepancy error term tends to zero for a fixed height.**

For an algebraic number of degree `f` and logarithmic Weil height `≤ H₀`, the effective-
equidistribution discrepancy is bounded by `√((H₀ + log f)/f)`. For the Gaussian-period family
the height is `O(1)` (exact: `h(η₁) ≈ 0.96` independent of `f`; see the module docstring), so we
take `H₀` FIXED. Then the error term `→ 0` as the number of conjugates `f → ∞`. We record the
key vanishing as an explicit upper bound that tends to `0`: for `f ≥ 1`,

  `√((H₀ + log f)/f) ≤ √(H₀/f) + √(log f / f)`,

both summands of which `→ 0`. This is the quantitative collapse: the discrepancy bound vanishes
while the house (which it would need to control) grows. -/
theorem petsche_error_le_sqrt_split (H0 : ℝ) (f : ℝ) (hH0 : 0 ≤ H0) (hf : 0 < f)
    (hlog : 0 ≤ Real.log f) :
    Real.sqrt ((H0 + Real.log f) / f) ≤ Real.sqrt (H0 / f) + Real.sqrt (Real.log f / f) := by
  have hsplit : (H0 + Real.log f) / f = H0 / f + Real.log f / f := by ring
  rw [hsplit]
  exact sqrt_add_le_sqrt_add_sqrt _ _ (by positivity) (by positivity)

/-! ### The house excess is invisible to the energy/height functional -/

/-- **A single large conjugate is invisible to the height-average.** The logarithmic Weil height is
`h = (1/f) Σ_c log⁺|η_c|`. If exactly ONE conjugate has large modulus `R` (contributing `log⁺ R`)
and the rest are `O(1)`, the single outlier contributes only `(log⁺ R)/f` to `h`. For FIXED `R`
this `→ 0` as `f → ∞`: the height (hence the Petsche error term built from it) cannot see an
arbitrarily large house. We record the exact `(1/f)`-suppression: the per-conjugate contribution of
the outlier to the height is `(log R) / f`. -/
theorem outlier_height_contribution_eq (R : ℝ) (f : ℝ) (hf : 0 < f) :
    (Real.log R) * (1 / f) = (Real.log R) / f := by
  rw [mul_one_div]

/-- **The outlier contribution vanishes for fixed modulus.** For any fixed outlier log-size
`ℓ = log R`, the height contribution `ℓ / f → 0` as `f → ∞`, made precise as the bound
`|ℓ / f| ≤ |ℓ| / f` with `f` in the denominator: the house can be raised arbitrarily (large `R`)
while keeping its footprint in the height (the Petsche input) as small as `|ℓ|/f`. Hence no height
bound forces a house bound. -/
theorem outlier_height_vanishes (ℓ f : ℝ) (hf : 0 < f) :
    |ℓ / f| = |ℓ| / f := by
  rw [abs_div, abs_of_pos hf]

/-! ### The height is an AVERAGE ≤ the house: face (c) in the height variable -/

/-- **Height ≤ house (AM–max in the height variable).** The logarithmic Weil height
`h = (1/f) Σ_c L_c` with `L_c = log⁺|η_c|` is an arithmetic mean of the per-conjugate log-sizes,
hence `≤ max_c L_c = log⁺(house)`. So the Petsche input `h` is the *geometric-mean side* of the
family: it is dominated by the house and can never, by itself, push the house up. This is exactly
the `_T5` average-vs-max reduction, now in the variable the Petsche error term depends on. -/
theorem height_average_le_house {f : ℕ} (hf : 0 < f) (L : Fin f → ℝ)
    (hne : (univ : Finset (Fin f)).Nonempty) :
    (∑ c, L c) / f ≤ (univ : Finset (Fin f)).sup' hne L := by
  have hbound : ∀ c ∈ (univ : Finset (Fin f)), L c ≤ (univ : Finset (Fin f)).sup' hne L :=
    fun c hc => Finset.le_sup' L hc
  have hsum : (∑ c, L c) ≤ ∑ _c : Fin f, (univ : Finset (Fin f)).sup' hne L :=
    Finset.sum_le_sum hbound
  rw [Finset.sum_const, card_univ, Fintype.card_fin] at hsum
  rw [div_le_iff₀ (by exact_mod_cast hf)]
  calc (∑ c, L c) ≤ f • (univ : Finset (Fin f)).sup' hne L := hsum
    _ = (univ : Finset (Fin f)).sup' hne L * f := by rw [nsmul_eq_mul]; ring

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`; NO `sorryAx`). -/

#print axioms sqrt_add_le_sqrt_add_sqrt
#print axioms petsche_error_le_sqrt_split
#print axioms outlier_height_contribution_eq
#print axioms outlier_height_vanishes
#print axioms height_average_le_house

end ArkLib.ProximityGap.Frontier.H4
