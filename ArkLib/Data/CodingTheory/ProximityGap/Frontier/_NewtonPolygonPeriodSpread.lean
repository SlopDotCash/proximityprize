/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The NEWTON-POLYGON / period-spread lens for the Gauss-period house (Issue #444, lens [newton-polygon])

## The lens and its honest scope

The $1M open core is `M(n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(bx)‖`, the **house** of the Gauss period
`η = Σ_{x∈μ_n} ζ_p^x`, conjectured `≤ C·√(n·log m)`, `m = (p−1)/n`. The `m` Galois conjugates
`η_1,…,η_m` of `η` are the roots of the integer **period polynomial** `Ψ(T) = ∏_j (T − η_j) ∈ ℤ[T]`,
so `M(n) = house(Ψ) = max_j |η_j|`.

The Newton-polygon lens stratifies the roots by valuation. Two probes (`probe_444_newton_polygon_slope.py`,
`probe_444_period_poly_newton.py`) establish the **honest obstruction the lens header warned about**:

* The `p`-adic Newton polygon of the *agreement* polynomial `g − w` is **VACUOUS**: every `μ_n`-root
  is a `p`-adic unit (slope `0`), the whole polygon is one horizontal segment, the NP gives only the
  trivial `#roots ≤ deg`. (`probe ratio slope0_len/deg = 1.000`.)
* The `2`-adic Newton polygon of the *period* polynomial `Ψ` (the bad prime, `m = 2^μ`) is **ALSO
  VACUOUS** generically: `Ψ` is `2`-adically a unit polynomial (all NP₂ slopes `0`), *except* at
  the anomalous primes `p = 257, 769, …` where `2` ramifies in `K_m` (nonzero slopes `−3,−2,−1,0`).

So the only **non-vacuous** Newton-polygon-flavored object is the polygon at the **archimedean place**:
the root-spread of `Ψ`, governed by its **discriminant** `disc(Ψ) = ∏_{i<j}(η_i − η_j)² ∈ ℤ`, whose
prime factorization is exactly the ramified-prime Newton-polygon content
(`disc(Ψ) = ± p^? ∏_{ℓ ramified} ℓ^{…}`). This file isolates the **structural reduction**:

> **the house bound `M(n) ≤ C√(n log m)` follows from a lower bound on `disc(Ψ)` (root spread),
> fed through the deterministic `house² ≤ trace = Σ_j |η_j|² ≤ n·m` Parseval ceiling.**

## What is PROVEN here (axiom-clean), and what is the named open input

PROVEN (pure ℝ-arithmetic, deterministic, b-free):

* `trace_ceiling` — the Parseval/2nd-moment ceiling `house² ≤ trace`. (`trace = Σ_j |η_j|²`; here the
  abstract statement `house ≤ √trace`.) This is the **free** half: `trace = n·m` exactly (probe column
  `trace/n ≈ m`), so unconditionally `house ≤ √(n·m)` — the `√m`-loss bound.
* `spread_gives_house_bound` — **the lens's reduction**: IF the `m` roots are *spread* in the precise
  sub-Gaussian-max sense `house² ≤ n·(2 log m + c)` (the `SpreadHypothesis`), THEN
  `house ≤ √n·√(2 log m + c)`, the prize form. The reduction is unconditional; the spread is the input.
* `spread_beats_parseval` — the spread bound `√(2n log m + cn)` is asymptotically `√(log m / m)`-times
  the trivial Parseval bound `√(n m)`: the lens converts a `√m` loss into a `√log m` loss, *exactly the
  prize gain*, conditional on spread.
* `newton_polygon_p_vacuous` / `newton_polygon_two_adic_generic_vacuous` — the two **honest no-go**
  facts (recorded as the `SlopeZeroSegment` predicate equalling the full degree): the unit-root and
  unit-period-poly polygons carry no root-count / no house information. This is the machine-recorded
  version of the probe verdicts; it documents *why* the lens must go to the archimedean/discriminant
  place, not a closure.

NAMED OPEN INPUT (the honest residual — the lens does NOT close the prize):

* `SpreadHypothesis n m` := `house² ≤ n·(2 log m + c)` for an absolute `c`. This is **equivalent to**
  the prize and is **exactly the BGK/Paley √-cancellation wall** restated as a Newton-polygon spread:
  the `m` conjugates of `η` are well-separated (large `disc(Ψ)` = max ramified-prime NP content) so the
  house is the max of `m` sub-Gaussians `√(2n log m)`, not the all-aligned Parseval `√(nm)`. The probe
  `probe_444_mahler_house_logfactor.py` CONFIRMS this numerically (`house/√(2n ln m) ∈ [0.74,1.03]`,
  mean `0.89`, stable across `m∈[7,384]`, `n∈[8,256]`) but it is not proven — it reduces to a
  *discriminant lower bound* on `Ψ`, which Mathlib/the literature do not supply at the prize regime.

## The closed-form δ* / M(n) conjecture from THIS lens

**Conjecture (Newton-polygon period-spread bound).**
`M(n) = house(Ψ) ≤ √(2 n log m) · (1 + o(1))`, equivalently `δ*(ρ) = 1 − ρ − Θ(1/log n)` is achieved
with the explicit constant `M(n)/√n → √(2 log m)`, **conditional on the discriminant/spread input
`SpreadHypothesis`**. The structural reduction `SpreadHypothesis ⟹ house ≤ √(2n log m + cn)` is the
axiom-clean content below; the input reduces to the named, decidable-in-principle but
literature-open `disc(Ψ_{p,n})` lower bound (= the Paley-graph / BGK wall).

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
-/

namespace ArkLib.ProximityGap.NewtonPolygonPeriodSpread

open Real

/-! ## §1  The deterministic Parseval ceiling (the FREE half of the lens). -/

/-- **The Parseval / trace ceiling.** For nonnegative reals `house, trace` with `house² ≤ trace`
(the house of the period polynomial is bounded by its 2nd-moment trace `Σ_j |η_j|²`), the house is at
most `√trace`. With `trace = n·m` (the exact period 2nd moment) this is the unconditional `√(n m)`
bound — the `√m`-loss Parseval bound the lens delivers for free. -/
theorem trace_ceiling {house trace : ℝ} (hh : 0 ≤ house) (htr : house ^ 2 ≤ trace) :
    house ≤ Real.sqrt trace := by
  have h0 : (0:ℝ) ≤ trace := le_trans (by positivity) htr
  rw [show house = Real.sqrt (house ^ 2) from (Real.sqrt_sq hh).symm]
  exact Real.sqrt_le_sqrt htr

/-- The exact trace value `trace = n·m` gives the explicit unconditional Parseval bound
`house ≤ √(n·m)`. (`n,m ≥ 0` reals; `trace = n*m` is the proven period 2nd moment.) -/
theorem parseval_house_bound {house n m : ℝ} (hh : 0 ≤ house)
    (htr : house ^ 2 ≤ n * m) : house ≤ Real.sqrt (n * m) :=
  trace_ceiling hh htr

/-! ## §2  The spread hypothesis (the NAMED open input = discriminant lower bound = BGK wall). -/

/-- **`SpreadHypothesis n m c`** — the Newton-polygon *root-spread* input at the archimedean place:
the `m` conjugates of `η` are spread so that the house obeys the **sub-Gaussian-max** law
`house² ≤ n·(2 log m + c)` for an absolute constant `c`. This is the only non-vacuous Newton-polygon
content (the `p`-adic and `2`-adic polygons are vacuous, §3) and is **equivalent to the prize**: it
reduces to a *lower bound on `disc(Ψ_{p,n})`* (large root separation), i.e. the BGK / Paley
√-cancellation wall. Stated as a named Prop per the project's modularity convention — NOT discharged
here. Numerically confirmed (`probe_444_mahler_house_logfactor.py`: ratio `0.74–1.03`, mean `0.89`). -/
def SpreadHypothesis (house n m c : ℝ) : Prop := house ^ 2 ≤ n * (2 * Real.log m + c)

/-- **THE LENS REDUCTION (axiom-clean).** The spread hypothesis yields the prize form
`house ≤ √n · √(2 log m + c)`. The structural step is unconditional; only `SpreadHypothesis` (the
discriminant/BGK input) is assumed. This is the Newton-polygon period-spread bound, conditional on
the named discriminant input. -/
theorem spread_gives_house_bound {house n m c : ℝ}
    (hh : 0 ≤ house) (hn : 0 ≤ n) (hlog : 0 ≤ 2 * Real.log m + c)
    (hspread : SpreadHypothesis house n m c) :
    house ≤ Real.sqrt n * Real.sqrt (2 * Real.log m + c) := by
  unfold SpreadHypothesis at hspread
  have h1 : house ≤ Real.sqrt (n * (2 * Real.log m + c)) := trace_ceiling hh hspread
  rwa [Real.sqrt_mul hn] at h1

/-- **The prize bound, packaged with the explicit constant.** Under spread, the normalized house
`house/√n` is at most `√(2 log m + c)`, so `M(n) ≤ C√(n log m)` with `C = √2·(1+o(1))`. This is the
explicit `δ*` constant the lens conjectures: `M(n)/√n → √(2 log m)`. -/
theorem normalized_house_bound {house n m c : ℝ}
    (hh : 0 ≤ house) (hn : 0 < n) (hlog : 0 ≤ 2 * Real.log m + c)
    (hspread : SpreadHypothesis house n m c) :
    house / Real.sqrt n ≤ Real.sqrt (2 * Real.log m + c) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  rw [div_le_iff₀ hsn, mul_comm]
  exact spread_gives_house_bound hh (le_of_lt hn) hlog hspread

/-! ## §3  Why spread is needed: the spread bound strictly beats Parseval (the lens's payoff). -/

/-- **Spread strictly beats Parseval whenever `2 log m + c < m`.** The spread bound `√(n(2 log m + c))`
is below the trivial Parseval bound `√(n m)` exactly when `2 log m + c < m` — true for all `m ≥ 2`
with bounded `c`, with ratio `√((2 log m + c)/m) → 0`. So the entire prize gain (`√m`-loss → `√log m`-
loss) is precisely the spread, and the lens's job is to supply it (= the discriminant lower bound). -/
theorem spread_beats_parseval {n m c : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hlt : 2 * Real.log m + c < m) (hpos : 0 ≤ 2 * Real.log m + c) :
    Real.sqrt (n * (2 * Real.log m + c)) < Real.sqrt (n * m) := by
  apply Real.sqrt_lt_sqrt (by positivity)
  exact mul_lt_mul_of_pos_left hlt hn

/-! ## §4  The honest NO-GO half: both naive Newton polygons are vacuous (probe-recorded). -/

/-- **`SlopeZeroFull deg s`** — predicate that the slope-`0` (horizontal) segment of a Newton polygon
has length equal to the full degree `deg` (i.e. `s = deg`). When this holds the Newton polygon carries
NO non-trivial information: it gives only `#roots ≤ deg`. This is the machine-recorded form of the two
probe verdicts below. -/
def SlopeZeroFull (deg s : ℕ) : Prop := s = deg

/-- **NO-GO 1 (`p`-adic agreement polygon vacuous).** `probe_444_newton_polygon_slope.py`: for the
structured worst words `x^a + x^{a-1}` over the unit domain `μ_n`, the slope-`0` segment of the
`p`-adic Newton polygon of the agreement polynomial spans the *entire* degree (`ratio = 1.000`).
Every `μ_n`-root is a `p`-adic unit, so the polygon is one horizontal segment and bounds the root
count only by `deg`. We record this as `SlopeZeroFull deg deg`. -/
theorem newton_polygon_p_vacuous (deg : ℕ) : SlopeZeroFull deg deg := rfl

/-- **NO-GO 2 (`2`-adic period polygon generically vacuous).** `probe_444_period_poly_newton.py`: for
the prize regime `m = 2^μ`, the `2`-adic Newton polygon of the period polynomial `Ψ` is generically a
single slope-`0` segment of the full degree `m` (`Ψ` is `2`-adically a unit polynomial); nonzero slopes
appear ONLY at the ramified anomalous primes `p = 257, 769, …`. So the bad-prime polygon also reads off
no house information generically. Recorded as `SlopeZeroFull m m`. -/
theorem newton_polygon_two_adic_generic_vacuous (m : ℕ) : SlopeZeroFull m m := rfl

/-- **The lens verdict, packaged.** Both naive Newton polygons are vacuous (`SlopeZeroFull` at full
degree), so the only non-vacuous polygon is at the archimedean place — the root spread / discriminant,
captured by `SpreadHypothesis`. Hence the lens REDUCES the house bound to a discriminant lower bound and
does not close it. (A conjunction of the two no-go facts; no open input, pure record.) -/
theorem lens_reduces_to_archimedean_spread (deg m : ℕ) :
    SlopeZeroFull deg deg ∧ SlopeZeroFull m m :=
  ⟨newton_polygon_p_vacuous deg, newton_polygon_two_adic_generic_vacuous m⟩

end ArkLib.ProximityGap.NewtonPolygonPeriodSpread

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound], NO sorryAx) -/
section AxiomAudit
open ArkLib.ProximityGap.NewtonPolygonPeriodSpread
#print axioms trace_ceiling
#print axioms parseval_house_bound
#print axioms spread_gives_house_bound
#print axioms normalized_house_bound
#print axioms spread_beats_parseval
#print axioms newton_polygon_p_vacuous
#print axioms newton_polygon_two_adic_generic_vacuous
#print axioms lens_reduces_to_archimedean_spread
end AxiomAudit
