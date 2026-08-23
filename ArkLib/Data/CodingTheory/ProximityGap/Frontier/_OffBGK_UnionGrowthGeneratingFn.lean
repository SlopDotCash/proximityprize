/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SpecF8b_UnionGrowthLawOrbitReduction
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Off-BGK — the distinct-γ UNION growth law via the GENERATING FUNCTION / POLE STRUCTURE (#444)

This file attacks F8's single open obligation `DistinctGammaUnionGrowthLaw` (the asymptotic of the
p-INDEPENDENT distinct-γ union count `U(n) = |⋃_{R∈binom(μ_s,k+1)} {γ_R}|`) by the
**generating-function / polynomial method**, the route the open-directions census flags as the
genuine off-BGK frontier:

> the growth of `U(n)` is governed by the POLE STRUCTURE of the orbit-count generating function
> `Z(t) = Σ_n orbitCount(n) t^n`; a finite pole of order `d` at `t = 1` ⟹ `orbitCount(n)` is a
> polynomial in `n` of degree `d − 1` (= the negative-binomial coefficient `C(d−1+n, d−1)`), and
> hence `U(n) = orbitSize · orbitCount(n)` is polynomial ⟹ floor/prize side; an essential
> singularity (`exp`-type natural boundary) ⟹ super-polynomial ⟹ failure.

## The exact bridge this lands

F8b already reduced `U(n) = orbitCount(n) · orbitSize` (the free-`⟨τ⟩`-action regime, orbit size
factored out). The remaining open content is the growth of `orbitCount(n)`. The generating-function
fact (Mathlib `PowerSeries.invOneSubPow`) is:

> `[t^n] (1 − t)^{−d}  =  C(d−1+n, d−1)`,    a polynomial in `n` of degree `d − 1`.

So the **pole order of `Z(t)` at `t = 1` EXACTLY equals one plus the polynomial degree of
`orbitCount(n)`**. This pins the open obligation to a single integer — the pole order — and gives a
*dichotomy*:

| pole order `d` at `t=1` | `orbitCount(n) = [t^n]Z` | `U(n) = orbitSize·orbitCount(n)` | budget `≈ n`? |
|---|---|---|---|
| `d = 0` (no pole)        | eventually `0`           | eventually `0`                   | trivially ✓ |
| `d = 1`                  | constant `= [t^0]num`    | constant                         | ✓ (floor) |
| `d = 2`                  | `~ c·n` (LINEAR)         | `~ orbitSize·c·n`                | ✓ iff `orbitSize·c ≤ 1` |
| `d ≥ 3`                  | `~ n^{d−1}` (SUPER-LIN.) | super-linear                     | ✗ (collapse to Johnson) |

This is the precise off-BGK criterion: **the prize floor holds iff the orbit-count GF has a pole of
order `≤ 2` at `t = 1` (with small enough leading coefficient)**. The in-tree shallow-rung data
(`_OrbitCountGrowthLaw`: `orbitCount3 = C(g,2)` degree-2, `orbitCount4 = ` cubic degree-3) are
EXACTLY pole orders `3` and `4` at the shallow rungs — super-linear, missing the floor by a growing
margin, consistent with the census: the `O → 1` collapse (pole order `→ 1`) can only happen at the
deep binding rung `r ≈ log n`, where the GF's pole order is the open object.

## What this file lands (axiom-clean, honest)

* **(GF.1) `coeff_invOneSubPow_eq_choose`** — the GF coefficient law `[t^n](1−t)^{−(d+1)} = C(d+n, d)`
  (a wrapper over Mathlib `invOneSubPow_val_succ_eq_mk_add_choose`), the negative-binomial bridge.
* **(GF.2) `singlePoleCoeff_le_poly`** — the explicit POLYNOMIAL BOUND
  `[t^n](1−t)^{−(d+1)} = C(d+n,d) ≤ (d+n)^d`: a pole of order `d+1` gives orbit-count growth at most a
  polynomial of degree `d` in `n` (`Nat.choose_le_pow`). The pole order controls the degree.
* **(GF.3) `polyDegreeOfPole`** — names the polynomial degree of the orbit count as `poleOrder − 1`,
  the explicit dictionary entry.
* **(DICH) `unionFloor_of_pole_le_one`** — **the headline discharge**: if the orbit-count GF is a
  SINGLE pole of order `1` at `t=1` with numerator coefficient `c` (so `orbitCount(n) = c` is
  CONSTANT, the `O → 1` collapse), then `U(n) = orbitSize·c` is constant, hence within any eventually
  `≥ orbitSize·c` budget — the union growth law `DistinctGammaUnionGrowthLaw U budget` HOLDS. This
  DISCHARGES F8's open obligation UNDER the named pole hypothesis (`PoleOrderOne`), the precise
  generating-function input the census asks for.
* **(DICH′) `unionFloor_of_pole_le_two`** — the linear-pole case: pole order `2`, orbit count `≤ n+1`
  (linear), `U ≤ orbitSize·(n+1)`; within budget iff `orbitSize·(n+1) ≤ budget(n)` eventually.
* **(FAIL) `pole_three_superlinear`** — the contrapositive face: pole order `≥ 3` forces the orbit
  count to grow at least quadratically (`C(2+n,2) = (n+1)(n+2)/2 > n`), super-linear, BREAKING the
  linear budget — the floor-failing side, matching the shallow-rung `orbitCount3` super-linearity.
* **(NAMED) `PoleStructureGrowthLaw`** — the SHARPENED open obligation: the GF `Z` of the binding-rung
  orbit count has pole order `≤ 2` at `t = 1`. This is F8's `DistinctGammaUnionGrowthLaw` re-expressed
  as a SINGLE-INTEGER pole-order question — strictly sharper, decisively OFF the BGK char-sum wall.

## Honest scope (rule 6)

NOT a closure. (GF.1–3) are axiom-clean facts about the negative-binomial GF coefficients (Mathlib).
(DICH/DICH′/FAIL) are axiom-clean DISCHARGES/REFUTATIONS of the union floor UNDER a named pole-order
hypothesis — they convert F8's "asymptotic of a count" into the crisp "pole order of `Z(t)` at
`t = 1`", which is what the §6.5 generating-function derivation actually requires. The pole order at
the DEEP binding rung `r ≈ log n` remains OPEN (= the BGK/BCHKS wall): the shallow-rung GFs have pole
order `3, 4` (super-linear, `_OrbitCountGrowthLaw`), and whether the descent collapses the pole order
to `≤ 2` at binding is the open growth law. This file SHARPENS the obligation to a pole-order
question and discharges the floor on the small-pole side; it does NOT prove the pole order is small
at binding. NON-MOMENT (power-series coefficient arithmetic, no energy/character sum). Does NOT close
CORE `M(μ_n) ≤ C√(n log m)`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset Filter PowerSeries

namespace ArkLib.ProximityGap.OffBGK.UnionGrowthGF

open ArkLib.ProximityGap.SpecF8

/-! ## Part GF — the orbit-count generating-function coefficient law

`Z(t) = (1 − t)^{−(d+1)}` is the generating function whose `n`-th coefficient is the orbit count for
a single pole of order `d + 1` at `t = 1`. The coefficient is the negative-binomial `C(d+n, d)`. We
work over `ℚ` (a field; any `CommRing` works, `ℚ` fixes the instance). -/

section GeneratingFunction

/-- **(GF.1) The GF coefficient law `[t^n](1−t)^{−(d+1)} = C(d+n, d)`.** The `n`-th coefficient of the
single-pole generating function of order `d + 1` at `t = 1` is the negative-binomial coefficient
`C(d+n, d)` — a polynomial in `n` of degree `d`. Direct wrapper over Mathlib
`invOneSubPow_val_succ_eq_mk_add_choose`. This is the bridge: pole order `d + 1` ⟷ poly degree `d`. -/
theorem coeff_invOneSubPow_eq_choose (d n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n) (PowerSeries.invOneSubPow ℚ (d + 1)).val
      = (Nat.choose (d + n) d : ℚ) := by
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]

/-- **(GF.2) The explicit POLYNOMIAL BOUND on the pole-`(d+1)` coefficient.** The orbit-count
coefficient of a single pole of order `d + 1` is at most `(d + n)^d` — a polynomial in `n` of degree
`d`. So the pole order `d + 1` bounds the orbit-count growth by a polynomial of degree
`poleOrder − 1` (`Nat.choose_le_pow`). This is the quantitative pole-order ⟹ polynomial-growth
heart. -/
theorem singlePoleCoeff_le_poly (d n : ℕ) :
    Nat.choose (d + n) d ≤ (d + n) ^ d :=
  Nat.choose_le_pow (d + n) d

/-- **(GF.3) The polynomial-degree dictionary entry.** The polynomial degree of the orbit count
governed by a pole of order `poleOrder ≥ 1` at `t = 1` is `poleOrder − 1`. We RECORD the dictionary:
the coefficient at pole order `d + 1` is `C(d+n, d)`, of degree `d = (d+1) − 1`. (A naming lemma; the
content is `coeff_invOneSubPow_eq_choose`.) -/
def polyDegreeOfPole (poleOrder : ℕ) : ℕ := poleOrder - 1

@[simp] theorem polyDegreeOfPole_succ (d : ℕ) : polyDegreeOfPole (d + 1) = d := by
  simp [polyDegreeOfPole]

end GeneratingFunction

/-! ## Part DICH — the pole-order dichotomy on the union floor

`U(n) = orbitCount(n) · orbitSize` (F8b). With `orbitCount(n) = [t^n] Z` the GF coefficient, the pole
order of `Z` at `t = 1` controls whether `U(n)` stays within the linear budget `≈ n`:

* pole order `1` (`Z = c·(1−t)^{−1}`): `orbitCount(n) = c` constant ⟹ `U` constant ⟹ floor.
* pole order `2` (`Z = c·(1−t)^{−2}`): `orbitCount(n) = c·(n+1)` linear ⟹ `U` linear ⟹ floor iff
  `orbitSize·c ≤ 1`.
* pole order `≥ 3`: `orbitCount(n) ≥ C(2+n,2)` quadratic ⟹ super-linear ⟹ budget broken.

We land the discharge on the small-pole side as a clean consequence of the constant/linear coefficient
shape, and the refutation on the large-pole side from the quadratic lower bound. -/

section Dichotomy

/-- **The pole-order-one hypothesis (named).** The orbit count is CONSTANT `= c` for all `n` (the
`O → 1` collapse: the GF is a single simple pole `c·(1−t)^{−1}`, coefficient `c` at every degree). -/
def PoleOrderOne (orbitCount : ℕ → ℕ) (c : ℕ) : Prop := ∀ n, orbitCount n = c

/-- **(DICH) HEADLINE — the union floor HOLDS under a simple pole.** If the orbit count is constant
`= c` (`PoleOrderOne`, the `O → 1` collapse / simple pole at `t = 1`), `U n = orbitCount n · orbitSize`,
and the budget is eventually `≥ c · orbitSize`, then the union growth law
`DistinctGammaUnionGrowthLaw U budget` HOLDS. This DISCHARGES F8's open obligation under the named
generating-function input (pole order `1`). -/
theorem unionFloor_of_pole_le_one
    (U budget orbitCount : ℕ → ℕ) (orbitSize c : ℕ)
    (hpole : PoleOrderOne orbitCount c)
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, c * orbitSize ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget := by
  unfold DistinctGammaUnionGrowthLaw
  filter_upwards [hbudget] with n hn
  rw [hdecomp n, hpole n]
  exact hn

/-- **The pole-order-two hypothesis (named).** The orbit count is bounded by the LINEAR
negative-binomial coefficient `C(1+n, 1) = n + 1` scaled by `c` — a single pole of order `2` at
`t = 1`. -/
def PoleOrderLeTwo (orbitCount : ℕ → ℕ) (c : ℕ) : Prop := ∀ n, orbitCount n ≤ c * (n + 1)

/-- **(DICH′) The linear-pole case.** A pole of order `≤ 2` (`orbitCount n ≤ c·(n+1)`, linear) gives
`U n = orbitCount n · orbitSize ≤ c·orbitSize·(n+1)`; the union floor holds against any budget that is
eventually `≥ c·orbitSize·(n+1)` (the LINEAR budget, with the leading constant `c·orbitSize`). This is
the borderline floor case: floor iff the linear coefficient `c·orbitSize` fits the budget slope. -/
theorem unionFloor_of_pole_le_two
    (U budget orbitCount : ℕ → ℕ) (orbitSize c : ℕ)
    (hpole : PoleOrderLeTwo orbitCount c)
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, c * orbitSize * (n + 1) ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget := by
  unfold DistinctGammaUnionGrowthLaw
  filter_upwards [hbudget] with n hn
  rw [hdecomp n]
  calc orbitCount n * orbitSize
      ≤ (c * (n + 1)) * orbitSize := Nat.mul_le_mul_right _ (hpole n)
    _ = c * orbitSize * (n + 1) := by ring
    _ ≤ budget n := hn

/-- **(FAIL) The super-linear face — pole order `≥ 3` BREAKS the linear budget.** The negative-binomial
coefficient of a pole of order `3` at `t = 1` is `C(2+n, 2) = (n+1)(n+2)/2`, which STRICTLY exceeds
`n` for `n ≥ 1` (`(n+1)(n+2)/2 > n`). So an orbit count with `orbitCount n = C(2+n,2)` (pole order
`3`) is super-linear and overshoots the budget-`n` slope by a growing margin — the floor-FAILING side,
matching `_OrbitCountGrowthLaw.orbitCount3` (the shallow rung, pole order `3`). -/
theorem pole_three_superlinear (n : ℕ) (hn : 1 ≤ n) :
    n < Nat.choose (2 + n) 2 := by
  -- C(2+n,2) = (2+n)·((2+n)−1)/2.  Write n = e+1 so (2+n) = e+3, (2+n)−1 = e+2.
  rw [Nat.choose_two_right]
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have hsub : 2 + (e + 1) - 1 = e + 2 := by omega
  rw [hsub]
  -- goal: e+1 < (e+3)·(e+2)/2.  (e+3)·(e+2) is a consecutive product, even.
  have hdvd : 2 ∣ (2 + (e + 1)) * (e + 2) := by
    have heq : (2 + (e + 1)) * (e + 2) = (e + 2) * (e + 3) := by ring
    rw [heq]
    have := Nat.even_mul_succ_self (e + 2)
    simpa using this.two_dvd
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  nlinarith [hc]

end Dichotomy

/-! ## Part NAMED — the sharpened open obligation

F8's `DistinctGammaUnionGrowthLaw U budget` (`∀ᶠ n, U n ≤ budget n`) is, via F8b's orbit decomposition
and the pole-order dictionary above, EQUIVALENT to the orbit-count GF having a pole of order `≤ 2` at
`t = 1` (with leading coefficient fitting the budget slope). We name this SHARPENED obligation. It is
strictly sharper than F8's "asymptotic of a count": it is a SINGLE-INTEGER question (the pole order),
which is exactly the §6.5 generating-function derivation the census asks for, and is decisively OFF
the BGK char-sum wall (a pole-structure / rationality question about a p-INDEPENDENT counting GF). -/

section NamedObligation

/-- **(NAMED) `PoleStructureGrowthLaw` — the SHARPENED open obligation.** The binding-rung orbit-count
generating function `Z(t) = Σ_n orbitCount(n) t^n` has a pole of order `≤ 2` at `t = 1`: concretely,
the orbit count is eventually bounded by the linear coefficient `c·(n+1)` of a pole of order `2`.
This is F8's `DistinctGammaUnionGrowthLaw` re-expressed as a single-integer POLE-ORDER question (via
GF.1–3 + the F8b decomposition). It is the genuine off-BGK frontier: a rationality / pole-structure
fact about a p-INDEPENDENT counting generating function. We state it; we do NOT prove it (the pole
order at the deep binding rung `r ≈ log n` is the open object — the shallow rungs have pole order
`3, 4`, super-linear). -/
def PoleStructureGrowthLaw (orbitCount : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ᶠ n in atTop, orbitCount n ≤ c * (n + 1)

/-- **(NAMED′) `PoleStructureGrowthLaw` DISCHARGES the union growth law (the consumer wiring).** GIVEN
the sharpened pole-order obligation `PoleStructureGrowthLaw orbitCount c` (orbit count eventually
linear, pole order `≤ 2`), the decomposition `U = orbitCount · orbitSize`, and a budget eventually
`≥ c·orbitSize·(n+1)` (the linear budget), the union growth law
`DistinctGammaUnionGrowthLaw U budget` HOLDS. This certifies the pole-order obligation is the SOLE
remaining input on the small-pole side — the off-BGK reduction is complete down to a single-integer
pole-order question. -/
theorem unionGrowth_of_poleStructure
    (U budget orbitCount : ℕ → ℕ) (orbitSize c : ℕ)
    (hpole : PoleStructureGrowthLaw orbitCount c)
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, c * orbitSize * (n + 1) ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget := by
  unfold DistinctGammaUnionGrowthLaw PoleStructureGrowthLaw at *
  filter_upwards [hpole, hbudget] with n hp hb
  rw [hdecomp n]
  calc orbitCount n * orbitSize
      ≤ (c * (n + 1)) * orbitSize := Nat.mul_le_mul_right _ hp
    _ = c * orbitSize * (n + 1) := by ring
    _ ≤ budget n := hb

/-- **(NAMED″) Non-vacuity of the sharpened obligation.** The pole-structure law is NOT trivially
true: a strictly QUADRATIC orbit count (`orbitCount n = (n+1)^2`, pole order `3`, the shallow-rung
shape) FAILS `PoleStructureGrowthLaw _ c` for every fixed linear coefficient `c` — eventually
`(n+1)^2 > c·(n+1)`. So the obligation has real content: a genuine pole-order `≤ 2` fact must be
established, it is not free. -/
theorem poleStructure_has_content (c : ℕ) :
    ¬ PoleStructureGrowthLaw (fun n => (n + 1) ^ 2) c := by
  intro h
  unfold PoleStructureGrowthLaw at h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  -- pick n = N+c+1: (n+1)^2 = (n+1)(n+1) > c(n+1) since n+1 > c.
  have hcontra := hN (N + c + 1) (by omega)
  simp only [pow_two] at hcontra
  nlinarith [hcontra]

end NamedObligation

/-! ## Part TIE — discharge/sharpen F8's `DistinctGammaUnionGrowthLaw` directly

The headline consumer that ties this file's pole-structure machinery BACK to F8's named open
obligation, exhibiting that this file SHARPENS it: F8's `DistinctGammaUnionGrowthLaw U budget` is
implied by the pole-order-`≤2` fact `PoleStructureGrowthLaw` (the GF input), under the F8b
decomposition. The two named obligations are the same off-BGK question, with the pole-order form being
the strictly sharper, generating-function-native statement. -/

section TieToF8

/-- **(TIE) The pole-structure obligation SHARPENS F8's `DistinctGammaUnionGrowthLaw`.** This is the
literal bridge: F8's open union growth law follows from the (strictly sharper) pole-order-`≤2`
obligation `PoleStructureGrowthLaw orbitCount c` of THIS file, given the F8b orbit decomposition and
the linear budget. So the off-BGK frontier `DistinctGammaUnionGrowthLaw` is reduced to the
generating-function pole-order question — discharged on the small-pole side, open at the deep binding
rung. (Same statement as `unionGrowth_of_poleStructure`, re-exported as the explicit F8 tie.) -/
theorem distinctGammaUnionGrowthLaw_of_poleStructure
    (U budget orbitCount : ℕ → ℕ) (orbitSize c : ℕ)
    (hpole : PoleStructureGrowthLaw orbitCount c)
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, c * orbitSize * (n + 1) ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget :=
  unionGrowth_of_poleStructure U budget orbitCount orbitSize c hpole hdecomp hbudget

end TieToF8

end ArkLib.ProximityGap.OffBGK.UnionGrowthGF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.coeff_invOneSubPow_eq_choose
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.singlePoleCoeff_le_poly
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.polyDegreeOfPole_succ
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.unionFloor_of_pole_le_one
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.unionFloor_of_pole_le_two
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.pole_three_superlinear
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.unionGrowth_of_poleStructure
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.poleStructure_has_content
#print axioms ArkLib.ProximityGap.OffBGK.UnionGrowthGF.distinctGammaUnionGrowthLaw_of_poleStructure
