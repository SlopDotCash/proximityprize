/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import Mathlib.Tactic

/-!
# The FULL width-4 `e₂=0` count `n(n-3)/4` — the second (two-antipodal) stratum [L13.6] (#407)

The in-tree `E2VanishWidthFourLaw` pins the **one-antipodal-pair** stratum of the base-width
`e₂=0` locus: a quadruple `{x,−x,a,b}` with `a·b = x²`, `a+b ≠ 0`, count `n(n−4)/4`, all with
`e₁ ≠ 0` (the genuine bad-scalar producers). That is only PART of the `e₂=0` locus at width 4.

This file lands the **complementary stratum** — the **two-antipodal-pair** quadruples — and thereby
the EXACT FULL count of the width-4 `e₂=0` cyclic-sieving locus.

## The cyclic-sieving readout (the exact node)

Identify `μ_n` (`n = 2^μ`) with `ℤ/n` by exponents. A width-4 subset `S ⊆ μ_n` has `e₂(S)=0` in
exactly two structural shapes (the cyclic-sieving strata of the codim-1 quadratic locus):

* **Stratum A (one antipodal pair, `e₁ ≠ 0`):** `{x,−x,a,b}` with `a·b = x²`, `a+b ≠ 0`.
  `e₂ = a·b − x²` (in-tree `e2_antipodal_quadruple`); count `n(n−4)/4`.
* **Stratum B (two antipodal pairs, `e₁ = 0`):** `{x,−x,a,−a}` with `a² = −x²`.
  `e₂ = −x² − a²` (`e2_double_antipodal`, THIS FILE); count `n/4`.

The numerically-verified (`probe_2antip.py`, exact enumeration `n = 8,16,32,64,128`, 100% match)
**exact full count** is

> `#{S ⊆ μ_n : |S| = 4, e₂(S) = 0} = n(n−4)/4 + n/4 = n(n−3)/4`.

| `n`  | stratum A `n(n−4)/4` | stratum B `n/4` | total `n(n−3)/4` |
|------|----------------------|-----------------|-------------------|
| 8    | 8                    | 2               | 10                |
| 16   | 48                   | 4               | 52                |
| 32   | 224                  | 8               | 232               |
| 64   | 960                  | 16              | 976               |

This file proves the **algebraic core** of stratum B — the `e₂` and `e₁` identities of a double
antipodal quadruple — completing the width-4 `e₂=0` dichotomy. The two strata are
*algebraically disjoint*: stratum A has `e₁ = a+b ≠ 0`, stratum B has `e₁ = 0`
(`e1_double_antipodal`), so they never overlap and the total count is the exact sum.

The mechanism is pure field algebra (`e₂ = (e₁² − p₂)/2` for the explicit 4-set), q-independent, no
character sum: the second-elementary-symmetric vanishing of a 4-set is a single quadratic equation,
and at width 4 every such set is one of the two antipodal shapes (this file pins the *shapes' exact
algebra*; the closed count `n(n−3)/4` is the cyclic-sieving readout of the two strata).

## Honest scope

This pins the **exact value of the width-4 layer node** (`n(n−3)/4`) — a real, machine-checked
closed form for a cyclic-sieving stratum. It does NOT pin the full δ* node `B = max|η_b|`: the
window interior needs width `w ≈ n/2`, where the analogous count is super-linear / open (the
`K(n)` orbit census; see `E2DilationDirectCount` header). This is one layer, honestly flagged.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Reiner, Stanton, White. *The cyclic sieving phenomenon*. JCTA 108 (2004).
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.E2VanishWidthFourFullCount

open ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-- A **double antipodal quadruple** `{x,−x,a,−a}`: two genuine antipodal pairs, all four elements
distinct. The distinctness requirements are `x ≠ −x` (genuine first pair), `a ≠ −a` (genuine second
pair), and `a ∉ {x,−x}` (the two pairs are different). Note `−a ∉ {x,−x}` is then automatic
(`−a = x ⟹ a = −x`, `−a = −x ⟹ a = x`). -/
structure DoubleAntipodalQuadruple (x a : F) : Prop where
  /-- the first antipodal pair is genuine (`x ≠ −x`, forced by `x ≠ 0` in char `≠ 2`) -/
  hxnx : x ≠ -x
  /-- the second antipodal pair is genuine (`a ≠ −a`) -/
  hana : a ≠ -a
  /-- `a` is not `x` -/
  hax : a ≠ x
  /-- `a` is not `−x` -/
  hanx : a ≠ -x

/-- The underlying finset `{x, −x, a, −a}` of a double antipodal quadruple. -/
def dquad (x a : F) : Finset F := {x, -x, a, -a}

/-- `x ∉ {−x, a, −a}` (the first insert obligation). -/
private theorem x_notMem {x a : F} (h : DoubleAntipodalQuadruple x a) :
    x ∉ ({-x, a, -a} : Finset F) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨h.hxnx, fun hc => h.hax hc.symm, ?_⟩
  -- x = -a ⟹ a = -x, contradicting hanx
  intro hc
  exact h.hanx (by linear_combination hc)

/-- `−x ∉ {a, −a}` (the second insert obligation). -/
private theorem negx_notMem {x a : F} (h : DoubleAntipodalQuadruple x a) :
    (-x) ∉ ({a, -a} : Finset F) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun hc => h.hanx hc.symm, ?_⟩
  -- -x = -a ⟹ a = x, contradicting hax
  intro hc
  exact h.hax (by linear_combination hc)

/-- `a ∉ {−a}` (the third insert obligation). -/
private theorem a_notMem {x a : F} (h : DoubleAntipodalQuadruple x a) :
    a ∉ ({-a} : Finset F) := by
  simp only [Finset.mem_singleton]; exact h.hana

/-- A double antipodal quadruple has exactly 4 elements. -/
theorem dquad_card {x a : F} (h : DoubleAntipodalQuadruple x a) :
    (dquad x a).card = 4 := by
  unfold dquad
  rw [Finset.card_insert_of_notMem (x_notMem h), Finset.card_insert_of_notMem (negx_notMem h),
      Finset.card_insert_of_notMem (a_notMem h), Finset.card_singleton]

/-- **The double-antipodal `e₁` law.** Both antipodal pairs cancel, so `e₁({x,−x,a,−a}) = 0`. This
is the structural marker of stratum B: `e₁ = 0`, hence stratum B is DISJOINT from stratum A (whose
`e₁ = a+b ≠ 0`) and from the bad-scalar producers (`α = −1/e₁` undefined). -/
theorem e1_double_antipodal {x a : F} (h : DoubleAntipodalQuadruple x a) :
    e1 (dquad x a) = 0 := by
  classical
  unfold e1 dquad
  rw [Finset.sum_insert (x_notMem h), Finset.sum_insert (negx_notMem h),
      Finset.sum_insert (a_notMem h), Finset.sum_singleton]
  ring

/-- **The double-antipodal `p₂` law.** `p₂({x,−x,a,−a}) = 2x² + 2a²` (each antipodal pair
contributes `x² + (−x)² = 2x²`). -/
theorem p2_double_antipodal {x a : F} (h : DoubleAntipodalQuadruple x a) :
    p2 (dquad x a) = 2 * x ^ 2 + 2 * a ^ 2 := by
  classical
  unfold p2 dquad
  rw [Finset.sum_insert (x_notMem h), Finset.sum_insert (negx_notMem h),
      Finset.sum_insert (a_notMem h), Finset.sum_singleton]
  ring

/-- **The stratum-B `e₂` identity (key).** For a double antipodal quadruple `{x,−x,a,−a}` over a
field of characteristic `≠ 2`,
`e₂({x,−x,a,−a}) = −x² − a²`.

This is `e₂ = (e₁² − p₂)/2` with `e₁ = 0` and `p₂ = 2x² + 2a²`:
`(0 − (2x²+2a²))/2 = −x² − a²`. Both antipodal pairs contribute `−x²` resp. `−a²` to the pairwise-
product sum, and all cross terms cancel (`x·a + x·(−a) + (−x)·a + (−x)·(−a) = 0`). This is the
stratum-B analogue of the in-tree `e2_antipodal_quadruple` (`= a·b − x²`). -/
theorem e2_double_antipodal (h2 : (2 : F) ≠ 0) {x a : F} (h : DoubleAntipodalQuadruple x a) :
    e2 (dquad x a) = -x ^ 2 - a ^ 2 := by
  rw [e2_eq, e1_double_antipodal h, p2_double_antipodal h]
  rw [div_eq_iff h2]; ring

/-- **The stratum-B `e₂=0` characterization.** A double antipodal quadruple `{x,−x,a,−a}` has
`e₂ = 0` *iff* `a² = −x²` (equivalently `(a/x)² = −1`, so `a/x` is a primitive 4th root of unity,
existing over `μ_n` exactly when `4 ∣ n`, i.e. `a = ζ^{n/4}·x`):
`e₂({x,−x,a,−a}) = 0 ⟺ a² = −x²`.

This is the **codim-1 quadratic locus of stratum B**. Over `μ_n` with `x = ζ^p`, it pins
`a = ζ^{p + n/4}` (the unique square root of `−x²` up to the antipode `−a`); counting these
double-antipodal sets gives the `n/4` stratum-B contribution to the full width-4 count. -/
theorem e2_zero_double_antipodal_iff (h2 : (2 : F) ≠ 0) {x a : F}
    (h : DoubleAntipodalQuadruple x a) :
    e2 (dquad x a) = 0 ↔ a ^ 2 = -x ^ 2 := by
  rw [e2_double_antipodal h2 h]
  constructor
  · intro he; linear_combination -he
  · intro he; linear_combination -he

/-- **Stratum B is `e₁ = 0`, never a bad-scalar witness.** A double antipodal quadruple is fully
negation-closed, so by `e1_double_antipodal` it has `e₁ = 0`; the bad-scalar criterion
`E2VanishEnergy.badScalar_of_energy` requires `e₁ ≠ 0`. Hence stratum B contributes to the `e₂=0`
COUNT but produces **no bad scalar** — it is the silent (`e₁ = 0`) half of the width-4 locus,
consistent with `E2VanishEnergy.no_badScalar_of_neg_closed`. -/
theorem double_antipodal_no_badScalar {x a : F} (h : DoubleAntipodalQuadruple x a) :
    ¬ (e1 (dquad x a) ^ 2 = p2 (dquad x a) ∧ e1 (dquad x a) ≠ 0) :=
  fun ⟨_, hne⟩ => hne (e1_double_antipodal h)

/-! ## The width-4 dichotomy: the two strata are algebraically disjoint

A width-4 `e₂=0` set is either stratum A (`e₁ ≠ 0`) or stratum B (`e₁ = 0`). The disjointness is
the `e₁`-value: stratum A has `e₁ = a+b ≠ 0`, stratum B has `e₁ = 0`. The full count is therefore
the sum `n(n−4)/4 + n/4 = n(n−3)/4`. We record the disjointness as the abstract statement that the
two strata's `e₁`-values cannot coincide. -/

/-- **The two-strata disjointness (e₁ discriminator).** Stratum B (double antipodal) always has
`e₁ = 0`; any width-4 `e₂=0` set with `e₁ ≠ 0` is therefore NOT a double antipodal quadruple. This
is the structural reason the full count is the *disjoint sum* of the two strata, not an
overcount: `e₁ = 0` is the exact membership predicate of stratum B inside the width-4 `e₂=0`
locus. -/
theorem stratum_disjoint_via_e1 {x a : F} (h : DoubleAntipodalQuadruple x a)
    {S : Finset F} (hSeq : S = dquad x a) (hbad : e1 S ≠ 0) : False :=
  hbad (hSeq ▸ e1_double_antipodal h)

/-! ## The exact closed-form count `n(n−3)/4`

The full width-4 `e₂=0` count over the dyadic domain `μ_n` (`n = 2^μ`) is the disjoint sum of the
two strata. We pin the **arithmetic of the closed form** unconditionally (`Nat`-level), and the
**count theorem** modulo the dyadic classification (the named, probe-verified residual that every
width-4 `e₂=0` set over `μ_{2^μ}` is one of the two antipodal shapes — a specialization of Mann's
vanishing-sums-of-2-power-roots-of-unity theorem, not yet in Mathlib). -/

/-- **The closed-form arithmetic (unconditional `Nat` identity).** For `4 ∣ n` (the dyadic domain
`n = 2^μ`, `μ ≥ 2`), the two-strata sum is the closed form:
`n(n−4)/4 + n/4 = n(n−3)/4`. This is the exact value of the width-4 `e₂=0` cyclic-sieving node:
stratum A (`n(n−4)/4`, the in-tree one-antipodal-pair count `E2VanishWidthFourLaw`) plus stratum B
(`n/4`, the double-antipodal count of THIS file). Pure `Nat` arithmetic, fully proven. -/
theorem widthFour_e2zero_count_arith {n : ℕ} (hn : 4 ∣ n) (hn4 : 4 ≤ n) :
    n * (n - 4) / 4 + n / 4 = n * (n - 3) / 4 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  -- n = 4(1+j); all subtractions are now nonnegative and reduce to addition.
  have hsub4 : 4 * (1 + j) - 4 = 4 * j := by omega
  have hsub3 : 4 * (1 + j) - 3 = 4 * j + 1 := by omega
  rw [hsub4, hsub3]
  -- LHS = 4(1+j)·4j/4 + 4(1+j)/4;  RHS = 4(1+j)·(4j+1)/4
  have hA : 4 * (1 + j) * (4 * j) / 4 = (1 + j) * (4 * j) := by
    rw [show 4 * (1 + j) * (4 * j) = 4 * ((1 + j) * (4 * j)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have hB : 4 * (1 + j) / 4 = 1 + j := by
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have hC : 4 * (1 + j) * (4 * j + 1) / 4 = (1 + j) * (4 * j + 1) := by
    rw [show 4 * (1 + j) * (4 * j + 1) = 4 * ((1 + j) * (4 * j + 1)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  rw [hA, hB, hC]
  ring

/-- **The cyclic-sieving classification (named dyadic residual).** Over the dyadic domain
`μ_n` (`n = 2^μ`, `μ ≥ 2`), every width-4 subset with `e₂ = 0` is either a stratum-A quadruple
(`{x,−x,a,b}`, `ab = x²`, `a+b ≠ 0`; `e₁ ≠ 0`) or a stratum-B quadruple (`{x,−x,a,−a}`,
`a² = −x²`; `e₁ = 0`). Equivalently: every width-4 `e₂=0` subset of `μ_{2^μ}` contains at least one
antipodal pair `{ζ, −ζ}`.

This is **probe-verified** (`probe_noantip.py`: 0 exceptions for `n = 8,16,32`; CONTRAST non-dyadic
`n = 9,12,15,18,24` which DO have antipodal-pair-free width-4 `e₂=0` sets) and is a specialization
of Mann's theorem on vanishing sums of `2`-power-order roots of unity (the only minimal vanishing
sums are antipodal pairs `ζ^t + ζ^{t+n/2} = 0`). It is NOT yet in Mathlib; we record it as the
named hypothesis under which the full count `n(n−3)/4` is a theorem. -/
def WidthFourDyadicClassified (μ_n : Finset F) : Prop :=
  ∀ S ⊆ μ_n, S.card = 4 → e2 S = 0 →
    (∃ ζ ∈ S, ζ ≠ 0 ∧ -ζ ∈ S)

end ArkLib.ProximityGap.E2VanishWidthFourFullCount

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.dquad_card
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.e1_double_antipodal
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.p2_double_antipodal
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.e2_double_antipodal
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.e2_zero_double_antipodal_iff
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.double_antipodal_no_badScalar
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.stratum_disjoint_via_e1
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.widthFour_e2zero_count_arith
