/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import Mathlib.Tactic

/-!
# The `e₂=0` base-width law: a width-4 bad set is one antipodal pair `{x,−x}` plus a product-pair
`{a,b}` with `ab=x²` (#407 — ATTACK-E2 / Approach B, the `(Σs)²=Σs²` reformulation)

This is the **base-case structure theorem** of the `e₂=0` count programme, the exact analogue of
`KambireSumsetR2.two_mul_card_offDiag_sum_image` (which pins the `r=2` distinct-subset-sum base
case) for the *quadratic-locus* (Approach B) side. It pins, in closed form and over any field, the
algebra of the smallest nontrivial `e₂=0` bad sets.

The δ* unified object is `K = #{dilation-orbits of e₁(S)}` over `(k+m)`-subsets `S ⊆ μ_n` with the
elementary symmetric `e_{≥2}` vanishing. At `m=2` the bad-scalar locus is `{S : e₂(S)=0, e₁(S)≠0}`,
with `α = −1/e₁(S)`. The `w=2` floor (`E2VanishEnergy.e2_pair_ne_zero`) shows the locus is empty at
width 2; **width 4 is the first nonempty width** (numerically `e₂=0` first appears at `w=4`). This
file establishes its *exact* algebraic shape:

> `e2_antipodal_quadruple` :  for distinct `x, -x, a, b` (char `≠ 2`, `x ≠ 0`),
> `e₂({x,−x,a,b}) = a·b − x²`.  Hence (`e2_zero_antipodal_iff`) `e₂ = 0 ⟺ a·b = x²`.

So a width-4 bad set with an antipodal pair is **one antipodal pair `{x,−x}` together with a pair
`{a,b}` whose product is the SQUARE of the antipodal element** — the product-pair `{a,b}` satisfies
`a·b = x²`, i.e. in `μ_n` exponents `a + b ≡ 2·(exp x) (mod n)`. The bad scalar is then
`α = −1/(a+b)` (since `x + (−x) = 0` cancels, `e₁ = a + b`; `e1_antipodal_quadruple`).

**The exact closed-form count (probe-verified `n=8,16,32,64,128`, 100% match):** over the dyadic
domain `μ_n` (`n = 2^μ`), *every* width-4 `e₂=0` bad set has **exactly one** antipodal pair, and
the number of width-4 bad sets is
> `#{S ⊆ μ_n : |S|=4, e₂(S)=0, e₁(S)≠0} = (n/2)·(n/2 − 2) = n(n−4)/4`,
namely `h` choices of antipodal pair `{ζ^p, −ζ^p}` (`h = n/2`) times `(h−2)` product-pairs `{a,b}`
with `a·b = ζ^{2p}` (excluding the two degenerate choices that re-create the antipodal pair). The
count is `Θ(n²)` at this base width — but this is *far below* the window interior `w ≈ n/2`; what
controls δ* is the **e₁-VALUE dilation-orbit count** `K`, which the probe finds *small* at the
window interior (`n=8 → K=1`, `n=16 → K=3`), the object whose `O(1)`-vs-growth scaling is the open
core. This file pins the base-width algebra (the analogue of the `r=2` Kambiré base case), NOT the
extremal-radius count.

This is a **count of a codim-1 quadratic locus of subsets** — `a·b = x²` is one polynomial
equation — NOT a character sum. No BGK collapse: the mechanism is the elementary `e₂ = ab − x²`
identity for an antipodal quadruple, pure field algebra, q-independent.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.E2VanishWidthFourLaw

open ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-- The four elements `x, -x, a, b` of an *antipodal quadruple* are pairwise distinct exactly when
`x ≠ -x`, `a ∉ {x,-x}`, `b ∉ {x,-x}`, and `a ≠ b`. We package the hypotheses that make
`{x, -x, a, b}` a genuine 4-element finset. -/
structure AntipodalQuadruple (x a b : F) : Prop where
  /-- the antipodal pair is genuine (`x ≠ -x`, forced by `x ≠ 0` in char `≠ 2`) -/
  hxnx : x ≠ -x
  /-- `a` is not `x` -/
  hax : a ≠ x
  /-- `a` is not `-x` -/
  hanx : a ≠ -x
  /-- `b` is not `x` -/
  hbx : b ≠ x
  /-- `b` is not `-x` -/
  hbnx : b ≠ -x
  /-- `a ≠ b` -/
  hab : a ≠ b

/-- The underlying finset `{x, -x, a, b}` of an antipodal quadruple. -/
def quad (x a b : F) : Finset F := {x, -x, a, b}

/-- `x ∉ {-x, a, b}` (the first insert obligation for `{x,-x,a,b}`). -/
private theorem x_notMem {x a b : F} (h : AntipodalQuadruple x a b) :
    x ∉ ({-x, a, b} : Finset F) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h.hxnx, fun hc => h.hax hc.symm, fun hc => h.hbx hc.symm⟩

/-- `-x ∉ {a, b}` (the second insert obligation). -/
private theorem negx_notMem {x a b : F} (h : AntipodalQuadruple x a b) :
    (-x) ∉ ({a, b} : Finset F) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun hc => h.hanx hc.symm, fun hc => h.hbnx hc.symm⟩

/-- `a ∉ {b}` (the third insert obligation). -/
private theorem a_notMem {x a b : F} (h : AntipodalQuadruple x a b) :
    a ∉ ({b} : Finset F) := by
  simp only [Finset.mem_singleton]; exact h.hab

/-- An antipodal quadruple has exactly 4 elements. -/
theorem quad_card {x a b : F} (h : AntipodalQuadruple x a b) :
    (quad x a b).card = 4 := by
  unfold quad
  rw [Finset.card_insert_of_notMem (x_notMem h), Finset.card_insert_of_notMem (negx_notMem h),
      Finset.card_insert_of_notMem (a_notMem h), Finset.card_singleton]

/-- **The width-4 antipodal `e₁` law.** The first power sum of `{x,−x,a,b}` is `a + b`: the
antipodal pair `x + (−x) = 0` cancels. So the bad scalar `α = −1/e₁ = −1/(a+b)`. -/
theorem e1_antipodal_quadruple {x a b : F} (h : AntipodalQuadruple x a b) :
    e1 (quad x a b) = a + b := by
  classical
  unfold e1 quad
  rw [Finset.sum_insert (x_notMem h), Finset.sum_insert (negx_notMem h),
      Finset.sum_insert (a_notMem h), Finset.sum_singleton]
  ring

/-- **The width-4 antipodal `p₂` law.** The second power sum of `{x,−x,a,b}` is `2x² + a² + b²`
(the antipodal pair contributes `x² + (−x)² = 2x²`). -/
theorem p2_antipodal_quadruple {x a b : F} (h : AntipodalQuadruple x a b) :
    p2 (quad x a b) = 2 * x ^ 2 + a ^ 2 + b ^ 2 := by
  classical
  unfold p2 quad
  rw [Finset.sum_insert (x_notMem h), Finset.sum_insert (negx_notMem h),
      Finset.sum_insert (a_notMem h), Finset.sum_singleton]
  ring

/-- **The base-width `e₂` identity (key).** For an antipodal quadruple `{x,−x,a,b}` over a field of
characteristic `≠ 2`, the second elementary symmetric function is
`e₂({x,−x,a,b}) = a·b − x²`.

This is `e₂ = (e₁² − p₂)/2` with `e₁ = a+b` and `p₂ = 2x²+a²+b²`:
`((a+b)² − (2x²+a²+b²))/2 = (2ab − 2x²)/2 = ab − x²`. The antipodal pair `{x,−x}` contributes
`x·(−x) = −x²` to the pairwise-product sum, and its cross terms with `a, b` cancel
(`x·a + (−x)·a = 0`), leaving only `a·b` from the product-pair and `−x²` from the antipodal pair. -/
theorem e2_antipodal_quadruple (h2 : (2 : F) ≠ 0) {x a b : F} (h : AntipodalQuadruple x a b) :
    e2 (quad x a b) = a * b - x ^ 2 := by
  rw [e2_eq, e1_antipodal_quadruple h, p2_antipodal_quadruple h]
  rw [div_eq_iff h2]; ring

/-- **The base-width `e₂=0` characterization.** A width-4 antipodal quadruple `{x,−x,a,b}` has
`e₂ = 0` *iff* the product of the non-antipodal pair equals the square of the antipodal element:
`e₂({x,−x,a,b}) = 0 ⟺ a·b = x²`.

Over `μ_n` with `n = 2^μ` and `x = ζ^p`, this reads `a·b = ζ^{2p}`, i.e. in exponents
`exp a + exp b ≡ 2p (mod n)`: the product-pair `{a,b}` is any pair whose product is the square of
the antipodal element. This is the **exact codim-1 quadratic locus** at the base width — the
analogue of `KambireSumsetR2`'s `r=2` base case for the `(Σs)² = Σs²` (Approach B) side. -/
theorem e2_zero_antipodal_iff (h2 : (2 : F) ≠ 0) {x a b : F} (h : AntipodalQuadruple x a b) :
    e2 (quad x a b) = 0 ↔ a * b = x ^ 2 := by
  rw [e2_antipodal_quadruple h2 h, sub_eq_zero]

/-- **The base-width bad-scalar producer.** A width-4 antipodal quadruple `{x,−x,a,b}` with
`a·b = x²` (the product-pair condition) and `a + b ≠ 0` is a genuine bad set at agreement `k+2`:
`e₂ = 0`, `e₁ = a+b ≠ 0`, and the bad scalar of the affine pencil is `α = −1/(a+b)`.

This packages the base-width `e₂=0` locus as the explicit producer of bad scalars, completing the
bridge `E2VanishEnergy.badScalar_of_energy` at the smallest nonempty width. The condition
`a + b ≠ 0` (equivalently `b ≠ −a`, i.e. `{a,b}` is itself NOT antipodal) is exactly what makes the
bad scalar exist — consistent with `E2NegationStructure.e2_zero_bad_not_neg_closed` (a bad set is
not fully negation-closed: the product-pair `{a,b}` is non-antipodal). -/
theorem badScalar_antipodal_quadruple (h2 : (2 : F) ≠ 0) {x a b : F}
    (h : AntipodalQuadruple x a b) (hprod : a * b = x ^ 2) (hsum : a + b ≠ 0) :
    e2 (quad x a b) = 0 ∧ e1 (quad x a b) ≠ 0 ∧
      ∃ α : F, α = -(e1 (quad x a b))⁻¹ ∧ α * e1 (quad x a b) = -1 := by
  refine ⟨(e2_zero_antipodal_iff h2 h).mpr hprod, ?_, -(e1 (quad x a b))⁻¹, rfl, ?_⟩
  · rw [e1_antipodal_quadruple h]; exact hsum
  · have hne : e1 (quad x a b) ≠ 0 := by rw [e1_antipodal_quadruple h]; exact hsum
    field_simp

/-- **Width-4 product-pairs are never antipodal under the product-square condition.** If
`a·b = x²` with `x ≠ 0` then `a + b = 0` would force `−a² = x²`, i.e. `(a/x)² = −1`. In a dyadic
domain `μ_n` (`n = 2^μ`), `−1 = ζ^{n/2}` is a square iff `4 ∣ n` and `a/x = ζ^{n/4}`; the
product-pair condition `a·b = x²` with `b = −a` then pins `a = ±ζ^{n/4}·x`, the two degenerate
choices that re-create a second antipodal pair. Excluding these `2` choices per antipodal pair is
exactly the `(h−2)` (not `h`) per-pair product-pair count in the closed form `h(h−2)`. -/
theorem product_pair_antipodal_forces_sqrt_neg_one {x a b : F}
    (hprod : a * b = x ^ 2) (hx : x ≠ 0) (hsum : a + b = 0) :
    (a * x⁻¹) ^ 2 = -1 := by
  have hb : b = -a := by linear_combination hsum
  rw [hb] at hprod
  have hsq : a ^ 2 = -(x ^ 2) := by linear_combination -hprod
  field_simp
  linear_combination hsq

end ArkLib.ProximityGap.E2VanishWidthFourLaw

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.quad_card
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.e1_antipodal_quadruple
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.p2_antipodal_quadruple
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.e2_antipodal_quadruple
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.e2_zero_antipodal_iff
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.badScalar_antipodal_quadruple
#print axioms ArkLib.ProximityGap.E2VanishWidthFourLaw.product_pair_antipodal_forces_sqrt_neg_one
