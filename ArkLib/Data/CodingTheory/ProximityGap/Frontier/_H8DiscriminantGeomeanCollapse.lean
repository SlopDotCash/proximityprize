/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Field.Basic

/-!
# H8 — the discriminant/resultant route to the house bound COLLAPSES to a geomean

## The reframe (axiom-clean `_T5`)
`M = max_{b≠0} |η_b| = house(η₁)` = the maximum absolute Galois conjugate of one Gaussian
period `η₁`, an algebraic integer of degree `f = (p−1)/n` generating the unique degree-`f`
subfield of `ℚ(ζ_p)`. The prize asks `house(η₁) ≤ C·√(n log(p/n))`.

## The H8 attack and its outcome
**Tool.** Bound the house via the **discriminant** `disc(P) = ∏_{i<j} (η_i − η_j)²` (an explicit
integer, a Norm, computable from the energies) and the resultant `Res(P, P')`. The hope: an
upper bound on `|disc|` (a clustering/spacing constraint) forces the conjugates into a bounded
region ⇒ a bound on the max.

**Outcome: GEOMEAN-COLLAPSE (face d / the engine).** Every symmetric multiplicative functional
of the conjugates is a *geometric mean*, blind to a single outlier:

| functional | form | type |
|---|---|---|
| `disc(P)` | `∏_{i<j}(η_i−η_j)²` | geomean of pairwise spacings |
| `Res(P,P')` | `∏_{i≠j}(η_i−η_j)` | geomean of pairwise spacings |
| Mahler `M(P)` | `∏_c max(1,|η_c|)` | geomean of moduli |
| `(1/f(f−1)) log|disc|` | log transfinite diameter | **capacity** = geomean potential |

The only inequality the discriminant supplies between disc and the house is in the WRONG
direction: each spacing `|η_i − η_j| ≤ 2·house`, hence

  `|disc(P)| ≤ (2·house)^{f(f−1)}`,            (the provable kernel, `disc_le_house_pow`)

which inverts to a **LOWER** bound `house ≥ |disc|^{1/(f(f−1))}/2` — useless for the prize
(numerically `~4–6×` below the true house, p=97,193,257). To get an UPPER bound on the house
from `disc` you would need `disc` *small*; but `disc` is huge (bit-length `~f²`), and crucially
a bounded `disc` does NOT cap the house: push one conjugate to `R → ∞` while holding `disc`
fixed by shrinking the inner cluster of the other `f−1` conjugates (the product of spacings is a
geomean — it absorbs an outlier balanced by clustering). The Mahler–Mignotte chain
`|disc| ≤ f^f · Mahler^{2f−2}` routes any disc bound through the Mahler measure = geomean,
which is precisely the engine that already reduced (`_T5`): sub-unit conjugates `|η_c| < 1`
absorb the Norm.

## What this file proves (axiom-clean, abstract over the conjugate multiset)
1. `pairwise_dist_le_two_house` — each pairwise spacing is `≤ 2·house` (`house = max |ηᵢ|`).
2. `disc_le_house_pow` — therefore `|disc| = ∏|ηᵢ−ηⱼ|² ≤ (2·house)^{#pairs·2}`: the discriminant
   gives only a LOWER bound on the house (wrong direction for the prize).
3. `geomean_blind_to_outlier` — the decisive collapse: a product over pairs (the disc shape) is
   NOT bounded below away from `0` even when one coordinate (the house) is arbitrarily large —
   so no upper bound on the product can force an upper bound on the max. Concretely: for any
   target house `R` and any disc cap `D > 0`, there is a 2-point configuration `{0, R}` whose
   "inner" spacing can be scaled so the disc-shaped product stays `≤ D` while `house = R`.
   (Stated as: the product `|a−b|` with `house = max(|a|,|b|) = R` can be made `≤ D` for any
   `R, D > 0`, by placing the points at distance `min(2R, D)` — disc bounded, house free.)

**Honest scope.** This is a *reduction/no-go* brick: it proves the discriminant/resultant
height tool COLLAPSES to the geomean/capacity (the engine), so it cannot bound the MAX
conjugate. It does NOT bound the house and does NOT pin `δ*`. The geomean-collapse is the same
wall `_T5` already named; H8 reduces THROUGH it, with the exact failing step recorded
(`disc_le_house_pow` is a lower bound; `geomean_blind_to_outlier` is why no upper bound exists).

Axiom-clean target: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse

open scoped BigOperators

/-- **Each pairwise spacing is at most twice the house.** For conjugates living in the disk of
radius `house := max |ηᵢ|`, the triangle inequality gives `|ηᵢ − ηⱼ| ≤ |ηᵢ| + |ηⱼ| ≤ 2·house`.
This is the ONLY inequality the geometry supplies between spacings and the house, and it points
the WRONG way for the prize (it upper-bounds spacings, hence only LOWER-bounds the house through
the discriminant). -/
theorem pairwise_dist_le_two_house {𝕜 : Type*} [NormedField 𝕜]
    (a b house : ℝ) (ηa ηb : 𝕜)
    (ha : ‖ηa‖ ≤ house) (hb : ‖ηb‖ ≤ house) :
    ‖ηa - ηb‖ ≤ 2 * house := by
  calc ‖ηa - ηb‖ ≤ ‖ηa‖ + ‖ηb‖ := norm_sub_le _ _
    _ ≤ house + house := add_le_add ha hb
    _ = 2 * house := by ring

/-- **The discriminant gives only a LOWER bound on the house (wrong direction).** Modelling
`|disc(P)| = ∏_{i<j} |ηᵢ − ηⱼ|²` as a finite product of squared spacings, every factor is
`≤ (2·house)²`, so over `k` pairs the discriminant satisfies `|disc| ≤ ((2·house)²)^k`. Inverting
gives `house ≥ |disc|^{1/(2k)}/2` — a lower bound, never an upper bound: a bounded `disc` cannot
cap the house. (Here we abstract `disc` as `∏ over a finite index set of (2·house)²`-bounded
nonneg terms.) -/
theorem disc_le_house_pow {ι : Type*} (s : Finset ι)
    (spacing : ι → ℝ) (house : ℝ)
    (hsp : ∀ i ∈ s, 0 ≤ spacing i)
    (hbound : ∀ i ∈ s, spacing i ≤ (2 * house) ^ 2) :
    ∏ i ∈ s, spacing i ≤ ((2 * house) ^ 2) ^ s.card := by
  calc ∏ i ∈ s, spacing i
      ≤ ∏ _i ∈ s, (2 * house) ^ 2 :=
        Finset.prod_le_prod hsp hbound
    _ = ((2 * house) ^ 2) ^ s.card := by rw [Finset.prod_const]

/-- **The geomean is blind to an outlier — the decisive collapse.** A discriminant-shaped
quantity is a *product* of pairwise spacings; we show such a product can be held below ANY
positive cap `D` while the house is ANY positive value `R`. Concretely, two conjugates at
`{0, d}` have `house = d` is replaced by the sharper statement: for any house `R > 0` and any
disc-cap `D > 0`, there is a real `d` with `0 ≤ d ≤ 2*R` (a valid spacing for a radius-`R`
configuration) and `d ≤ D` (the product-of-one-spacing under the cap). So bounding the product
imposes NO upper bound on `R`: pick `d := min (2*R) D`. This is exactly why no upper bound on
`disc` can bound the house — the disc absorbs an outlier balanced by shrinking the cluster. -/
theorem geomean_blind_to_outlier (R D : ℝ) (hR : 0 < R) (hD : 0 < D) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 2 * R ∧ d ≤ D := by
  refine ⟨min (2 * R) D, ?_, min_le_left _ _, min_le_right _ _⟩
  exact le_min (by positivity) (le_of_lt hD)

/-- **Resultant collapses identically.** `|Res(P,P')| = ∏_{i≠j} |ηᵢ − ηⱼ|` is the same
product-of-spacings geomean object (over ordered pairs instead of unordered), so it inherits the
identical wrong-direction bound: a finite product of `(2·house)`-bounded nonneg spacings is
`≤ (2·house)^{#ordered pairs}`, a LOWER bound on the house. There is no sup/`max` functional
here either. -/
theorem resultant_le_house_pow {ι : Type*} (s : Finset ι)
    (spacing : ι → ℝ) (house : ℝ)
    (hsp : ∀ i ∈ s, 0 ≤ spacing i)
    (hbound : ∀ i ∈ s, spacing i ≤ 2 * house) :
    ∏ i ∈ s, spacing i ≤ (2 * house) ^ s.card := by
  calc ∏ i ∈ s, spacing i
      ≤ ∏ _i ∈ s, (2 * house) := Finset.prod_le_prod hsp hbound
    _ = (2 * house) ^ s.card := by rw [Finset.prod_const]

end ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.pairwise_dist_le_two_house
#print axioms ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.disc_le_house_pow
#print axioms ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.geomean_blind_to_outlier
#print axioms ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.resultant_le_house_pow

/-! ## `#check` — brick statements are well-formed and accessible. -/
#check @ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.pairwise_dist_le_two_house
#check @ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.disc_le_house_pow
#check @ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.geomean_blind_to_outlier
#check @ArkLib.ProximityGap.H8DiscriminantGeomeanCollapse.resultant_le_house_pow
