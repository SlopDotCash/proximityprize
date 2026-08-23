/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADualPencilLaw

/-!
# The structured incidence census (#357 round 8): horizontal and vertical circuit families

The pencil criterion (`dependent_iff_collinear`) reduces the wide circuits of the window's
collision matroid to collinear triples of pair-points `(e, m) = (sum, product)`. Two line
families are *structural* — they exist for symmetry reasons and account for the bulk of
the smooth-domain census (`24` of `μ₈`'s `40`):

* `dependent_of_equal_products` — **horizontal lines**: three disjoint pairs with equal
  products have dependent duals (their points share the `m`-coordinate — collinear for
  free). Over `μ_n` the product of `{ζ^i, ζ^j}` is `ζ^{i+j}`: every *exponent-sum class*
  is a horizontal family (`equal_products_of_exponent_sum`), giving the `20` horizontal
  circuits of `μ₈` — at every scale `n`, a closed-form census.
* `dependent_of_equal_sums` — **vertical lines**: three disjoint pairs with equal sums
  have dependent duals. Over `μ_n` (n even) the antipodal pairs `{x, −x}` all have sum
  `0` (`antipodal_pair_sum_zero`), giving the `4` vertical circuits of `μ₈`.

Both corollaries hold for **every** evaluation domain and **every** scale — the
production-scale structured census is closed-form. What remains open (the round-8(b)
target, where the genuinely new arithmetic lives) is the *slanted* family: cross-class
collinearities of the configuration `{(ζ^i + ζ^j, ζ^{i+j})}` — sections of Dickson-type
curves (`m = ζ^s` fixed ⟹ `e = ζ^j + ζ^{s−j}`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-7 pencil-law comment); `MCADualPencilLaw.lean`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ProximityGap.MCAIncidenceCensus

open ProximityGap.MCADualPencilLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable (domain : ι ↪ F) {a a' b b' c c' : ι}

/-- **The horizontal family.** Three disjoint pairs with equal products carry a wide
circuit: their `(e,m)`-points share the `m`-coordinate, hence are collinear. -/
theorem dependent_of_equal_products (h6 : Distinct6 a a' b b' c c')
    (h1 : domain a * domain a' = domain b * domain b')
    (h2 : domain a * domain a' = domain c * domain c') :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c, c'} i
        + γ * dualVec domain {b, b', c, c'} i = 0 := by
  rw [dependent_iff_collinear domain h6]
  rw [← h1, ← h2]
  ring

/-- **The vertical family.** Three disjoint pairs with equal sums carry a wide circuit:
their `(e,m)`-points share the `e`-coordinate. -/
theorem dependent_of_equal_sums (h6 : Distinct6 a a' b b' c c')
    (h1 : domain a + domain a' = domain b + domain b')
    (h2 : domain a + domain a' = domain c + domain c') :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c, c'} i
        + γ * dualVec domain {b, b', c, c'} i = 0 := by
  rw [dependent_iff_collinear domain h6]
  rw [← h1, ← h2]
  ring

/-- **The μ_n horizontal supply**: root-of-unity pairs in one exponent-sum class share
their product — `ζ^i · ζ^j = ζ^{i+j}` depends only on `i + j`. -/
theorem equal_products_of_exponent_sum {ζ : F} {i j i' j' : ℕ}
    (hsum : i + j = i' + j') :
    (ζ ^ i) * (ζ ^ j) = (ζ ^ i') * (ζ ^ j') := by
  rw [← pow_add, ← pow_add, hsum]

/-- The exponent-sum classes wrap modulo the order: `ζ^i·ζ^j = ζ^{i'}·ζ^{j'}` whenever
`i + j ≡ i' + j' (mod n)` for `ζ^n = 1`. -/
theorem equal_products_of_exponent_sum_mod {ζ : F} {n i j i' j' : ℕ}
    (hζ : ζ ^ n = 1) (hmod : (i + j) % n = (i' + j') % n) :
    (ζ ^ i) * (ζ ^ j) = (ζ ^ i') * (ζ ^ j') := by
  rw [← pow_add, ← pow_add]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hmod
    rw [hmod]
  · calc ζ ^ (i + j) = ζ ^ (n * ((i + j) / n) + (i + j) % n) := by
          rw [Nat.div_add_mod]
      _ = (ζ ^ n) ^ ((i + j) / n) * ζ ^ ((i + j) % n) := by
          rw [pow_add, pow_mul]
      _ = ζ ^ ((i' + j') % n) := by rw [hζ, one_pow, one_mul, hmod]
      _ = (ζ ^ n) ^ ((i' + j') / n) * ζ ^ ((i' + j') % n) := by
          rw [hζ, one_pow, one_mul]
      _ = ζ ^ (i' + j') := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]

/-- **The μ_n vertical (antipodal) supply**: antipodal pairs `{x, −x}` all have sum
zero. -/
theorem antipodal_pair_sum_zero (x y : F) (hx : y = -x) : x + y = 0 := by
  rw [hx]
  ring

/-- **The structured-census package for smooth domains**: any three disjoint antipodal
pairs of any domain are a wide circuit (vertical family at `e = 0`). -/
theorem dependent_of_antipodal_triple (h6 : Distinct6 a a' b b' c c')
    (h1 : domain a' = -domain a) (h2 : domain b' = -domain b)
    (h3 : domain c' = -domain c) :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c, c'} i
        + γ * dualVec domain {b, b', c, c'} i = 0 := by
  apply dependent_of_equal_sums domain h6
  · rw [antipodal_pair_sum_zero (domain a) (domain a') h1,
      antipodal_pair_sum_zero (domain b) (domain b') h2]
  · rw [antipodal_pair_sum_zero (domain a) (domain a') h1,
      antipodal_pair_sum_zero (domain c) (domain c') h3]

/-- **The slanted family (the μ_n-specific lines).** One antipodal pair `{w, −w}` and two
difference-`d` root-of-unity pairs `{ζ^i, ζ^{i+d}}`, `{ζ^j, ζ^{j+d}}` are a wide circuit
whenever the **exponent relation** `w² = ζ^{i+j+d}` holds (over `μ_n`: `2k ≡ i+j+d
(mod n)` for `w = ±ζ^k`): the collinearity determinant telescopes to zero by pure
exponent arithmetic. These are the `16` slanted circuits of `μ₈` (probe-classified:
every slanted line passes through exactly one vertical-axis point), completing the
`20 + 4 + 16 = 40` census. -/
theorem dependent_of_slanted (h6 : Distinct6 a a' b b' c c') {ζ w : F} {i j d : ℕ}
    (hva : domain a = w) (hva' : domain a' = -w)
    (hvb : domain b = ζ ^ i) (hvb' : domain b' = ζ ^ (i + d))
    (hvc : domain c = ζ ^ j) (hvc' : domain c' = ζ ^ (j + d))
    (hw : w * w = ζ ^ (i + j + d)) :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i', α * dualVec domain {a, a', b, b'} i'
        + β * dualVec domain {a, a', c, c'} i'
        + γ * dualVec domain {b, b', c, c'} i' = 0 := by
  rw [dependent_iff_collinear domain h6]
  rw [hva, hva', hvb, hvb', hvc, hvc']
  linear_combination (ζ ^ i * ζ ^ d + ζ ^ i - ζ ^ j * ζ ^ d - ζ ^ j) * hw

/-- **The horizontal stratum is exactly the exponent-sum classes (upper half,
unconditional).** Two root-of-unity pairs share their product **iff** their exponent sums
agree modulo the order. With `dependent_of_equal_products`, the horizontal census at every
scale is exactly `Σ_s C(η_s, 3)` over exponent-sum classes — no field-size threshold
enters the horizontal stratum. -/
theorem equal_products_iff_same_class {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) {i j i' j' : ℕ} :
    (ζ ^ i) * (ζ ^ j) = (ζ ^ i') * (ζ ^ j') ↔ (i + j) % n = (i' + j') % n := by
  constructor
  · intro h
    have hred : ∀ A : ℕ, ζ ^ A = ζ ^ (A % n) := by
      intro A
      conv_lhs => rw [← Nat.div_add_mod A n]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    rw [← pow_add, ← pow_add, hred (i + j), hred (i' + j')] at h
    exact hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h
  · intro h
    exact equal_products_of_exponent_sum_mod hζ.pow_eq_one h

/-! ## Source audit -/

#print axioms dependent_of_equal_products
#print axioms dependent_of_equal_sums
#print axioms equal_products_of_exponent_sum_mod
#print axioms dependent_of_antipodal_triple
#print axioms dependent_of_slanted
#print axioms equal_products_iff_same_class

end ProximityGap.MCAIncidenceCensus
