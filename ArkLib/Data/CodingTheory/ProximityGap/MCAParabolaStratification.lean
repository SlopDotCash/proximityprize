/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAIncidenceCensus

/-!
# The parabola stratification (#357 round 9): the geometry of the circuit configuration

The pencil criterion places the wide circuits of the window's collision matroid on
collinear triples of the pair-point configuration `Γ_n = {(ζ^i + ζ^j, ζ^{i+j})} ⊆ F²`.
This file proves the **geometric stratification** that organizes the entire census:

* `parabola_law` — every difference-`d` pair lies on the parabola
  `e² · ζ^d = (1 + ζ^d)² · m`: the configuration is a union of `⌊n/2⌋` explicit
  parabolas, one per difference class (the antipodal class `d = n/2` degenerating to the
  vertical line `e = 0`, since `1 + ζ^{n/2} = 0`).
* `parabola_det_factor` / `independent_of_same_parabola` — **the negative census law**: a
  nondegenerate parabola is strictly convex — the collinearity determinant of three of
  its points factors as a Vandermonde, so **three pairs of one (non-antipodal)
  difference class never form a wide circuit**. Probe-verified: zero violations at `μ₈`
  and `μ₁₆`.

Together with the supply families (`MCAIncidenceCensus`): every wide circuit uses at most
two points per nondegenerate parabola, and the full census is the line-incidence
distribution `Σ_L C(N_L, 3)` of a union of parabolas with root-of-unity points — the
horizontal lines meet each parabola once (`N = ⌊n/2⌋`), the vertical line is the
degenerate parabola itself (`N = n/2`), and slanted lines meet each parabola at most
twice with incidence governed by bounded vanishing sums of `2^k`-th roots (the
antipodal multiset law). The production-scale census is the solution census of these
line–parabola systems.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-8/9 comments); `MCADualPencilLaw.lean`, `MCAIncidenceCensus.lean`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ProximityGap.MCAParabolaStratification

open ProximityGap.MCADualPencilLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The parabola law.** A difference-`d` root-of-unity pair `{ζ^i, ζ^{i+d}}` satisfies
`e² · ζ^d = (1 + ζ^d)² · m`: each difference class lies on one explicit parabola. -/
theorem parabola_law (ζ : F) (i d : ℕ) :
    (ζ ^ i + ζ ^ (i + d)) ^ 2 * ζ ^ d = (1 + ζ ^ d) ^ 2 * (ζ ^ i * ζ ^ (i + d)) := by
  rw [pow_add]
  ring

/-- **The Vandermonde factorization of the collinearity determinant on a parabola.** For
three points with `eᵢ² = c·mᵢ`: the determinant times `c` is the Vandermonde product. -/
theorem parabola_det_factor {c e₁ e₂ e₃ m₁ m₂ m₃ : F}
    (h1 : e₁ ^ 2 = c * m₁) (h2 : e₂ ^ 2 = c * m₂) (h3 : e₃ ^ 2 = c * m₃) :
    ((e₂ - e₁) * (m₃ - m₁) - (m₂ - m₁) * (e₃ - e₁)) * c
      = (e₂ - e₁) * (e₃ - e₁) * (e₃ - e₂) := by
  linear_combination (e₁ - e₂) * h3 + (e₃ - e₁) * h2 + (e₂ - e₃) * h1

/-- **The negative census law.** Three disjoint pairs lying on one *nondegenerate*
parabola (`eᵢ² = c·mᵢ`, `c ≠ 0`) with distinct `e`-coordinates are **never** a wide
circuit: the Vandermonde factor is nonzero, so the points are not collinear. -/
theorem independent_of_same_parabola (domain : ι ↪ F) {a a' b b' c' c'' : ι}
    (h6 : Distinct6 a a' b b' c' c'') {c : F} (hc : c ≠ 0)
    (h1 : (domain a + domain a') ^ 2 = c * (domain a * domain a'))
    (h2 : (domain b + domain b') ^ 2 = c * (domain b * domain b'))
    (h3 : (domain c' + domain c'') ^ 2 = c * (domain c' * domain c''))
    (he12 : domain a + domain a' ≠ domain b + domain b')
    (he13 : domain a + domain a' ≠ domain c' + domain c'')
    (he23 : domain b + domain b' ≠ domain c' + domain c'') :
    ¬ ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c', c''} i
        + γ * dualVec domain {b, b', c', c''} i = 0 := by
  rw [dependent_iff_collinear domain h6]
  intro hcol
  -- the determinant vanishes, but its `c`-multiple is a nonzero Vandermonde
  have hdet : ((domain b + domain b') - (domain a + domain a'))
      * ((domain c' * domain c'') - (domain a * domain a'))
      - ((domain b * domain b') - (domain a * domain a'))
      * ((domain c' + domain c'') - (domain a + domain a')) = 0 := by
    linear_combination hcol
  have hfac := parabola_det_factor h1 h2 h3
  rw [show ((domain b + domain b') - (domain a + domain a'))
      * ((domain c' * domain c'') - (domain a * domain a'))
      - ((domain b * domain b') - (domain a * domain a'))
      * ((domain c' + domain c'') - (domain a + domain a'))
      = ((domain b + domain b') - (domain a + domain a'))
        * ((domain c' * domain c'') - (domain a * domain a'))
        - ((domain b * domain b') - (domain a * domain a'))
        * ((domain c' + domain c'') - (domain a + domain a')) from rfl] at hfac
  rw [hdet, zero_mul] at hfac
  have hV : ((domain b + domain b') - (domain a + domain a'))
      * ((domain c' + domain c'') - (domain a + domain a'))
      * ((domain c' + domain c'') - (domain b + domain b')) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact sub_ne_zero.mpr (Ne.symm he12)
    · exact sub_ne_zero.mpr (Ne.symm he13)
    · exact sub_ne_zero.mpr (Ne.symm he23)
  exact hV hfac.symm

/-- **The μ_n instantiation**: three disjoint pairs of one non-antipodal difference class
(`1 + ζ^d ≠ 0`, `ζ ≠ 0`) with distinct `e`-coordinates are never a wide circuit. -/
theorem independent_of_same_diff (domain : ι ↪ F) {a a' b b' c' c'' : ι}
    (h6 : Distinct6 a a' b b' c' c'') {ζ : F} (hζ : ζ ≠ 0) {i j k d : ℕ}
    (hd : (1 : F) + ζ ^ d ≠ 0)
    (hva : domain a = ζ ^ i) (hva' : domain a' = ζ ^ (i + d))
    (hvb : domain b = ζ ^ j) (hvb' : domain b' = ζ ^ (j + d))
    (hvc : domain c' = ζ ^ k) (hvc' : domain c'' = ζ ^ (k + d))
    (he12 : domain a + domain a' ≠ domain b + domain b')
    (he13 : domain a + domain a' ≠ domain c' + domain c'')
    (he23 : domain b + domain b' ≠ domain c' + domain c'') :
    ¬ ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i', α * dualVec domain {a, a', b, b'} i'
        + β * dualVec domain {a, a', c', c''} i'
        + γ * dualVec domain {b, b', c', c''} i' = 0 := by
  have hzd : ζ ^ d ≠ 0 := pow_ne_zero d hζ
  have hcne : ((1 : F) + ζ ^ d) ^ 2 / ζ ^ d ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hd) hzd
  apply independent_of_same_parabola domain h6 hcne _ _ _ he12 he13 he23
  · rw [hva, hva', div_mul_eq_mul_div, eq_div_iff hzd, mul_comm ((ζ ^ i + ζ ^ (i + d)) ^ 2) (ζ ^ d)]
    rw [mul_comm]
    exact parabola_law ζ i d
  · rw [hvb, hvb', div_mul_eq_mul_div, eq_div_iff hzd, mul_comm ((ζ ^ j + ζ ^ (j + d)) ^ 2) (ζ ^ d)]
    rw [mul_comm]
    exact parabola_law ζ j d
  · rw [hvc, hvc', div_mul_eq_mul_div, eq_div_iff hzd, mul_comm ((ζ ^ k + ζ ^ (k + d)) ^ 2) (ζ ^ d)]
    rw [mul_comm]
    exact parabola_law ζ k d

/-! ## Source audit -/

#print axioms parabola_law
#print axioms parabola_det_factor
#print axioms independent_of_same_parabola
#print axioms independent_of_same_diff

end ProximityGap.MCAParabolaStratification
