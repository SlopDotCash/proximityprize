/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.ToMathlib.PowerSeriesHenselianA
import ArkLib.ToMathlib.PowerSeriesNewton

/-!
# Hensel / Newton root UNIQUENESS over `k⟦X⟧`

`PowerSeriesHenselianA.lean` and `PowerSeriesNewton.lean` provide *existence* of a Hensel/Newton
lift: a polynomial `f` over `k⟦X⟧` (k a field) with an approximate simple root `a₀`
(`f(a₀) ≡ 0 mod X`, `f'(a₀)` a unit) has an exact root `a ≡ a₀ mod X`.  This file supplies the
companion **uniqueness** statement.

The main result is `hensel_root_unique`: any two exact roots that both reduce to the same
approximation `a₀` modulo `X`, at which the derivative is a unit, are equal.

## Proof idea

Apply the Taylor / `Polynomial.binomExpansion` factorization at the *root* `b`, with increment
`a - b`:
```
f(a) = f(b) + f'(b)·(a-b) + c·(a-b)²
```
Since `f a = f b = 0` this collapses to
```
0 = (a-b) · (f'(b) + c·(a-b)).
```
The cofactor `g := f'(b) + c·(a-b)` is a **unit**:

* `f'(b)` is a unit because `b ≡ a₀ mod X` forces `f'(b) ≡ f'(a₀) mod X` (`isUnit_eval_of_X_dvd`,
  from `PowerSeriesNewton`), and `f'(a₀)` is a unit by hypothesis;
* `c·(a-b)` lies in `span {X}` (the maximal ideal) because `a ≡ b mod X`;
* a unit plus a maximal-ideal element is a unit — over the field `k` this is just
  `PowerSeries.isUnit_iff_constantCoeff`, since the extra term contributes nothing to the constant
  coefficient.

Then `k⟦X⟧` is an integral domain, so `(a-b)·g = 0` with `g` a unit gives `a - b = 0`.

This brick is **L15** of the proximity-prize ingredient-C/D bridge
(`research/proximity-prize/ingredient-D-DAG-2026-06-05.md`): Hensel-lift uniqueness, the substrate
underneath the converse bridge `matching point ⟹ π_z(β R t) = 0` (L14).

Everything is kernel-clean.
-/

set_option linter.style.longLine false

open PowerSeries

namespace ArkLib

variable {k : Type*} [Field k]

/-- If `a` and `b` are both congruent to `a₀` modulo `X` (membership in `span {X}`), then so are
they to each other: `X ∣ a - b`. -/
theorem X_dvd_sub_of_sub_mem_span
    {a b a₀ : PowerSeries k}
    (ha : a - a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (hb : b - a₀ ∈ Ideal.span {(X : PowerSeries k)}) :
    (X : PowerSeries k) ∣ (a - b) := by
  rw [Ideal.mem_span_singleton] at ha hb
  have : a - b = (a - a₀) - (b - a₀) := by ring
  rw [this]
  exact dvd_sub ha hb

/-- **Hensel / Newton root uniqueness over `k⟦X⟧`.**
If `f : (k⟦X⟧)[Y]` has two roots `a`, `b`, both congruent modulo `X` to a common approximation
`a₀` at which the derivative `f'(a₀)` is a unit (the root is *simple* at `a₀`), then `a = b`.

This is the uniqueness companion to `powerSeries_hensel_lift` /
`powerSeries_newton_root` (existence). -/
theorem hensel_root_unique (f : Polynomial (PowerSeries k))
    {a b a₀ : PowerSeries k}
    (ha_root : f.IsRoot a) (hb_root : f.IsRoot b)
    (ha : a - a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (hb : b - a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (hderiv : IsUnit (f.derivative.eval a₀)) :
    a = b := by
  -- `X ∣ a - b`, and (symmetrically) `X ∣ b - a₀`.
  have hXab : (X : PowerSeries k) ∣ (a - b) := X_dvd_sub_of_sub_mem_span ha hb
  -- `f'(b)` is a unit: `b ≡ a₀ mod X`, and the derivative-unit is preserved under congruence.
  -- `isUnit_eval_of_X_dvd` needs `X ∣ a₀ - b` to transport
  -- `IsUnit (f'.eval a₀) → IsUnit (f'.eval b)`.
  have hXa₀b : (X : PowerSeries k) ∣ (a₀ - b) := by
    rw [Ideal.mem_span_singleton] at hb
    have : a₀ - b = -(b - a₀) := by ring
    rw [this]; exact hb.neg_right
  have hub : IsUnit (f.derivative.eval b) :=
    isUnit_eval_of_X_dvd f.derivative hXa₀b hderiv
  -- Taylor factorisation at the root `b`, increment `a - b`.
  obtain ⟨c, hc⟩ := f.binomExpansion b (a - b)
  have hba : b + (a - b) = a := by ring
  rw [hba] at hc
  -- `f a = f b = 0`, so `0 = f'(b)·(a-b) + c·(a-b)²`.
  rw [Polynomial.IsRoot.def] at ha_root hb_root
  rw [ha_root, hb_root, zero_add] at hc
  -- Factor out `(a - b)`: `0 = (a-b) · (f'(b) + c·(a-b))`.
  set g : PowerSeries k := f.derivative.eval b + c * (a - b) with hg_def
  have hfact : (a - b) * g = 0 := by
    rw [hg_def]; rw [eq_comm] at hc; linear_combination hc
  -- The cofactor `g` is a unit: its constant coefficient equals that of `f'(b)` (a unit),
  -- since `X ∣ a - b` kills the `c·(a-b)` contribution to the constant coefficient.
  have hg_unit : IsUnit g := by
    rw [isUnit_iff_constantCoeff] at hub ⊢
    have hcc : constantCoeff (R := k) g = constantCoeff (R := k) (f.derivative.eval b) := by
      rw [hg_def, map_add, map_mul]
      have : constantCoeff (R := k) (a - b) = 0 := by
        rw [← X_dvd_iff]; exact hXab
      rw [this, mul_zero, add_zero]
    rwa [hcc]
  -- `k⟦X⟧` is a domain and `g` a unit, so `a - b = 0`.
  have : a - b = 0 := (IsUnit.mul_left_eq_zero hg_unit).1 hfact
  rwa [sub_eq_zero] at this

/-- **Existence-and-uniqueness over `k⟦X⟧`** (`HenselianLocalRing` route): a monic `f` with an
approximate simple root `a₀` has a *unique* exact root congruent to `a₀` modulo `X`.  Combines
`powerSeries_hensel_lift` (existence) with `hensel_root_unique` (uniqueness). -/
theorem powerSeries_hensel_lift_unique (f : Polynomial (PowerSeries k)) (hf : f.Monic)
    (a₀ : PowerSeries k)
    (h₁ : f.eval a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃! a : PowerSeries k, f.IsRoot a ∧
      a - a₀ ∈ Ideal.span {(X : PowerSeries k)} := by
  obtain ⟨a, ha_root, ha_sub⟩ := powerSeries_hensel_lift f hf a₀ h₁ h₂
  refine ⟨a, ⟨ha_root, ha_sub⟩, ?_⟩
  rintro b ⟨hb_root, hb_sub⟩
  exact hensel_root_unique f hb_root ha_root hb_sub ha_sub h₂

/-- **The lifted root equals the constructive Newton root.**  The exact root produced by the
constructive Newton sequence (`powerSeries_newton_root`) coincides with *any* root congruent to the
approximation `a₀` modulo `X` — uniqueness ties the abstract existence to the explicit sequence.

Concretely: if `a` is the constructive Newton root (`witness` of `powerSeries_newton_root`) and `b`
is any root congruent to `a₀` mod `X`, then `a = b`. -/
theorem newton_root_eq_of_isRoot (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : f.eval a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (h₂ : IsUnit (f.derivative.eval a₀))
    {b : PowerSeries k} (hb_root : f.IsRoot b)
    (hb_sub : b - a₀ ∈ Ideal.span {(X : PowerSeries k)}) :
    (powerSeries_newton_root f a₀ h₁ h₂).choose = b := by
  obtain ⟨ha_root, ha_sub⟩ := (powerSeries_newton_root f a₀ h₁ h₂).choose_spec
  exact hensel_root_unique f ha_root hb_root ha_sub hb_sub h₂

/-- **Constructive existence-and-uniqueness over `k⟦X⟧`** (Newton route): the explicit Newton-limit
root is the *unique* root congruent to `a₀` modulo `X`.  No monicity required — the unit derivative
powers both existence and uniqueness. -/
theorem powerSeries_newton_root_unique (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : f.eval a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃! a : PowerSeries k, f.IsRoot a ∧
      a - a₀ ∈ Ideal.span {(X : PowerSeries k)} := by
  obtain ⟨a, ha_root, ha_sub⟩ := powerSeries_newton_root f a₀ h₁ h₂
  refine ⟨a, ⟨ha_root, ha_sub⟩, ?_⟩
  rintro b ⟨hb_root, hb_sub⟩
  exact hensel_root_unique f hb_root ha_root hb_sub ha_sub h₂

end ArkLib
