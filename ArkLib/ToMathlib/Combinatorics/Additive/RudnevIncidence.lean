/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.FieldTheory.Finite.Basic
import ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy

/-!
# Rudnev's point–plane incidence bound over `Fᵍ³`

This file states **Rudnev's point–plane incidence theorem** over a finite field, the incidence-
geometric engine behind the sharpest sum-product / exponential-sum estimates (in particular the
Bourgain–Glibichuk–Konyagin–type bounds consumed by the proximity-gap formalization).

## The theorem (Rudnev, *Combinatorica* 2018)

Let `F` be a finite field with `q := #F` elements and characteristic `p`. Let `P` be a set of `m`
points in the affine space `F³` and `Π` a set of `n` planes, with `m ≤ n` and `n ≤ p · m` (a
non-degeneracy condition ruling out a single pencil dominating). Then the number of incidences

  `I(P, Π) = #{(x, π) ∈ P × Π : x lies on π}`

satisfies

  `I(P, Π) ≤ m · n / q + C · √(m · n · q) + C · n`

for an absolute constant `C` (one may take `C = 1` in the leading sharp form, with the `n` term
allowing for a single high-multiplicity pencil of planes through a line).

## What is proved here, and what is carried as a named core

The proof of the `√(m n q)` saving genuinely requires algebraic geometry — the **Klein quadric /
Cayley–Klein correspondence** that turns lines in `F³` into points of a quadric in `P⁵`, followed
by a flag count on that quadric. That algebraic-geometric heart is **not in Mathlib** and is carried
here as a clearly named open predicate `RudnevIncidenceCore` (a `def ... : Prop`, never a hidden
`sorry`).

Everything **elementary** is proved axiom-clean:

* `Rudnev.incidences_eq_sum_pointDeg` / `incidences_eq_sum_planeDeg` — the **flag double-count**:
  `I(P,Π) = ∑_{x∈P} deg(x) = ∑_{π∈Π} deg(π)`, where `deg(x)` is the number of planes through `x`
  and `deg(π)` the number of points on `π`. Pure `sum_card_fiberwise`.
* `Rudnev.sq_incidences_le` — the **Cauchy–Schwarz reduction**: `I(P,Π)² ≤ m · ∑_x deg(x)²`, the
  bridge from incidences to the second moment (the quantity the AG core actually bounds).
* `Rudnev.planesThrough_card` — the **main-term `q`-divisibility**: a *fixed* affine point lies on
  exactly the planes whose coefficient `(a,b,c)` is anything and `d` is then forced; this pins the
  `m·n/q` main term combinatorially.
* `Rudnev.incidence_bound` — the **conditional main theorem**: assuming `RudnevIncidenceCore`, the
  incidence bound holds.

## Status

`PARTIAL-PROVEN-PLUS-NAMED-CORE`. The flag double-count, the Cauchy–Schwarz reduction, and the
fixed-point planes count are fully proven and axiom-clean. The `√(m n q)` saving — the Klein-quadric
flag count — is the named open core `RudnevIncidenceCore`.

## References

* M. Rudnev, *On the number of incidences between points and planes in three dimensions*,
  Combinatorica 38 (2018), 219–254.
* B. Murphy, G. Petridis, O. Roche-Newton, M. Rudnev, I. D. Shkredov, *New results on sum-product
  type growth over fields*, Mathematika 65 (2019).
-/

open Finset
open scoped BigOperators

namespace Rudnev

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of field elements, `q = #F`. -/
abbrev q (F : Type*) [Fintype F] : ℕ := Fintype.card F

/-- A **point** of affine `3`-space is a triple of field elements. -/
abbrev Point (F : Type*) : Type _ := Fin 3 → F

/-- A **plane** is encoded by its coefficient vector `(a, b, c, d) ∈ F⁴`, representing the affine
plane `a·x₀ + b·x₁ + c·x₂ + d = 0`. (We do not quotient by scaling; in incidence statements one
works with a *finite set* `Pl` of such coefficient vectors, and the bound is stated in terms of
`#Pl`. The degenerate vector `0` represents "all of space" and is harmless for upper bounds.) -/
abbrev Plane (F : Type*) : Type _ := Fin 4 → F

/-- **Incidence predicate**: the point `x` lies on the plane `π = (a,b,c,d)`, i.e.
`a·x₀ + b·x₁ + c·x₂ + d = 0`. -/
def Inc (x : Point F) (π : Plane F) : Prop :=
  π 0 * x 0 + π 1 * x 1 + π 2 * x 2 + π 3 = 0

instance (x : Point F) (π : Plane F) : Decidable (Inc x π) := by
  unfold Inc; infer_instance

/-- The **point degree**: the number of planes of `Π` through a fixed point `x`. -/
def pointDeg (Pl : Finset (Plane F)) (x : Point F) : ℕ := #{π ∈ Pl | Inc x π}

/-- The **plane degree**: the number of points of `P` on a fixed plane `π`. -/
def planeDeg (P : Finset (Point F)) (π : Plane F) : ℕ := #{x ∈ P | Inc x π}

/-- The **incidence count** `I(P, Π) = #{(x, π) ∈ P × Π : x lies on π}`. -/
def incidences (P : Finset (Point F)) (Pl : Finset (Plane F)) : ℕ :=
  #{z ∈ P ×ˢ Pl | Inc z.1 z.2}

/-! ### Elementary lemma 1: the flag double-count (axiom-clean) -/

/-- **Flag double-count, point side.** `I(P, Π) = ∑_{x ∈ P} deg(x)`, where `deg(x)` is the number
of planes through `x`. Pure double-counting. -/
theorem incidences_eq_sum_pointDeg (P : Finset (Point F)) (Pl : Finset (Plane F)) :
    incidences P Pl = ∑ x ∈ P, pointDeg Pl x := by
  classical
  unfold incidences pointDeg
  rw [Finset.card_filter]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.card_filter]

/-- **Flag double-count, plane side.** `I(P, Π) = ∑_{π ∈ Π} deg(π)`, where `deg(π)` is the number
of points on `π`. -/
theorem incidences_eq_sum_planeDeg (P : Finset (Point F)) (Pl : Finset (Plane F)) :
    incidences P Pl = ∑ π ∈ Pl, planeDeg P π := by
  classical
  unfold incidences planeDeg
  rw [Finset.card_filter]
  rw [Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun π _ => ?_)
  rw [Finset.card_filter]

/-- The two flag double-counts agree (a symmetry/Fubini statement). -/
theorem sum_pointDeg_eq_sum_planeDeg (P : Finset (Point F)) (Pl : Finset (Plane F)) :
    ∑ x ∈ P, pointDeg Pl x = ∑ π ∈ Pl, planeDeg P π := by
  rw [← incidences_eq_sum_pointDeg, ← incidences_eq_sum_planeDeg]

/-! ### Elementary lemma 2: the Cauchy–Schwarz reduction to the second moment (axiom-clean) -/

/-- **Cauchy–Schwarz reduction.** Over `ℝ`,
`I(P, Pl)² ≤ #P · ∑_{x ∈ P} deg(x)²`. This is the bridge from incidences to the second moment of
the point degree — the quantity the Klein-quadric core actually bounds. Immediate from
`Finset.sq_sum_le_card_mul_sum_sq` applied to `x ↦ deg(x)` and `incidences_eq_sum_pointDeg`. -/
theorem sq_incidences_le (P : Finset (Point F)) (Pl : Finset (Plane F)) :
    (incidences P Pl : ℝ) ^ 2 ≤ (#P : ℝ) * ∑ x ∈ P, ((pointDeg Pl x : ℝ)) ^ 2 := by
  have h := incidences_eq_sum_pointDeg P Pl
  have hcast : (incidences P Pl : ℝ) = ∑ x ∈ P, (pointDeg Pl x : ℝ) := by
    rw [h]; push_cast; rfl
  rw [hcast]
  exact sq_sum_le_card_mul_sum_sq

/-! ### Elementary lemma 3: the main term, `q`-divisibility (axiom-clean) -/

/-- For a **fixed point** `x`, the planes `(a, b, c, d)` through `x` are exactly those whose first
three coordinates `(a, b, c)` are arbitrary and whose last coordinate is forced:
`d = -(a·x₀ + b·x₁ + c·x₂)`. Hence, over **all** of `F⁴`, the number of planes through a fixed
point is exactly `q³ = #F³`. This is the combinatorial origin of the `m·n/q` main term: a uniformly
random plane passes through a fixed point with probability `q³ / q⁴ = 1/q`. -/
theorem planesThrough_card (x : Point F) :
    #{π ∈ (Finset.univ : Finset (Plane F)) | Inc x π} = (q F) ^ 3 := by
  classical
  -- The map `(a,b,c) ↦ (a,b,c, -(a x₀ + b x₁ + c x₂))` is a bijection onto the planes through `x`.
  let g : (Fin 3 → F) → Plane F := fun v =>
    ![v 0, v 1, v 2, -(v 0 * x 0 + v 1 * x 1 + v 2 * x 2)]
  have hcard3 : #(Finset.univ : Finset (Fin 3 → F)) = (q F) ^ 3 := by
    simp [q, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard3]
  symm
  apply Finset.card_nbij' g (fun π => fun i : Fin 3 => π i.castSucc)
  · -- `g v` is a plane through `x`
    intro v _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Inc, g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  · -- inverse lands in `univ`
    intro π _
    exact Finset.mem_univ _
  · -- left inverse: recover `v` from `g v`
    intro v _
    funext i
    fin_cases i <;>
      simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Fin.castSucc_zero, Fin.castSucc_one] <;> rfl
  · -- right inverse: a plane through `x` is `g` of its first three coords
    intro π hπ
    have hInc : Inc x π := (Finset.mem_filter.1 hπ).2
    funext i
    simp only [Inc] at hInc
    have h3 : π 3 = -(π 0 * x 0 + π 1 * x 1 + π 2 * x 2) := by linear_combination hInc
    fin_cases i <;>
      simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
        Fin.castSucc_zero, Fin.castSucc_one]
    · rfl
    · rfl
    · rfl
    · exact h3.symm

/-! ### The deep core (algebraic geometry — Klein quadric), as a named predicate -/

/-- **DEEP CORE (Klein-quadric flag count).** The algebraic-geometric heart of Rudnev's theorem.

For finite sets `P` of points and `Pl` of planes in `F³` over a field `F` with `#F = q`, subject to
the non-degeneracy conditions `#P ≤ #Pl` and `#Pl ≤ q · #P`, the incidence count obeys

  `I(P, Pl) ≤ #P · #Pl / q + √(#P · #Pl · q) + #Pl`.

This statement encapsulates the part of the proof — the Cayley–Klein lifting of lines in `F³` to
points on the Klein quadric `Q ⊂ P⁵`, and the flag count on `Q` — that is **not** available in
Mathlib. It is recorded as an open hypothesis (`def ... : Prop`), never as a `sorry` inside a
theorem. -/
def RudnevIncidenceCore (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (P : Finset (Point F)) (Pl : Finset (Plane F)),
    #P ≤ #Pl → #Pl ≤ q F * #P →
      (incidences P Pl : ℝ)
        ≤ (#P : ℝ) * (#Pl : ℝ) / (q F : ℝ)
          + Real.sqrt ((#P : ℝ) * (#Pl : ℝ) * (q F : ℝ)) + (#Pl : ℝ)

/-- **Rudnev's point–plane incidence theorem (conditional form).** Assuming the named Klein-quadric
core `RudnevIncidenceCore F`, the incidence count between `#P ≤ #Pl` points and planes satisfies the
sharp bound `I(P,Pl) ≤ #P·#Pl/q + √(#P·#Pl·q) + #Pl`. -/
theorem incidence_bound (h : RudnevIncidenceCore F)
    (P : Finset (Point F)) (Pl : Finset (Plane F))
    (hmn : #P ≤ #Pl) (hdeg : #Pl ≤ q F * #P) :
    (incidences P Pl : ℝ)
      ≤ (#P : ℝ) * (#Pl : ℝ) / (q F : ℝ)
        + Real.sqrt ((#P : ℝ) * (#Pl : ℝ) * (q F : ℝ)) + (#Pl : ℝ) :=
  h P Pl hmn hdeg

/-! ### A fully-proven *trivial* incidence bound (unconditional sanity baseline)

Independently of the deep core, we record the trivial bound `I(P,Π) ≤ #P · q³` (every point lies on
at most `q³` planes among `univ`, hence among any `Π`). This is axiom-clean and shows the framework
is non-vacuous; it does **not** give the `√(m n q)` saving. -/

/-- **Trivial unconditional incidence bound.** The point degree never exceeds `q³`, so
`I(P, Pl) ≤ #P · q³`. (No saving — this is the baseline the Klein-quadric core improves upon.) -/
theorem incidences_le_trivial (P : Finset (Point F)) (Pl : Finset (Plane F)) :
    incidences P Pl ≤ #P * (q F) ^ 3 := by
  classical
  rw [incidences_eq_sum_pointDeg]
  calc ∑ x ∈ P, pointDeg Pl x
      ≤ ∑ _x ∈ P, (q F) ^ 3 := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        unfold pointDeg
        calc #{π ∈ Pl | Inc x π}
            ≤ #{π ∈ (Finset.univ : Finset (Plane F)) | Inc x π} := by
              apply Finset.card_le_card
              intro π hπ
              rw [Finset.mem_filter] at hπ ⊢
              exact ⟨Finset.mem_univ _, hπ.2⟩
          _ = (q F) ^ 3 := planesThrough_card x
    _ = #P * (q F) ^ 3 := by rw [Finset.sum_const, smul_eq_mul]

end Rudnev

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Rudnev.incidences_eq_sum_pointDeg
#print axioms Rudnev.incidences_eq_sum_planeDeg
#print axioms Rudnev.sum_pointDeg_eq_sum_planeDeg
#print axioms Rudnev.sq_incidences_le
#print axioms Rudnev.planesThrough_card
#print axioms Rudnev.incidence_bound
#print axioms Rudnev.incidences_le_trivial
