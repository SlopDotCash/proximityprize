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
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Rudnev's point–plane incidence bound over `Fᵍ³`

This file states **Rudnev's point–plane incidence theorem** over a finite field, the incidence-
geometric engine behind the sharpest sum-product / exponential-sum estimates (in particular the
Bourgain–Glibichuk–Konyagin–type bounds consumed by the proximity-gap formalization).

## The theorem (Rudnev, *Combinatorica* 2018)

Rudnev's point–plane theorem ([arXiv:1407.0426](https://arxiv.org/abs/1407.0426), Theorem 3) is
stated over any field `F` of characteristic `p ≠ 2`: for a set `P` of `m` points and a set `Π` of
`n` planes with `m ≥ n`, and `n = O(p²)` when `p > 0`,

  `I(P, Π) = #{(x, π) ∈ P × Π : x lies on π} = O(m · √n + m · k)`,

where `k` is the **maximum number of collinear planes** of `Π` (planes through one common line).
The collinearity term `m · k` cannot be dropped: a pencil of planes through a line containing all
points has `I = m · n`. The bound has implicit absolute constants (`C` for the `O`, and `c₀` in
`n ≤ c₀ · p²`); a statement about a *single* finite field with free constants would be trivially
true, so the faithful formal target `RudnevIncidenceTheorem` quantifies the constants outside all
finite fields.

### Correction of an earlier encoding (audit L57)

An earlier version of this file carried as its "core" the bound
`I(P, Π) ≤ m·n/q + √(m·n·q) + n` under only the cardinality guards `m ≤ n ≤ q·m` (the header then
claimed that these guards rule out a dominating pencil). That predicate is **false**: over `F₅` the
five points `(t, 0, 0)` and the six distinct normalized planes `y + a·z = 0` (`a ∈ F₅`) and `z = 0`
all contain the `x`-axis, giving `I = 30 > 12 + √150`. It is kept below only under the explicit name
`NaiveIncidenceBound`, together with the kernel-checked refutation
`not_naiveIncidenceBound_zmod5`; the named core is now `RudnevIncidenceCore`, which carries
Rudnev's collinearity parameter, characteristic restriction and genuine-plane condition.

## What is proved here, and what is carried as a named core

The proof of the `m · √n` saving genuinely requires algebraic geometry — the **Klein quadric /
Cayley–Klein correspondence** that turns lines in `F³` into points of a quadric in `P⁵`, followed
by an incidence count on that quadric. That heart is **not in Mathlib** and is carried here as the
named predicate `RudnevIncidenceCore C c₀ F` (a `def ... : Prop`, never a hidden `sorry`); the
published theorem is `RudnevIncidenceTheorem := ∃ C c₀, 0 < c₀ ∧ ∀ finite F, RudnevIncidenceCore
C c₀ F` (restricted here to finite fields).

Everything **elementary** is proved axiom-clean:

* `Rudnev.incidences_eq_sum_pointDeg` / `incidences_eq_sum_planeDeg` — the **flag double-count**:
  `I(P,Π) = ∑_{x∈P} deg(x) = ∑_{π∈Π} deg(π)`, where `deg(x)` is the number of planes through `x`
  and `deg(π)` the number of points on `π`. Pure `sum_card_fiberwise`.
* `Rudnev.sq_incidences_le` — the **Cauchy–Schwarz reduction**: `I(P,Π)² ≤ m · ∑_x deg(x)²`.
* `Rudnev.planesThrough_card` — over **all** coefficient vectors `F⁴`, a fixed point lies on
  exactly `q³` of them.
* `Rudnev.incidence_bound` — the **conditional main theorem**: assuming `RudnevIncidenceCore C c₀ F`
  the bound `I ≤ C · (m·√n + m·k)` holds under Rudnev's hypotheses.
* `Rudnev.not_naiveIncidenceBound_zmod5` — the refutation of the earlier (false) encoding.

## Status

`PARTIAL-PROVEN-PLUS-NAMED-CORE`. The elementary lemmas are proven; the incidence saving is the
named core `RudnevIncidenceCore`, whose content is Rudnev's published theorem (not formalized).

## References

* M. Rudnev, *On the number of incidences between points and planes in three dimensions*,
  Combinatorica 38 (2018), 219–254.
* M. Rudnev, arXiv:1407.0426 (Theorem 3 and abstract).
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

/-- A coefficient vector `π = (a, b, c, d)` is a **normalized genuine plane** if its normal
`(a, b, c)` is nonzero and its first nonzero normal coordinate equals `1`. Distinct normalized
vectors represent distinct affine planes, so a `Finset` of them is a genuine set of planes (this
excludes the zero vector, the empty "planes" `(0, 0, 0, d)` and scalar duplicates). -/
def IsNormalizedPlane (π : Plane F) : Prop :=
  π 0 = 1 ∨ (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 0 ∧ π 1 = 0 ∧ π 2 = 1)

instance (π : Plane F) : Decidable (IsNormalizedPlane π) := by
  unfold IsNormalizedPlane; infer_instance

/-- The plane `π` contains the affine line `{a + t·v : t ∈ F}` (for a direction `v ≠ 0`): the base
point lies on `π` and the direction is orthogonal to the normal of `π`. -/
def ContainsLine (π : Plane F) (a v : Point F) : Prop :=
  Inc a π ∧ π 0 * v 0 + π 1 * v 1 + π 2 * v 2 = 0

instance (π : Plane F) (a v : Point F) : Decidable (ContainsLine π a v) := by
  unfold ContainsLine; infer_instance

/-- **Rudnev's collinearity parameter** `k`: the maximum number of planes of `Pl` containing a
common affine line (lines given by a base point and a nonzero direction). -/
def maxCollinearPlanes (Pl : Finset (Plane F)) : ℕ :=
  ((Finset.univ : Finset (Point F × Point F)).filter (fun av => av.2 ≠ 0)).sup
    (fun av => #{π ∈ Pl | ContainsLine π av.1 av.2})

/-- **DEEP CORE (Rudnev's point–plane incidence bound, with constants `C`, `c₀`).**

Over the finite field `F` of characteristic `p = ringChar F ≠ 2`: for every finite set `P` of
points and every finite set `Pl` of normalized genuine planes with `#Pl ≤ #P` and
`#Pl ≤ c₀ · p²`,

  `I(P, Pl) ≤ C · (#P · √#Pl + #P · k)`, where `k = maxCollinearPlanes Pl`.

This is the finite-field instance of [Rudnev 2018, Theorem 3]. For a *fixed* finite field and free
`C` it is trivially satisfiable, so the meaningful target is `RudnevIncidenceTheorem`, which fixes
`C` and `c₀` uniformly over all finite fields. The Klein-quadric proof is **not** available in
Mathlib; this is recorded as a hypothesis (`def ... : Prop`), never as a `sorry`. -/
def RudnevIncidenceCore (C c₀ : ℝ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ringChar F ≠ 2 →
  ∀ (P : Finset (Point F)) (Pl : Finset (Plane F)),
    (∀ π ∈ Pl, IsNormalizedPlane π) →
    #Pl ≤ #P → (#Pl : ℝ) ≤ c₀ * (ringChar F : ℝ) ^ 2 →
      (incidences P Pl : ℝ)
        ≤ C * ((#P : ℝ) * Real.sqrt (#Pl : ℝ) + (#P : ℝ) * (maxCollinearPlanes Pl : ℝ))

/-- **Rudnev's theorem over finite fields (uniform constants).** There are absolute constants
`C` and `c₀ > 0` such that `RudnevIncidenceCore C c₀ F` holds for every finite field `F`
(in `Type`). This is the published result (restricted to finite fields); it is not formalized. -/
def RudnevIncidenceTheorem : Prop :=
  ∃ C c₀ : ℝ, 0 < c₀ ∧
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], RudnevIncidenceCore C c₀ F

/-- **Rudnev's point–plane incidence theorem (conditional form).** Assuming the named core
`RudnevIncidenceCore C c₀ F`, the incidence count between `#P ≥ #Pl` points and normalized planes
satisfies `I(P, Pl) ≤ C · (#P · √#Pl + #P · k)` under Rudnev's characteristic restriction. -/
theorem incidence_bound {C c₀ : ℝ} (h : RudnevIncidenceCore C c₀ F) (hchar : ringChar F ≠ 2)
    (P : Finset (Point F)) (Pl : Finset (Plane F)) (hPl : ∀ π ∈ Pl, IsNormalizedPlane π)
    (hnm : #Pl ≤ #P) (hp : (#Pl : ℝ) ≤ c₀ * (ringChar F : ℝ) ^ 2) :
    (incidences P Pl : ℝ)
      ≤ C * ((#P : ℝ) * Real.sqrt (#Pl : ℝ) + (#P : ℝ) * (maxCollinearPlanes Pl : ℝ)) :=
  h hchar P Pl hPl hnm hp

/-! ### The earlier (false) encoding, kept with its refutation (audit L57) -/

/-- **The earlier, false encoding of the core.** `I(P, Pl) ≤ #P·#Pl/q + √(#P·#Pl·q) + #Pl`
under only `#P ≤ #Pl ≤ q·#P`. It omits Rudnev's collinearity parameter and is refuted over `F₅` by
`not_naiveIncidenceBound_zmod5`. Kept only as a documented counterexample target; do **not** use it
as a residual. -/
def NaiveIncidenceBound (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (P : Finset (Point F)) (Pl : Finset (Plane F)),
    #P ≤ #Pl → #Pl ≤ q F * #P →
      (incidences P Pl : ℝ)
        ≤ (#P : ℝ) * (#Pl : ℝ) / (q F : ℝ)
          + Real.sqrt ((#P : ℝ) * (#Pl : ℝ) * (q F : ℝ)) + (#Pl : ℝ)

section NaiveRefutation

private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The five points `(t, 0, 0)` of the `x`-axis over `F₅`. -/
def naiveCounterPoints : Finset (Point (ZMod 5)) :=
  Finset.univ.image (fun t : ZMod 5 => ![t, 0, 0])

/-- Six distinct normalized planes through the `x`-axis over `F₅`: `y + a·z = 0` and `z = 0`. -/
def naiveCounterPlanes : Finset (Plane (ZMod 5)) :=
  insert ![0, 0, 1, 0] (Finset.univ.image (fun a : ZMod 5 => ![0, 1, a, 0]))

theorem naiveCounter_counts :
    naiveCounterPoints.card = 5 ∧ naiveCounterPlanes.card = 6 ∧
      incidences naiveCounterPoints naiveCounterPlanes = 30 := by
  decide

theorem naiveCounterPlanes_normalized :
    ∀ π ∈ naiveCounterPlanes, IsNormalizedPlane π := by
  intro π hπ
  simp only [naiveCounterPlanes, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hπ
  rcases hπ with rfl | ⟨a, rfl⟩
  · right; right; simp
  · right; left; simp

/-- **Refutation of the earlier encoding (audit L57).** `NaiveIncidenceBound (ZMod 5)` is false:
five collinear points and six normalized planes through their line give `30` incidences, while the
claimed right side is `6 + √150 + 6 < 30`. -/
theorem not_naiveIncidenceBound_zmod5 : ¬ NaiveIncidenceBound (ZMod 5) := by
  intro h
  have hb := h naiveCounterPoints naiveCounterPlanes (by decide) (by decide)
  rw [naiveCounter_counts.1, naiveCounter_counts.2.1, naiveCounter_counts.2.2] at hb
  norm_num [q] at hb
  have hs : Real.sqrt (150 : ℝ) ^ 2 = 150 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (150 : ℝ)]

end NaiveRefutation

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
#print axioms Rudnev.not_naiveIncidenceBound_zmod5
