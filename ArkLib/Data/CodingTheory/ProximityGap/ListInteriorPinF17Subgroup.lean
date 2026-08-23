/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorTwoSidedF7
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A verified TWO-SIDED interior list-size pin on a genuine SMOOTH domain: `RS[F₁₇, ⟨2⟩, 2]`
# (Issue #232, ROUND 3)

`ListInteriorTwoSidedF7.lean` pins the interior list size of `RS[F₇, F₇, 2]` to `[6,7]` at the
interior radius `δ = 4/7`, but its evaluation domain is the **whole field** `F₇`. The open prize
(ABF26 / Issue #232) is about Reed–Solomon codes on a **smooth domain**: a *multiplicative subgroup*
of `2`-power order — exactly the FRI / STARK setting. This file carries the two-sided interior pin
onto such a genuine smooth domain.

## The instance (smooth domain)

`F = ZMod 17`. The multiplicative group `F₁₇ˣ` is cyclic of order `16`, and `2` is an element of
**order `8`** (a `2`-power), so `L = ⟨2⟩ = {2⁰, 2¹, …, 2⁷} = {1,2,4,8,16,15,13,9}` is the unique
multiplicative subgroup of order `8`. It is *exactly the set of `8`th roots of unity*
`{x : x⁸ = 1}` (`smooth_domain_eq_roots_of_unity`), i.e. a genuine smooth evaluation domain of
`2`-power order, not the full field. We take `k = 2` (degree-`<2` polynomials = lines), so the rate
is `ρ = k/n = 2/8 = 1/4`:

* Johnson radius `1 − √ρ = 1 − √(1/4) = 1/2`;
* capacity radius `1 − ρ = 3/4`;
* the **open gap** is `δ ∈ (1/2, 3/4)`.

The agreement radius `a = 3` (codewords agree with the received word on `≥ 3` of the `8`
coordinates) corresponds to relative distance `δ = (n − a)/n = 5/8 = 0.625`, **strictly interior**
to that gap (`five_eighths_strictly_interior`).

## What is verified here

* `smooth_domain_eq_roots_of_unity`, `D_injective` — the domain `D i = 2^i` is an injective
  embedding of `Fin 8` whose image is precisely the order-`8` multiplicative subgroup (the `8`th
  roots of unity). This is what makes the instance a *smooth-domain* Reed–Solomon code.
* `interior_list_lower_bound_seven` — an **explicit received word**
  `w = (5,15,15,16,2,10,14,11)` and an explicit `7`-element list `L` of distinct RS codewords of
  degree-`<2` polynomials *evaluated on the smooth domain*, each agreeing with `w` on `≥ 3`
  coordinates. So at the interior radius `a = 3` the list size of this smooth-domain code is `≥ 7`.
* `interior_list_upper_bound_nine` — the matching Fisher / Corrádi pair-packing upper bound
  (`reedSolomon_pairPacking_list_bound`, imported, domain-agnostic): any list of distinct
  degree-`<2` RS codewords on `D` agreeing with `w` on `≥ 3` coordinates has `|L| ≤ 9`
  (`|L|·C(3,2) ≤ C(8,2)`, i.e. `3·|L| ≤ 28`).
* `interior_list_two_sided` — combining the two: at the interior radius `δ = 5/8` on the **smooth
  domain**, the list size is pinned to `[7, 9]`.

Everything is `sorry`-free and axiom-clean. The hypotheses are satisfiable (the `7`-element list is
exhibited concretely), so the statements are non-vacuous.

## Honest assessment (smooth-vs-full-field, and the wall)

This is the most prize-faithful explicit data point in the repo: the domain is an *actual* `2`-power
multiplicative subgroup, the FRI setting. But it is *one explicit instance*, and the upper bound is
the same field-blind Fisher pair-packing bound that gives `[6,7]` on the full field — it does
**not** exploit the smooth structure to beat the `≤ k − 1` agreement ceiling. The `[7,9]` window is
near-tight (within two) but the *general* matching interior upper bound for smooth-domain RS — the
open prize — is untouched: closing it still requires the open super-polynomial smooth-domain
subset/incidence count documented in `ListIncidencePolyMethod.lean`. What is new here is
*faithfulness of the setting*, not a technique past the wall.
-/

namespace ArkLib.CodingTheory.Round3SmoothF17

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex (agree)
open ArkLib.CodingTheory.TinyInteriorTwoSided (reedSolomon_pairPacking_list_bound)

/-- `17` is prime, so `ZMod 17` is a field. This makes `RS[F₁₇, ⟨2⟩, 2]` a genuine Reed–Solomon
code (degree-`<k` polynomials over a field, evaluated on an injective smooth domain). -/
instance fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ### The smooth evaluation domain: the multiplicative subgroup `⟨2⟩` of order `8`. -/

/-- The smooth evaluation domain `D i = 2^i` of `Fin 8` into `F₁₇`. Its image is the cyclic
multiplicative subgroup `⟨2⟩ = {1,2,4,8,16,15,13,9}` of order `8` (`2` has order `8` in `F₁₇ˣ`).
This is a `2`-power-order multiplicative subgroup — a genuine *smooth* domain (the FRI setting),
not the whole field. -/
def D : Fin 8 ↪ ZMod 17 := ⟨fun i => (2 : ZMod 17) ^ (i : ℕ), by decide⟩

/-- The domain map is injective (it is an `Embedding`, but we record the underlying statement). -/
theorem D_injective : Function.Injective D := D.injective

/-- **The domain is a genuine smooth subgroup.** The image of `D` is *exactly* the set of `8`th
roots of unity `{x : ZMod 17 | x⁸ = 1}`, which is the unique multiplicative subgroup of order `8`
in the cyclic group `F₁₇ˣ`. This certifies that `D` enumerates a `2`-power-order multiplicative
subgroup — the smooth evaluation domain the open prize is about. -/
theorem smooth_domain_eq_roots_of_unity :
    (Finset.univ.image D) = (Finset.univ.filter (fun x : ZMod 17 => x ^ 8 = 1)) := by
  decide

/-! ### The explicit received word and the seven smooth-domain codewords. -/

/-- The explicit received word `w = (5,15,15,16,2,10,14,11)` (interior radius `δ = 5/8`). -/
def w : Fin 8 → ZMod 17 := ![5, 15, 15, 16, 2, 10, 14, 11]

/-- The seven codewords agreeing with `w` on `≥ 3` of the `8` smooth-domain coordinates, as
evaluation vectors of the lines `p₀=3x+9, p₁=4x+1, p₂=5x, p₃=6x+8, p₄=10x+12, p₅=14x+4,
p₆=15x+6`. -/
def c0 : Fin 8 → ZMod 17 := ![12, 15, 4, 16, 6, 3, 14, 2]
def c1 : Fin 8 → ZMod 17 := ![5, 9, 0, 16, 14, 10, 2, 3]
def c2 : Fin 8 → ZMod 17 := ![5, 10, 3, 6, 12, 7, 14, 11]
def c3 : Fin 8 → ZMod 17 := ![14, 3, 15, 5, 2, 13, 1, 11]
def c4 : Fin 8 → ZMod 17 := ![5, 15, 1, 7, 2, 9, 6, 0]
def c5 : Fin 8 → ZMod 17 := ![1, 15, 9, 14, 7, 10, 16, 11]
def c6 : Fin 8 → ZMod 17 := ![4, 2, 15, 7, 8, 10, 14, 5]

/-- The explicit degree-`<2` polynomials whose smooth-domain RS codewords are `c0,…,c6`. -/
noncomputable def p0 : (ZMod 17)[X] := C 3 * X + C 9
noncomputable def p1 : (ZMod 17)[X] := C 4 * X + C 1
noncomputable def p2 : (ZMod 17)[X] := C 5 * X
noncomputable def p3 : (ZMod 17)[X] := C 6 * X + C 8
noncomputable def p4 : (ZMod 17)[X] := C 10 * X + C 12
noncomputable def p5 : (ZMod 17)[X] := C 14 * X + C 4
noncomputable def p6 : (ZMod 17)[X] := C 15 * X + C 6

/-- The candidate list `L = {c0,…,c6}`. -/
def L : Finset (Fin 8 → ZMod 17) := {c0, c1, c2, c3, c4, c5, c6}

/-! ### Each `cⱼ` is genuinely the smooth-domain RS codeword of a degree-`<2` polynomial. -/

lemma c0_isRS : c0 = (fun i => p0.eval (D i)) := by
  funext i; simp only [c0, p0, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c1_isRS : c1 = (fun i => p1.eval (D i)) := by
  funext i; simp only [c1, p1, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c2_isRS : c2 = (fun i => p2.eval (D i)) := by
  funext i; simp only [c2, p2, D, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c3_isRS : c3 = (fun i => p3.eval (D i)) := by
  funext i; simp only [c3, p3, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c4_isRS : c4 = (fun i => p4.eval (D i)) := by
  funext i; simp only [c4, p4, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c5_isRS : c5 = (fun i => p5.eval (D i)) := by
  funext i; simp only [c5, p5, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c6_isRS : c6 = (fun i => p6.eval (D i)) := by
  funext i; simp only [c6, p6, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide

lemma p0_deg : p0.natDegree < 2 := by unfold p0; compute_degree!
lemma p1_deg : p1.natDegree < 2 := by unfold p1; compute_degree!
lemma p2_deg : p2.natDegree < 2 := by unfold p2; compute_degree!
lemma p3_deg : p3.natDegree < 2 := by unfold p3; compute_degree!
lemma p4_deg : p4.natDegree < 2 := by unfold p4; compute_degree!
lemma p5_deg : p5.natDegree < 2 := by unfold p5; compute_degree!
lemma p6_deg : p6.natDegree < 2 := by unfold p6; compute_degree!

/-- **Every element of `L` is a smooth-domain Reed–Solomon codeword of degree `< 2`.** This is the
non-vacuity witness that `L` lives inside the smooth-domain RS code `RS[F₁₇, ⟨2⟩, 2]`. -/
theorem L_subset_code :
    ∀ c ∈ L, ∃ q : (ZMod 17)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i) := by
  intro c hc
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h
  · exact ⟨p0, p0_deg, h ▸ c0_isRS⟩
  · exact ⟨p1, p1_deg, h ▸ c1_isRS⟩
  · exact ⟨p2, p2_deg, h ▸ c2_isRS⟩
  · exact ⟨p3, p3_deg, h ▸ c3_isRS⟩
  · exact ⟨p4, p4_deg, h ▸ c4_isRS⟩
  · exact ⟨p5, p5_deg, h ▸ c5_isRS⟩
  · exact ⟨p6, p6_deg, h ▸ c6_isRS⟩

/-- **The list has exactly seven elements.** All seven explicit smooth-domain codewords are
pairwise distinct. -/
theorem witness_list_card_seven : L.card = 7 := by decide

/-- **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 3`
coordinates, i.e. has Hamming distance `≤ 5` from `w` — relative radius `δ = 5/8`. -/
theorem all_agree_ge_three : ∀ c ∈ L, 3 ≤ agree c w := by
  intro c hc
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h <;> subst h <;> decide

/-! ### Lower bound: a 7-element interior list on the smooth domain. -/

/-- **Explicit interior list-size lower bound for the smooth-domain code `RS[F₁₇, ⟨2⟩, 2]`.**

There is a received word `w` and a `Finset` `L` of size `7`, *all of whose elements are
Reed–Solomon codewords of degree-`<2` polynomials on the smooth domain `D = ⟨2⟩`* (the order-`8`
multiplicative subgroup), each agreeing with `w` on at least `3` of the `8` coordinates.
Equivalently: at the relative radius `δ = (8−3)/8 = 5/8`, **strictly inside the open proximity gap**
`(1 − √ρ, 1 − ρ) = (1/2, 3/4)` (`five_eighths_strictly_interior`), the list size of this
*smooth-domain* code is `≥ 7`. -/
theorem interior_list_lower_bound_seven :
    ∃ (w' : Fin 8 → ZMod 17) (L' : Finset (Fin 8 → ZMod 17)),
      L'.card = 7 ∧
      (∀ c ∈ L', ∃ q : (ZMod 17)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) ∧
      (∀ c ∈ L', 3 ≤ agree c w') :=
  ⟨w, L, witness_list_card_seven, L_subset_code, all_agree_ge_three⟩

/-! ### Upper bound: the domain-agnostic Fisher pair-packing bound. -/

/-- **Interior list-size UPPER bound for the smooth-domain code `RS[F₁₇, ⟨2⟩, 2]`.** Any list `L`
of distinct degree-`<2` RS codewords on the smooth domain `D`, each agreeing with a received word
`w` on `≥ 3` of the `8` coordinates (relative radius `δ = 5/8`, strictly inside the open gap), has
`|L| ≤ 9`.

Proof: the imported domain-agnostic Fisher / Corrádi pair-packing bound gives
`|L| · C(3, 2) ≤ C(8, 2)`, i.e. `3·|L| ≤ 28`, so `|L| ≤ 9`. -/
theorem interior_list_upper_bound_nine (w' : Fin 8 → ZMod 17)
    (L' : Finset (Fin 8 → ZMod 17))
    (hpoly : ∀ c ∈ L', ∃ q : (ZMod 17)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i))
    (hclose : ∀ c ∈ L', 3 ≤ agree c w') :
    L'.card ≤ 9 := by
  have h := reedSolomon_pairPacking_list_bound (ι := Fin 8) (F := ZMod 17) D w' L' 3 hpoly hclose
  have e1 : (3 : ℕ).choose 2 = 3 := by decide
  have e2 : (8 : ℕ).choose 2 = 28 := by decide
  rw [Fintype.card_fin, e1, e2] at h
  -- now `h : L'.card * 3 ≤ 28`.
  omega

/-! ### The two-sided interior pin on the smooth domain. -/

/-- **Two-sided interior list-size pin for the smooth-domain code `RS[F₁₇, ⟨2⟩, 2]` at `δ = 5/8`.**

There exists a received word `w` and a list `L` of distinct degree-`<2` Reed–Solomon codewords on
the **smooth domain** `D = ⟨2⟩` (the order-`8` multiplicative subgroup), each agreeing with `w` on
`≥ 3` of the `8` coordinates (relative radius `δ = 5/8`, strictly interior to the open proximity gap
`(1/2, 3/4)` by `five_eighths_strictly_interior`), with **`7 ≤ |L|`**; and **every** such list has
**`|L| ≤ 9`**.

So at this interior radius the list size of this explicit *smooth-domain* code is pinned to `[7, 9]`
— a verified, near-tight two-sided interior data point on the prize's real setting (a `2`-power
multiplicative subgroup, the FRI domain), not the full field. The lower bound is the explicit
`7`-element witness `interior_list_lower_bound_seven`; the upper bound is the domain-agnostic Fisher
pair-packing bound `interior_list_upper_bound_nine`. -/
theorem interior_list_two_sided :
    (∃ (w' : Fin 8 → ZMod 17) (L' : Finset (Fin 8 → ZMod 17)),
        7 ≤ L'.card ∧
        (∀ c ∈ L', ∃ q : (ZMod 17)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) ∧
        (∀ c ∈ L', 3 ≤ agree c w')) ∧
    (∀ (w' : Fin 8 → ZMod 17) (L' : Finset (Fin 8 → ZMod 17)),
        (∀ c ∈ L', ∃ q : (ZMod 17)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) →
        (∀ c ∈ L', 3 ≤ agree c w') →
        L'.card ≤ 9) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨w', L', hcard, hpoly, hclose⟩ := interior_list_lower_bound_seven
    exact ⟨w', L', by rw [hcard], hpoly, hclose⟩
  · exact fun w' L' hpoly hclose => interior_list_upper_bound_nine w' L' hpoly hclose

/-! ### The radius `δ = 5/8` is strictly inside the open gap. -/

/-- **Gap placement.** The relative radius `δ = 5/8` (agreement `a = 3` out of `n = 8`) is strictly
between the Johnson radius `1 − √ρ = 1/2` and the capacity radius `1 − ρ = 3/4`, for the rate
`ρ = 2/8 = 1/4`. Since `√(1/4) = 1/2`: lower side `1/2 < 5/8` and upper side `5/8 < 3/4`. So this
verified `7`-element smooth-domain list is genuinely a data point in the *interior* of the open
proximity gap. -/
theorem five_eighths_strictly_interior :
    1 - Real.sqrt (2 / 8) < (5 : ℝ) / 8 ∧ (5 : ℝ) / 8 < 1 - 2 / 8 := by
  refine ⟨?_, by norm_num⟩
  have hsqrt : Real.sqrt (2 / 8) = 1 / 2 := by
    rw [show (2 : ℝ) / 8 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]; norm_num

end ArkLib.CodingTheory.Round3SmoothF17

#print axioms ArkLib.CodingTheory.Round3SmoothF17.interior_list_two_sided
#print axioms ArkLib.CodingTheory.Round3SmoothF17.smooth_domain_eq_roots_of_unity
