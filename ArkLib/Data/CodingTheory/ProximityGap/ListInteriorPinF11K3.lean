/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListIncidencePolyMethod
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonJohnson
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A verified TWO-SIDED interior list-size pin for `RS[F₁₁, F₁₁, 3]` (Issue #232, ROUND 3)

ROUND 2 produced a verified two-sided interior list-size pin for the tiny *degree-`< 2`* code
`RS[F₇, F₇, 2]` at the interior radius `δ = 4/7`, with the list size provably in `[6, 7]`
(`ListInteriorTwoSidedF7.interior_list_two_sided`). The upper bound there came from the `k = 2`
Fisher / pair-packing argument (`pairPacking_card_le`).

This file is the ROUND-3 scale-up **in the degree parameter `k`**: a verified two-sided interior
list-size pin for the *degree-`< 3`* code `RS[F₁₁, F₁₁, 3]` (rate `ρ = 3/11`). It demonstrates that
the polynomial-method incidence machinery (`PolynomialMethod.poly_method_subset_incidence_bound`,
the `k`-uniform generalisation `|L| · C(a,k) ≤ C(n,k)` of the round-2 pair-packing bound) scales in
`k`: the upper bound here is the *cubic* (`k = 3`) incidence inequality, not the quadratic one.

## The instance

`C = RS[F = ZMod 11, L = all of F₁₁ (domain `D i = i`, `n = 11`), k = 3]` — evaluations of the
degree-`≤ 2` (quadratic) polynomials on the eleven points `0,1,…,10`. The rate is `ρ = k/n = 3/11`,
so:

* Johnson radius `1 − √ρ = 1 − √(3/11) ≈ 0.4778`;
* capacity radius `1 − ρ = 8/11 ≈ 0.7273`;
* the **open gap** the prize asks about is `δ ∈ (0.4778, 0.7273)`.

The relative agreement radius `a = 5` (require codewords to agree with the received word on `≥ 5` of
`11` coordinates) corresponds to relative distance `δ = (n − a)/n = 6/11 ≈ 0.5455`, which is
**strictly interior** to that gap (`six_elevenths_strictly_interior`).

## The two sides

* **Lower bound (`interior_list_lower_bound_k3`).** An explicit received word
  `w = (2,4,8,5,2,4,9,1,1,9,10)` and an explicit `7`-element list `L` of *distinct* degree-`< 3`
  Reed–Solomon codewords (the quadratics with coefficient triples
  `(0,3,2),(0,8,3),(4,6,5),(5,8,2),(6,8,1),(7,5,2),(8,7,0)`), each agreeing with `w` on `≥ 5`
  coordinates. So at this interior radius the list size is `≥ 7`. (Found by a verified search; the
  list is `decide`-checked here for distinctness and agreement.)

* **Upper bound (`interior_list_upper_bound_k3`).** Any list of distinct degree-`< 3` RS codewords on
  `D`, each agreeing with `w` on `≥ 5` coordinates, has `|L| ≤ 16`. This is the *cubic* incidence
  bound: `poly_method_subset_incidence_bound` gives `|L| · C(5,3) ≤ C(11,3)`, i.e. `|L| · 10 ≤ 165`,
  so `|L| ≤ 16`.

* **Two-sided pin (`interior_list_two_sided_k3`).** Combining the two, the true interior list size at
  `δ = 6/11` of this explicit `k = 3` code lies in `[7, 16]`.

Everything is `sorry`-free and axiom-clean. The hypotheses are satisfiable (the lower-bound witness is
exhibited concretely), so the window `[7,16]` is non-empty and the bound is genuine. This is a verified
interior **`δ*` data point at `k = 3`** — it confirms the method *scales in the degree parameter*, but
it is not a general matching upper bound for smooth-domain RS (still the open prize). The incidence
upper bound `C(n,k)/C(a,k)` is field-blind (`PolynomialMethod.abstract_incidence_bound`) and stays
super-polynomial at any fixed interior agreement (`PolynomialMethod.incidence_superpoly_witness`), so
this pin lands on the same convergent wall as round 2: a sharper-than-Johnson but still field-blind
finite list bound, near-tight on a single explicit instance.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Issue #232; the open gap `(1 − √ρ, 1 − ρ)`.
-/

namespace ArkLib.CodingTheory.TinyInteriorK3

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex (agree)

/-- `11` is prime, so `ZMod 11` is a field. This is what makes `RS[F₁₁, F₁₁, 3]` a genuine
Reed–Solomon code (degree-`<k` polynomials over a field, evaluated on an injective domain). -/
instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The evaluation domain: all eleven points of `F₁₁`, indexed by `Fin 11` via `D i = i`. -/
def D : Fin 11 ↪ ZMod 11 := ⟨fun i => (i : ZMod 11), by decide⟩

/-- The explicit received word `w = (2,4,8,5,2,4,9,1,1,9,10)`. -/
def w : Fin 11 → ZMod 11 := ![2, 4, 8, 5, 2, 4, 9, 1, 1, 9, 10]

/-! ### The seven explicit degree-`<3` Reed–Solomon codewords. -/

def c0 : Fin 11 → ZMod 11 := ![2, 5, 8, 0, 3, 6, 9, 1, 4, 7, 10]
def c1 : Fin 11 → ZMod 11 := ![3, 0, 8, 5, 2, 10, 7, 4, 1, 9, 6]
def c2 : Fin 11 → ZMod 11 := ![5, 4, 0, 4, 5, 3, 9, 1, 1, 9, 3]
def c3 : Fin 11 → ZMod 11 := ![2, 4, 5, 5, 4, 2, 10, 6, 1, 6, 10]
def c4 : Fin 11 → ZMod 11 := ![1, 4, 8, 2, 8, 4, 1, 10, 9, 9, 10]
def c5 : Fin 11 → ZMod 11 := ![2, 3, 7, 3, 2, 4, 9, 6, 6, 9, 4]
def c6 : Fin 11 → ZMod 11 := ![0, 4, 2, 5, 2, 4, 0, 1, 7, 7, 1]

/-- The explicit degree-`<3` (quadratic) polynomials whose RS codewords are `c0,…,c6`. -/
noncomputable def p0 : (ZMod 11)[X] := C 3 * X + C 2
noncomputable def p1 : (ZMod 11)[X] := C 8 * X + C 3
noncomputable def p2 : (ZMod 11)[X] := C 4 * X ^ 2 + C 6 * X + C 5
noncomputable def p3 : (ZMod 11)[X] := C 5 * X ^ 2 + C 8 * X + C 2
noncomputable def p4 : (ZMod 11)[X] := C 6 * X ^ 2 + C 8 * X + C 1
noncomputable def p5 : (ZMod 11)[X] := C 7 * X ^ 2 + C 5 * X + C 2
noncomputable def p6 : (ZMod 11)[X] := C 8 * X ^ 2 + C 7 * X

/-- The candidate list `L = {c0,…,c6}`. -/
def L : Finset (Fin 11 → ZMod 11) := {c0, c1, c2, c3, c4, c5, c6}

/-! ### Each `cⱼ` is genuinely the RS codeword of a degree-`<3` polynomial. -/

lemma c0_isRS : c0 = (fun i => p0.eval (D i)) := by
  funext i
  simp only [c0, p0, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fin_cases i <;> decide
lemma c1_isRS : c1 = (fun i => p1.eval (D i)) := by
  funext i
  simp only [c1, p1, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c2_isRS : c2 = (fun i => p2.eval (D i)) := by
  funext i
  simp only [c2, p2, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fin_cases i <;> decide
lemma c3_isRS : c3 = (fun i => p3.eval (D i)) := by
  funext i
  simp only [c3, p3, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fin_cases i <;> decide
lemma c4_isRS : c4 = (fun i => p4.eval (D i)) := by
  funext i
  simp only [c4, p4, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fin_cases i <;> decide
lemma c5_isRS : c5 = (fun i => p5.eval (D i)) := by
  funext i
  simp only [c5, p5, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fin_cases i <;> decide
lemma c6_isRS : c6 = (fun i => p6.eval (D i)) := by
  funext i
  simp only [c6, p6, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  fin_cases i <;> decide

lemma p0_deg : p0.natDegree < 3 := by unfold p0; compute_degree!
lemma p1_deg : p1.natDegree < 3 := by unfold p1; compute_degree!
lemma p2_deg : p2.natDegree < 3 := by unfold p2; compute_degree!
lemma p3_deg : p3.natDegree < 3 := by unfold p3; compute_degree!
lemma p4_deg : p4.natDegree < 3 := by unfold p4; compute_degree!
lemma p5_deg : p5.natDegree < 3 := by unfold p5; compute_degree!
lemma p6_deg : p6.natDegree < 3 := by unfold p6; compute_degree!

/-- **Every element of `L` is a Reed–Solomon codeword of degree `< 3`.** Non-vacuity: `L` lives inside
the RS code `RS[F₁₁, F₁₁, 3]`. -/
theorem L_subset_code :
    ∀ c ∈ L, ∃ q : (ZMod 11)[X], q.natDegree < 3 ∧ c = fun i => q.eval (D i) := by
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

/-! ### The seven codewords are pairwise distinct, so `|L| = 7`. -/

/-- **The list has exactly seven elements.** All seven explicit codewords are pairwise distinct. -/
theorem witness_list_card_seven : L.card = 7 := by decide

/-! ### Each codeword agrees with `w` on at least `5` of the `11` coordinates. -/

/-- **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 5`
coordinates, i.e. has Hamming distance `≤ 6` from `w` — relative radius `δ = 6/11`. -/
theorem all_agree_ge_five : ∀ c ∈ L, 5 ≤ agree c w := by
  intro c hc
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h <;> subst h <;> decide

/-! ### Main lower bound: a 7-element interior list. -/

/-- **Explicit interior list-size LOWER bound for `RS[F₁₁, F₁₁, 3]`.**

There is a received word `w` and a `Finset` `L` of size `7`, *all of whose elements are Reed–Solomon
codewords of degree-`<3` polynomials on the smooth domain `D`*, each agreeing with `w` on at least `5`
of the `11` coordinates. Equivalently: at the relative radius `δ = 6/11`, which is **strictly inside
the open proximity gap** `(1 − √ρ, 1 − ρ) = (1 − √(3/11), 8/11)`
(see `six_elevenths_strictly_interior`), the list size of this explicit `k = 3` code is `≥ 7`. -/
theorem interior_list_lower_bound_k3 :
    ∃ (w' : Fin 11 → ZMod 11) (L' : Finset (Fin 11 → ZMod 11)),
      L'.card = 7 ∧
      (∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 3 ∧ c = fun i => q.eval (D i)) ∧
      (∀ c ∈ L', 5 ≤ agree c w') :=
  ⟨w, L, witness_list_card_seven, L_subset_code, all_agree_ge_five⟩

/-! ### Main upper bound: the cubic (`k = 3`) incidence bound. -/

open ArkLib.CodingTheory.PolynomialMethod in
/-- **Interior list-size UPPER bound for `RS[F₁₁, F₁₁, 3]` (cubic incidence bound).** Any list `L` of
*distinct* degree-`<3` RS codewords on the smooth domain `D`, each agreeing with a received word `w`
on `≥ 5` of the `11` coordinates (relative radius `δ = 6/11`, strictly interior to the open gap), has
`|L| ≤ 16`.

Proof: the cubic incidence bound `poly_method_subset_incidence_bound` gives
`|L| · C(5,3) ≤ C(11,3)`, i.e. `|L| · 10 ≤ 165`, so `|L| ≤ 16`. This is the `k = 3`
generalisation of the round-2 quadratic pair-packing bound. -/
theorem interior_list_upper_bound_k3 (w' : Fin 11 → ZMod 11)
    (L' : Finset (Fin 11 → ZMod 11))
    (hpoly : ∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 3 ∧ c = fun i => q.eval (D i))
    (hclose : ∀ c ∈ L', 5 ≤ agree c w') :
    L'.card ≤ 16 := by
  have h := poly_method_subset_incidence_bound (ι := Fin 11) (F := ZMod 11) D 3 w' L' 5 hpoly hclose
  -- `C(5,3) = 10`, `Fintype.card (Fin 11) = 11`, `C(11,3) = 165`.
  have e1 : Nat.choose 5 3 = 10 := by decide
  have e2 : Nat.choose 11 3 = 165 := by decide
  rw [Fintype.card_fin, e1, e2] at h
  -- now `h : L'.card * 10 ≤ 165`.
  omega

/-! ### The two-sided interior pin. -/

/-- **Two-sided interior list-size pin for `RS[F₁₁, F₁₁, 3]` at `δ = 6/11`.**

There exists a received word `w` and a list `L` of distinct degree-`<3` Reed–Solomon codewords on the
smooth domain `D`, each agreeing with `w` on `≥ 5` of the `11` coordinates (relative radius
`δ = 6/11`, strictly interior to the open proximity gap `(1 − √(3/11), 8/11)` by
`six_elevenths_strictly_interior`), with **`7 ≤ |L|`**; and **every** such list has **`|L| ≤ 16`**.

So at this interior radius the list size of this explicit `k = 3` code is pinned to `[7, 16]` — a
verified two-sided interior data point *at degree parameter `k = 3`*, scaling the round-2 `RS[F₇,F₇,2]`
pin up in `k`. The lower bound is the explicit `7`-element witness of `interior_list_lower_bound_k3`;
the upper bound is the cubic incidence bound `interior_list_upper_bound_k3`. -/
theorem interior_list_two_sided_k3 :
    (∃ (w' : Fin 11 → ZMod 11) (L' : Finset (Fin 11 → ZMod 11)),
        7 ≤ L'.card ∧
        (∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 3 ∧ c = fun i => q.eval (D i)) ∧
        (∀ c ∈ L', 5 ≤ agree c w')) ∧
    (∀ (w' : Fin 11 → ZMod 11) (L' : Finset (Fin 11 → ZMod 11)),
        (∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 3 ∧ c = fun i => q.eval (D i)) →
        (∀ c ∈ L', 5 ≤ agree c w') →
        L'.card ≤ 16) := by
  refine ⟨?_, fun w' L' hpoly hclose => interior_list_upper_bound_k3 w' L' hpoly hclose⟩
  obtain ⟨w', L', hcard, hpoly, hclose⟩ := interior_list_lower_bound_k3
  exact ⟨w', L', by rw [hcard], hpoly, hclose⟩

/-! ### The radius `δ = 6/11` is strictly inside the open gap. -/

/-- **Gap placement.** The relative radius `δ = 6/11` (agreement `a = 5` out of `n = 11`) is strictly
between the Johnson radius `1 − √ρ` and the capacity radius `1 − ρ = 8/11`, for the rate `ρ = 3/11`.

* Upper side `6/11 < 8/11` is immediate.
* Lower side `1 − √(3/11) < 6/11`, i.e. `5/11 < √(3/11)`: squaring (both sides nonneg),
  `25/121 < 3/11 = 33/121`. ✓

So this verified `7`-element list is genuinely a data point in the *interior* of the open proximity
gap, not in the already-resolved Johnson or capacity regimes. -/
theorem six_elevenths_strictly_interior :
    1 - Real.sqrt (3 / 11) < (6 : ℝ) / 11 ∧ (6 : ℝ) / 11 < 1 - 3 / 11 := by
  refine ⟨?_, by norm_num⟩
  -- want 1 - √(3/11) < 6/11, i.e. 5/11 < √(3/11).
  have hlt : (5 : ℝ) / 11 < Real.sqrt (3 / 11) := by
    have hnn : (0 : ℝ) ≤ 5 / 11 := by norm_num
    rw [Real.lt_sqrt hnn]
    norm_num
  linarith

end ArkLib.CodingTheory.TinyInteriorK3

#print axioms ArkLib.CodingTheory.TinyInteriorK3.interior_list_two_sided_k3
#print axioms ArkLib.CodingTheory.TinyInteriorK3.interior_list_upper_bound_k3
