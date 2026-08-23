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
# A verified TWO-SIDED interior list-size pin for `RS[F₁₁, F₁₁, 2]` at `δ = 8/11` (ROUND 3)

This file extends the verified `δ*` table of two-sided interior list-size data points (after the
`RS[F₇, F₇, 2]` pin `[6, 7]` at `δ = 4/7` of `ListInteriorTwoSidedF7.lean`) with a **second explicit
instance**:

`C = RS[F = ZMod 11, L = all of F₁₁ (the smooth domain `DD = id`, `n = 11`), k = 2]`, rate
`ρ = k/n = 2/11`. The parameters are:

* Johnson radius `1 − √ρ = 1 − √(2/11) ≈ 0.5736`;
* capacity radius `1 − ρ = 9/11 ≈ 0.8182`;
* so the **open gap** the prize (ABF26 / Issue #232) asks about is `δ ∈ (0.5736, 0.8182)`.

We work at agreement `a = 3` out of `n = 11`, i.e. relative distance `δ = (11 − 3)/11 = 8/11 ≈ 0.7273`,
which is **strictly interior** to that gap (proven in `eight_elevenths_strictly_interior`).

## What is verified here

* `interior_list_upper_bound_eighteen` — the **matching Fisher / pair-packing upper bound**. Reusing
  `reedSolomon_pairPacking_list_bound` from `ListInteriorTwoSidedF7.lean` (distinct degree-`<2`
  codewords agree on `≤ 1` point, so their `w`-agreement sets meet in `≤ 1`), any list of distinct
  degree-`<2` RS codewords on `D = id` each agreeing with a received word `w` on `≥ 3` of the `11`
  coordinates satisfies `|L| · C(3, 2) ≤ C(11, 2)`, i.e. `3·|L| ≤ 55`, hence **`|L| ≤ 18`**.
* `interior_list_lower_bound_fifteen` — an **explicit lower bound**. We exhibit a received word
  `w = (0,1,8,5,9,4,7,2,6,3,10)` (the cubing permutation `i ↦ i³ mod 11`) and an explicit **15**-element
  list of distinct linear (degree-`<2`) polynomials, each agreeing with `w` on exactly `3` of the `11`
  coordinates. So at the interior radius `a = 3` the list size of this explicit code is `≥ 15`.
* `interior_list_two_sided_f11` — the combined **two-sided pin `list ∈ [15, 18]`** at the strictly
  interior radius `δ = 8/11`.

Everything is `sorry`-free and axiom-clean. The hypotheses are satisfiable (the witnesses are exhibited
concretely), so the statements are non-vacuous and the `[15, 18]` window is non-empty. This is a second
verified interior `δ*` data point — not the general matching upper bound for smooth-domain RS that the
open prize lacks, but the sharpest two-sided window elementary pair-packing yields for this explicit
instance.
-/

namespace ArkLib.CodingTheory.TinyInteriorF11

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex
open ArkLib.CodingTheory.TinyInteriorTwoSided (reedSolomon_pairPacking_list_bound)

/-- `11` is prime, so `ZMod 11` is a field, making `RS[F₁₁, F₁₁, 2]` a genuine Reed–Solomon code. -/
instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The evaluation domain: all eleven points of `F₁₁`, indexed by `Fin 11` via `DD i = i`. -/
def DD : Fin 11 ↪ ZMod 11 := ⟨fun i => (i : ZMod 11), by decide⟩

/-- The explicit received word `w = (0,1,8,5,9,4,7,2,6,3,10)` (the cubing permutation `i ↦ i³`). -/
def w11 : Fin 11 → ZMod 11 := ![0, 1, 8, 5, 9, 4, 7, 2, 6, 3, 10]

/-! ### The fifteen codewords, as evaluation vectors of distinct linear polynomials.

Each `dⱼ` is `i ↦ (aⱼ · i + bⱼ)` for the listed slope/intercept, and agrees with `w11` on exactly
`3` of the `11` coordinates (verified by `decide` in `all_agree_ge_three_f11`). -/

def d0  : Fin 11 → ZMod 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]   -- 1·x + 0
def d1  : Fin 11 → ZMod 11 := ![1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10]   -- 2·x + 1
def d2  : Fin 11 → ZMod 11 := ![10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8]   -- 2·x + 10
def d3  : Fin 11 → ZMod 11 := ![0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8]   -- 3·x + 0
def d4  : Fin 11 → ZMod 11 := ![0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7]   -- 4·x + 0
def d5  : Fin 11 → ZMod 11 := ![0, 5, 10, 4, 9, 3, 8, 2, 7, 1, 6]   -- 5·x + 0
def d6  : Fin 11 → ZMod 11 := ![4, 10, 5, 0, 6, 1, 7, 2, 8, 3, 9]   -- 6·x + 4
def d7  : Fin 11 → ZMod 11 := ![7, 2, 8, 3, 9, 4, 10, 5, 0, 6, 1]   -- 6·x + 7
def d8  : Fin 11 → ZMod 11 := ![5, 1, 8, 4, 0, 7, 3, 10, 6, 2, 9]   -- 7·x + 5
def d9  : Fin 11 → ZMod 11 := ![6, 2, 9, 5, 1, 8, 4, 0, 7, 3, 10]   -- 7·x + 6
def d10 : Fin 11 → ZMod 11 := ![3, 0, 8, 5, 2, 10, 7, 4, 1, 9, 6]   -- 8·x + 3
def d11 : Fin 11 → ZMod 11 := ![8, 5, 2, 10, 7, 4, 1, 9, 6, 3, 0]   -- 8·x + 8
def d12 : Fin 11 → ZMod 11 := ![0, 9, 7, 5, 3, 1, 10, 8, 6, 4, 2]   -- 9·x + 0
def d13 : Fin 11 → ZMod 11 := ![2, 1, 0, 10, 9, 8, 7, 6, 5, 4, 3]   -- 10·x + 2
def d14 : Fin 11 → ZMod 11 := ![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 10]   -- 10·x + 9

/-- The explicit degree-`<2` polynomials whose RS codewords are `d0,…,d14`. -/
noncomputable def q0  : (ZMod 11)[X] := X
noncomputable def q1  : (ZMod 11)[X] := C 2 * X + C 1
noncomputable def q2  : (ZMod 11)[X] := C 2 * X + C 10
noncomputable def q3  : (ZMod 11)[X] := C 3 * X
noncomputable def q4  : (ZMod 11)[X] := C 4 * X
noncomputable def q5  : (ZMod 11)[X] := C 5 * X
noncomputable def q6  : (ZMod 11)[X] := C 6 * X + C 4
noncomputable def q7  : (ZMod 11)[X] := C 6 * X + C 7
noncomputable def q8  : (ZMod 11)[X] := C 7 * X + C 5
noncomputable def q9  : (ZMod 11)[X] := C 7 * X + C 6
noncomputable def q10 : (ZMod 11)[X] := C 8 * X + C 3
noncomputable def q11 : (ZMod 11)[X] := C 8 * X + C 8
noncomputable def q12 : (ZMod 11)[X] := C 9 * X
noncomputable def q13 : (ZMod 11)[X] := C 10 * X + C 2
noncomputable def q14 : (ZMod 11)[X] := C 10 * X + C 9

/-- The candidate list `L₁₁ = {d0, …, d14}`. -/
def L11 : Finset (Fin 11 → ZMod 11) :=
  {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14}

/-! ### Each `dⱼ` is genuinely the RS codeword of its degree-`<2` polynomial. -/

lemma d0_isRS : d0 = (fun i => q0.eval (DD i)) := by
  funext i; simp only [d0, q0, DD, Function.Embedding.coeFn_mk, eval_X]; fin_cases i <;> decide
lemma d1_isRS : d1 = (fun i => q1.eval (DD i)) := by
  funext i
  simp only [d1, q1, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d2_isRS : d2 = (fun i => q2.eval (DD i)) := by
  funext i
  simp only [d2, q2, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d3_isRS : d3 = (fun i => q3.eval (DD i)) := by
  funext i
  simp only [d3, q3, DD, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d4_isRS : d4 = (fun i => q4.eval (DD i)) := by
  funext i
  simp only [d4, q4, DD, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d5_isRS : d5 = (fun i => q5.eval (DD i)) := by
  funext i
  simp only [d5, q5, DD, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d6_isRS : d6 = (fun i => q6.eval (DD i)) := by
  funext i
  simp only [d6, q6, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d7_isRS : d7 = (fun i => q7.eval (DD i)) := by
  funext i
  simp only [d7, q7, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d8_isRS : d8 = (fun i => q8.eval (DD i)) := by
  funext i
  simp only [d8, q8, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d9_isRS : d9 = (fun i => q9.eval (DD i)) := by
  funext i
  simp only [d9, q9, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d10_isRS : d10 = (fun i => q10.eval (DD i)) := by
  funext i
  simp only [d10, q10, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d11_isRS : d11 = (fun i => q11.eval (DD i)) := by
  funext i
  simp only [d11, q11, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d12_isRS : d12 = (fun i => q12.eval (DD i)) := by
  funext i
  simp only [d12, q12, DD, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d13_isRS : d13 = (fun i => q13.eval (DD i)) := by
  funext i
  simp only [d13, q13, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma d14_isRS : d14 = (fun i => q14.eval (DD i)) := by
  funext i
  simp only [d14, q14, DD, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide

lemma q0_deg : q0.natDegree < 2 := by unfold q0; compute_degree!
lemma q1_deg : q1.natDegree < 2 := by unfold q1; compute_degree!
lemma q2_deg : q2.natDegree < 2 := by unfold q2; compute_degree!
lemma q3_deg : q3.natDegree < 2 := by unfold q3; compute_degree!
lemma q4_deg : q4.natDegree < 2 := by unfold q4; compute_degree!
lemma q5_deg : q5.natDegree < 2 := by unfold q5; compute_degree!
lemma q6_deg : q6.natDegree < 2 := by unfold q6; compute_degree!
lemma q7_deg : q7.natDegree < 2 := by unfold q7; compute_degree!
lemma q8_deg : q8.natDegree < 2 := by unfold q8; compute_degree!
lemma q9_deg : q9.natDegree < 2 := by unfold q9; compute_degree!
lemma q10_deg : q10.natDegree < 2 := by unfold q10; compute_degree!
lemma q11_deg : q11.natDegree < 2 := by unfold q11; compute_degree!
lemma q12_deg : q12.natDegree < 2 := by unfold q12; compute_degree!
lemma q13_deg : q13.natDegree < 2 := by unfold q13; compute_degree!
lemma q14_deg : q14.natDegree < 2 := by unfold q14; compute_degree!

/-- **Every element of `L₁₁` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity
witness that `L₁₁` lives inside the RS code `RS[F₁₁, F₁₁, 2]`. -/
theorem L11_subset_code :
    ∀ c ∈ L11, ∃ q : (ZMod 11)[X], q.natDegree < 2 ∧ c = fun i => q.eval (DD i) := by
  intro c hc
  simp only [L11, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨q0,  q0_deg,  h ▸ d0_isRS⟩
  · exact ⟨q1,  q1_deg,  h ▸ d1_isRS⟩
  · exact ⟨q2,  q2_deg,  h ▸ d2_isRS⟩
  · exact ⟨q3,  q3_deg,  h ▸ d3_isRS⟩
  · exact ⟨q4,  q4_deg,  h ▸ d4_isRS⟩
  · exact ⟨q5,  q5_deg,  h ▸ d5_isRS⟩
  · exact ⟨q6,  q6_deg,  h ▸ d6_isRS⟩
  · exact ⟨q7,  q7_deg,  h ▸ d7_isRS⟩
  · exact ⟨q8,  q8_deg,  h ▸ d8_isRS⟩
  · exact ⟨q9,  q9_deg,  h ▸ d9_isRS⟩
  · exact ⟨q10, q10_deg, h ▸ d10_isRS⟩
  · exact ⟨q11, q11_deg, h ▸ d11_isRS⟩
  · exact ⟨q12, q12_deg, h ▸ d12_isRS⟩
  · exact ⟨q13, q13_deg, h ▸ d13_isRS⟩
  · exact ⟨q14, q14_deg, h ▸ d14_isRS⟩

/-! ### The fifteen codewords are pairwise distinct, so `|L₁₁| = 15`. -/

/-- **The list has exactly fifteen elements.** All fifteen explicit codewords are pairwise distinct
(they are evaluations of distinct linear polynomials). -/
theorem witness_list_card_fifteen : L11.card = 15 := by decide

/-! ### Each codeword agrees with `w11` on at least `3` of the `11` coordinates. -/

/-- **Interior agreement.** Every codeword in `L₁₁` agrees with the received word `w11` on `≥ 3`
coordinates, i.e. has Hamming distance `≤ 8` from `w11` — relative radius `δ = 8/11`. -/
theorem all_agree_ge_three_f11 : ∀ c ∈ L11, 3 ≤ agree c w11 := by
  intro c hc
  simp only [L11, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-! ### Main lower bound: a 15-element interior list. -/

/-- **Explicit interior list-size lower bound for `RS[F₁₁, F₁₁, 2]`.**

There is a received word `w11` and a `Finset` `L₁₁` of size `15`, *all of whose elements are
Reed–Solomon codewords of degree-`<2` polynomials on the smooth domain `DD`*, each agreeing with
`w11` on at least `3` of the `11` coordinates. Equivalently: at the relative radius
`δ = (11−3)/11 = 8/11`, which is **strictly inside the open proximity gap**
`(1 − √ρ, 1 − ρ) = (1 − √(2/11), 9/11)` (see `eight_elevenths_strictly_interior`), the list size of
this explicit code is `≥ 15`. -/
theorem interior_list_lower_bound_fifteen :
    ∃ (w' : Fin 11 → ZMod 11) (L' : Finset (Fin 11 → ZMod 11)),
      L'.card = 15 ∧
      (∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 2 ∧ c = fun i => q.eval (DD i)) ∧
      (∀ c ∈ L', 3 ≤ agree c w') :=
  ⟨w11, L11, witness_list_card_fifteen, L11_subset_code, all_agree_ge_three_f11⟩

/-! ### Main upper bound: Fisher pair-packing gives `|L| ≤ 18`. -/

/-- **Interior list-size UPPER bound for `RS[F₁₁, F₁₁, 2]`.** Any list `L` of distinct degree-`<2`
RS codewords on the smooth domain `DD`, each agreeing with a received word `w` on `≥ 3` of the `11`
coordinates (relative radius `δ = 8/11`, strictly inside the open gap), has `|L| ≤ 18`.

Proof: `reedSolomon_pairPacking_list_bound` gives `|L| · C(3, 2) ≤ C(11, 2)`, i.e. `3·|L| ≤ 55`, so
`|L| ≤ 18`. -/
theorem interior_list_upper_bound_eighteen (w' : Fin 11 → ZMod 11)
    (L' : Finset (Fin 11 → ZMod 11))
    (hpoly : ∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 2 ∧ c = fun i => q.eval (DD i))
    (hclose : ∀ c ∈ L', 3 ≤ agree c w') :
    L'.card ≤ 18 := by
  have h := reedSolomon_pairPacking_list_bound (ι := Fin 11) (F := ZMod 11) DD w' L' 3 hpoly hclose
  -- `C(3,2) = 3`, `Fintype.card (Fin 11) = 11`, `C(11,2) = 55`.
  have e1 : (3 : ℕ).choose 2 = 3 := by decide
  have e2 : (11 : ℕ).choose 2 = 55 := by decide
  rw [Fintype.card_fin, e1, e2] at h
  -- now `h : L'.card * 3 ≤ 55`.
  omega

/-! ### The two-sided pin `list ∈ [15, 18]` at the interior radius `δ = 8/11`. -/

/-- **Two-sided interior list-size pin for `RS[F₁₁, F₁₁, 2]` at `δ = 8/11`.**

There exists a received word `w` and a list `L` of distinct degree-`<2` Reed–Solomon codewords on
the smooth domain `DD`, each agreeing with `w` on `≥ 3` of the `11` coordinates (relative radius
`δ = 8/11`, strictly interior to the open proximity gap `(1 − √(2/11), 9/11)` by
`eight_elevenths_strictly_interior`), with **`15 ≤ |L|`**; and **every** such list has
**`|L| ≤ 18`**.

So at this interior radius the list size of this explicit code is pinned to `[15, 18]` — a verified
two-sided interior data point. The lower bound is the explicit witness of
`interior_list_lower_bound_fifteen`; the upper bound is the Fisher pair-packing bound
`interior_list_upper_bound_eighteen`. This is a second entry in the verified `δ*` table (after the
`RS[F₇, F₇, 2]` pin `[6, 7]` at `δ = 4/7`): the sharpest two-sided window elementary pair-packing
yields for this explicit smooth-domain instance, not the general matching upper bound the open prize
(ABF26 / Issue #232) lacks. -/
theorem interior_list_two_sided_f11 :
    (∃ (w' : Fin 11 → ZMod 11) (L' : Finset (Fin 11 → ZMod 11)),
        15 ≤ L'.card ∧
        (∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 2 ∧ c = fun i => q.eval (DD i)) ∧
        (∀ c ∈ L', 3 ≤ agree c w')) ∧
    (∀ (w' : Fin 11 → ZMod 11) (L' : Finset (Fin 11 → ZMod 11)),
        (∀ c ∈ L', ∃ q : (ZMod 11)[X], q.natDegree < 2 ∧ c = fun i => q.eval (DD i)) →
        (∀ c ∈ L', 3 ≤ agree c w') →
        L'.card ≤ 18) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨w', L', hcard, hpoly, hclose⟩ := interior_list_lower_bound_fifteen
    exact ⟨w', L', by rw [hcard], hpoly, hclose⟩
  · exact fun w' L' hpoly hclose => interior_list_upper_bound_eighteen w' L' hpoly hclose

/-! ### The radius `δ = 8/11` is strictly inside the open gap. -/

/-- **Gap placement.** The relative radius `δ = 8/11` (agreement `a = 3` out of `n = 11`) is
strictly between the Johnson radius `1 − √ρ` and the capacity radius `1 − ρ = 9/11`, for the rate
`ρ = 2/11`.

* Upper side `8/11 < 9/11` is immediate.
* Lower side `1 − √(2/11) < 8/11`, i.e. `3/11 < √(2/11)`: squaring (both sides nonneg),
  `9/121 < 2/11 = 22/121`. ✓

So this verified `[15, 18]` window is genuinely a data point in the *interior* of the open proximity
gap, not in the already-resolved Johnson or capacity regimes. -/
theorem eight_elevenths_strictly_interior :
    1 - Real.sqrt (2 / 11) < (8 : ℝ) / 11 ∧ (8 : ℝ) / 11 < 1 - 2 / 11 := by
  refine ⟨?_, by norm_num⟩
  -- want 1 - √(2/11) < 8/11, i.e. 3/11 < √(2/11).
  have hlt : (3 : ℝ) / 11 < Real.sqrt (2 / 11) := by
    have hnn : (0 : ℝ) ≤ 3 / 11 := by norm_num
    rw [Real.lt_sqrt hnn]
    norm_num
  linarith

end ArkLib.CodingTheory.TinyInteriorF11

#print axioms ArkLib.CodingTheory.TinyInteriorF11.interior_list_two_sided_f11
#print axioms ArkLib.CodingTheory.TinyInteriorF11.interior_list_upper_bound_eighteen
#print axioms ArkLib.CodingTheory.TinyInteriorF11.interior_list_lower_bound_fifteen
