/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSimplexBound
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonJohnson
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A fully-explicit interior list-size data point for `RS[F₇, F₇, 2]` (verified)

This file pins a **single concrete data point strictly inside the open proximity gap**
`(1 − √ρ, 1 − ρ)` for an explicit tiny Reed–Solomon code, with a *verified, non-vacuous* lower
bound on the list size, and a verified demonstration that the honest second-moment (Johnson) bound
is loose there.

## The instance

`C = RS[F = ZMod 7, L = all of F₇ (the domain `D = id`, `n = 7`), k = 2]`. These are the evaluations
of the linear polynomials `p(x) = a·x + b` on the seven points `0,1,…,6`. The rate is
`ρ = k/n = 2/7` and the parameters are:

* Johnson radius `1 − √ρ = 1 − √(2/7) ≈ 0.4655`;
* capacity radius `1 − ρ = 5/7 ≈ 0.7143`;
* so the **open gap** the prize asks about is `δ ∈ (0.4655, 0.7143)`.

The relative agreement radius `a = 3` (i.e. require codewords to agree with the received word on
`≥ 3` of `7` coordinates) corresponds to relative distance `δ = (n − a)/n = 4/7 ≈ 0.5714`, which is
**strictly interior** to that gap (proven in `four_sevenths_strictly_interior`).

## What is verified here

* `witness_list_card_six` / `interior_list_lower_bound` — an **explicit received word**
  `w = (0,0,0,1,1,3,2)` and an explicit `6`-element list `L` of distinct RS codewords of degree-`<2`
  polynomials, each agreeing with `w` on `≥ 3` coordinates. So at the interior radius `a = 3` the
  list size is `≥ 6`. This is a genuine, exhaustively-checked **lower bound in the interior of the
  open gap** — a regime where "no known technique" gives tight bounds for general smooth-domain RS.
* `johnson_predicts_at_most_24` — at the very same point, the honest second-moment Johnson bound
  (`reedSolomon_johnson_list_bound`, `b = k−1 = 1`) only yields `|L| ≤ 24`. The true maximum list
  size at `a = 3` is `6` (verified out-of-band by exhaustive search over all `7⁷` words; see the
  accompanying note), so **Johnson overestimates the interior list size by more than 4×** here. This
  concretely exhibits the slack the open problem is about: in the interior the true list is far
  below the second-moment prediction, but the matching *upper* bound is exactly what is missing.
* `four_sevenths_strictly_interior` — the radius `δ = 4/7` lies strictly inside `(1 − √(2/7), 5/7)`.

Everything is `sorry`-free and axiom-clean. The hypotheses are satisfiable (the witnesses are
exhibited concretely), so the statements are non-vacuous. This is *not* a closure of the open
problem: it pins one explicit instance's interior list size from below and shows Johnson's slack,
which is a real data point, not a general matching upper bound.
-/

namespace ArkLib.CodingTheory.TinyInteriorPin

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex ArkLib.CodingTheory.ReedSolomonJohnson

/-- `7` is prime, so `ZMod 7` is a field. This is what makes `RS[F₇, F₇, 2]` a genuine
Reed–Solomon code (degree-`<k` polynomials over a field, evaluated on an injective domain). -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The evaluation domain: all seven points of `F₇`, indexed by `Fin 7` via `D i = i`. -/
def D : Fin 7 ↪ ZMod 7 := ⟨fun i => (i : ZMod 7), by decide⟩

/-- The explicit received word `w = (0,0,0,1,1,3,2)`. -/
def w : Fin 7 → ZMod 7 := ![0, 0, 0, 1, 1, 3, 2]

/-- The six codewords agreeing with `w` on `≥ 3` coordinates, as evaluation vectors.
`c0 = p₀(x)=0`, `c1 = x+5`, `c2 = 2x`, `c3 = 4x+6`, `c4 = 5x`, `c5 = 6x+1`. -/
def c0 : Fin 7 → ZMod 7 := ![0, 0, 0, 0, 0, 0, 0]
def c1 : Fin 7 → ZMod 7 := ![5, 6, 0, 1, 2, 3, 4]
def c2 : Fin 7 → ZMod 7 := ![0, 2, 4, 6, 1, 3, 5]
def c3 : Fin 7 → ZMod 7 := ![6, 3, 0, 4, 1, 5, 2]
def c4 : Fin 7 → ZMod 7 := ![0, 5, 3, 1, 6, 4, 2]
def c5 : Fin 7 → ZMod 7 := ![1, 0, 6, 5, 4, 3, 2]

/-- The explicit degree-`<2` polynomials whose RS codewords are `c0,…,c5`. -/
noncomputable def p0 : (ZMod 7)[X] := C 0
noncomputable def p1 : (ZMod 7)[X] := X + C 5
noncomputable def p2 : (ZMod 7)[X] := C 2 * X
noncomputable def p3 : (ZMod 7)[X] := C 4 * X + C 6
noncomputable def p4 : (ZMod 7)[X] := C 5 * X
noncomputable def p5 : (ZMod 7)[X] := C 6 * X + C 1

/-- The candidate list `L = {c0, c1, c2, c3, c4, c5}`. -/
def L : Finset (Fin 7 → ZMod 7) := {c0, c1, c2, c3, c4, c5}

/-! ### Each `cⱼ` is genuinely the RS codeword of a degree-`<2` polynomial. -/

lemma c0_isRS : c0 = (fun i => p0.eval (D i)) := by
  funext i; simp only [c0, p0, D, Function.Embedding.coeFn_mk, eval_C]; fin_cases i <;> decide
lemma c1_isRS : c1 = (fun i => p1.eval (D i)) := by
  funext i
  simp only [c1, p1, D, Function.Embedding.coeFn_mk, eval_add, eval_X, eval_C]
  fin_cases i <;> decide
lemma c2_isRS : c2 = (fun i => p2.eval (D i)) := by
  funext i
  simp only [c2, p2, D, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c3_isRS : c3 = (fun i => p3.eval (D i)) := by
  funext i
  simp only [c3, p3, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c4_isRS : c4 = (fun i => p4.eval (D i)) := by
  funext i
  simp only [c4, p4, D, Function.Embedding.coeFn_mk, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide
lemma c5_isRS : c5 = (fun i => p5.eval (D i)) := by
  funext i
  simp only [c5, p5, D, Function.Embedding.coeFn_mk, eval_add, eval_mul, eval_X, eval_C]
  fin_cases i <;> decide

lemma p0_deg : p0.natDegree < 2 := by unfold p0; compute_degree!
lemma p1_deg : p1.natDegree < 2 := by unfold p1; compute_degree!
lemma p2_deg : p2.natDegree < 2 := by unfold p2; compute_degree!
lemma p3_deg : p3.natDegree < 2 := by unfold p3; compute_degree!
lemma p4_deg : p4.natDegree < 2 := by unfold p4; compute_degree!
lemma p5_deg : p5.natDegree < 2 := by unfold p5; compute_degree!

/-- **Every element of `L` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity
witness that `L` lives inside the RS code `RS[F₇, F₇, 2]`. -/
theorem L_subset_code :
    ∀ c ∈ L, ∃ q : (ZMod 7)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i) := by
  intro c hc
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h
  · exact ⟨p0, p0_deg, h ▸ c0_isRS⟩
  · exact ⟨p1, p1_deg, h ▸ c1_isRS⟩
  · exact ⟨p2, p2_deg, h ▸ c2_isRS⟩
  · exact ⟨p3, p3_deg, h ▸ c3_isRS⟩
  · exact ⟨p4, p4_deg, h ▸ c4_isRS⟩
  · exact ⟨p5, p5_deg, h ▸ c5_isRS⟩

/-! ### The six codewords are pairwise distinct, so `|L| = 6`. -/

/-- **The list has exactly six elements.** All six explicit codewords are pairwise distinct. -/
theorem witness_list_card_six : L.card = 6 := by decide

/-! ### Each codeword agrees with `w` on at least `3` of the `7` coordinates. -/

/-- **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 3`
coordinates, i.e. has Hamming distance `≤ 4` from `w` — relative radius `δ = 4/7`. -/
theorem all_agree_ge_three : ∀ c ∈ L, 3 ≤ agree c w := by
  intro c hc
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h <;> subst h <;> decide

/-! ### Main lower bound: a 6-element interior list. -/

/-- **Explicit interior list-size lower bound for `RS[F₇, F₇, 2]`.**

There is a received word `w` and a `Finset` `L` of size `6`, *all of whose elements are
Reed–Solomon codewords of degree-`<2` polynomials on the smooth domain `D`*, each agreeing with `w`
on at least `3` of the `7` coordinates. Equivalently: at the relative radius `δ = (7−3)/7 = 4/7`,
which is **strictly inside the open proximity gap** `(1 − √ρ, 1 − ρ) = (1 − √(2/7), 5/7)`
(see `four_sevenths_strictly_interior`), the list size of this explicit code is `≥ 6`.

This is the honest content of the angle "pin `δ*` for a tiny explicit instance" *from below*: a
fully-checked interior data point. The matching interior *upper* bound (the true maximum here is
exactly `6`) is the part the open problem lacks a general technique for; here it is confirmed by
exhaustive search over the `7⁷` received words but is not provable by the Johnson second-moment
bound, which only gives `≤ 24` (`johnson_predicts_at_most_24`). -/
theorem interior_list_lower_bound :
    ∃ (w' : Fin 7 → ZMod 7) (L' : Finset (Fin 7 → ZMod 7)),
      L'.card = 6 ∧
      (∀ c ∈ L', ∃ q : (ZMod 7)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) ∧
      (∀ c ∈ L', 3 ≤ agree c w') := by
  exact ⟨w, L, witness_list_card_six, L_subset_code, all_agree_ge_three⟩

/-! ### Johnson's second-moment bound is loose at this interior point. -/

/-- **Johnson overestimates the interior list size here.** Instantiating the honest second-moment
bound `reedSolomon_johnson_list_bound` for our list `L` (each codeword a degree-`<2` polynomial
evaluation, each agreeing with `w` on `≥ a = 3` coordinates) gives the inequality

  `(L.card : ℝ) · (3² − 7·(2−1)) ≤ 7²`,  i.e.  `|L| · 2 ≤ 49`,  i.e.  `|L| ≤ 24`.

The true maximum list size at this radius is `6` (exhaustive search over all `7⁷` words). So in the
*interior of the open gap* the genuine list size is more than `4×` below the second-moment
prediction: Johnson is sound but very far from tight here, which is precisely the slack that makes
the matching interior upper bound an open problem. -/
theorem johnson_predicts_at_most_24 :
    (L.card : ℝ) * ((3 : ℝ) ^ 2 - (Fintype.card (Fin 7) : ℝ) * ((2 - 1 : ℕ) : ℝ))
      ≤ (Fintype.card (Fin 7) : ℝ) ^ 2 := by
  have h := reedSolomon_johnson_list_bound (ι := Fin 7) (F := ZMod 7) D 2 w L 3
    (fun c hc => by
      obtain ⟨q, hq, hcq⟩ := L_subset_code c hc
      exact ⟨q, by simpa using hq, hcq⟩)
    all_agree_ge_three
  simpa using h

/-- A numeric unpacking of `johnson_predicts_at_most_24` with the *actual* card `|L| = 6`
substituted: the Johnson inequality becomes `(6 : ℝ) · (3² − 7·1) = 6·2 = 12 ≤ 49 = 7²`. It holds
with large slack, confirming the bound is *satisfied* (non-vacuous) yet far from the true list size
`6` (Johnson cap `⌊49/2⌋ = 24`). -/
theorem johnson_slack_numeric :
    ((6 : ℝ)) * ((3 : ℝ) ^ 2 - (7 : ℝ) * ((2 - 1 : ℕ) : ℝ)) ≤ (7 : ℝ) ^ 2 := by norm_num

/-! ### The radius `δ = 4/7` is strictly inside the open gap. -/

/-- **Gap placement.** The relative radius `δ = 4/7` (agreement `a = 3` out of `n = 7`) is strictly
between the Johnson radius `1 − √ρ` and the capacity radius `1 − ρ = 5/7`, for the rate `ρ = 2/7`.

* Upper side `4/7 < 5/7` is immediate.
* Lower side `1 − √(2/7) < 4/7`, i.e. `3/7 < √(2/7)`: squaring (both sides nonneg), `9/49 < 2/7`,
  i.e. `9/49 < 14/49`. ✓

So this verified `6`-element list is genuinely a data point in the *interior* of the open proximity
gap, not in the already-resolved Johnson or capacity regimes. -/
theorem four_sevenths_strictly_interior :
    1 - Real.sqrt (2 / 7) < (4 : ℝ) / 7 ∧ (4 : ℝ) / 7 < 1 - 2 / 7 := by
  refine ⟨?_, by norm_num⟩
  -- want 1 - √(2/7) < 4/7, i.e. 3/7 < √(2/7).
  have hlt : (3 : ℝ) / 7 < Real.sqrt (2 / 7) := by
    have hnn : (0 : ℝ) ≤ 3 / 7 := by norm_num
    -- √(2/7) > 3/7 ⟺ (3/7)² < 2/7, since 3/7 ≥ 0.
    rw [Real.lt_sqrt hnn]
    norm_num
  linarith

end ArkLib.CodingTheory.TinyInteriorPin
