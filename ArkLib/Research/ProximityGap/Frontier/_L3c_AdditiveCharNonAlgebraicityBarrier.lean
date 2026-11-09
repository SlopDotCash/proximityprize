/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (L3c)
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# L3c — the additive-character DEGREE barrier: a direct polynomial-surrogate Stepanov attack on the
  sup-norm needs field-scale degree `≥ p − 1` (#444)

## THE PRIZE OBJECT (BGK / Paley sup-norm wall)

`M(n) = max_{b ≠ 0} |η_b|`, `η_b = ∑_{x ∈ μ_n} e_p(b·x)`, for the thin 2-power subgroup
`μ_n ⊆ F_p^×` (`n = 2^μ ∣ p − 1`, `p` prime, `β = log_n p ∈ [4,5]`). Target `M(n) ≤ C√(n log(p/n))`.

## THE BRIEF'S ANGLE AND WHY IT NEEDS A FRESH FENCE

L3a's "DC-domination" finding suggests a **signed / Stepanov-style auxiliary-polynomial** argument
that does NOT go through `|η_b|^{2r}` (the even-moment / energy route, which is DC-dominated and
reduces to the in-tree W7 crux). The campaign already fenced two Stepanov sub-routes:
* `StepanovStructuredVacuous` / `_wf5G2_stepanov_supnorm`: Stepanov on the **polynomial root count**
  collapses — `X^n − 1` is **separable**, so the multiplicity is pinned to `M = 1` (no `√` saving).
* `StepanovWeilQVacuous`: the Stepanov–Weil `√q` FIELD bound is vacuous because `p ≈ n^4 ≫ n^2`.

Those fence the route where the auxiliary polynomial counts ROOTS of an algebraic relation. They do
NOT address the *direct* attack: build an `F_p`-polynomial surrogate `g` whose VALUES over `μ_n`
reconstruct the additive phase `e_p(b·x)` finely enough to expose the cancellation in `η_b`.

## THE L3c FENCE (this file): a frequency-sensitive surrogate has degree `≥ p − 1`

The decisive obstruction is a THEOREM. The only Stepanov-countable invariant of `g`'s value
distribution that can depend on the encoded frequency `b` is its full-field sum `∑_{x} g(x)` (the
`b = 0` / principal-character projection). But:

  **(K)  Every polynomial `g ∈ F_p[X]` with `natDegree g < p − 1` has `∑_{x ∈ F_p} g(x) = 0`.**

(`poly_sum_zero_of_natDegree_lt`, from Mathlib `FiniteField.sum_pow_lt_card_sub_one`, termwise.)

So a low-degree surrogate carries the same full-field signal `0` regardless of `b` — it cannot
distinguish the worst frequency `b*`. Contrapositive:

  **(L3c-FENCE)  Any surrogate that is frequency-SENSITIVE (its full-field sum is nonzero, so it can
  distinguish `b ≠ 0`) must have `natDegree ≥ p − 1`.**

A degree-`≥ p−1` auxiliary gives a Stepanov degree budget at FIELD scale (`≈ n^β`), not subgroup
scale (`n`) — strictly worse than the trivial `M(n) ≤ n`. This is a genuinely DIFFERENT side from
the separability fence: there the obstruction is `M = 1` (no multiplicity); here it is
`deg ≥ p − 1` (the only `b`-sensitive algebraic invariant lives at field-scale degree).

## What is PROVEN here (all axiom-clean: `propext, Classical.choice, Quot.sound`)

1. `poly_sum_zero_of_natDegree_lt` — kernel (K): `natDegree g < q − 1 ⟹ ∑_{x:K} g(x) = 0`.
2. `monomial_sum_zero_below_top` — the pure monomial `X^i` for `i < q − 1` has full-field sum `0`
   (no monomial below the top degree `q − 1` is frequency-sensitive).
3. `freqSensitive_forces_high_degree` — **the fence**: `FreqSensitive g ⟹ natDegree g ≥ q − 1`.
4. `direct_surrogate_below_trivial_impossible` — prize-scale verdict: with `q − 1 ≥ n²`
   (automatic for `β ≥ 2`), a frequency-sensitive surrogate has `(natDegree g : ℝ) ≥ n²`, so its
   degree budget exceeds even the trivial degree bound `n`.

## SCOPE / HONESTY

This fences the *direct-surrogate* Stepanov route by a degree barrier; it is the easy LOWER /
no-go direction. It does NOT prove `M(n) ≤ C√(n log(p/n))` (the analytic UPPER bound — the open BGK
wall). The only frequency-sensitive algebraic invariant of `(η_b)_b` that survives the degree
barrier is the **even moment** `∑_b η_b^{2r} = p · E_r(μ_n)` (a degree-`2r` symmetric class function
whose full-field projection is nonzero) — i.e. the energy/Wick route, terminal at the BGK wall
(`DCWickWraparoundTransfer`). That residual is stated only in prose here; it is **not** formalized as
a named Prop (a faithful encoding would be a meta-statement about the algebra of `Gal`-invariant
class functions, which this file does not attempt — and a naive `∃ c, Φ η = c (…)` encoding is
vacuous because `c` is an unconstrained set-function, so it is deliberately omitted).

## VERDICT

**REDUCES-TO-WALL via "direct-surrogate degree barrier" — fences a genuinely new side**
(deg ≥ p−1) distinct from the recorded multiplicity barrier (M = 1). Together they exhaust the
auxiliary-polynomial method on the sup-norm; the surviving even-moment route is the BGK wall.

## References
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement* (#444).
- Mathlib `FiniteField.sum_pow_lt_card_sub_one` (the power-sum vanishing identity = kernel K).
- In-tree: `StepanovStructuredVacuous`, `StepanovWeilQVacuous`, `_wf5G2_stepanov_supnorm`
  (the dual multiplicity fences); `_wf7W7_NewtonSlopeDCDominance` (the surviving moment route).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.L3c

open Polynomial BigOperators Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### §1  The algebraic kernel (K): low-degree polynomials are full-field-sum blind. -/

/-- **Kernel (K).**  Over a finite field `K` of cardinality `q`, every polynomial `g` with
`natDegree g < q − 1` has full-field sum `∑_{x:K} g.eval x = 0`.  Proof: expand `g` in monomials
and use `FiniteField.sum_pow_lt_card_sub_one` (`∑ x^i = 0` for `i < q − 1`) termwise. -/
theorem poly_sum_zero_of_natDegree_lt (g : K[X]) (hdeg : g.natDegree < Fintype.card K - 1) :
    ∑ x : K, g.eval x = 0 := by
  classical
  have hsum : ∀ x : K, g.eval x = ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * x ^ i := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
  calc ∑ x : K, g.eval x
      = ∑ x : K, ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * x ^ i := by
        exact Finset.sum_congr rfl (fun x _ => hsum x)
    _ = ∑ i ∈ Finset.range (g.natDegree + 1), ∑ x : K, g.coeff i * x ^ i :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * (∑ x : K, x ^ i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        have hilt : i < Fintype.card K - 1 := by omega
        rw [FiniteField.sum_pow_lt_card_sub_one (K := K) i hilt, mul_zero]

/-- **Monomial vanishing below the top degree.**  For the pure monomial `X^i` with `i < q − 1`, the
full-field sum is `0` — no monomial below `X^{q−1}` is frequency-sensitive. -/
theorem monomial_sum_zero_below_top (i : ℕ) (hi : i < Fintype.card K - 1) :
    ∑ x : K, (X ^ i : K[X]).eval x = 0 := by
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  exact FiniteField.sum_pow_lt_card_sub_one (K := K) i hi

/-! ### §2  The fence: a frequency-sensitive surrogate has degree `≥ q − 1`. -/

/-- A polynomial surrogate is **frequency-sensitive** if its full-field sum (the only Stepanov-
countable invariant of its value distribution that can depend on the encoded frequency `b`) is
nonzero — i.e. it sees something beyond the principal/DC projection. -/
def FreqSensitive (g : K[X]) : Prop := (∑ x : K, g.eval x) ≠ 0

/-- **The L3c fence (degree barrier).**  Any frequency-sensitive surrogate `g` has
`natDegree g ≥ q − 1`.  Contrapositive of kernel (K): a degree-`< q−1` polynomial sums to `0`,
hence is NOT frequency-sensitive.  So the direct-surrogate Stepanov attack on `|η_b|` can only use
auxiliaries of field-scale degree `≥ q − 1 ≈ n^β`. -/
theorem freqSensitive_forces_high_degree (g : K[X]) (hfs : FreqSensitive g) :
    Fintype.card K - 1 ≤ g.natDegree := by
  by_contra hlt
  push Not at hlt
  exact hfs (poly_sum_zero_of_natDegree_lt g hlt)

/-- **Low-degree blindness, contrapositive form.**  A polynomial whose degree is below the
top finite-field degree `q − 1` is not frequency-sensitive: its full-field sum is forced
to vanish.  This is the exact consumer form used to rule out subgroup-scale direct
surrogates before taking the prize-scale arithmetic corollary below. -/
theorem not_freqSensitive_of_natDegree_lt (g : K[X])
    (hdeg : g.natDegree < Fintype.card K - 1) : ¬ FreqSensitive g := by
  intro hfs
  exact hfs (poly_sum_zero_of_natDegree_lt g hdeg)

/-- **Subgroup-scale direct surrogates are blind.**  If a proposed direct algebraic surrogate
has degree at most a subgroup-scale budget `n`, and `n < q − 1`, then it cannot be
frequency-sensitive.  Thus any direct-surrogate Stepanov attack must leave the subgroup
degree scale and pay the field-scale `q − 1` barrier. -/
theorem no_subgroupScale_freqSensitive (g : K[X]) (n : ℕ)
    (hdeg : g.natDegree ≤ n) (hn : n < Fintype.card K - 1) : ¬ FreqSensitive g := by
  exact not_freqSensitive_of_natDegree_lt g (lt_of_le_of_lt hdeg hn)

/-! ### §3  Real-arithmetic packaging at the prize scale `q − 1 ≥ n²`. -/

/-- **The prize-scale verdict.**  In the prize regime the field is much larger than the subgroup:
`q − 1 ≥ n²` (automatic since `β ≥ 2`).  A frequency-sensitive surrogate then has
`(natDegree g : ℝ) ≥ n²`, so the direct-surrogate Stepanov count `M·|S| ≤ deg g` carries a degree
budget `≥ n²` — strictly above the trivial degree bound `n`.  Hence the direct route cannot even
match the trivial `M(n) ≤ n`, let alone reach the prize `C√(n log(p/n))`. -/
theorem direct_surrogate_below_trivial_impossible
    (g : K[X]) (hfs : FreqSensitive g) (n : ℕ)
    (hprize : (n : ℝ) ^ 2 ≤ ((Fintype.card K : ℝ) - 1)) :
    (n : ℝ)^2 ≤ (g.natDegree : ℝ) := by
  have hfence : Fintype.card K - 1 ≤ g.natDegree := freqSensitive_forces_high_degree g hfs
  have hcast : ((Fintype.card K : ℝ) - 1) ≤ (g.natDegree : ℝ) := by
    have hpos : 1 ≤ Fintype.card K := Fintype.card_pos
    have : ((Fintype.card K - 1 : ℕ) : ℝ) ≤ (g.natDegree : ℝ) := by exact_mod_cast hfence
    rwa [Nat.cast_sub hpos, Nat.cast_one] at this
  linarith

/-- **Prize-regime subgroup-scale blindness.**  In the prize-sized window `n² ≤ q − 1`,
every degree-`≤ n` direct surrogate is frequency-blind (for the nontrivial case `2 ≤ n`).
This is the usable no-go form: subgroup-scale auxiliary polynomials cannot see the worst
frequency; frequency sensitivity starts only at field-scale degree. -/
theorem no_subgroupScale_freqSensitive_of_prizeNat
    (g : K[X]) (n : ℕ) (hn : 2 ≤ n) (hprize : n ^ 2 ≤ Fintype.card K - 1)
    (hdeg : g.natDegree ≤ n) : ¬ FreqSensitive g := by
  apply no_subgroupScale_freqSensitive g n hdeg
  have hn_sq : n < n ^ 2 := by
    nlinarith [hn]
  exact lt_of_lt_of_le hn_sq hprize

end ArkLib.ProximityGap.Frontier.L3c

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Frontier.L3c.poly_sum_zero_of_natDegree_lt
#print axioms ArkLib.ProximityGap.Frontier.L3c.monomial_sum_zero_below_top
#print axioms ArkLib.ProximityGap.Frontier.L3c.freqSensitive_forces_high_degree
#print axioms ArkLib.ProximityGap.Frontier.L3c.not_freqSensitive_of_natDegree_lt
#print axioms ArkLib.ProximityGap.Frontier.L3c.no_subgroupScale_freqSensitive
#print axioms ArkLib.ProximityGap.Frontier.L3c.direct_surrogate_below_trivial_impossible
#print axioms ArkLib.ProximityGap.Frontier.L3c.no_subgroupScale_freqSensitive_of_prizeNat
