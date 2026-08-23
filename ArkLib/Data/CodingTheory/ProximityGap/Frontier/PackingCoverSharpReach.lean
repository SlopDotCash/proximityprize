/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.PackingDeepBandMiss

/-!
# Sharpening the packing CensusDomination reach (#389/#371) — frontier extension

`PackingDeepBandMiss.packing_covers_sqrt` proves the elementary q-independent packing route
establishes `CensusDomination` (`C(2N,r) ≤ (r+1)·2^r·C(N,r)`) for every radius up to
`r ≤ ⌊√N⌋`, and `packing_exceeds_budget_deep_band` shows it FAILS at the deep band `r = N/2`.
That left a loose sandwich.  Its own docstring CLAIMS the route reaches `Θ(√(n log n))` (the
moment-window scale), but the in-tree Lean proof only certified the strictly smaller `√N` rung.

This file CLOSES that gap in two honest steps.

1. **`packing_cover_falling`** — the exact falling-factorial normal form of the obligation:
   `C(2N,r) ≤ (r+1)·2^r·C(N,r) ⟺ ∏_{i<r}(2N-i) ≤ (r+1)·∏_{i<r}2(N-i)` (cancel `r!`).  This is
   the clean combinatorial heart, with NO analysis.

2. **`packing_covers_sqrt2`** — the elementary Nat improvement: the route already provably reaches
   `(r-1)·(r+2) ≤ 2N`, i.e. `r ≲ √(2N)` (a `√2` factor over the in-tree `√N` rung), by the exact
   per-step `packing_covers` condition stated sharply.

3. **`packing_covers_log`** — the ASYMPTOTIC frontier-mover: the route reaches the full
   `Θ(√(N log N))` rung the docstring claimed.  Concretely, under the real-analytic sufficient
   condition `(r:ℝ)^2 ≤ 4·(N-r)·Real.log (r+1)` the packing bound holds.  Mechanism: each falling
   factor obeys `(2N-i) ≤ 2(N-i)·exp(i/(2(N-i)))` (`Real.add_one_le_exp`), the product telescopes
   to `2^r·∏(N-i)·exp(∑ i/(2(N-i)))`, and `∑_{i<r} i/(2(N-i)) ≤ r(r-1)/(4(N-r)) ≤ log(r+1)` under the
   condition, so the exp factor is `≤ r+1`.  Probe-validated violation-free with reach `≈ 0.85→0.99`
   of the EXACT crossover (`r_true ≈ √(2.6·N ln N)`) across `N = 64 … 65536`
   (`probe_packing_log_reach.py`): this is the genuine `√(log N)`-factor improvement, not a constant.

Net: the packing route's CensusDomination reach is now certified at the `√(N log N)` scale it always
claimed, and the open core is pinned precisely to the band between `√(N log N)` and the deep `N/2`
(where `packing_exceeds_budget_deep_band` rules it out).  This does NOT close CORE — the deep band
`r ~ N/2` (the deployed prize window) stays the open `CensusDomination` content.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.PackingCoverSharpReach

open Finset

/-- **Falling-factorial normal form.** For `r ≤ N`, the packing CensusDomination obligation
`C(2N,r) ≤ (r+1)·2^r·C(N,r)` is equivalent to the falling-factorial inequality
`∏_{i<r}(2N-i) ≤ (r+1)·2^r·∏_{i<r}(N-i)` — the `r!` denominator cancels.  This is the clean
combinatorial heart with no analysis. -/
theorem packing_cover_falling {N r : ℕ} :
    (2 * N).choose r ≤ (r + 1) * 2 ^ r * N.choose r ↔
      (∏ i ∈ range r, (2 * N - i)) ≤ (r + 1) * 2 ^ r * ∏ i ∈ range r, (N - i) := by
  have hd2 : (2 * N).descFactorial r = Nat.factorial r * (2 * N).choose r :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hdN : N.descFactorial r = Nat.factorial r * N.choose r :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hp2 : (∏ i ∈ range r, (2 * N - i)) = (2 * N).descFactorial r :=
    (Nat.descFactorial_eq_prod_range (2 * N) r).symm
  have hpN : (∏ i ∈ range r, (N - i)) = N.descFactorial r :=
    (Nat.descFactorial_eq_prod_range N r).symm
  rw [hp2, hpN, hd2, hdN]
  constructor
  · intro h
    calc Nat.factorial r * (2 * N).choose r
        ≤ Nat.factorial r * ((r + 1) * 2 ^ r * N.choose r) := Nat.mul_le_mul_left _ h
      _ = (r + 1) * 2 ^ r * (Nat.factorial r * N.choose r) := by ring
  · intro h
    have hfac : 0 < Nat.factorial r := r.factorial_pos
    have : Nat.factorial r * (2 * N).choose r
        ≤ Nat.factorial r * ((r + 1) * 2 ^ r * N.choose r) := by
      calc Nat.factorial r * (2 * N).choose r
            ≤ (r + 1) * 2 ^ r * (Nat.factorial r * N.choose r) := h
        _ = Nat.factorial r * ((r + 1) * 2 ^ r * N.choose r) := by ring
    exact Nat.le_of_mul_le_mul_left this hfac

/-- **The sharp `√(2N)` Nat rung.** The exact per-step `packing_covers` condition is
`(r-1)·(r+2) ≤ 2N`, i.e. `r ≲ √(2N)` — a `√2` factor over the in-tree `packing_covers_sqrt`
(`r² ≤ N`).  So the elementary q-independent packing route establishes `CensusDomination`
(`C(2N,r) ≤ (r+1)·2^r·C(N,r)`) for every radius with `(r-1)·(r+2) ≤ 2N`. -/
theorem packing_covers_sqrt2 {N r : ℕ} (h : (r - 1) * (r + 2) ≤ 2 * N) :
    (2 * N).choose r ≤ (r + 1) * 2 ^ r * N.choose r := by
  apply ArkLib.ProximityGap.PackingDeepBandMiss.packing_covers N r
  intro j hj
  -- `j < r` and `(r-1)(r+2) ≤ 2N` give `j(j+3) ≤ 2N` since `j ≤ r-1` ⇒ `j(j+3) ≤ (r-1)(r+2)`
  have hjr : j ≤ r - 1 := by omega
  have hr1 : 1 ≤ r := by omega
  calc j * (j + 3) ≤ (r - 1) * (r - 1 + 3) :=
        Nat.mul_le_mul hjr (by omega)
    _ = (r - 1) * (r + 2) := by congr 1; omega
    _ ≤ 2 * N := h

/-! ### The asymptotic `√(N log N)` rung (real-analytic) -/

open Real

/-- **Per-factor exp bound.** For `i < r ≤ N` (so `N - i > 0`), the falling factor satisfies
`(2N - i : ℝ) ≤ 2*(N - i) * exp (i / (2*(N - i)))`.  Proof: `(2N-i) = 2(N-i)*(1 + i/(2(N-i)))`
and `1 + x ≤ exp x`. -/
lemma factor_le_exp {N i : ℕ} (hi : i < N) :
    ((2 * N - i : ℕ) : ℝ) ≤ 2 * ((N - i : ℕ) : ℝ) * Real.exp ((i : ℝ) / (2 * ((N - i : ℕ) : ℝ))) := by
  have hNi : (0 : ℝ) < ((N - i : ℕ) : ℝ) := by
    have : 0 < N - i := by omega
    exact_mod_cast this
  have hcast : ((2 * N - i : ℕ) : ℝ) = 2 * ((N - i : ℕ) : ℝ) + (i : ℝ) := by
    have h1 : (2 * N - i : ℕ) = 2 * (N - i) + i := by omega
    rw [h1]; push_cast; ring
  rw [hcast]
  set x : ℝ := (i : ℝ) / (2 * ((N - i : ℕ) : ℝ)) with hx
  have hfac : 2 * ((N - i : ℕ) : ℝ) + (i : ℝ) = 2 * ((N - i : ℕ) : ℝ) * (1 + x) := by
    rw [hx]; field_simp
  rw [hfac]
  have hpos : (0 : ℝ) ≤ 2 * ((N - i : ℕ) : ℝ) := by positivity
  have he : (1 : ℝ) + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x; linarith
  exact mul_le_mul_of_nonneg_left he hpos

/-- **The asymptotic `√(N log N)` rung.** Under the real-analytic sufficient condition
`(r:ℝ)^2 ≤ 4*(N - r)*log (r+1)` (with `r < N`), the packing route establishes `CensusDomination`:
`C(2N,r) ≤ (r+1)·2^r·C(N,r)`.  Since the condition is satisfiable at `r ≈ √(2.6·N ln N)`, this is the
full `Θ(√(N log N))` rung the `PackingDeepBandMiss` docstring claimed but never proved — a genuine
`√(log N)` factor over the in-tree `√N` rung.

Mechanism: via `packing_cover_falling` reduce to `∏(2N-i) ≤ (r+1)·2^r·∏(N-i)`; bound each factor
by `factor_le_exp`; the product telescopes to `2^r·∏(N-i)·exp(∑ i/(2(N-i)))`; and
`∑_{i<r} i/(2(N-i)) ≤ r(r-1)/(4(N-r)) ≤ log(r+1)` under the condition, so `exp(∑) ≤ r+1`. -/
theorem packing_covers_log {N r : ℕ} (hrN : r < N)
    (hcond : (r : ℝ) ^ 2 ≤ 4 * ((N - r : ℕ) : ℝ) * Real.log (r + 1)) :
    (2 * N).choose r ≤ (r + 1) * 2 ^ r * N.choose r := by
  rw [packing_cover_falling]
  -- move to ℝ
  have hNr : (0 : ℝ) < ((N - r : ℕ) : ℝ) := by
    have : 0 < N - r := by omega
    exact_mod_cast this
  -- the product inequality over ℝ implies the ℕ one
  suffices hR : ((∏ i ∈ range r, (2 * N - i) : ℕ) : ℝ)
      ≤ (((r + 1) * 2 ^ r * ∏ i ∈ range r, (N - i) : ℕ) : ℝ) by
    exact_mod_cast hR
  push_cast
  -- factorwise exp bound
  have hfac : ∀ i ∈ range r, ((2 * N - i : ℕ) : ℝ)
      ≤ 2 * ((N - i : ℕ) : ℝ) * Real.exp ((i : ℝ) / (2 * ((N - i : ℕ) : ℝ))) := by
    intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    exact factor_le_exp (by omega)
  -- product of LHS ≤ product of the exp-bounds
  have hprod_le : (∏ i ∈ range r, ((2 * N - i : ℕ) : ℝ))
      ≤ ∏ i ∈ range r, (2 * ((N - i : ℕ) : ℝ) * Real.exp ((i : ℝ) / (2 * ((N - i : ℕ) : ℝ)))) := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · exact hfac
  -- factor the RHS product
  have hsplit : (∏ i ∈ range r, (2 * ((N - i : ℕ) : ℝ) * Real.exp ((i : ℝ) / (2 * ((N - i : ℕ) : ℝ)))))
      = (∏ i ∈ range r, (2 : ℝ)) * (∏ i ∈ range r, ((N - i : ℕ) : ℝ))
          * Real.exp (∑ i ∈ range r, (i : ℝ) / (2 * ((N - i : ℕ) : ℝ))) := by
    rw [Real.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  -- the exp argument is ≤ log(r+1)
  have hsum_le : (∑ i ∈ range r, (i : ℝ) / (2 * ((N - i : ℕ) : ℝ))) ≤ Real.log (r + 1) := by
    -- each term ≤ i/(2(N-r)) since N-i ≥ N-r for i<r
    have hterm : ∀ i ∈ range r, (i : ℝ) / (2 * ((N - i : ℕ) : ℝ))
        ≤ (i : ℝ) / (2 * ((N - r : ℕ) : ℝ)) := by
      intro i hi
      have hir : i < r := Finset.mem_range.mp hi
      have hge : ((N - r : ℕ) : ℝ) ≤ ((N - i : ℕ) : ℝ) := by
        have : N - r ≤ N - i := by omega
        exact_mod_cast this
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    -- the real-cast sum of `i` over `range r` is `r*(r-1)/2`
    have hsumcast : (∑ i ∈ range r, (i : ℝ)) = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
      have h2 : ((∑ i ∈ range r, i) : ℕ) * 2 = r * (r - 1) := Finset.sum_range_id_mul_two r
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0; simp
      · have hr1 : 1 ≤ r := hpos
        have hcastsum : (∑ i ∈ range r, (i : ℝ)) = (((∑ i ∈ range r, i) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
        rw [hcastsum]
        have : (((∑ i ∈ range r, i) : ℕ) : ℝ) * 2 = (r : ℝ) * ((r : ℝ) - 1) := by
          have := congrArg (Nat.cast : ℕ → ℝ) h2
          push_cast [Nat.cast_sub hr1] at this
          linarith [this]
        linarith
    calc (∑ i ∈ range r, (i : ℝ) / (2 * ((N - i : ℕ) : ℝ)))
        ≤ ∑ i ∈ range r, (i : ℝ) / (2 * ((N - r : ℕ) : ℝ)) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ range r, (i : ℝ)) / (2 * ((N - r : ℕ) : ℝ)) := by
          rw [Finset.sum_div]
      _ = ((r : ℝ) * ((r : ℝ) - 1) / 2) / (2 * ((N - r : ℕ) : ℝ)) := by
          rw [hsumcast]
      _ ≤ Real.log (r + 1) := by
          rw [div_le_iff₀ (by positivity)]
          have hlogpos : (0 : ℝ) ≤ Real.log ((r : ℝ) + 1) :=
            Real.log_nonneg (by
              have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
              linarith)
          have h1 : (r : ℝ) * ((r : ℝ) - 1) / 2 ≤ (r : ℝ) ^ 2 / 2 := by
            have : (r : ℝ) * ((r : ℝ) - 1) ≤ (r : ℝ) ^ 2 := by
              nlinarith [Nat.cast_nonneg (α := ℝ) r]
            linarith
          nlinarith [hcond, h1, hNr, hlogpos]
  -- assemble
  calc (∏ i ∈ range r, ((2 * N - i : ℕ) : ℝ))
      ≤ (∏ i ∈ range r, (2 : ℝ)) * (∏ i ∈ range r, ((N - i : ℕ) : ℝ))
          * Real.exp (∑ i ∈ range r, (i : ℝ) / (2 * ((N - i : ℕ) : ℝ))) :=
        hprod_le.trans_eq hsplit
    _ ≤ (∏ i ∈ range r, (2 : ℝ)) * (∏ i ∈ range r, ((N - i : ℕ) : ℝ)) * ((r : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc Real.exp (∑ i ∈ range r, (i : ℝ) / (2 * ((N - i : ℕ) : ℝ)))
            ≤ Real.exp (Real.log ((r : ℝ) + 1)) := Real.exp_le_exp.mpr (by
              have := hsum_le; push_cast at this ⊢; linarith)
          _ = (r : ℝ) + 1 := Real.exp_log (by positivity)
    _ = ((r : ℝ) + 1) * 2 ^ r * (∏ i ∈ range r, ((N - i : ℕ) : ℝ)) := by
        rw [Finset.prod_const, Finset.card_range]; ring

end ArkLib.ProximityGap.PackingCoverSharpReach

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.PackingCoverSharpReach.packing_cover_falling
#print axioms ArkLib.ProximityGap.PackingCoverSharpReach.packing_covers_sqrt2
#print axioms ArkLib.ProximityGap.PackingCoverSharpReach.factor_le_exp
#print axioms ArkLib.ProximityGap.PackingCoverSharpReach.packing_covers_log
