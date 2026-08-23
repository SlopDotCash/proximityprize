/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Issue #232 — the GS threshold converges to Johnson FROM ABOVE (the "reaches" direction)

The in-tree walls (`GSJohnsonWall`, `GSExactCountWall`) prove the GS certificate system can never
certify agreement below the Johnson radius `√(c·n)` (`c = k−1`), at any multiplicity.  This file
proves the matching **"reaches" direction**: for *every* multiplicity `m`, the system IS feasible at
an explicitly constructed agreement threshold `t` with

  `(t − 2)² · m ≤ c · n · (m + 1)`,

i.e. `t ≤ √(c·n·(1 + 1/m)) + 2` — converging to the Johnson radius `√(c·n)` from above as
`m → ∞`.  Construction: `D = ⌊√(c·n·m·(m+1))⌋ + 1` and `t = ⌊D/m⌋ + 1`; feasibility is
`c·n·m·(m+1) < D² ≤ D·(D+c)` (the defining property of `Nat.sqrt`) and `D < t·m` (division with
remainder).

**Consequence (the two-sided characterization, now complete):** the GS-certifiable agreement
threshold at multiplicity `m` is sandwiched

  `√(c·n)  <  t_GS(m)  ≤  √(c·n·(1+1/m)) + 2`,

so it equals the Johnson radius exactly in the `m → ∞` limit — neither more (the walls) nor less
(this file).  The machine the literature uses is thereby *characterized*, not merely bounded: any
certificate past Johnson for the prize must be a genuinely different system.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ArkLib.CodingTheory.GSReachesJohnson

/-- The constructed weighted-degree budget: `D = ⌊√(c·n·m·(m+1))⌋ + 1`. -/
def Dgs (c n m : ℕ) : ℕ := Nat.sqrt (c * n * m * (m + 1)) + 1

/-- The constructed agreement threshold: `t = ⌊D/m⌋ + 1`. -/
def tgs (c n m : ℕ) : ℕ := Dgs c n m / m + 1

/-- **Feasibility, constraint side:** `c·n·m·(m+1) < D·(D+c)` — from `x < (⌊√x⌋+1)² = D² ≤ D(D+c)`. -/
theorem feasible_constraints (c n m : ℕ) :
    c * n * m * (m + 1) < Dgs c n m * (Dgs c n m + c) := by
  have h1 : c * n * m * (m + 1) < (Nat.sqrt (c * n * m * (m + 1)) + 1) ^ 2 :=
    Nat.lt_succ_sqrt' _
  have h2 : (Dgs c n m) ^ 2 ≤ Dgs c n m * (Dgs c n m + c) := by
    rw [pow_two]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  calc c * n * m * (m + 1) < (Dgs c n m) ^ 2 := h1
    _ ≤ Dgs c n m * (Dgs c n m + c) := h2

/-- **Feasibility, root-order side:** `D < t·m` — division with remainder. -/
theorem feasible_root_order (c n m : ℕ) (hm : 0 < m) :
    Dgs c n m < tgs c n m * m := by
  have hdm := (Nat.div_add_mod (Dgs c n m) m).symm
  have hml : Dgs c n m % m < m := Nat.mod_lt _ hm
  rw [tgs, Nat.add_mul, Nat.one_mul]
  calc Dgs c n m = m * (Dgs c n m / m) + Dgs c n m % m := hdm
    _ < m * (Dgs c n m / m) + m := by omega
    _ = Dgs c n m / m * m + m := by ring

/-- **The convergence bound:** `(t − 2)² · m ≤ c·n·(m+1)`, i.e. `t ≤ √(c·n·(1+1/m)) + 2`.
Chain: `t − 2 ≤ ⌊√(cnm(m+1))⌋/m`, so `(t−2)²·m² ≤ (⌊√·⌋)² ≤ c·n·m·(m+1)`, and cancel one `m`. -/
theorem t_close_to_johnson (c n m : ℕ) (hm : 0 < m) :
    (tgs c n m - 2) ^ 2 * m ≤ c * n * (m + 1) := by
  set s := Nat.sqrt (c * n * m * (m + 1)) with hs
  -- t − 2 ≤ s/m  (since D = s+1 and (s+1)/m ≤ s/m + 1)
  have hstep : tgs c n m - 2 ≤ s / m := by
    have hdiv : (s + 1) / m ≤ s / m + 1 := by
      calc (s + 1) / m ≤ (s + m) / m := Nat.div_le_div_right (by omega)
        _ = s / m + 1 := Nat.add_div_right s hm
    rw [tgs, Dgs, ← hs]
    generalize hA : (s + 1) / m = A at hdiv ⊢
    generalize hB : s / m = B at hdiv ⊢
    omega
  -- (s/m)²·m² ≤ s² ≤ cnm(m+1)
  have hsq : (s / m) ^ 2 * m ^ 2 ≤ c * n * m * (m + 1) := by
    have h1 : s / m * m ≤ s := Nat.div_mul_le_self s m
    have h2 : (s / m * m) * (s / m * m) ≤ s * s := Nat.mul_le_mul h1 h1
    have h3 : s * s ≤ c * n * m * (m + 1) := by
      rw [hs]
      first
        | exact Nat.sqrt_le _
        | exact Nat.sqrt_le' _
        | exact Nat.sqrt_le_self _
        | simpa [pow_two] using Nat.sqrt_le' (c * n * m * (m + 1))
    calc (s / m) ^ 2 * m ^ 2 = (s / m * m) * (s / m * m) := by ring
      _ ≤ s * s := h2
      _ ≤ c * n * m * (m + 1) := h3
  -- cancel one factor of m
  have hmono : (tgs c n m - 2) ^ 2 * m ^ 2 ≤ (s / m) ^ 2 * m ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hstep 2)
  have hchain : (tgs c n m - 2) ^ 2 * m ^ 2 ≤ c * n * m * (m + 1) :=
    le_trans hmono hsq
  have hexp : (tgs c n m - 2) ^ 2 * m ^ 2 = m * ((tgs c n m - 2) ^ 2 * m) := by ring
  have hexp2 : c * n * m * (m + 1) = m * (c * n * (m + 1)) := by ring
  rw [hexp, hexp2] at hchain
  exact Nat.le_of_mul_le_mul_left hchain hm

/-- **The "reaches" theorem (bundled):** for every `c, n` and every multiplicity `m ≥ 1`, the GS
parameter system is feasible (`c·n·m·(m+1) < D·(D+c)` and `D < t·m`) at the constructed `(t, D)`,
with `t` converging to the Johnson radius: `(t−2)²·m ≤ c·n·(m+1)`.

Paired with the walls (`GSJohnsonWall.gs_johnson_wall`, `GSExactCountWall.exact_wall`), this
**characterizes** the GS threshold:  `√(c·n) < t_GS(m) ≤ √(c·n·(1+1/m)) + 2` — exactly Johnson in
the limit.  Any certificate past Johnson must be a genuinely different system. -/
theorem gs_reaches_johnson (c n m : ℕ) (hm : 0 < m) :
    ∃ t D : ℕ,
      c * n * m * (m + 1) < D * (D + c) ∧
      D < t * m ∧
      (t - 2) ^ 2 * m ≤ c * n * (m + 1) :=
  ⟨tgs c n m, Dgs c n m, feasible_constraints c n m, feasible_root_order c n m hm,
   t_close_to_johnson c n m hm⟩

/-- **Non-vacuity at prize scale** (`n = 2²⁰, c = 2¹⁹ − 1, m = 64`): the construction certifies
`t = tgs ≤ 747260` — within `0.8%` of the Johnson agreement `√(c·n) ≈ 741454.5` — confirming the
convergence is genuine at the prize's own parameters (`(t−2)²·64 ≤ c·n·65` by the theorem, and the
explicit bound `741454² < c·n` places Johnson just below). -/
theorem nonvacuous_prize_scale :
    (tgs (2 ^ 19 - 1) (2 ^ 20) 64 - 2) ^ 2 * 64 ≤ (2 ^ 19 - 1) * 2 ^ 20 * 65 ∧
    741454 ^ 2 < (2 ^ 19 - 1) * 2 ^ 20 :=
  ⟨t_close_to_johnson _ _ _ (by norm_num), by norm_num⟩

end ArkLib.CodingTheory.GSReachesJohnson

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.GSReachesJohnson.feasible_constraints
#print axioms ArkLib.CodingTheory.GSReachesJohnson.feasible_root_order
#print axioms ArkLib.CodingTheory.GSReachesJohnson.t_close_to_johnson
#print axioms ArkLib.CodingTheory.GSReachesJohnson.gs_reaches_johnson
#print axioms ArkLib.CodingTheory.GSReachesJohnson.nonvacuous_prize_scale
