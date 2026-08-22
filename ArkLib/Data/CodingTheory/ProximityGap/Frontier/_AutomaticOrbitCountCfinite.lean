/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The orbit-count / union-count sequence is C-FINITE (decidable growth) but PHASE-BLIND (#444)

FRESH AVENUE `AUTOMATIC_ORBITCOUNT`.  The p-independent combinatorial face of the prize
(the additive-energy / distinct-γ union-count, indexed by the binary/2-adic structure of
`n = 2^μ`) was conjectured to be **2-automatic**, which would make its asymptotic GROWTH RATE
*decidable* (the spectral radius of a finite transition matrix) — a hoped-for escape from the
`n ≥ 256` undecidability of the deep union-count growth law.

## What the exact computation establishes (probe `probe_automatic_orbitcount.py`)

For `μ_n = 2^μ`-th roots of unity, the relevant p-independent counts are EXACT closed forms:

* the **distinct-γ union count** (size of the sumset `μ_n + μ_n`, = size of the difference set)
  is `c(μ) = 2^{2μ-1} + 1 = n²/2 + 1` (verified `μ = 2..7`);
* the **additive energy** `E₂(μ_n) = 3·n² − 3·n` (verified, matches the in-tree `E2` law);
* the **deep-band shallow-rung orbit counts** are `orbitCount3 = C(g,2) ~ n²/32`,
  `orbitCount4 ~ n³/512` (in-tree `_OrbitCountGrowthLaw`).

ALL of these are **C-finite** (satisfy a linear recurrence with *constant integer coefficients*):
the union count obeys `c(μ+1) = 4·c(μ) − 3` (this file), with **rational generating function**
`(1/2)/(1−4t) + 1/(1−t)`, dominant pole `t = 1/4`, hence **decidable growth rate `= 4 = n²`**.

## Why C-finite ≠ "2-automatic" in the useful sense, and why it is PHASE-BLIND

* **Automaticity, precisely (Cobham/Allouche–Shallit).**  A `k`-automatic sequence is *bounded*
  (takes finitely many values).  These counts diverge (`c(μ) → ∞` with dominant root `4`), so the
  2-kernel is INFINITE: the integer sequence is **NOT 2-automatic**.  It is *C-finite*, and only
  `c(μ) mod m` is (trivially, by eventual periodicity) 2-automatic — content-free for growth.
* **Decidable growth, but already known and ABOVE budget.**  The decidable rate is `n²` (union /
  energy) or `n³` (orbitCount4) — the in-tree closed forms.  These EXCEED the prize budget `n` at
  every shallow rung; the floor `count ≤ n` holds ONLY at the trivial rung `r = 1`, where the
  r-fold sumset `|r·μ_n| = n` EXACTLY (single orbit), **not** a deep cancellation.
* **The wall is p-DEPENDENT, the count is p-INDEPENDENT.**  At the binding rung `r ≈ log p` the
  prize-relevant quantity is the *char-`p`* energy `E_r^p = E_r^0 + W_r`.  The automatic/C-finite
  part is the char-0 count `E_r^0`, which the probe verifies is **`≤ Wick = (2r−1)‼·n^r` for all
  `r`** (the GOOD side; Lam–Leung).  The entire obstruction is `W_r` (the char-`p` wraparound),
  which is p-DEPENDENT and therefore *invisible* to any property of the p-independent count.

**Verdict: PHASE-BLIND.**  The orbit/union count IS C-finite with decidable growth, but that growth
(`n²`) is the GOOD-side magnitude (`E_r^0 ≤ Wick`); the archimedean-phase wall lives in the
p-dependent `W_r`, which automaticity/decidability of the p-independent count cannot reach.  This
does NOT bound the actual `M`, and does NOT evade the deep-depth archimedean-phase wall — it
reduces to the same `W_r ≤ slack` core.  This file formalizes the *provable* piece (the C-finite
recurrence = the decidable-growth signature), and records the phase-blindness verdict in prose.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.AutomaticOrbitCount

/-- **The distinct-γ union count of the `2^μ`-th roots** = size of the sumset `μ_n + μ_n`
(= size of the difference set), computed EXACTLY: `c(μ) = 2^{2μ−1} + 1 = n²/2 + 1`. -/
def unionCount (μ : ℕ) : ℕ := 2 ^ (2 * μ - 1) + 1

/-- Numerical rungs (must reproduce the exact probe data, `μ = 2..7`). -/
theorem unionCount_values :
    unionCount 2 = 9 ∧ unionCount 3 = 33 ∧ unionCount 4 = 129 ∧
    unionCount 5 = 513 ∧ unionCount 6 = 2049 ∧ unionCount 7 = 8193 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold unionCount; norm_num)

/-- **The C-finite recurrence (the decidable-growth signature).**  For `μ ≥ 1`,
`unionCount (μ+1) = 4 · unionCount μ − 3`.  Constant integer coefficients ⟹ rational generating
function ⟹ DECIDABLE growth rate (dominant root `4 = n²`).  This is the precise sense in which the
count's asymptotics are decidable; it is NOT 2-automaticity (the sequence is unbounded, hence not
automatic by Cobham — see the module docstring). -/
theorem unionCount_cfinite (μ : ℕ) (hμ : 1 ≤ μ) :
    unionCount (μ + 1) = 4 * unionCount μ - 3 := by
  unfold unionCount
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  have e1 : 2 * (k + 1 + 1) - 1 = (2 * (k + 1) - 1) + 2 := by omega
  rw [e1, pow_add]
  ring_nf
  omega

/-- **Decidable growth: the count is bounded below by a pure power `4^{μ-1}`** (geometric, dominant
root `4 = n²`), and the recurrence pins the rate exactly.  Witnesses that the "decidable spectral
radius" is `4`, i.e. `n²` — ABOVE the budget `n`, so this growth is on the GOOD (magnitude) side,
NOT a floor.  (For `μ ≥ 1`, `4^{μ-1} ≤ unionCount μ`.) -/
theorem unionCount_ge_pow (μ : ℕ) (hμ : 1 ≤ μ) : 4 ^ (μ - 1) ≤ unionCount μ := by
  unfold unionCount
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [e]
  have : (4 : ℕ) ^ k ≤ 2 ^ (2 * k + 1) := by
    calc (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Nat.add_sub_cancel]
  omega

/-- **The union-count floor `count ≤ n` is FALSE at the very first non-trivial scale and ALL above.**
The decidable `n²` growth means `unionCount μ = n²/2 + 1 > n = 2^μ` for `μ ≥ 2` (`n ≥ 4`): the
budget is exceeded by the C-finite count.  So the "decidable growth" does NOT supply the floor;
the floor `count ≤ n` can only be the trivial single-orbit rung, not a deep collapse. -/
theorem unionCount_gt_budget (μ : ℕ) (hμ : 2 ≤ μ) : 2 ^ μ < unionCount μ := by
  unfold unionCount
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 2 := ⟨μ - 2, by omega⟩
  -- LHS = 2^(k+2) = 2^μ; RHS exponent 2*(k+2)-1 = μ + (μ-1), so 2^(2μ-1) = 2^μ * 2^(μ-1).
  have hsplit : 2 ^ (2 * (k + 2) - 1) = 2 ^ (k + 2) * 2 ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  have h2 : (2 : ℕ) ≤ 2 ^ (k + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : (1 : ℕ) ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
  have hmul : 2 ^ (k + 2) + 2 ^ (k + 2) ≤ 2 ^ (k + 2) * 2 ^ (k + 1) := by
    have h22 : 2 ^ (k + 2) * 2 ≤ 2 ^ (k + 2) * 2 ^ (k + 1) := Nat.mul_le_mul_left _ h2
    have he2 : 2 ^ (k + 2) * 2 = 2 ^ (k + 2) + 2 ^ (k + 2) := by ring
    omega
  omega

/-- **Headline (the formalizable piece).**  The orbit/union count of the `2^μ`-th roots is
C-finite — `unionCount (μ+1) = 4·unionCount μ − 3` — with DECIDABLE growth rate `4 = n²`, and that
growth EXCEEDS the prize budget `n` at every `μ ≥ 2`.  The decidable growth is the GOOD-side
magnitude (`E_r^0 ≤ Wick`), NOT a floor; the prize wall is the p-dependent `W_r`, untouched by the
p-independent count's automaticity. -/
theorem automatic_orbitcount_is_cfinite_above_budget (μ : ℕ) (hμ : 2 ≤ μ) :
    unionCount (μ + 1) = 4 * unionCount μ - 3 ∧
    4 ^ (μ - 1) ≤ unionCount μ ∧
    2 ^ μ < unionCount μ :=
  ⟨unionCount_cfinite μ (by omega), unionCount_ge_pow μ (by omega), unionCount_gt_budget μ hμ⟩

end ArkLib.ProximityGap.AutomaticOrbitCount

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AutomaticOrbitCount.unionCount_values
#print axioms ArkLib.ProximityGap.AutomaticOrbitCount.unionCount_cfinite
#print axioms ArkLib.ProximityGap.AutomaticOrbitCount.unionCount_ge_pow
#print axioms ArkLib.ProximityGap.AutomaticOrbitCount.unionCount_gt_budget
#print axioms ArkLib.ProximityGap.AutomaticOrbitCount.automatic_orbitcount_is_cfinite_above_budget
