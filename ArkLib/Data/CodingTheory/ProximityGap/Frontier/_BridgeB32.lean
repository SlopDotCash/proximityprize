/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Bridge B32 (target E7) — `m* = o(n)` vs. the constant-gap bracket P5 (#444)

**Spec (verbatim).** `m*=o(n) ⇒ deltaStar → capacity − c_ρ` (bridge E1 to the upper bracket P5).
**Substrate.** the master gap identity E1 (`_BridgeB01.lean`,
`deltaStar = 1 − ρ − (m*−1)/n`) and `DeltaStarConstantGapBelowCapacity.lean`
(`δ* ≤ 1 − ρ − c_ρ`, the constant gap below capacity).

## The honest verdict on the spec claim

The spec's *literal* target limit is **ill-posed / false as stated**, and pinning down exactly
why is the content of this bridge. Unwinding E1 (the proven algebra brick B01) at a sequence of
tower scales `n` with the rate `ρ` fixed gives the **exact** capacity gap

  `capacity − δ*ₙ  =  (m*ₙ − 1) / n`            (E1, capacity form).

Two mutually exclusive consequences follow, depending on the `m*` growth law:

* **If `m* = o(n)`** (i.e. `m*ₙ / n → 0`), then `(m*ₙ − 1)/n → 0`, hence
  `δ*ₙ → 1 − ρ = capacity` — the limit is *capacity itself*, **not** `capacity − c_ρ` for any
  positive constant `c_ρ`.  (`tendsto_deltaStar_capacity_of_mStar_little_o`.)

* **The constant-gap bracket P5** says `capacity − δ*ₙ ≥ c_ρ` for an absolute `c_ρ > 0`
  (`c_ρ ≈ ρ/127`).  Plugged into the E1 identity this forces `m*ₙ ≥ c_ρ·n + 1`, i.e.
  `m*ₙ / n ≥ c_ρ > 0` for all `n` — so **`m*` is `Ω(n)`, and `m* = o(n)` is impossible**.
  (`mStar_ge_of_constant_gap`, `mStar_little_o_incompatible_with_constant_gap`.)

So the two hypotheses the spec asks us to "combine" are in *direct tension*: `m* = o(n)` drives
`δ*` to *full capacity*, while P5 holds it a constant `c_ρ` *below* capacity. They cannot both
hold; the spec's claimed limit `capacity − c_ρ` is exactly the P5 ceiling that the `o(n)` regime
would have to *violate*. The genuine theorem (the contrapositive) is:

  **P5 (constant gap) ⟹ `m*` grows linearly (`Ω(n)`) ⟹ `δ*` stays a constant below capacity.**

That is the real bridge from E1 to P5, and it *refutes* the E7 hope `m* = o(n)` *under P5*.

## What is proved here (axiom-clean, no `sorry`)

Everything is over `ℝ`, taking the E1 identity (B01) and the P5 gap bound as named hypotheses
(an honest reduction: the *upstream* facts that E1 holds and that P5's `c_ρ`-gap holds are the
proven anchors B01 / `DeltaStarConstantGapBelowCapacity`; here we discharge the *deduction* that
combines them). A self-contained ε–N convergence predicate `TendstoSeq` keeps imports light;
no `Filter`/topology limit machinery is needed.

* `capacity_gap_eq_mStar` — E1 in capacity form: `(1−ρ) − δ*ₙ = (m*ₙ − 1)/n`.
* `tendsto_deltaStar_capacity_of_mStar_little_o` — `m* = o(n) ⇒ δ*ₙ → 1 − ρ` (NOT `−c_ρ`).
* `mStar_ge_of_constant_gap` — P5 ⇒ `m*ₙ ≥ c_ρ·n + 1` (the linear lower bound on `m*`).
* `mStar_little_o_incompatible_with_constant_gap` — P5 with `c_ρ > 0` ⇒ `m* = o(n)` is FALSE.

Issue #444.
-/

namespace ArkLib.ProximityGap.BridgeB32

/-- A self-contained ε–N convergence predicate (`uₙ → L`): for every `ε > 0` there is an `N`
beyond which `|uₙ − L| < ε`.  Kept local to avoid importing topology limit machinery; it is the
standard definition of a real sequence limit. -/
def TendstoSeq (u : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |u n - L| < ε

/-- **E1 in capacity form (the algebra of `_BridgeB01.capacity_gap_eq`, sequence version).**
Given the E1 identity `δ*ₙ = 1 − ρ − (m*ₙ − 1)/n` at scale `n ≠ 0`, the capacity gap is exactly
`(m*ₙ − 1)/n`. -/
theorem capacity_gap_eq_mStar
    (n rho deltaStar mstar : ℝ) (_hn : n ≠ 0)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n) :
    (1 - rho) - deltaStar = (mstar - 1) / n := by
  rw [hE1]; ring

/-! ## 1. The `m* = o(n)` regime drives `δ*` to FULL capacity (not `capacity − c_ρ`). -/

/-- **`m* = o(n) ⇒ δ*ₙ → 1 − ρ` (full capacity).**

Hypotheses (the honest inputs):
* `hE1 : ∀ n, 1 ≤ n → deltaStar n = 1 − rho − (mstar n − 1)/n` — the E1 identity (anchor B01)
  at every tower scale `n ≥ 1`, with the rate `rho` fixed across the tower.
* `hlittle : TendstoSeq (fun n => mstar n / n) 0` — `m* = o(n)`: the binding depth is sublinear.
* `hmpos : ∀ n, 1 ≤ n → 1 ≤ mstar n` — `m* ≥ 1` (a binder exists at every scale; the cascade
  always reaches the budget, so the `(m*−1)` in E1 is `≥ 0`).

Conclusion: `δ*ₙ → 1 − ρ = capacity`. The limit is capacity *itself*; the spec's `capacity − c_ρ`
is NOT the limit of the `o(n)` regime. -/
theorem tendsto_deltaStar_capacity_of_mStar_little_o
    (deltaStar rho : ℝ → ℝ) (mstar : ℝ → ℝ) (rhoConst : ℝ)
    -- `rho` is the constant rate of the tower:
    (hrho : ∀ n : ℝ, rho n = rhoConst)
    (hE1 : ∀ n : ℝ, n ≠ 0 → deltaStar n = 1 - rho n - (mstar n - 1) / n)
    (hlittle : TendstoSeq (fun k => mstar (k : ℝ) / (k : ℝ)) 0)
    (hmpos : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ mstar (k : ℝ)) :
    TendstoSeq (fun k => deltaStar (k : ℝ)) (1 - rhoConst) := by
  intro ε hε
  -- From `m*/n → 0` get `N₀` past which `|m*ₖ/k| < ε`.
  obtain ⟨N₀, hN₀⟩ := hlittle ε hε
  refine ⟨max N₀ 1, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := le_trans (le_max_right N₀ 1) hk
  have hkN₀ : N₀ ≤ k := le_trans (le_max_left N₀ 1) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk1
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  -- E1 at scale `k`:  δ*ₖ = 1 − ρ − (m*ₖ − 1)/k.
  have hd : deltaStar (k : ℝ) = 1 - rhoConst - (mstar (k : ℝ) - 1) / (k : ℝ) := by
    rw [hE1 (k : ℝ) hkne, hrho]
  -- `δ*ₖ − (1 − ρ) = −(m*ₖ − 1)/k`, so the error is `(m*ₖ − 1)/k`.
  have herr : deltaStar (k : ℝ) - (1 - rhoConst) = -((mstar (k : ℝ) - 1) / (k : ℝ)) := by
    rw [hd]; ring
  -- Bound the error.  `0 ≤ (m*ₖ − 1)/k ≤ m*ₖ/k` (since `1 ≤ m*ₖ`, `0 < k`), and `m*ₖ/k < ε`.
  have hm1 : (1 : ℝ) ≤ mstar (k : ℝ) := hmpos k hk1
  have hnum_nonneg : (0 : ℝ) ≤ mstar (k : ℝ) - 1 := by linarith
  have hfrac_nonneg : (0 : ℝ) ≤ (mstar (k : ℝ) - 1) / (k : ℝ) :=
    div_nonneg hnum_nonneg (le_of_lt hkpos)
  have hfrac_le : (mstar (k : ℝ) - 1) / (k : ℝ) ≤ mstar (k : ℝ) / (k : ℝ) := by
    gcongr
    linarith
  -- `m*ₖ/k < ε` from the `o(n)` hypothesis (and `0 ≤ m*ₖ/k` ⟹ `|m*ₖ/k| = m*ₖ/k`).
  have hlt : |mstar (k : ℝ) / (k : ℝ) - 0| < ε := hN₀ k hkN₀
  have hmfrac_nonneg : (0 : ℝ) ≤ mstar (k : ℝ) / (k : ℝ) :=
    div_nonneg (le_trans zero_le_one hm1) (le_of_lt hkpos)
  have hmfrac_lt : mstar (k : ℝ) / (k : ℝ) < ε := by
    have : |mstar (k : ℝ) / (k : ℝ)| < ε := by simpa using hlt
    rwa [abs_of_nonneg hmfrac_nonneg] at this
  -- Assemble: `|δ*ₖ − (1 − ρ)| = (m*ₖ − 1)/k ≤ m*ₖ/k < ε`.
  rw [herr]
  rw [abs_neg, abs_of_nonneg hfrac_nonneg]
  exact lt_of_le_of_lt hfrac_le hmfrac_lt

/-! ## 2. The constant-gap bracket P5 forces `m* = Ω(n)` — refuting `m* = o(n)`. -/

/-- **P5 ⇒ `m*ₙ ≥ c_ρ·n + 1` (the linear lower bound on the binding depth).**

From the E1 identity at scale `n > 0` together with the P5 constant-gap bracket
`(1 − ρ) − δ*ₙ ≥ c_ρ` (`DeltaStarConstantGapBelowCapacity`, `δ* ≤ 1 − ρ − c_ρ`), the binding
depth `m*ₙ` is at least `c_ρ·n + 1`.  In particular, dividing by `n`, `m*ₙ / n ≥ c_ρ`. -/
theorem mStar_ge_of_constant_gap
    (n rho deltaStar mstar cρ : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n)
    (hP5 : deltaStar ≤ 1 - rho - cρ) :
    cρ * n + 1 ≤ mstar := by
  -- E1 capacity form: `(1 − ρ) − δ* = (m* − 1)/n`.
  have hgap : (1 - rho) - deltaStar = (mstar - 1) / n :=
    capacity_gap_eq_mStar n rho deltaStar mstar (ne_of_gt hn) hE1
  -- P5: `(1 − ρ) − δ* ≥ c_ρ`, so `(m* − 1)/n ≥ c_ρ`.
  have hge : cρ ≤ (mstar - 1) / n := by
    rw [← hgap]; linarith
  -- Multiply through by `n > 0`:  `c_ρ·n ≤ m* − 1`.
  have hmul : cρ * n ≤ mstar - 1 := by
    have := (le_div_iff₀ hn).mp hge
    linarith
  linarith

/-- **P5 (with `c_ρ > 0`) ⇒ `m* = o(n)` is FALSE.**

The constant-gap bracket holds at every tower scale `n ≥ 1` with the SAME absolute `c_ρ > 0`
(this is precisely the content of `DeltaStarConstantGapBelowCapacity` — `c_ρ ≈ ρ/127`). Then for
every `k ≥ 1` the binding-depth ratio is bounded below by the constant: `m*ₖ / k ≥ c_ρ`. Since
`c_ρ > 0`, the ratio cannot converge to `0`, i.e. `m* = o(n)` is impossible.

This is the honest contrapositive of the spec's E7 hope: **under P5, `m*` is `Ω(n)`** (it cannot
be `o(n)`), and therefore (by `tendsto_deltaStar_capacity_of_mStar_little_o` read in reverse) `δ*`
stays a constant `c_ρ` below capacity rather than approaching capacity. The spec's claimed limit
`capacity − c_ρ` is the P5 ceiling, NOT the limit of an `o(n)` regime (which would be full
capacity); the two hypotheses are mutually exclusive. -/
theorem mStar_little_o_incompatible_with_constant_gap
    (deltaStar rho mstar : ℝ → ℝ) (cρ : ℝ) (hcρ : 0 < cρ)
    (hE1 : ∀ n : ℝ, n ≠ 0 → deltaStar n = 1 - rho n - (mstar n - 1) / n)
    (hP5 : ∀ n : ℝ, deltaStar n ≤ 1 - rho n - cρ) :
    ¬ TendstoSeq (fun k => mstar (k : ℝ) / (k : ℝ)) 0 := by
  intro hlittle
  -- Get `N` past which `|m*ₖ/k| < c_ρ`.
  obtain ⟨N, hN⟩ := hlittle cρ hcρ
  -- Pick a scale `k = max N 1 ≥ 1`, so `k > 0`.
  set k : ℕ := max N 1 with hk
  have hk1 : 1 ≤ k := le_max_right N 1
  have hkN : N ≤ k := le_max_left N 1
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk1
  -- The lower bound from P5: `m*ₖ ≥ c_ρ·k + 1`, hence `m*ₖ/k ≥ c_ρ + 1/k > c_ρ`.
  have hlb : cρ * (k : ℝ) + 1 ≤ mstar (k : ℝ) :=
    mStar_ge_of_constant_gap (k : ℝ) (rho (k : ℝ)) (deltaStar (k : ℝ)) (mstar (k : ℝ)) cρ
      hkpos (hE1 (k : ℝ) (ne_of_gt hkpos)) (hP5 (k : ℝ))
  have hratio_ge : cρ ≤ mstar (k : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkpos]; nlinarith
  -- But `o(n)` says `m*ₖ/k < c_ρ` (the ratio is nonneg, so `|·| = ·`).
  have hratio_lt : mstar (k : ℝ) / (k : ℝ) < cρ := by
    have h := hN k hkN
    have hnn : (0 : ℝ) ≤ mstar (k : ℝ) / (k : ℝ) := by
      -- from `m*ₖ ≥ c_ρ·k + 1 > 0`
      have hmpos : (0 : ℝ) < mstar (k : ℝ) := by nlinarith
      exact div_nonneg (le_of_lt hmpos) (le_of_lt hkpos)
    have : |mstar (k : ℝ) / (k : ℝ)| < cρ := by simpa using h
    rwa [abs_of_nonneg hnn] at this
  exact absurd hratio_ge (not_le.mpr hratio_lt)

end ArkLib.ProximityGap.BridgeB32

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound`) -/
#print axioms ArkLib.ProximityGap.BridgeB32.capacity_gap_eq_mStar
#print axioms ArkLib.ProximityGap.BridgeB32.tendsto_deltaStar_capacity_of_mStar_little_o
#print axioms ArkLib.ProximityGap.BridgeB32.mStar_ge_of_constant_gap
#print axioms ArkLib.ProximityGap.BridgeB32.mStar_little_o_incompatible_with_constant_gap
