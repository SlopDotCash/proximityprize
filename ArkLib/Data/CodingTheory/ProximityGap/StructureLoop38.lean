/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 38 — the real FRI/proximity mechanism composes per-round events ADDITIVELY (union bound)

Loop 37 isolated the only surviving disproof shape: a per-round multiplier that grows in the depth
`m` **or** in the inverse gap `1/η`, charged as a genuine *per-round multiplicative* factor of the
smooth-domain GS/proximity process. This file records the decisive structural fact about the
*actual* mechanism.

The Ben-Sasson–Carmon–Ishai–Kopparty–Saraf "Proximity Gaps" soundness analysis (and the FRI
soundness it powers) bounds the total protocol error by a **union bound over the `m` fold rounds**:
each round contributes a single correlated-agreement / list-size event of probability at most
`p = B(ρ,η)/q`, and the total error is

    err ≤ ∑_{j<m} (per-round error) ≤ m · p .

This is **additive** accumulation (Loop 27/29 regime), not the multiplicative tower (Loop 35
danger). The depth factor `m` is absorbed by `m < 2^m`, and the one-shot per-round budget
`B(ρ,η)` lands in the depth-independent factor `G` exactly as Loop 37 requires. So the proven FRI
mechanism is in the **safe envelope**: the disproof would need the per-round events to *compound
multiplicatively*, which a union bound structurally never does.

What this brick proves (sorry-free, axiom-clean):

* `fri_union_bound` — a per-round error bounded by `p` sums to at most `m · p` over `m` rounds.
* `fri_total_error_le_domain_pow_mul` — `m · p ≤ (2^m) · p`, i.e. the union-bound total error has
  prize numerator exponent `c₁ = 1`, with the per-round budget `p` carried *once*.
* `fri_additive_beats_multiplicative` — for a per-round factor `a > 1`, the additive composition
  `m · a` is eventually dwarfed by the multiplicative composition `a^m`: at depth `m ≥ 2` with
  `a ≥ 2`, `m · a ≤ a^m`. Records that the union bound is strictly the cheaper (safe) mode and the
  multiplicative tower is the genuine danger Loop 37 forbids under a fixed `c₁`.

The honest open residual is unchanged: that the per-round event probability *stays* one-shot
(`≤ B(ρ,η)/q` with `B` depending only on `ρ,η`) throughout the small-gap band `δ ≤ 1−ρ−η` is exactly
the open BGM-for-smooth fact (Loop 17). In the Johnson range it is a theorem (BCIKS 2025/2055), and
there the union-bound structure here makes the prize hold outright. See `DISPROOF_LOG.md` (Loop38).
-/

namespace ArkLib.ProximityGap.StructureLoop38

open scoped BigOperators

/-- **The FRI union bound.** If every per-round error `e j` is at most the one-shot budget `p`, then
the total protocol error — the sum over the `m` fold rounds — is at most `m · p`. The per-round
events accumulate *additively*, never multiplicatively. -/
theorem fri_union_bound
    (e : ℕ → ℝ) {p : ℝ} {m : ℕ} (he : ∀ j, j < m → e j ≤ p) :
    (∑ j ∈ Finset.range m, e j) ≤ (m : ℝ) * p := by
  calc
    (∑ j ∈ Finset.range m, e j) ≤ ∑ _j ∈ Finset.range m, p := by
        refine Finset.sum_le_sum ?_
        intro j hj; exact he j (Finset.mem_range.mp hj)
    _ = (m : ℝ) * p := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The union-bound total error has prize numerator exponent `c₁ = 1`.** The depth factor `m` is
absorbed by `m < 2^m`, so the total error `m · p` is at most `(2^m) · p` — the prize shape with the
one-shot per-round budget `p` carried a single time, depth-exponential degree one. -/
theorem fri_total_error_le_domain_pow_mul
    {p : ℝ} {m : ℕ} (hp : 0 ≤ p) :
    (m : ℝ) * p ≤ ((2 : ℝ) ^ m) * p := by
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast this.le
      _ = (2 : ℝ) ^ m := by push_cast; ring
  exact mul_le_mul_of_nonneg_right hm hp

/-- **Additive composition is the cheaper (safe) mode; multiplicative is the danger.** For a
per-round factor `a ≥ 2` and depth `m ≥ 2`, the union-bound additive cost `m · a` is dominated by
the multiplicative tower `a ^ m`. The real FRI mechanism uses the former; a disproof of the prize
would require the latter — exactly the per-round multiplicative compounding Loop 37 shows cannot fit
a fixed numerator exponent. -/
theorem fri_additive_beats_multiplicative
    {a : ℝ} {m : ℕ} (ha : 2 ≤ a) (hm : 2 ≤ m) :
    (m : ℝ) * a ≤ a ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · -- m = 2 : `2 * a ≤ a ^ 2`
        have : a ^ 2 = a * a := by ring
        rw [this]
        have h1 : (((1 : ℕ) + 1 : ℕ) : ℝ) * a = 2 * a := by push_cast; ring
        nlinarith [ha]
    · -- m = k+1 with k ≥ 2
      have ihk := ih hk
      have hpos : (0 : ℝ) ≤ a ^ k := by positivity
      have hak : a ≤ a ^ k := by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ k := pow_le_pow_right₀ (by linarith) (by omega)
      have hstep : ((k : ℝ) + 1) * a = (k : ℝ) * a + a := by ring
      calc (((k : ℕ) + 1 : ℕ) : ℝ) * a
            = ((k : ℝ) + 1) * a := by push_cast; ring
        _ = (k : ℝ) * a + a := hstep
        _ ≤ a ^ k + a ^ k := by linarith [ihk, hak]
        _ = 2 * a ^ k := by ring
        _ ≤ a * a ^ k := by nlinarith [hpos, ha]
        _ = a ^ (k + 1) := by rw [pow_succ]; ring

end ArkLib.ProximityGap.StructureLoop38

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop38.fri_union_bound
#print axioms ArkLib.ProximityGap.StructureLoop38.fri_total_error_le_domain_pow_mul
#print axioms ArkLib.ProximityGap.StructureLoop38.fri_additive_beats_multiplicative
