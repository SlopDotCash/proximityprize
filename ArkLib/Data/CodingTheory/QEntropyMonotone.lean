/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityLeaves2
import ArkLib.Data.CodingTheory.EntropyCapacityValue

/-!
# Monotonicity of the q-ary entropy `qEntropy` below capacity

ArkLib's base-`q` entropy `CodingTheory.qEntropy` (ABF26 Def 2.2) has nonnegativity / boundary /
capacity lemmas, but lacked monotonicity. This file adds it, derived from Mathlib's
`Real.qaryEntropy_strictMonoOn` through the existing base-change bridge
`qEntropy_mul_log_eq_qaryEntropy` (`qEntropy q x · log q = Real.qaryEntropy q x`): dividing by the
positive constant `log q` (for `q ≥ 2`) preserves strict monotonicity.

`qEntropy q` is strictly increasing on `[0, 1 − 1/q]` (up to the capacity point `1 − 1/q`,
`qEntropy_capacity_eq_one`). Useful for relating `H_q(δ')` and `H_q(δ)` when `δ' ≤ δ` in the
sub-capacity regime, e.g. floor-vs-real radius comparisons in the entropy-volume / list-size
bounds. `sorry`/`axiom`-free, axiom-clean.
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- **`qEntropy q` is strictly monotone on `[0, 1 − 1/q]`.** Derived from Mathlib's
`Real.qaryEntropy_strictMonoOn` via the base-change bridge `qEntropy q x · log q = qaryEntropy q x`
(division by `log q > 0` preserves strict monotonicity). -/
theorem qEntropy_strictMonoOn (hq : 2 ≤ q) :
    StrictMonoOn (qEntropy q) (Set.Icc 0 (1 - 1 / (q : ℝ))) := by
  intro x hx y hy hxy
  have hlog : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have h := Real.qaryEntropy_strictMonoOn hq hx hy hxy
  rw [← qEntropy_mul_log_eq_qaryEntropy hq x, ← qEntropy_mul_log_eq_qaryEntropy hq y] at h
  exact lt_of_mul_lt_mul_right h hlog.le

/-- **`qEntropy q` is monotone on `[0, 1 − 1/q]`** (non-strict corollary). -/
theorem qEntropy_monotoneOn (hq : 2 ≤ q) :
    MonotoneOn (qEntropy q) (Set.Icc 0 (1 - 1 / (q : ℝ))) :=
  (qEntropy_strictMonoOn hq).monotoneOn

/-- **`qEntropy` comparison below capacity.** For `0 ≤ x ≤ y ≤ 1 − 1/q`, `H_q(x) ≤ H_q(y)`. -/
theorem qEntropy_le_qEntropy_of_le (hq : 2 ≤ q) {x y : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q x ≤ qEntropy q y :=
  qEntropy_monotoneOn hq ⟨hx0, le_trans hxy hy⟩ ⟨le_trans hx0 hxy, hy⟩ hxy

/-- The lattice radius `⌊δ * n⌋ / n` is nonnegative. -/
theorem floor_mul_div_nonneg {n : ℕ} {δ : ℝ} (hn : 0 < n) :
    0 ≤ (Nat.floor (δ * n) : ℝ) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- The lattice radius `⌊δ * n⌋ / n` is bounded by the original radius `δ`. -/
theorem floor_mul_div_le {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ0 : 0 ≤ δ) :
    (Nat.floor (δ * n) : ℝ) / n ≤ δ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul_nonneg : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ0 hnR.le
  have hfloor_le : (Nat.floor (δ * n) : ℝ) ≤ δ * n :=
    Nat.floor_le hmul_nonneg
  exact (div_le_iff₀ hnR).2 hfloor_le

/-- Finite-domain specialization of `floor_mul_div_le`. -/
theorem floor_mul_card_div_card_le {ι : Type} [Fintype ι] [Nonempty ι] {δ : ℝ}
    (hδ0 : 0 ≤ δ) :
    (Nat.floor (δ * Fintype.card ι) : ℝ) / Fintype.card ι ≤ δ :=
  floor_mul_div_le Fintype.card_pos hδ0

/-- **Floor-radius entropy comparison.**  Replacing a real radius `δ` by the lattice radius
`⌊δ * n⌋ / n` cannot increase `qEntropy` below capacity. -/
theorem qEntropy_floor_mul_div_le (hq : 2 ≤ q) {n : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q ((Nat.floor (δ * n) : ℝ) / n) ≤ qEntropy q δ := by
  have hfloor_div_nonneg : 0 ≤ (Nat.floor (δ * n) : ℝ) / n :=
    floor_mul_div_nonneg hn
  have hfloor_div_le : (Nat.floor (δ * n) : ℝ) / n ≤ δ :=
    floor_mul_div_le hn hδ0
  exact qEntropy_le_qEntropy_of_le hq hfloor_div_nonneg hfloor_div_le hδ

/-- Finite-domain specialization of `qEntropy_floor_mul_div_le`. -/
theorem qEntropy_floor_mul_card_div_card_le (hq : 2 ≤ q) {ι : Type}
    [Fintype ι] [Nonempty ι] {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q ((Nat.floor (δ * Fintype.card ι) : ℝ) / Fintype.card ι) ≤
      qEntropy q δ :=
  qEntropy_floor_mul_div_le hq Fintype.card_pos hδ0 hδ

/-- **`qEntropy q δ ≤ 1` below capacity.** On `[0, 1 − 1/q]` the q-ary entropy is bounded by its
capacity value `H_q(1 − 1/q) = 1` (`qEntropy_capacity_eq_one`), by monotonicity. -/
theorem qEntropy_le_one (hq : 2 ≤ q) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q δ ≤ 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hcap : qEntropy q (1 - 1 / (q : ℝ)) = 1 := by
    rw [show (1 : ℝ) - 1 / (q : ℝ) = ((q : ℝ) - 1) / (q : ℝ) by field_simp]
    exact qEntropy_capacity_eq_one hq
  calc qEntropy q δ ≤ qEntropy q (1 - 1 / (q : ℝ)) :=
        qEntropy_le_qEntropy_of_le hq hδ0 hδ le_rfl
    _ = 1 := hcap

/-- **Floored-radius entropy is at most capacity.**  Below capacity, the lattice radius
`⌊δ * n⌋ / n` has q-entropy at most `1`. -/
theorem qEntropy_floor_mul_div_le_one (hq : 2 ≤ q) {n : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q ((Nat.floor (δ * n) : ℝ) / n) ≤ 1 :=
  le_trans (qEntropy_floor_mul_div_le hq hn hδ0 hδ) (qEntropy_le_one hq hδ0 hδ)

/-- Finite-domain specialization of `qEntropy_floor_mul_div_le_one`. -/
theorem qEntropy_floor_mul_card_div_card_le_one (hq : 2 ≤ q) {ι : Type}
    [Fintype ι] [Nonempty ι] {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q ((Nat.floor (δ * Fintype.card ι) : ℝ) / Fintype.card ι) ≤ 1 :=
  qEntropy_floor_mul_div_le_one hq Fintype.card_pos hδ0 hδ

/-- **`qEntropy q δ > 0` strictly inside `(0, 1)`.**  From Mathlib's `Real.qaryEntropy_pos`
through the base-change bridge (division by `log q > 0` preserves strict positivity). -/
theorem qEntropy_pos (hq : 2 ≤ q) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < qEntropy q δ := by
  have hlog : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hpos := Real.qaryEntropy_pos (q := q) hδ0 hδ1
  have hbridge : qEntropy q δ = Real.qaryEntropy q δ / Real.log q := by
    rw [← qEntropy_mul_log_eq_qaryEntropy hq δ, mul_div_assoc, div_self (ne_of_gt hlog), mul_one]
  rw [hbridge]
  exact div_pos hpos hlog

end CodingTheory

-- Axiom audit: depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.qEntropy_pos
#print axioms CodingTheory.qEntropy_strictMonoOn
#print axioms CodingTheory.qEntropy_monotoneOn
#print axioms CodingTheory.qEntropy_le_qEntropy_of_le
#print axioms CodingTheory.floor_mul_div_nonneg
#print axioms CodingTheory.floor_mul_div_le
#print axioms CodingTheory.floor_mul_card_div_card_le
#print axioms CodingTheory.qEntropy_floor_mul_div_le
#print axioms CodingTheory.qEntropy_floor_mul_card_div_card_le
#print axioms CodingTheory.qEntropy_le_one
#print axioms CodingTheory.qEntropy_floor_mul_div_le_one
#print axioms CodingTheory.qEntropy_floor_mul_card_div_card_le_one
