/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Basic.Entropy

/-!
# Monotonicity of the q-ary entropy `qEntropy` below capacity

The canonical entropy module owns strict monotonicity, positivity and the bound by one.
This downstream module derives non-strict comparisons and floor-radius estimates from those
facts. In particular, replacing a radius by `⌊δ * n⌋ / n` cannot increase entropy below
capacity. The canonical `qEntropy_le_one` applies on all of `[0, 1]`, so no separate
below-capacity implementation is needed. Remaining statements are axiom-clean.
-/

namespace CodingTheory

open Real

variable {q : ℕ}

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

/-- **Floored-radius entropy is at most capacity.**  Below capacity, the lattice radius
`⌊δ * n⌋ / n` has q-entropy at most `1`. -/
theorem qEntropy_floor_mul_div_le_one (hq : 2 ≤ q) {n : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q ((Nat.floor (δ * n) : ℝ) / n) ≤ 1 :=
  le_trans (qEntropy_floor_mul_div_le hq hn hδ0 hδ) (qEntropy_le_one hδ0 (hδ.trans (sub_le_self _ (by positivity))))

/-- Finite-domain specialization of `qEntropy_floor_mul_div_le_one`. -/
theorem qEntropy_floor_mul_card_div_card_le_one (hq : 2 ≤ q) {ι : Type}
    [Fintype ι] [Nonempty ι] {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q ((Nat.floor (δ * Fintype.card ι) : ℝ) / Fintype.card ι) ≤ 1 :=
  qEntropy_floor_mul_div_le_one hq Fintype.card_pos hδ0 hδ

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
