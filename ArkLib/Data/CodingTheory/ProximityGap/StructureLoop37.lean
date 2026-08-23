/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 37 — the per-round multiplier must be gap-independent, not merely depth-independent

Loops 28/31/35 narrowed the only surviving disproof shape to an **unbounded cumulative exponent**:
a per-round multiplicative factor whose logarithm sums to more than `m·c` across the `m` fold
levels. This file sharpens that statement by exposing the interaction with the **fixed** prize
numerator exponent `c₁`.

The prize RHS has the form

    (1/q) · (2^m)^{c₁} / (ρ^{c₂} η^{c₃})

with a single constant triple `(c₁, c₂, c₃)` chosen **before** the field — in particular **before**
the gap `η`. The depth-exponential factor `(2^m)^{c₁}` is, arithmetically, an `m`-fold product of
the *single universal base* `2^{c₁}`. Therefore:

* **(safe)** A per-round multiplier bounded by the gap-INDEPENDENT base `2^{c₁}` accumulates to at
  most `(2^m)^{c₁}` — prize-safe (`const_multiplier_product_le_domain_pow`).
* **(obstruction)** A per-round multiplier carrying the *capacity budget* `B(ρ,η) ≈ 1/η`, which
  diverges as `η → 0`, strictly overflows `(2^m)^{c₁}` for **every** fixed `c₁` once the gap is
  small enough that `2^{c₁} < B(ρ,η)` (`gap_budget_per_round_overflows`,
  `exists_budget_overflowing`).

The consequence — recorded as `prize_decomposition` — is a structural decomposition of the prize
RHS: the depth-exponential part `(2^m)^{c₁}` may carry only the gap-INDEPENDENT universal constant,
while **all** gap dependence must be confined to the depth-INDEPENDENT factor
`G = 1/(ρ^{c₂} η^{c₃})` paid **once**, not per round. This explains the proven regimes: Johnson
(Loop11/P2) places the domain-size factor `n² = (2^m)²` with `c₁ = 2` and pushes the `ℓ⁷ρ²` list
budget into the denominator — exactly a single gap-dependent factor, never a per-round one.

So the surviving disproof shape is even narrower than Loop35 stated: the dangerous mechanism must
realize a cumulative exponent that grows **either** in the depth `m` **or** in the inverse gap
`1/η` faster than a single field-independent constant — and it must do so as a genuine *per-round*
multiplier of the actual smooth-domain GS/proximity process, not as a one-shot list/error budget.
A one-shot capacity budget (the only thing BGM/Johnson actually supply) lands in `G`, not in `c₁`,
and is therefore prize-safe. See `DISPROOF_LOG.md` (Loop37).
-/

namespace ArkLib.ProximityGap.StructureLoop37

open scoped BigOperators

/-- **Safe shape: a gap-independent per-round multiplier is absorbed.** If every per-round
multiplier `a j` is nonnegative and bounded by the universal base `2^c` (a bound that does **not**
depend on the gap), then the `m`-fold accumulated product is at most the final-domain degree-`c`
polynomial `(2^m)^c`. The depth-exponential factor can carry exactly this much and no more. -/
theorem const_multiplier_product_le_domain_pow
    (a : ℕ → ℝ) {c m : ℕ}
    (h0 : ∀ j, j < m → 0 ≤ a j)
    (hle : ∀ j, j < m → a j ≤ (2 : ℝ) ^ c) :
    (∏ j ∈ Finset.range m, a j) ≤ ((2 : ℝ) ^ m) ^ c := by
  calc
    (∏ j ∈ Finset.range m, a j) ≤ ∏ _j ∈ Finset.range m, ((2 : ℝ) ^ c) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro j hj; exact h0 j (Finset.mem_range.mp hj)
        · intro j hj; exact hle j (Finset.mem_range.mp hj)
    _ = ((2 : ℝ) ^ c) ^ m := by rw [Finset.prod_const, Finset.card_range]
    _ = ((2 : ℝ) ^ m) ^ c := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Obstruction: a gap-dependent per-round multiplier cannot fit a fixed numerator exponent.**
If a per-round multiplier `a` strictly exceeds the universal base `2^c` — which happens for the
capacity budget `B(ρ,η) ≈ 1/η` once the gap `η` is small enough that `2^c < B` — then over any
positive number of rounds the accumulated product `a^m` strictly exceeds the degree-`c`
final-domain polynomial. Hence no single field-independent `c₁` can absorb a per-round budget. -/
theorem gap_budget_per_round_overflows
    {a : ℝ} {c m : ℕ} (hm : 1 ≤ m) (ha : (2 : ℝ) ^ c < a) :
    ((2 : ℝ) ^ m) ^ c < a ^ m := by
  have hbase : ((2 : ℝ) ^ m) ^ c = ((2 : ℝ) ^ c) ^ m := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hbase]
  exact pow_lt_pow_left₀ ha (by positivity) (by omega)

/-- **The fixed-exponent constraint genuinely bites.** For every candidate numerator exponent `c`,
there is a capacity-budget value `B > 2^c` (realized by a small enough gap) against which the
per-round product overflows the degree-`c` final-domain polynomial at every positive depth. So the
per-round multiplier is forced to be gap-independent: any `c₁` chosen before the gap fails against a
sufficiently small gap if the budget is charged per round. -/
theorem exists_budget_overflowing (c : ℕ) :
    ∃ B : ℝ, (2 : ℝ) ^ c < B ∧ ∀ m, 1 ≤ m → ((2 : ℝ) ^ m) ^ c < B ^ m := by
  refine ⟨(2 : ℝ) ^ c + 1, by linarith, ?_⟩
  intro m hm
  exact gap_budget_per_round_overflows hm (by linarith)

/-- **Prize-form decomposition.** The prize RHS `(2^m)^{c₁} · G` is exactly an `m`-fold product of
the gap-INDEPENDENT universal per-round constant `2^{c₁}` times a *single* gap factor `G` paid
once (`G = 1/(ρ^{c₂} η^{c₃})`). The depth-exponential part carries only the universal constant; all
gap dependence is confined to the depth-independent factor `G`. This is the structural reason the
proven regimes (Johnson/Loop11) put the `n² = (2^m)²` factor with `c₁ = 2` and push the `ℓ⁷ρ²` list
budget into the denominator — paid once, never per round. -/
theorem prize_decomposition (c₁ m : ℕ) (G : ℝ) :
    (∏ _j ∈ Finset.range m, (2 : ℝ) ^ c₁) * G = ((2 : ℝ) ^ m) ^ c₁ * G := by
  rw [Finset.prod_const, Finset.card_range, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **The two safe accumulation modes, side by side.** A per-round multiplier bounded by the
universal base is absorbed into `(2^m)^c` (depth-exponential, gap-independent); a one-shot gap
budget `G ≥ 0` multiplies that by a depth-independent factor. Their composition is still of prize
shape. Any mechanism staying inside this envelope cannot disprove the prize. -/
theorem safe_envelope
    (a : ℕ → ℝ) {c m : ℕ} (G : ℝ) (hG : 0 ≤ G)
    (h0 : ∀ j, j < m → 0 ≤ a j)
    (hle : ∀ j, j < m → a j ≤ (2 : ℝ) ^ c) :
    (∏ j ∈ Finset.range m, a j) * G ≤ ((2 : ℝ) ^ m) ^ c * G := by
  exact mul_le_mul_of_nonneg_right
    (const_multiplier_product_le_domain_pow a h0 hle) hG

end ArkLib.ProximityGap.StructureLoop37

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop37.const_multiplier_product_le_domain_pow
#print axioms ArkLib.ProximityGap.StructureLoop37.gap_budget_per_round_overflows
#print axioms ArkLib.ProximityGap.StructureLoop37.exists_budget_overflowing
#print axioms ArkLib.ProximityGap.StructureLoop37.prize_decomposition
#print axioms ArkLib.ProximityGap.StructureLoop37.safe_envelope
