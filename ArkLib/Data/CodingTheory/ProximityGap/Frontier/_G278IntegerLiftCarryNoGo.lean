/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G278: integer-lift carry symmetry and two-block insufficiency for the CORE alignment (#466)

For the canonical adjacent-rank alignment, represent the order-`n` subgroup by integers in
`{1, …, p-1}` and split every counted congruence into its integer carry:

```text
2y + sum(B) - z - sum(A) = k p,
|A| = r, |B| = r-1.
```

Write `J_{r,k}` for the number of relations of carry `k`, `J_r = sum_k J_{r,k}`, and
`A_r = p J_r - n² C(n,r) C(n,r-1)` for the live centered gate.

This decomposition directly tests the characteristic-`p` wraparound mechanism left by G268.
It has two exact structural properties:

* negating every variable sends carry `k` to carry `-k`, because the signed coefficient sum is
  zero. Hence `J_{r,k} = J_{r,-k}`; a one-sided carry cannot create a sign bias;
* every characteristic-zero antipodal packet has carry zero. If the coefficients of `x` and
  `p-x` agree, its integer lift is `p * sum c_i`, which vanishes when the total coefficient sum
  is zero. Thus every nonzero carry is genuine characteristic-`p` wraparound, but carry zero may
  still contain characteristic-`p` residual mass.

The exact integer probe shows that this hidden zero-carry residual is load-bearing. At the genuine
cell `(n,p)=(16,433)`, both live ranks are positive, but neither block is sufficient:

```text
r=5: J_0 = 2,380,856 < need = 4,700,090,
     J_{k!=0} = 2,327,144 < residualNeed = 4,378,874;
r=6: J_0 = 10,052,820 < need = 20,680,392,
     J_{k!=0} = 10,627,692 < residualNeed = 19,615,944.
```

Only the sum of the two blocks crosses the gate. The same two-block insufficiency holds in all eight
exact rank-5/rank-6 cells recorded by the probe, including the late split-sign cell
`(n,p)=(32,70753)`. Therefore "count the visibly wrapped (`k != 0`) relations" is not a surviving
intermediate route: even in positive cells it supplies only part of the exact residual deficit.
One must also control the zero-carry characteristic-`p` residual, an exact integer equality count
for a thin multiplicative subgroup. Controlling that count is an incomplete-subgroup/interval
problem, outside the `|G| > p^(1/4)` range of current explicit interval estimates at the sponsors
(`|G| approximately p^(1/5.27)`).

The finite counts are computation-of-record in
`scripts/probes/g278_integer_lift_carry_exact.py`: exact integer subset-sum DP, exact `UInt64` dot
products (no FFT), and an independent modular-alignment cross-check. Lean proves the structural
identities and kernel-checks the calibrated two-rank consumer/no-go. This is route hygiene, not a
sponsor estimate and not prize closure. The surviving target remains the full row-labelled signed
sponsor covariance. CORE remains OPEN / ON-BGK.
-/

namespace ArkLib.ProximityGap.Frontier.G278IntegerLiftCarryNoGo

open scoped BigOperators

/-- The integer lift of the canonical adjacent-rank relation
`2y + sum(B) - z - sum(A)`. -/
def liftNumerator (y z sumA sumB : ℤ) : ℤ := 2 * y + sumB - z - sumA

/-- Negating every variable in `F_p`, represented by `x ↦ p-x`, negates the integer numerator.
Here `b` is the number of elements of `B`; `A` has `b+1` elements. The cancellation is exactly the
zero total coefficient identity `2+b-1-(b+1)=0`. -/
theorem liftNumerator_negated (p b y z sumA sumB : ℤ) :
    liftNumerator (p - y) (p - z) ((b + 1) * p - sumA) (b * p - sumB) =
      -liftNumerator y z sumA sumB := by
  unfold liftNumerator
  ring

/-- Consequently a carry-`k` relation is sent to a carry-`-k` relation by simultaneous negation. -/
theorem carry_negates (p b k y z sumA sumB : ℤ)
    (hcarry : liftNumerator y z sumA sumB = k * p) :
    liftNumerator (p - y) (p - z) ((b + 1) * p - sumA) (b * p - sumB) =
      (-k) * p := by
  rw [liftNumerator_negated, hcarry]
  ring

/-- Integer lift of an antipodally paired coefficient vector. The coefficient `c i` is attached to
both representatives `x i` and `p-x i`. -/
def antipodalLift {ι : Type} [Fintype ι] (p : ℤ) (c x : ι → ℤ) : ℤ :=
  ∑ i, (c i * x i + c i * (p - x i))

/-- Every paired contribution collapses to `p*c_i`; the whole lift is `p * sum c_i`. -/
theorem antipodalLift_eq_mul_sum {ι : Type} [Fintype ι] (p : ℤ) (c x : ι → ℤ) :
    antipodalLift p c x = p * ∑ i, c i := by
  unfold antipodalLift
  calc
    ∑ i, (c i * x i + c i * (p - x i)) = ∑ i, p * c i := by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    _ = p * ∑ i, c i := by rw [Finset.mul_sum]

/-- A lawful antipodal packet with zero total coefficient sum has integer carry zero.
Therefore every nonzero carry is genuinely characteristic-`p`; the converse fails because carry
zero also contains finite-characteristic residual relations. -/
theorem lawful_antipodal_carry_zero {ι : Type} [Fintype ι] (p : ℤ) (c x : ι → ℤ)
    (hsum : ∑ i, c i = 0) : antipodalLift p c x = 0 := by
  rw [antipodalLift_eq_mul_sum, hsum, mul_zero]

/-! ### Calibrated exact carry cells

`jZero` is `J_{r,0}`. `jNonzero` is `sum_{k != 0} J_{r,k}`. `lawful` is the complete
characteristic-zero antipodal floor from G268. `need = floor(B_r/p)+1` is the least total alignment
count proving `A_r>0`. Thus `residualNeed = need-lawful` is the exact amount that must be supplied
beyond the lawful floor.
-/

structure CarryCell where
  n : ℕ
  p : ℕ
  r : ℕ
  gate : ℤ
  lawful : ℕ
  jZero : ℕ
  jNonzero : ℕ
  need : ℕ
  deriving DecidableEq, Repr

/-- Exact residual count needed beyond the complete lawful antipodal floor. -/
def CarryCell.residualNeed (c : CarryCell) : ℕ := c.need - c.lawful

/-- Neither the zero-carry block nor the entire nonzero-carry block reaches its relevant
threshold. -/
def CarryCell.bothBlocksInsufficient (c : CarryCell) : Prop :=
  c.jZero < c.need ∧ c.jNonzero < c.residualNeed

/-- The full relation count crosses the centered gate threshold. -/
def CarryCell.fullSufficient (c : CarryCell) : Prop := c.need ≤ c.jZero + c.jNonzero

/-- Exact positive rank-five cell `(n,p,r)=(16,433,5)`. -/
def p433r5 : CarryCell :=
  { n := 16, p := 433, r := 5, gate := 3425440, lawful := 321216,
    jZero := 2380856, jNonzero := 2327144, need := 4700090 }

/-- Exact positive rank-six cell `(n,p,r)=(16,433,6)`. -/
def p433r6 : CarryCell :=
  { n := 16, p := 433, r := 6, gate := 52032, lawful := 1064448,
    jZero := 10052820, jNonzero := 10627692, need := 20680392 }

/-- At rank five the gate is positive only after combining both individually insufficient blocks. -/
theorem p433_rank5_requires_both :
    0 < p433r5.gate ∧ p433r5.bothBlocksInsufficient ∧ p433r5.fullSufficient := by
  norm_num [p433r5, CarryCell.bothBlocksInsufficient, CarryCell.fullSufficient,
    CarryCell.residualNeed]

/-- The same phenomenon holds at rank six in the identical genuine subgroup cell. -/
theorem p433_rank6_requires_both :
    0 < p433r6.gate ∧ p433r6.bothBlocksInsufficient ∧ p433r6.fullSufficient := by
  norm_num [p433r6, CarryCell.bothBlocksInsufficient, CarryCell.fullSufficient,
    CarryCell.residualNeed]

/-- Both live adjacent ranks require the zero-carry characteristic-`p` residual together with the
visibly wrapped nonzero carries. This is not a fixed-depth island. -/
theorem both_live_ranks_require_both_blocks :
    (0 < p433r5.gate ∧ p433r5.bothBlocksInsufficient ∧ p433r5.fullSufficient) ∧
    (0 < p433r6.gate ∧ p433r6.bothBlocksInsufficient ∧ p433r6.fullSufficient) := by
  exact ⟨p433_rank5_requires_both, p433_rank6_requires_both⟩

/-- A positive gate does not imply that all nonzero carries meet the residual deficit. Hence
"count every visibly wrapped relation" is not a sufficient consumer. -/
theorem not_nonzero_carry_block_certifies_gate :
    ¬ (0 < p433r5.gate → p433r5.residualNeed ≤ p433r5.jNonzero) := by
  decide

/-- Nor does the full zero-carry block certify the gate. The sign is set only after both blocks are
combined. -/
theorem not_zero_carry_block_certifies_gate :
    ¬ (0 < p433r5.gate → p433r5.need ≤ p433r5.jZero) := by
  decide

-- Axiom audit: structural identities use standard quotient/function extensionality only; calibrated
-- facts are kernel reductions. No `sorryAx`, no native decision procedure.
#print axioms liftNumerator_negated
#print axioms carry_negates
#print axioms antipodalLift_eq_mul_sum
#print axioms lawful_antipodal_carry_zero
#print axioms both_live_ranks_require_both_blocks
#print axioms not_nonzero_carry_block_certifies_gate
#print axioms not_zero_carry_block_certifies_gate

end ArkLib.ProximityGap.Frontier.G278IntegerLiftCarryNoGo
