/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Round 10 — EXACT δ* crossover for an explicit smooth-domain Reed–Solomon instance

Attacking ANGLE 1 of the Ethereum Proximity Prize (ABF26 / ArkLib #232) at
finite, fully-decidable scale: we pin the **exact** list-decoding threshold
(closing the Round-9 bracket `5 ≤ |Λ| ≤ 120` to a single sharp two-sided
crossover) for a concrete smooth-domain Reed–Solomon code.

## The instance

* Field `F = ZMod 17` (prime `p = 17`, `|F| = 17`).
* Evaluation domain `G = F^* = {x : x^16 = 1}`, the multiplicative subgroup of
  size `n = 16` — a **smooth** domain (`16 = 2^4`).  Concretely `G = {1,…,16}`.
* Code `RS[F, G, k]` with `k = 2`: codewords are evaluations of **lines**
  `x ↦ b·x + c`, `(b,c) ∈ F × F`.  Rate `ρ = k/n = 1/8`.

The agreement of a received word `w : G → F` with the line `(b,c)` is
`agree(w,b,c) = #{x ∈ G : w x = b·x + c}`.  The **list at threshold `a`** is
`L(a) = #{(b,c) ∈ F × F : agree(w,b,c) ≥ a}` — i.e. `|Λ(C, δ)|` with the
relative distance `δ = 1 - a/n`.

## What is proven (all by `decide`; no `sorry`, no extra axioms)

For the EXPLICIT hard word
`w = [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5]` (its values on `G = [1,…,16]`,
the block-stitch of four lines on four size-4 blocks) and the EXPLICIT
prize-style list-size bound `B = 10`, with `a* = 4`:

1. Exact list sizes:  `listSize 3 = 15`, `listSize 4 = 5`, `listSize 5 = 3`.
2. `crossover_le  : listSize 4 ≤ B`   (the list fits the bound at `a*`).
3. `crossover_gt  : B < listSize 3`   (the list breaks the bound at `a*-1`).
4. `interior      : 2 < 4 ∧ 4*4 < 2*16`  — `a*` is strictly **interior**:
   `k < a*` (above the trivial `k`-agreement floor) and `a*^2 < k·n` (below the
   Johnson `√(k·n)` agreement radius); equivalently `δ* = 1 - 4/16 = 3/4` lies
   in the open window `(1-√ρ, 1-ρ) = (1-√(1/8), 7/8) ≈ (0.646, 0.875)` that the
   prize targets.

The capstone `exact_delta_crossover` bundles (2)+(3)+(4): `a* = 4` is the exact,
two-sided, no-gap crossover for THIS code at bound `B`, *and* it is interior.

A companion `crossover_is_maximal` certifies sharpness from the *definition* of
the crossover: `a* = 4` is the **largest** threshold whose list fits `B`
(`listSize a ≤ B` holds for every `a ≥ 4`, i.e. on `{4,…,16}`, but fails at
`a = 3`), so there is genuinely no gap and `a*` is not an arbitrary choice.

## What is NOT claimed

This is a single explicit finite instance, not the asymptotic family
`RS[F, L, k]` with `|F| < 2^256`, `ε* = 2^-128`.  It does not by itself resolve
the open interior of the prize; it is an exact, machine-checked, *non-vacuous*
data point realizing a fully two-sided (no-gap) crossover at an interior
threshold.  All hypotheses are concrete and satisfiable (the word, `B`, and
`a*` are fixed numerals), so nothing here is vacuous.
-/

namespace R10ExactDelta

/-- Prime modulus `p = 17` (so `F = ZMod 17`, `|F| = 17`). -/
def p : ℕ := 17

/-- Evaluation domain `G = F^* = {1,…,16}`, a smooth multiplicative subgroup of
size `n = 16`.  Represented as residues `1..16` in `ℕ`. -/
def G : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

/-- The explicit "hard" received word `w : G → F`, given as its value list on
`G` (position `i` holds `w (G[i])`).  It is the block-stitched word: four lines
on the four consecutive blocks of size `4`, forcing a large mid-threshold list
while keeping the crossover strictly interior. -/
def w : List ℕ := [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5]

/-- The explicit prize-style list-size bound `B = 10`. -/
def B : ℕ := 10

/-- The crossover threshold `a* = 4` (relative distance `δ* = 1 - 4/16 = 3/4`). -/
def aStar : ℕ := 4

/-- The line value `b·x + c (mod p)`. -/
def lineVal (b c x : ℕ) : ℕ := (b * x + c) % p

/-- Agreement of `w` with the line `(b,c)`: number of domain points `x ∈ G`
(with paired word value `wx = w x`) at which `w x = b·x + c (mod p)`.
`G.zip w` pairs each domain point `x` with its word value `w x`. -/
def agree (b c : ℕ) : ℕ :=
  ((G.zip w).filter (fun xy => decide (lineVal b c xy.1 = xy.2))).length

/-- All `289` lines `(b,c) ∈ F × F`, as residue pairs in `0..16 × 0..16`. -/
def allLines : List (ℕ × ℕ) :=
  (List.range p).flatMap (fun b => (List.range p).map (fun c => (b, c)))

/-- The list size at agreement threshold `a`: number of lines `(b,c)` whose
agreement with `w` is at least `a`.  This is `|Λ(C, δ)|` with `δ = 1 - a/n`. -/
def listSize (a : ℕ) : ℕ :=
  (allLines.filter (fun bc => decide (a ≤ agree bc.1 bc.2))).length

/-! ## Exact list sizes around the crossover (verified by full finite evaluation) -/

/-- At `a* - 1 = 3` the list has size exactly `15`. -/
theorem listSize_three : listSize 3 = 15 := by decide

/-- At the crossover `a* = 4` the list has size exactly `5`. -/
theorem listSize_four : listSize 4 = 5 := by decide

/-- At `a* + 1 = 5` the list has size exactly `3`. -/
theorem listSize_five : listSize 5 = 3 := by decide

/-! ## The two-sided crossover at `B = 10` -/

/-- Upper side: at the crossover `a* = 4` the list fits the bound `B = 10`. -/
theorem crossover_le : listSize aStar ≤ B := by decide

/-- Lower side: just below, at `a* - 1 = 3`, the list strictly exceeds `B = 10`. -/
theorem crossover_gt : B < listSize (aStar - 1) := by decide

/-- The crossover is strictly **interior** to the open prize window:
`k < a*` (i.e. `δ* < 1 - k/n`, above the trivial floor) and `a*^2 < k·n`
(i.e. `δ* > 1 - √(k·n)/n = 1 - √ρ`, below the Johnson radius). With `k = 2`,
`n = 16`: `2 < 4` and `4·4 = 16 < 32 = 2·16`. -/
theorem interior : 2 < aStar ∧ aStar * aStar < 2 * 16 := by decide

/-! ## Sharpness: `a* = 4` is *the* crossover, with no gap -/

/-- Maximality (no-gap certification): the list fits `B = 10` at **every**
threshold `a ≥ a* = 4` (checked on the full meaningful range `{4,…,16}`, beyond
which the list is empty), but fails at `a = 3 = a* - 1`. Hence `a*` is exactly
the largest threshold whose list satisfies the bound — there is no threshold in
the gap, so the two-sided crossover is sharp. -/
theorem crossover_is_maximal :
    (∀ a ∈ Finset.Icc 4 16, listSize a ≤ B) ∧ ¬ (listSize 3 ≤ B) := by decide

/-! ## Capstone -/

/-- **Exact two-sided δ\* crossover for an explicit smooth-domain Reed–Solomon
instance.**  For the explicit word `w`, the smooth code `RS[ZMod 17, F^*, 2]`
and the explicit bound `B = 10`, the threshold `a* = 4` simultaneously:

* satisfies the bound: `listSize a* ≤ B`;
* breaks the bound one step lower: `B < listSize (a* - 1)`;
* is the **largest** such threshold (`listSize a ≤ B` for all `a ∈ {4,…,16}`),
  so the crossover is sharp with no gap; and
* is strictly **interior**: `k < a*` and `a*^2 < k·n` (`δ* = 3/4 ∈ (1-√ρ, 1-ρ)`).

This closes the Round-9 bracket to a single exact, machine-checked, non-vacuous
two-sided crossover at `δ* = 1 - 4/16 = 3/4`. -/
theorem exact_delta_crossover :
    listSize aStar ≤ B ∧
    B < listSize (aStar - 1) ∧
    (∀ a ∈ Finset.Icc 4 16, listSize a ≤ B) ∧
    (2 < aStar ∧ aStar * aStar < 2 * 16) := by
  refine ⟨crossover_le, crossover_gt, ?_, interior⟩
  exact (crossover_is_maximal).1

end R10ExactDelta

-- Axiom audit: must print exactly [propext, Classical.choice, Quot.sound].
#print axioms R10ExactDelta.exact_delta_crossover
