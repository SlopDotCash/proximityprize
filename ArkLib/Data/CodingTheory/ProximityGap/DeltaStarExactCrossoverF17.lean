/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Round 10 — fixed-word list-size crossover for an explicit smooth-domain RS instance

Attacking ANGLE 1 of the Ethereum Proximity Prize (ABF26 / ArkLib #232) at
finite, fully-decidable scale: for **one fixed received word** `w` we compute the
exact list sizes of a concrete smooth-domain Reed–Solomon code around a
list-budget crossover.  (The file name says "δ* exact crossover"; what is proved
is a fixed-word integer statistic, not the code's worst-word threshold — see
"What is NOT claimed".)

## The instance

* Field `F = ZMod 17` (prime `p = 17`, `|F| = 17`).
* Evaluation domain `G = F^* = {x : x^16 = 1}`, the multiplicative subgroup of
  size `n = 16` — a **smooth** domain (`16 = 2^4`).  Concretely `G = {1,…,16}`.
* Code `RS[F, G, k]` with `k = 2`: codewords are evaluations of **lines**
  `x ↦ b·x + c`, `(b,c) ∈ F × F`.  Rate `ρ = k/n = 1/8`.

The agreement of a received word `w : G → F` with the line `(b,c)` is
`agree(w,b,c) = #{x ∈ G : w x = b·x + c}`.  The **list at threshold `a`** is
`L(a) = #{(b,c) ∈ F × F : agree(w,b,c) ≥ a}` — the size of the list of codewords
within closed relative distance `1 - a/n` **of this one word `w`**.

## What is proven (all by `decide`; no `sorry`, no extra axioms)

For the EXPLICIT word
`w = [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5]` (its values on `G = [1,…,16]`,
the block-stitch of four lines on four size-4 blocks) and the EXPLICIT
list-size budget `B = 10`, with `wordCrossover = 4`:

1. Exact list sizes:  `listSize 3 = 15`, `listSize 4 = 5`, `listSize 5 = 3`.
2. `crossover_le  : listSize 4 ≤ B`   (the list fits the budget at agreement `4`).
3. `crossover_gt  : B < listSize 3`   (the list breaks the budget at agreement `3`).
4. `interior      : 2 < 4 ∧ 4*4 < 2*16` — `k < 4` and `4² < k·n`.

`crossover_is_least` records that the list fits `B` at **every** agreement threshold
`a ∈ {4,…,16}` (and trivially above `16`, where the list is empty) but not at `a = 3`.
Since `listSize` is antitone in `a`, `4` is the **smallest** integer agreement threshold
whose list fits `B` (not the largest: every larger threshold also fits).  The capstone
`word_list_crossover` bundles (2), (3), the range check, and (4).

## What is NOT claimed

* **No worst-word quantifier.**  Every declaration counts the 289 lines against the single
  fixed `w`; nothing quantifies over all received words.  A code threshold `δ*` (worst word)
  would additionally need a matching universal upper bound on `L(a)` over all words; this
  file only shows that `w` is a word whose list exceeds `B` at agreement `3`.
* **Integer threshold ≠ continuous radius.**  For closed balls of radius `δ`, the list of `w`
  is the set of lines with agreement `≥ ⌈16(1 - δ)⌉`; it stays within `B` for every
  `δ < 13/16` and fails at `δ = 13/16`.  So the supremum of good continuous radii for this
  word is `13/16`, not `3/4`.  The value `1 - 4/16 = 3/4` is only the largest good radius
  on the grid `{1 - a/16}`.
* **Not beyond the finite-distance Johnson threshold.**  The inequality `4² < k·n = 32`
  compares with the coarse rate expression `√(k·n)`.  For degree-`< 2` lines distinct
  codewords agree in at most `k - 1 = 1` point, so the sharper finite-distance Johnson
  agreement threshold is `√(n·(k - 1)) = 4`; this example sits exactly at that boundary.
  The displayed numerical window `(1-√ρ, 1-ρ) ≈ (0.646, 0.875)` containing `3/4` is true
  arithmetic but does not show progress beyond the Johnson threshold.
* This is a single explicit finite instance, not the asymptotic family
  `RS[F, L, k]` with `|F| < 2^256`, `ε* = 2^-128`, and it does not resolve the open interior
  of the prize.  All hypotheses are concrete numerals, so nothing here is vacuous.
-/

namespace R10ExactDelta

/-- Prime modulus `p = 17` (so `F = ZMod 17`, `|F| = 17`). -/
def p : ℕ := 17

/-- Evaluation domain `G = F^* = {1,…,16}`, a smooth multiplicative subgroup of
size `n = 16`.  Represented as residues `1..16` in `ℕ`. -/
def G : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

/-- The explicit received word `w : G → F`, given as its value list on
`G` (position `i` holds `w (G[i])`).  It is the block-stitched word: four lines
on the four consecutive blocks of size `4`, forcing a large mid-threshold list.
All list sizes in this file are for this one word only. -/
def w : List ℕ := [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5]

/-- The explicit list-size budget `B = 10`. -/
def B : ℕ := 10

/-- The fixed-word integer crossover `4`: the **smallest** agreement threshold at which the
list of the single word `w` fits `B`.  Its grid radius is `1 - 4/16 = 3/4`; the supremum of good
continuous closed-ball radii for `w` is `13/16`.  This is not the code's worst-word `δ*`. -/
def wordCrossover : ℕ := 4

@[deprecated wordCrossover (since := "2026-10-28")]
alias aStar := wordCrossover

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
agreement with the fixed word `w` is at least `a`, i.e. the list of `w` in the closed ball of
relative radius `1 - a/n`.  It is antitone in `a`.  (A fixed-word statistic: it is not the
worst-word list size `max_w |Λ(C, w, δ)|`.) -/
def listSize (a : ℕ) : ℕ :=
  (allLines.filter (fun bc => decide (a ≤ agree bc.1 bc.2))).length

/-! ## Exact list sizes around the crossover (verified by full finite evaluation) -/

/-- At agreement `3` the list of `w` has size exactly `15`. -/
theorem listSize_three : listSize 3 = 15 := by decide

/-- At agreement `4` the list of `w` has size exactly `5`. -/
theorem listSize_four : listSize 4 = 5 := by decide

/-- At agreement `5` the list of `w` has size exactly `3`. -/
theorem listSize_five : listSize 5 = 3 := by decide

/-! ## The two-sided fixed-word crossover at `B = 10` -/

/-- Upper side: at agreement `wordCrossover = 4` the list of `w` fits the budget `B = 10`. -/
theorem crossover_le : listSize wordCrossover ≤ B := by decide

/-- Lower side: at agreement `3` the list of `w` strictly exceeds `B = 10`. -/
theorem crossover_gt : B < listSize (wordCrossover - 1) := by decide

/-- Numerical position of the crossover: `k < 4` and `4² < k·n` (with `k = 2`, `n = 16`:
`2 < 4` and `16 < 32`).  The second inequality is relative to the coarse rate expression
`√(k·n)`; the sharper finite-distance Johnson agreement threshold `√(n·(k-1)) = 4` is attained
with equality, so this does not place the crossover beyond the Johnson threshold. -/
theorem interior : 2 < wordCrossover ∧ wordCrossover * wordCrossover < 2 * 16 := by decide

/-! ## Least fitting threshold -/

/-- The list of `w` fits `B = 10` at **every** agreement threshold `a ∈ {4,…,16}` (above `16`
the list is empty), but not at `a = 3`.  Since `listSize` is antitone, `4` is the **smallest**
integer agreement threshold whose list fits `B`; every larger threshold also fits. -/
theorem crossover_is_least :
    (∀ a ∈ Finset.Icc 4 16, listSize a ≤ B) ∧ ¬ (listSize 3 ≤ B) := by decide

@[deprecated crossover_is_least (since := "2026-10-28")]
alias crossover_is_maximal := crossover_is_least

/-! ## Capstone -/

/-- **Fixed-word two-sided list crossover for an explicit smooth-domain Reed–Solomon
instance.**  For the single explicit word `w`, the smooth code `RS[ZMod 17, F^*, 2]` and the
explicit budget `B = 10`, the integer agreement threshold `wordCrossover = 4`:

* fits the budget: `listSize 4 ≤ B`;
* breaks it one step lower: `B < listSize 3`;
* has every larger threshold fitting too (`listSize a ≤ B` for all `a ∈ {4,…,16}`), so it is
  the smallest fitting integer threshold; and
* satisfies `k < 4` and `4² < k·n`.

This is a statement about one word, not the worst-word code threshold `δ*`; its grid radius is
`1 - 4/16 = 3/4`, while the supremum of good continuous closed-ball radii for `w` is `13/16`. -/
theorem word_list_crossover :
    listSize wordCrossover ≤ B ∧
    B < listSize (wordCrossover - 1) ∧
    (∀ a ∈ Finset.Icc 4 16, listSize a ≤ B) ∧
    (2 < wordCrossover ∧ wordCrossover * wordCrossover < 2 * 16) := by
  refine ⟨crossover_le, crossover_gt, ?_, interior⟩
  exact crossover_is_least.1

@[deprecated word_list_crossover (since := "2026-10-28")]
alias exact_delta_crossover := word_list_crossover

end R10ExactDelta

-- Axiom audit: must print exactly [propext, Classical.choice, Quot.sound].
#print axioms R10ExactDelta.word_list_crossover
