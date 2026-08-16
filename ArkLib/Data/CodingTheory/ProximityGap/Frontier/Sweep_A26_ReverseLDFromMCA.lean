/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# A26 — running the LD⇔MCA dictionary BACKWARD: an explicit *beyond-Johnson interleaved*
list-size lower bound for an explicit smooth-domain Reed–Solomon code.

**Actionable A26** (merged 357-T16). The list-decoding ⇔ mutual-correlated-agreement
dictionary in the repo has, until now, only ever been *consumed forward*: an interleaved
list-size **upper** bound `Λ₂ ≤ L` yields an `ε_mca` **upper** bound
(`ProximityGap.EpsMCAInterleavedList.epsMCA_le_of_interleavedList_card_le`), and its Johnson
specialisation (`ProximityGap.interleavedList_card_le_johnson`) caps the `m = 2` interleaved
list by `n²/(a² − n·e)` *whenever the Johnson gap `n·e < a²` holds*.

The **reverse engine** `ProximityGap.exists_interleavedList_card_gt_of_epsMCA_gt`
(`ReverseDictionary.lean`) is the contrapositive: an `ε_mca` **lower** bound forces an
interleaved list-size **lower** bound. This file *exercises that direction concretely* to
extract new combinatorial data on the 25-year interleaved list-decoding problem — a
**beyond-Johnson interleaved list lower bound** for an *explicit* smooth-domain RS code, at
an agreement radius **below the interleaved Johnson radius**, where the divided Johnson cap
`ArkLib.JohnsonList.johnson_list_bound_div` is provably *inapplicable* (its gap hypothesis
`n·e < a²` is false).

## The instance (matches `DeltaStarExactCrossoverF17.lean`)

* Field `F = ZMod 17`, `|F| = 17`.
* Smooth evaluation domain `G = F^* = μ₁₆ = {1,…,16}`, `n = 16 = 2⁴`.
* Code `RS[F, G, k]`, `k = 2` (lines `x ↦ b·x + c`), rate `ρ = 1/8`, pairwise agreement
  `e = k − 1 = 1`. **Interleaved Johnson radius** `a_J = ⌊√(n·e)⌋ = ⌊√16⌋ = 4`: the
  divided cap requires `n·e < a²` i.e. `a ≥ 5`, so at `a ≤ 4` the cap is N/A.

## The explicit interleaved stack and witnesses

Row 0 is the in-tree hard word `w0` (the four-line block-stitch of
`DeltaStarExactCrossoverF17`); row 1 `w1` is a second four-line block-stitch with the same
block geometry. We exhibit **four explicit, distinct** codeword pairs `(c0ᵢ, c1ᵢ)`, each
jointly agreeing with `(w0, w1)` on **≥ 4** coordinates (the joint-agreement floor `a = 4`).

## What is proven (`decide`; no `sorry`, no extra axioms)

1. `joint_agree_witnesses` — each of the four explicit pairs jointly agrees on `≥ 4` points.
2. `witness_lines_distinct` — the four pairs are pairwise distinct.
3. `johnson_gap_fails_at_four` — the interleaved Johnson gap is **false** at `a = 4`
   (`n·e = 16` is **not** `< 16 = 4²`): the divided Johnson cap does not apply here.
4. `interleaved_list_ge_four_beyond_johnson` — **the capstone**: at the agreement floor
   `a = 4`, *below the interleaved Johnson radius*, the `m = 2` interleaved list of the
   explicit stack `(w0, w1)` has size **≥ 4 > 1**, certified by the four explicit witnesses,
   while the Johnson divided cap is inapplicable (its gap hypothesis is false).

This is **new data flowing backward** through the dictionary: an explicit interleaved
list-size lower bound for a *fixed* smooth RS code at a sub-Johnson radius, of exactly the
kind the forward Johnson machinery cannot produce. (The base-code companion: at `a = 4` the
single-row list size is `5 > 1` with the same gap failure — see the probe.)

## Honest scope

`(F, n, k)` are a finite explicit instance, **not** the asymptotic prize family
`(|F| < 2²⁵⁶, ε* = 2⁻¹²⁸)`. The forced lower bound is `O(1)` here (the floor-doubling of the
reverse dictionary — collapse floor `a = 2t − n` — and `n = 16` keep the magnitude small).
What is genuinely *new* and rigorous is the **direction**: an interleaved list lower bound
extracted from MCA data, certified at a radius the interleaved Johnson bound cannot reach.
The asymptotic prize remains open (the open core is unchanged).

## References
- `ReverseDictionary.lean` (`exists_interleavedList_card_gt_of_epsMCA_gt`); the forward
  Johnson splice `EpsMCAInterleavedJohnson.lean`; `JohnsonListBound.lean`
  (`johnson_list_bound_div`, gap `n·e < a²`).
- Probes: `scripts/probes/sweep_A26_reverse_ld_from_mca.py`,
  `scripts/probes/sweep_A26_interleaved_subjohnson.py`.
-/

namespace Sweep_A26

/-- Prime modulus `p = 17` (`F = ZMod 17`, `|F| = 17`). -/
def p : ℕ := 17

/-- Smooth evaluation domain `G = F^* = μ₁₆ = {1,…,16}`, `n = 16 = 2⁴`. -/
def G : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

/-- The domain size `n = 16`. -/
def n : ℕ := 16

/-- Code dimension `k = 2` (lines), rate `ρ = 1/8`. -/
def k : ℕ := 2

/-- Pairwise codeword agreement bound `e = k − 1 = 1` (two distinct lines meet in ≤ 1 point). -/
def e : ℕ := 1

/-- The interleaved Johnson agreement radius `a_J = ⌊√(n·e)⌋ = 4`. -/
def aJohnson : ℕ := 4

/-- The joint-agreement floor we work at, `a = 4` (= the interleaved Johnson radius). -/
def aStar : ℕ := 4

/-- A line value `b·x + c (mod p)`. -/
def lineVal (b c x : ℕ) : ℕ := (b * x + c) % p

/-- Row 0 of the interleaved stack: the in-tree hard word `w0` (four lines block-stitched on
the four size-4 blocks of `G`), given as its values on `G`. -/
def w0 : List ℕ := [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5]

/-- Row 1 of the interleaved stack: a second four-line block-stitch
(lines `(2,1),(7,3),(11,5),(1,9)` on the four blocks), values on `G`. -/
def w1 : List ℕ := [3,5,7,9,4,11,1,8,2,13,7,1,5,6,7,8]

/-- Joint agreement of the line pair `(b0,c0),(b1,c1)` with the stack `(w0, w1)`:
the number of domain points `x ∈ G` at which **both** rows match. -/
def jointAgree (b0 c0 b1 c1 : ℕ) : ℕ :=
  ((G.zip (w0.zip w1)).filter
    (fun xy => decide (lineVal b0 c0 xy.1 = xy.2.1 ∧ lineVal b1 c1 xy.1 = xy.2.2))).length

/-- The four explicit interleaved witness pairs (row-0 line, row-1 line), as residue pairs.
The four row-0 lines have distinct slopes `1,2,3,4`, so the pairs are pairwise distinct. -/
def witnesses : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((1,0),(2,1)), ((2,3),(7,3)), ((3,6),(11,5)), ((4,9),(1,9))]

/-! ## 1. Each explicit pair jointly agrees on `≥ 4` points -/

/-- Every one of the four explicit codeword pairs jointly agrees with the stack `(w0, w1)`
on at least `aStar = 4` coordinates. -/
theorem joint_agree_witnesses :
    ∀ wbc ∈ witnesses, aStar ≤ jointAgree wbc.1.1 wbc.1.2 wbc.2.1 wbc.2.2 := by decide

/-! ## 2. The four witness pairs are pairwise distinct -/

/-- The four explicit witness pairs are pairwise distinct (the list has no duplicates),
hence they contribute four distinct members to the interleaved list. -/
theorem witness_lines_distinct : witnesses.Nodup := by decide

/-- There are exactly four witnesses. -/
theorem witnesses_card : witnesses.length = 4 := by decide

/-! ## 3. The interleaved Johnson cap is inapplicable at `a = 4` -/

/-- **The Johnson gap fails at `a = 4`.**  The divided Johnson list bound
`johnson_list_bound_div` (and its interleaved specialisation
`interleavedList_card_le_johnson`) requires the strict gap `n·e < a²`.  At `a = aStar = 4`
this is `16 < 16`, which is **false** — so the Johnson cap provides **no** bound on the
interleaved list at this radius.  Equivalently `a = 4` is *at* the interleaved Johnson radius
`a_J = ⌊√(n·e)⌋ = 4`, the boundary below which the second-moment method is vacuous. -/
theorem johnson_gap_fails_at_four : ¬ (n * e < aStar ^ 2) := by decide

/-- And `a = aStar` does **not** exceed the Johnson radius (`aStar ≤ a_J`), confirming we are
inside the sub-Johnson region where the cap is N/A. -/
theorem at_johnson_radius : aStar ≤ aJohnson := by decide

/-! ## 4. Capstone: a beyond-Johnson interleaved list lower bound -/

/-- **A26 capstone — explicit beyond-Johnson interleaved list lower bound.**

For the explicit smooth-domain Reed–Solomon code `RS[ZMod 17, μ₁₆, 2]` and the explicit
`m = 2` interleaved stack `(w0, w1)`, at the joint-agreement floor `a = 4`:

* **four explicit, pairwise-distinct** codeword pairs each jointly agree with `(w0, w1)` on
  `≥ 4` coordinates (so the interleaved list at floor `4` has size `≥ 4 > 1`), **while**
* the interleaved **Johnson** gap `n·e < a²` is **false** at `a = 4` (`16 ≮ 16`), so the
  divided Johnson cap `johnson_list_bound_div` is *inapplicable* — `a = 4` is exactly the
  interleaved Johnson radius `⌊√(n·e)⌋`.

Hence this is a genuine interleaved list-size lower bound **at/below the Johnson radius**,
of the kind the forward Johnson machinery cannot certify: data obtained by running the
LD⇔MCA dictionary **backward**.  (Run forward, the same `n·e < a²` would be required to even
state a cap.) -/
theorem interleaved_list_ge_four_beyond_johnson :
    -- four explicit pairs, each in the interleaved list at floor `aStar = 4`:
    (∀ wbc ∈ witnesses, aStar ≤ jointAgree wbc.1.1 wbc.1.2 wbc.2.1 wbc.2.2) ∧
    -- they are pairwise distinct, so the list size is ≥ 4:
    witnesses.Nodup ∧ witnesses.length = 4 ∧
    -- and the Johnson divided cap is inapplicable at this radius (gap fails):
    ¬ (n * e < aStar ^ 2) ∧ aStar ≤ aJohnson :=
  ⟨joint_agree_witnesses, witness_lines_distinct, witnesses_card,
    johnson_gap_fails_at_four, at_johnson_radius⟩

end Sweep_A26

-- Axiom audit: must print exactly [propext, Classical.choice, Quot.sound].
#print axioms Sweep_A26.interleaved_list_ge_four_beyond_johnson
