/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Round 11 — A verified table of exact two-sided integer-floor list crossovers

Attacking ANGLE 2 of the Ethereum Proximity Prize (ABF26 / ArkLib #232) at
finite, fully-decidable scale.  Round 10 pinned the *exact* two-sided
list-decoding crossover for ONE smooth-domain Reed–Solomon instance
(`RS[ZMod 17, F^*, 2]`).  This file **scales that to a table**: three explicit,
prize-faithful, smooth-domain instances, each with a complete machine-checked
two-sided interior crossover.

## Setup common to every row

Fix a prime field `F = ZMod p` (`p ≤ 97`).  The evaluation domain `G ⊆ F^*` is
a **multiplicative subgroup of 2-power size** `n` (a *smooth* domain), namely
`G = {x : x^n = 1}` when `n ∣ (p-1)`.  The code is `RS[F, G, k]`: codewords are
the evaluations on `G` of polynomials of degree `< k` (`k = 2`: lines; `k = 3`:
quadratics).  The **rate** is `ρ = k/n`.

For a received word `w : G → F`, the *agreement* of `w` with a polynomial is the
number of points of `G` where they coincide, and the **list at threshold `a`**

  `listSize a = #{ polys P : agree(w, P) ≥ a }`

is exactly the ordinary fixed-word list `|Λ(C, w, δ)|` at the sample radius
`δ = 1 - a/n`. (These are fixed-word ordinary lists for one explicit received
word per row, **not** worst-stack `ε_mca` thresholds.)

An integer agreement floor `a*` (named `aMinGood` in the code) is a
**two-sided crossover at bound `B`** when `listSize a* ≤ B < listSize (a*-1)`.
Since `listSize` is antitone in the threshold, the good floors are exactly the
`a ≥ a*`: `a*` is the **minimum** good integer agreement floor (every larger
floor is also good), not the largest one.

**Radius cell.** In the ordinary radius convention the list at radius `δ` is
the list at floor `⌈(1-δ)n⌉`, so the bound holds exactly for
`δ < 1 - (a*-1)/n` and fails at `δ = 1 - (a*-1)/n`. The good radii form the
half-open cell `[0, 1 - (a*-1)/n)`: its supremum `1 - (a*-1)/n` is **not**
attained, and `1 - a*/n` is merely an attained good sample radius. For row 1 the
radial supremum is `3/4` (not `11/16`); for rows 2/3 it is `3/4` (not `5/8`).

The **integer** floor `a*` is interior to the agreement window when

  `k < a*`        (above the trivial `k`-agreement floor) and
  `a*^2 < k·n`    (below the Johnson `√(kn)` agreement radius),

so the attained sample radius `1 - a*/n` lies in `(1 - √ρ, 1 - ρ)`. The radial
supremum need not: for rows 2/3, `a* - 1 = k`, so the supremum `3/4` equals the
capacity endpoint `1 - ρ` and is **not** strictly interior. For row 1 the
supremum `3/4` is strictly interior (`1 - √(3/16) < 3/4 < 13/16`).

## What is proven for EACH row (`decide` + structural antitonicity)

* exact list sizes `listSize a* = …` and `listSize (a*-1) = …`;
* `crossover_le : listSize a* ≤ B` and `crossover_gt : B < listSize (a*-1)`;
* **no gap above `a*`**, proven *structurally* from antitonicity of `listSize`
  in `a` (no expensive finite range scan):  `listSize a ≤ B` for **every**
  `a ≥ a*`, while it fails at `a*-1` (and hence, by antitonicity, at every
  `a ≤ a*-1`).  Thus `a*` is exactly the minimum good integer floor;
* **INTERIOR (integer floor)** : `k < a*` and `a*^2 < k·n`.

The three rows:

| field    | `n`  | `k` | `a*` | `B`  | list at `a*` | list at `a*-1` | int. floor     | good radii |
|----------|------|-----|------|------|--------------|----------------|----------------|------------|
| `ZMod 17`| `16` | `3` | `5`  | `10` | `10`         | `62`           | `3<5`, `25<48` | `[0, 3/4)` |
| `ZMod 41`| `8`  | `2` | `3`  | `10` | `4`          | `20`           | `2<3`, `9<16`  | `[0, 3/4)` |
| `ZMod 97`| `8`  | `2` | `3`  | `10` | `3`          | `22`           | `2<3`, `9<16`  | `[0, 3/4)` |

The capstone `delta_star_table` bundles all three rows.

## What is NOT claimed

Each row is a single explicit finite instance, not the asymptotic prize family
`RS[F, L, k]` with `|F| < 2^256`, `ε* = 2^-128`.  The table does not by itself
resolve the open interior; it is a set of exact, machine-checked, *non-vacuous*
data points, each realizing a fully two-sided (no-gap) crossover at an interior
integer agreement floor, across three distinct smooth fields and two rates.  Every
hypothesis is a fixed numeral (word, `B`, `a*`), hence concrete and satisfiable —
nothing is vacuous.  The subgroup claims are themselves machine-checked
(`G_pow_eq_one` lemmas below).
-/

namespace R11DeltaTable

/-! ## Generic decidable list-size core (shared by every row) -/

/-- Generic list-size at threshold `a`: the number of polynomial indices `i`
(drawn from the explicit list `P`) whose agreement `ag i` with the received word
is at least `a`.  Instantiated per row with the concrete polynomial enumeration
and agreement function, this computes `|Λ(C, δ)|` with `δ = 1 - a/n`. -/
def genListSize {ι : Type} (P : List ι) (ag : ι → ℕ) (a : ℕ) : ℕ :=
  (P.filter (fun i => decide (a ≤ ag i))).length

/-- **Antitonicity of the list size in the threshold.**  A larger agreement
threshold can only shrink the list: if `a ≤ a'` then `listSize a' ≤ listSize a`.
This is the structural engine for the no-gap maximality certification (it
replaces an expensive finite range scan by an exact monotonicity argument). -/
theorem genListSize_antitone {ι : Type} (P : List ι) (ag : ι → ℕ)
    {a a' : ℕ} (h : a ≤ a') : genListSize P ag a' ≤ genListSize P ag a := by
  unfold genListSize
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro i hi
  simp only [decide_eq_true_eq] at hi ⊢
  exact le_trans h hi

/-- **No gap above the crossover (generic).**  If the list fits the bound `B` at
the crossover `a*`, then by antitonicity it fits `B` at *every* threshold
`a ≥ a*`.  Combined with the strict failure at `a*-1`, this certifies that `a*`
is the **minimum** integer agreement floor whose list satisfies the bound (all
larger floors also satisfy it): there is no gap.  (The theorem name is
historical.) -/
theorem maximal_of_crossover_le {ι : Type} (P : List ι) (ag : ι → ℕ)
    (aMinGood B : ℕ) (hle : genListSize P ag aMinGood ≤ B) :
    ∀ a, aMinGood ≤ a → genListSize P ag a ≤ B :=
  fun _ ha => le_trans (genListSize_antitone P ag ha) hle

/-! ## Row 1 — `RS[ZMod 17, {x : x^16 = 1}, 3]`  (quadratics, `n = 16`, `k = 3`)

Domain `G = F^* = {1,…,16}` (smooth, `16 = 2^4`).  Codewords are evaluations of
quadratics `x ↦ b·x² + c·x + d`.  Rate `ρ = 3/16`.  Hard word `w₁` is the
block-stitch of four quadratics on the four size-4 blocks of `G`.  Crossover
`a* = 5`, bound `B = 10`. -/
namespace Row1

set_option maxRecDepth 100000

/-- Prime modulus, `F = ZMod 17`. -/
def p : ℕ := 17
/-- Smooth domain `G = {x : x¹⁶ = 1} = {1,…,16}`, size `n = 16 = 2⁴`. -/
def G : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
/-- Quadratic value `b·x² + c·x + d (mod p)`. -/
def polyVal (b c d x : ℕ) : ℕ := (b * x * x + c * x + d) % p
/-- Agreement of `w₁` with the quadratic `(b,c,d)` on `G`. -/
def agree (b c d : ℕ) : ℕ :=
  ((G.zip w).filter (fun xy => decide (polyVal b c d xy.1 = xy.2))).length
where
  /-- The explicit hard received word (its values on `G`). -/
  w : List ℕ := [1, 4, 9, 16, 7, 13, 6, 3, 11, 2, 16, 2, 3, 6, 2, 8]
/-- All `17³ = 4913` quadratics `(b,c,d) ∈ F³`. -/
def allPoly : List (ℕ × ℕ × ℕ) :=
  (List.range p).flatMap (fun b =>
    (List.range p).flatMap (fun c =>
      (List.range p).map (fun d => (b, c, d))))
/-- Agreement as a function of the packed index, for the generic core. -/
def agIdx (i : ℕ × ℕ × ℕ) : ℕ := agree i.1 i.2.1 i.2.2
/-- `listSize a = |Λ(C, δ)|`, `δ = 1 - a/16`. -/
def listSize (a : ℕ) : ℕ := genListSize allPoly agIdx a

/-- The minimum good integer agreement floor `a* = 5`. The good radii are exactly
`δ < 1 - 4/16 = 3/4` (supremum `3/4`, not attained); `11/16 = 1 - 5/16` is an attained
good sample radius, not the radial threshold. -/
def aMinGood : ℕ := 5
/-- The prize-style list-size bound. -/
def B : ℕ := 10

/-- Smoothness check: every element of `G` is a 16-th root of unity in `F`,
i.e. `G` really is the 2-power multiplicative subgroup `{x : x¹⁶ = 1}`. -/
theorem G_pow_eq_one : ∀ x ∈ G, (x ^ 16) % p = 1 := by decide

/-- Exact list size at the crossover `a* = 5`. -/
theorem listSize_aMinGood : listSize 5 = 10 := by decide
/-- Exact list size just below, at `a* - 1 = 4`. -/
theorem listSize_pred : listSize 4 = 62 := by decide

/-- Upper side: the list fits `B = 10` at the crossover. -/
theorem crossover_le : listSize aMinGood ≤ B := by decide
/-- Lower side: the list strictly exceeds `B` one step below. -/
theorem crossover_gt : B < listSize (aMinGood - 1) := by decide
/-- No gap above `a*`: the list fits `B` at every floor `a ≥ a* = 5`. -/
theorem maximal : ∀ a, aMinGood ≤ a → listSize a ≤ B :=
  maximal_of_crossover_le allPoly agIdx aMinGood B crossover_le
/-- The integer floor is interior: `k < a*` and `a*² < k·n`
(`3 < 5` and `25 < 48 = 3·16`). -/
theorem interior : 3 < aMinGood ∧ aMinGood * aMinGood < 3 * 16 := by decide

end Row1

/-! ## Row 2 — `RS[ZMod 41, {x : x^8 = 1}, 2]`  (lines, `n = 8`, `k = 2`)

`ZMod 41` has multiplicative order `40 = 2³·5`; its 2-power subgroup
`G = {x : x⁸ = 1} = {1,3,9,14,27,32,38,40}` has size `n = 8 = 2³` (smooth).
Codewords are evaluations of lines `x ↦ b·x + c`.  Rate `ρ = 2/8 = 1/4`.  Hard
word `w₂` is the block-stitch of four lines on the four size-2 blocks of `G`.
Crossover `a* = 3`, bound `B = 10`. -/
namespace Row2

set_option maxRecDepth 100000

/-- Prime modulus, `F = ZMod 41`. -/
def p : ℕ := 41
/-- Smooth domain `G = {x : x⁸ = 1}`, size `n = 8 = 2³`. -/
def G : List ℕ := [1,3,9,14,27,32,38,40]
/-- Line value `b·x + c (mod p)`. -/
def polyVal (b c x : ℕ) : ℕ := (b * x + c) % p
/-- Agreement of `w₂` with the line `(b,c)` on `G`. -/
def agree (b c : ℕ) : ℕ :=
  ((G.zip w).filter (fun xy => decide (polyVal b c xy.1 = xy.2))).length
where
  /-- The explicit hard received word (its values on `G`). -/
  w : List ℕ := [1, 3, 19, 29, 1, 16, 30, 40]
/-- All `41² = 1681` lines `(b,c) ∈ F²`. -/
def allPoly : List (ℕ × ℕ) :=
  (List.range p).flatMap (fun b => (List.range p).map (fun c => (b, c)))
/-- Agreement as a function of the packed index. -/
def agIdx (i : ℕ × ℕ) : ℕ := agree i.1 i.2
/-- `listSize a = |Λ(C, δ)|`, `δ = 1 - a/8`. -/
def listSize (a : ℕ) : ℕ := genListSize allPoly agIdx a

/-- The minimum good integer agreement floor `a* = 3`. The good radii are exactly
`δ < 1 - 2/8 = 3/4` (supremum `3/4 = 1 - ρ`, the capacity endpoint, not attained);
`5/8 = 1 - 3/8` is an attained good sample radius, not the radial threshold. -/
def aMinGood : ℕ := 3
/-- The prize-style list-size bound. -/
def B : ℕ := 10

/-- Smoothness check: `G = {x : x⁸ = 1}` in `F = ZMod 41`. -/
theorem G_pow_eq_one : ∀ x ∈ G, (x ^ 8) % p = 1 := by decide

/-- Exact list size at the crossover `a* = 3`. -/
theorem listSize_aMinGood : listSize 3 = 4 := by decide
/-- Exact list size just below, at `a* - 1 = 2`. -/
theorem listSize_pred : listSize 2 = 20 := by decide

/-- Upper side: the list fits `B = 10` at the crossover. -/
theorem crossover_le : listSize aMinGood ≤ B := by decide
/-- Lower side: the list strictly exceeds `B` one step below. -/
theorem crossover_gt : B < listSize (aMinGood - 1) := by decide
/-- No gap above `a*`: the list fits `B` at every floor `a ≥ a* = 3`. -/
theorem maximal : ∀ a, aMinGood ≤ a → listSize a ≤ B :=
  maximal_of_crossover_le allPoly agIdx aMinGood B crossover_le
/-- The integer floor is interior: `k < a*` and `a*² < k·n`
(`2 < 3` and `9 < 16 = 2·8`). -/
theorem interior : 2 < aMinGood ∧ aMinGood * aMinGood < 2 * 8 := by decide

end Row2

/-! ## Row 3 — `RS[ZMod 97, {x : x^8 = 1}, 2]`  (lines, `n = 8`, `k = 2`)

`ZMod 97` has multiplicative order `96 = 2⁵·3`; its size-8 2-power subgroup
`G = {x : x⁸ = 1} = {1,22,33,47,50,64,75,96}` is smooth (`8 = 2³`).  Codewords
are evaluations of lines.  Rate `ρ = 1/4`.  Hard word `w₃` is the block-stitch
of four lines on the four size-2 blocks of `G`.  Crossover `a* = 3`, bound
`B = 10`.  (A distinct, larger field from Row 2 at the same `(n,k)`.) -/
namespace Row3

set_option maxRecDepth 100000

/-- Prime modulus, `F = ZMod 97`. -/
def p : ℕ := 97
/-- Smooth domain `G = {x : x⁸ = 1}`, size `n = 8 = 2³`. -/
def G : List ℕ := [1,22,33,47,50,64,75,96]
/-- Line value `b·x + c (mod p)`. -/
def polyVal (b c x : ℕ) : ℕ := (b * x + c) % p
/-- Agreement of `w₃` with the line `(b,c)` on `G`. -/
def agree (b c : ℕ) : ℕ :=
  ((G.zip w).filter (fun xy => decide (polyVal b c xy.1 = xy.2))).length
where
  /-- The explicit hard received word (its values on `G`). -/
  w : List ℕ := [1, 22, 67, 95, 55, 0, 88, 96]
/-- All `97² = 9409` lines `(b,c) ∈ F²`. -/
def allPoly : List (ℕ × ℕ) :=
  (List.range p).flatMap (fun b => (List.range p).map (fun c => (b, c)))
/-- Agreement as a function of the packed index. -/
def agIdx (i : ℕ × ℕ) : ℕ := agree i.1 i.2
/-- `listSize a = |Λ(C, δ)|`, `δ = 1 - a/8`. -/
def listSize (a : ℕ) : ℕ := genListSize allPoly agIdx a

/-- The minimum good integer agreement floor `a* = 3`. The good radii are exactly
`δ < 1 - 2/8 = 3/4` (supremum `3/4 = 1 - ρ`, the capacity endpoint, not attained);
`5/8 = 1 - 3/8` is an attained good sample radius, not the radial threshold. -/
def aMinGood : ℕ := 3
/-- The prize-style list-size bound. -/
def B : ℕ := 10

/-- Smoothness check: `G = {x : x⁸ = 1}` in `F = ZMod 97`. -/
theorem G_pow_eq_one : ∀ x ∈ G, (x ^ 8) % p = 1 := by decide

/-- Exact list size at the crossover `a* = 3`. -/
theorem listSize_aMinGood : listSize 3 = 3 := by decide
/-- Exact list size just below, at `a* - 1 = 2`. -/
theorem listSize_pred : listSize 2 = 22 := by decide

/-- Upper side: the list fits `B = 10` at the crossover. -/
theorem crossover_le : listSize aMinGood ≤ B := by decide
/-- Lower side: the list strictly exceeds `B` one step below. -/
theorem crossover_gt : B < listSize (aMinGood - 1) := by decide
/-- No gap above `a*`: the list fits `B` at every floor `a ≥ a* = 3`. -/
theorem maximal : ∀ a, aMinGood ≤ a → listSize a ≤ B :=
  maximal_of_crossover_le allPoly agIdx aMinGood B crossover_le
/-- The integer floor is interior: `k < a*` and `a*² < k·n`
(`2 < 3` and `9 < 16 = 2·8`). -/
theorem interior : 2 < aMinGood ∧ aMinGood * aMinGood < 2 * 8 := by decide

end Row3

/-! ## Capstone — the verified δ* table -/

/-- **A verified table of exact two-sided integer-floor list crossovers.**

For each of three explicit, prize-faithful, smooth-domain Reed–Solomon instances
— `RS[ZMod 17, F^*, 3]` (`n=16`), `RS[ZMod 41, {x:x⁸=1}, 2]` (`n=8`) and
`RS[ZMod 97, {x:x⁸=1}, 2]` (`n=8`) — with explicit hard words and the explicit
bound `B = 10`, the listed threshold `a*` is simultaneously:

* a **two-sided crossover**: `listSize a* ≤ B < listSize (a*-1)`;
* the **minimum** good integer agreement floor (`listSize a ≤ B` for *all*
  `a ≥ a*`, and it fails below), so the crossover is sharp with no gap; and
* an **interior integer floor**: `k < a*` and `a*² < k·n` (so the attained
  sample radius `1 - a*/n` lies in `(1-√ρ, 1-ρ)`).

In radius terms the bound holds exactly on the half-open cell
`[0, 1 - (a*-1)/n)`, with unattained supremum `3/4` in every row; for rows 2/3
that supremum equals the capacity endpoint `1 - ρ`. These are ordinary
fixed-word lists for one explicit word per row, not worst-stack `ε_mca`
thresholds.

This scales the single Round-10 crossover to three machine-checked, non-vacuous
rows across distinct fields and two rates. -/
theorem delta_star_table :
    -- Row 1: ZMod 17, n=16, k=3, a*=5, B=10
    (Row1.listSize Row1.aMinGood ≤ Row1.B ∧
     Row1.B < Row1.listSize (Row1.aMinGood - 1) ∧
     (∀ a, Row1.aMinGood ≤ a → Row1.listSize a ≤ Row1.B) ∧
     (3 < Row1.aMinGood ∧ Row1.aMinGood * Row1.aMinGood < 3 * 16)) ∧
    -- Row 2: ZMod 41, n=8, k=2, a*=3, B=10
    (Row2.listSize Row2.aMinGood ≤ Row2.B ∧
     Row2.B < Row2.listSize (Row2.aMinGood - 1) ∧
     (∀ a, Row2.aMinGood ≤ a → Row2.listSize a ≤ Row2.B) ∧
     (2 < Row2.aMinGood ∧ Row2.aMinGood * Row2.aMinGood < 2 * 8)) ∧
    -- Row 3: ZMod 97, n=8, k=2, a*=3, B=10
    (Row3.listSize Row3.aMinGood ≤ Row3.B ∧
     Row3.B < Row3.listSize (Row3.aMinGood - 1) ∧
     (∀ a, Row3.aMinGood ≤ a → Row3.listSize a ≤ Row3.B) ∧
     (2 < Row3.aMinGood ∧ Row3.aMinGood * Row3.aMinGood < 2 * 8)) :=
  ⟨⟨Row1.crossover_le, Row1.crossover_gt, Row1.maximal, Row1.interior⟩,
   ⟨Row2.crossover_le, Row2.crossover_gt, Row2.maximal, Row2.interior⟩,
   ⟨Row3.crossover_le, Row3.crossover_gt, Row3.maximal, Row3.interior⟩⟩

end R11DeltaTable

-- Axiom audit: must print exactly [propext, Classical.choice, Quot.sound].
#print axioms R11DeltaTable.delta_star_table
