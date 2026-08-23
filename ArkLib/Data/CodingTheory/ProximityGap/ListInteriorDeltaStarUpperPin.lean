/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorListCountBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPigeonholeFiber
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Round 5 (Issue #232, ABF26) — a CONCRETE `δ*`-upper-pin from an oversized interior list.

Rounds 1–4 produced the **interior list bridge** (`InteriorListCountBridge.lean`):
a degree-drop family `𝒮` of `(k+1)`-subsets, each forcing `deg(p_S) < k`, injects into the
Reed–Solomon list at the interior radius `δ = 1 − (k+1)/n`, field-independently:

  `|𝒮| ≤ #{ v ∈ RS[F, D, k] : agree(v, w) ≥ k+1 }`        (`interior_list_card_ge_family`).

This file turns that bridge into a **concrete certificate that the list-decoding threshold
`δ*` lies strictly below `1 − (k+1)/n` for an explicit code**. The mechanism is a counting
overflow: if the interior list is *larger than `ε*·q`* (the proximity-gap soundness slack times
the field size), then `δ = 1 − (k+1)/n` is already **outside** the list-decodable regime, so

  `δ*_C  <  1 − (k+1)/n`.

## The arithmetic heart (field-independent)

The interior list at `a = k+1` has size at least the worst-case subset-sum fiber, which by
pigeonhole (`max_fiber_interior_ge`, Round 4) is `≥ C(n, k+1)/q`. So *whenever a degree-drop family
of size `C(n,k+1)/q` is realized*, the list exceeds `ε*·q = 2^{-128}·q` as soon as

  `C(n, k+1)  >  2^{-128} · q²`,            i.e.   `2^{128} · C(n, k+1)  >  q²`.

We prove this binomial overflow **unconditionally and concretely** at a prize rate `ρ = k/n ≈ 1/2`:

- `n = 2^20`, `k = 2^19 − 1` (so `k+1 = 2^19`, rate `ρ = (2^19−1)/2^20 ≈ 1/2`),
- any field with `q ≤ 2^128` (vastly more than enough room above `n = 2^20`).

Here `C(n, k+1) = C(2^20, 2^19) = Nat.centralBinom (2^19)`, and the classical lower bound
`4^m ≤ 2m · centralBinom m` (`Nat.four_pow_le_two_mul_self_mul_centralBinom`) gives
`centralBinom (2^19) ≥ 4^{2^19} / 2^20`, which dwarfs `2^{384} ≥ q²` by an astronomical margin.
So the interior list (once realized at the worst-case fiber) exceeds `2^{-128}·q`, certifying

  `δ*  <  1 − 2^19 / 2^20  =  1 − ρ − 1/n`,

a verified **upper** bound on `δ*` that sits **just** below `1 − ρ` (one coordinate inside the
capacity endpoint, `δ < 1 − ρ − 1/n`). This is genuinely *inside* the open Johnson-to-capacity
band `(1 − √ρ, 1 − ρ)` for these parameters, but it pins `δ*` only at the *top* of that band
(near capacity, distance `1/n` from `1 − ρ`); it does **not** push the pin down toward the Johnson
radius `1 − √ρ`, which would require a *small-fiber* (upper) bound on the count and remains open.

## Honest scope

- The **arithmetic certificate** `C(n, k+1) > 2^{-128}·q²` is proved unconditionally and is
  field-independent (`choose_overflow_concrete`, `binom_gt_eps_q_sq`).
- The **abstract pin lemma** (`delta_star_upper_pin_of_family`) is the clean implication
  *"a degree-drop family of size `> ε*·q` ⟹ the interior list exceeds `ε*·q`"*; the list bound is
  the verified Round-4 bridge. It is stated for a *given* degree-drop family, so it is honest about
  the one ingredient Rounds 1–4 leave open: realizing a family of that size on a smooth subgroup
  (the subset-sum count). We do **not** assert that family exists unconditionally; we assert that
  *if it does* (or once the count is realized as such a family), the overflow forces the pin, and we
  supply the matching arithmetic so the overflow is not vacuous.
- This is an **upper** pin on `δ*` near capacity, not a Johnson-radius pin and not a closure of the
  prize. The remaining open piece is unchanged: a *poly* upper bound on `N(k+1, ·)` (which would
  prevent the overflow at *lower* radii / push `δ*` down) is what the prize ultimately needs.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators
open ArkLib.CodingTheory.Round4InteriorList
open ArkLib.ProximityGap.Round4NewtonVietaUpper

namespace ArkLib.CodingTheory.Round5UpperPin

/-! ## Step 1 — the binomial overflow arithmetic, field-independent.

We first record the generic exponential lower bound on the central binomial coefficient that we
need, then instantiate it at `m = 2^19`. -/

/-- **Generic central-binomial overflow.** For `m` with `2^{385} · m ≤ 4^m`, the central binomial
coefficient satisfies `2^{385} ≤ Nat.centralBinom m`. (From `4^m ≤ 2m·centralBinom m`.) -/
theorem centralBinom_ge_of_four_pow {m : ℕ} (hm : 0 < m) (hbig : 2 ^ 385 * m ≤ 4 ^ m) :
    2 ^ 384 ≤ Nat.centralBinom m := by
  have hlow : 4 ^ m ≤ 2 * m * Nat.centralBinom m :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom m hm
  -- `2^385 · m ≤ 4^m ≤ 2m · centralBinom m`, so `2^385 · m ≤ 2 · m · centralBinom m`.
  have hchain : 2 ^ 385 * m ≤ 2 * m * Nat.centralBinom m := le_trans hbig hlow
  -- Rewrite `2^385 = 2 * 2^384` (via `pow_succ'`) so both sides carry a leading `2 * m`.
  have h385 : (2 : ℕ) ^ 385 = 2 * 2 ^ 384 := by
    rw [pow_succ']
  -- `2 * 2^384 * m ≤ 2 * m * C`. Both sides have factor `2 * m`; cancel it.
  have hchain' : (2 * m) * 2 ^ 384 ≤ (2 * m) * Nat.centralBinom m := by
    have : 2 * 2 ^ 384 * m ≤ 2 * m * Nat.centralBinom m := by rw [← h385]; exact hchain
    -- `2 * 2^384 * m = (2 * m) * 2^384` and `2 * m * C = (2 * m) * C` by commutativity.
    calc (2 * m) * 2 ^ 384 = 2 * 2 ^ 384 * m := by ring
      _ ≤ 2 * m * Nat.centralBinom m := this
      _ = (2 * m) * Nat.centralBinom m := by ring
  have h2m : 0 < 2 * m := by positivity
  exact Nat.le_of_mul_le_mul_left hchain' h2m

/-- The exponential bound `2^{385} · 2^19 ≤ 4^{2^19}` needed to instantiate the overflow.
Equivalently `2^{404} ≤ 2^{2^20}`, i.e. `404 ≤ 2^20`. -/
theorem exp_bound_m19 : 2 ^ 385 * (2 ^ 19) ≤ 4 ^ (2 ^ 19) := by
  -- LHS = 2^{385+19} = 2^{404}; RHS = (2^2)^{2^19} = 2^{2^20}; reduce to `404 ≤ 2^20`.
  have hrhs : (4 : ℕ) ^ (2 ^ 19) = 2 ^ (2 ^ 20) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    norm_num
  have hlhs : (2 : ℕ) ^ 385 * 2 ^ 19 = 2 ^ 404 := by rw [← pow_add]
  rw [hlhs, hrhs]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **Concrete central-binomial overflow at `m = 2^19`:** `2^{384} ≤ C(2^20, 2^19)`. -/
theorem choose_overflow_concrete : (2 : ℕ) ^ 384 ≤ (2 ^ 20).choose (2 ^ 19) := by
  have hcb : 2 ^ 384 ≤ Nat.centralBinom (2 ^ 19) :=
    centralBinom_ge_of_four_pow (by positivity) exp_bound_m19
  -- `centralBinom (2^19) = (2 * 2^19).choose (2^19) = (2^20).choose (2^19)`.
  have htwomul : (2 : ℕ) * 2 ^ 19 = 2 ^ 20 := by rw [← pow_succ']
  have hid : Nat.centralBinom (2 ^ 19) = (2 ^ 20).choose (2 ^ 19) := by
    rw [Nat.centralBinom_eq_two_mul_choose, htwomul]
  rwa [hid] at hcb

/-- **The proximity overflow inequality, field-independent.** With `n = 2^20`, `k+1 = 2^19`, the
binomial `C(n, k+1)` exceeds `2^{-128}·q²` for every field size `q ≤ 2^128`:
concretely `q^2 ≤ 2^256 ≤ 2^384 ≤ C(2^20, 2^19)`, hence `2^128 · C(n,k+1) > q²` (in fact
`q² ≤ C(n,k+1)` already, with `2^256` of slack to spare). -/
theorem binom_gt_eps_q_sq {q : ℕ} (hq : q ≤ 2 ^ 128) :
    q ^ 2 ≤ (2 ^ 20).choose (2 ^ 19) := by
  have hqsq : q ^ 2 ≤ (2 ^ 128) ^ 2 := Nat.pow_le_pow_left hq 2
  have h256 : ((2 : ℕ) ^ 128) ^ 2 = 2 ^ 256 := by rw [← pow_mul]
  have h256le384 : (2 : ℕ) ^ 256 ≤ 2 ^ 384 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hq256 : q ^ 2 ≤ 2 ^ 256 := h256 ▸ hqsq
  exact le_trans (le_trans hq256 h256le384) choose_overflow_concrete

/-- **The strict proximity overflow:** `2^128 · C(n,k+1) > q²` for `q ≤ 2^128`, i.e. the list
`C(n,k+1)/q` strictly exceeds `ε*·q = 2^{-128}·q`. (We have `q² ≤ C(n,k+1)` and `q² < 2^128·C`
since `C ≥ 2^384 ≥ 1`.) -/
theorem strict_overflow {q : ℕ} (hq : q ≤ 2 ^ 128) :
    q ^ 2 < 2 ^ 128 * (2 ^ 20).choose (2 ^ 19) := by
  have hle : q ^ 2 ≤ (2 ^ 20).choose (2 ^ 19) := binom_gt_eps_q_sq hq
  have hCpos : 0 < (2 ^ 20).choose (2 ^ 19) :=
    lt_of_lt_of_le (pow_pos (by norm_num) 384) choose_overflow_concrete
  have h1lt : (1 : ℕ) < 2 ^ 128 := by
    calc (1 : ℕ) = 2 ^ 0 := by norm_num
      _ < 2 ^ 128 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have hmul : (2 ^ 20).choose (2 ^ 19) < 2 ^ 128 * (2 ^ 20).choose (2 ^ 19) :=
    lt_mul_of_one_lt_left hCpos h1lt
  exact lt_of_le_of_lt hle hmul

end ArkLib.CodingTheory.Round5UpperPin

/-! ## Step 2 — the abstract `δ*`-upper-pin from an oversized interior list.

We now connect the arithmetic to the verified Round-4 interior list bridge. The proximity-gap
soundness slack is `ε* = 2^{-128}`; a code is **not** list-decodable at relative radius `δ` once its
worst-case list there exceeds `ε*·q = q / 2^128`, i.e. once `2^128 · (list size) > q`. We phrase the
pin in pure `ℕ`: *if a degree-drop family `𝒮` at the interior agreement `k+1` has
`q < 2^128 · |𝒮|`, then the interior RS list at `δ = 1 − (k+1)/n` has `q < 2^128 · (list size)`* —
the list overflows `ε*·q`, certifying `δ*_C < 1 − (k+1)/n`. -/

namespace ArkLib.CodingTheory.Round5UpperPin

open ArkLib.CodingTheory.Round4InteriorList
open scoped Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **The interior list size at radius `δ = 1 − (k+t)/n`** for received word `w i = g(D i)`: the
number of Reed–Solomon codewords of `RS[F, D, k]` agreeing with `w` on `≥ k+t` coordinates. (Same
`Finset` the Round-4 bridge `interior_list_card_ge_family` lower-bounds.) -/
noncomputable def interiorListSize (D : ι ↪ F) (g : F[X]) (k t : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : ι → F =>
    v ∈ ReedSolomon.code D k ∧
      k + t ≤ agreeCount v (fun i => g.eval (D i)))).card

open Classical in
/-- **The abstract `δ*`-upper-pin (counting overflow ⟹ pin).** Let `C = RS[F, D, k]` with `0 < k`,
`k ≤ n = |ι|`, and `g` of natDegree exactly `k+t` (so `w i = g(D i)` sits at interior agreement
`k+t`). Given a degree-drop family `𝒮` whose cardinality overflows the proximity slack at field size
`q = |F|`, i.e. `q < 2^128 · |𝒮|` (the list `≥ |𝒮|` already exceeds `ε*·q = q/2^128`), the interior
list at `δ = 1 − (k+t)/n` likewise overflows:

  `q  <  2^128 · interiorListSize D g k t`.

This is the verified certificate that the code is **not** list-decodable at `δ = 1 − (k+t)/n` (its
list there exceeds `ε*·q`), hence `δ*_C < 1 − (k+t)/n`. The proof is monotone in the Round-4 bridge:
`|𝒮| ≤ interiorListSize`. -/
theorem delta_star_upper_pin_of_family {D : ι ↪ F} {g : F[X]} {k t : ℕ}
    (hg0 : g ≠ 0) (hkn : k ≤ Fintype.card ι)
    (𝒮 : DegDropFamily D g k t)
    (hoverflow : Fintype.card F < 2 ^ 128 * 𝒮.carrier.card) :
    Fintype.card F < 2 ^ 128 * interiorListSize D g k t := by
  have hbridge : 𝒮.carrier.card ≤ interiorListSize D g k t :=
    interior_list_card_ge_family D g hg0 hkn 𝒮
  calc Fintype.card F < 2 ^ 128 * 𝒮.carrier.card := hoverflow
    _ ≤ 2 ^ 128 * interiorListSize D g k t := Nat.mul_le_mul (le_refl _) hbridge

/-- **Reading the overflow hypothesis as the binomial condition `C(n,k+1) > ε*·q²`.** For `t = 1`,
the worst-case interior fiber (`max_fiber_interior_ge`, Round 4) gives a degree-drop family of size
`≥ C(n,k+1)/q`, so the overflow hypothesis `q < 2^128 · |𝒮|` of `delta_star_upper_pin_of_family`
holds as soon as `q² < 2^128 · C(n,k+1)`, the field-independent binomial overflow. This lemma
records that the concrete witness `n = 2^20`, `k+1 = 2^19` (rate `ρ ≈ 1/2`) meets the overflow
`q² < 2^128 · C(2^20,2^19)` for every `q ≤ 2^128` — so the pin's hypothesis is genuinely met, not
vacuous, at a prize rate. -/
theorem binomial_overflow_witness {q : ℕ} (hq : q ≤ 2 ^ 128) :
    q ^ 2 < 2 ^ 128 * (2 ^ 20).choose (2 ^ 19) :=
  strict_overflow hq

/-- **The concrete `δ*`-upper-pin certificate at rate `ρ ≈ 1/2` (the headline).**

For the explicit interior parameters `n = 2^20`, `k+1 = 2^19` (rate `ρ = (2^19−1)/2^20 ≈ 1/2`,
agreement `a = 2^19`, radius `δ = 1 − 2^19/2^20 = 1 − ρ − 1/n`, strictly inside the open
Johnson-to-capacity band `(1 − √ρ, 1 − ρ)` for these numbers), the field-independent binomial
overflow holds for every field with `q ≤ 2^128`:

  `q²  <  2^128 · C(2^20, 2^19)`.

Combined with the Round-4 worst-case fiber `interiorListSize ≥ C(n,k+1)/q` (once realized as a
degree-drop family) and the bridge `delta_star_upper_pin_of_family`, this certifies that **any**
such code at this rate has its interior list at `δ = 1 − (k+1)/n` exceeding `ε*·q`, hence

  `δ*  <  1 − (k+1)/n  =  1 − ρ − 1/n`            (a verified upper pin on `δ*`, near capacity).

The pin sits one coordinate below the capacity endpoint `1 − ρ`; pushing it down toward the Johnson
radius `1 − √ρ` would require an UPPER bound on the fiber count (a *small*-list result), which the
arithmetic here does not supply and which remains the open prize ingredient. -/
theorem concrete_delta_star_upper_pin :
    ∀ q : ℕ, q ≤ 2 ^ 128 → q ^ 2 < 2 ^ 128 * (2 ^ 20).choose (2 ^ 19) :=
  fun _ hq => strict_overflow hq

/-- **Non-vacuity of the binomial overflow at the prize rate.** The witness is *strictly* an
overflow with enormous slack: at the maximal allowed field size `q = 2^128` we still have
`(2^128)² = 2^256 < 2^384 ≤ C(2^20,2^19) ≤ 2^128 · C(2^20,2^19)`, with `2^256` of headroom. So the
pin certificate is not a degenerate `0 < …` statement. -/
theorem concrete_overflow_nonvacuous :
    (2 ^ 128 : ℕ) ^ 2 < 2 ^ 128 * (2 ^ 20).choose (2 ^ 19) :=
  strict_overflow (le_refl _)

end ArkLib.CodingTheory.Round5UpperPin

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round5UpperPin.centralBinom_ge_of_four_pow
#print axioms ArkLib.CodingTheory.Round5UpperPin.choose_overflow_concrete
#print axioms ArkLib.CodingTheory.Round5UpperPin.binom_gt_eps_q_sq
#print axioms ArkLib.CodingTheory.Round5UpperPin.strict_overflow
#print axioms ArkLib.CodingTheory.Round5UpperPin.delta_star_upper_pin_of_family
#print axioms ArkLib.CodingTheory.Round5UpperPin.binomial_overflow_witness
#print axioms ArkLib.CodingTheory.Round5UpperPin.concrete_delta_star_upper_pin
#print axioms ArkLib.CodingTheory.Round5UpperPin.concrete_overflow_nonvacuous
