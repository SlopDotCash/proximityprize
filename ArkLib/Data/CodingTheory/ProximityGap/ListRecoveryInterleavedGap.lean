/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedLambdaGe
import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# List-recovery / interleaved reformulation: the list-size sandwich (#232, ABF26 §5)

This file attacks the **list-recovery / `m`-interleaved** reformulation of the Proximity Prize open
core (Issue #232, ABF26 *Grand List Decoding Challenge*).  ABF26 §5 asks whether the single-code
list-decoding challenge (pin `δ*` for `C = RS[F, smooth domain, k]`) and the *interleaved* challenge
(pin `δ*` for `C^{≡m}`) **collapse** onto the same answer.  Round-1 found a convergent obstruction:
every standard technique hits the same "`≤ k-1` freely placed agreement positions" wall, fully
realizable inside the smooth domain.  The honest question for this angle is whether the interleaved
structure pins `δ*` *differently*.

## What is proven here (all `sorry`-free, axiom-clean)

The in-tree development already has the two **one-sided** interleaved list-size bounds, each proven
independently:

* `Lambda_interleaved_le_pow` (`InterleavedListSize`): the elementary, `m`-dependent **upper** bound
  `Λ(C^{≡m}, δ) ≤ (Λ(C, δ))^m`, from column projection + per-column base lists.
* `Lambda_interleaved_ge` (`InterleavedLambdaGe`): the **lower** bound `Λ(C, δ) ≤ Λ(C^{≡m}, δ)`, from
  the diagonal embedding `c ↦ (i,_) ↦ c i`.

This file *composes* them into the genuinely new content of the §5-collapse question:

1. `Lambda_interleaved_sandwich` — the two-sided sandwich
   `Λ(C, δ) ≤ Λ(C^{≡m}, δ) ≤ (Λ(C, δ))^m`, in one statement.

2. `interleaved_poly_of_base_poly` / `base_poly_of_interleaved_poly` — the **polynomial-threshold
   transfer**: if the base list is `≤ B` then the interleaved list is `≤ B^m`; conversely if the
   interleaved list is `≤ B` then the base list is `≤ B`.  Hence for *fixed* `m`, the base list is
   polynomial in `|F|` **iff** the interleaved list is.

3. `interleaved_finite_iff_base_finite` — finiteness collapse: `Λ(C^{≡m}, δ) < ⊤ ⟺ Λ(C, δ) < ⊤`
   (the interleaving neither creates nor destroys infinite lists).

4. `deltaStar_collapse_forward` / `deltaStar_collapse_backward` — the **budget-changing list-size
   transfer** (the historical `deltaStar_*` names do not mean an equality of thresholds): a
   radius `δ` that is "good" for the base code at budget `B` (`Λ(C,δ) ≤ B`) is "good" for the
   interleaved code at the *larger* budget `B^m`, and a radius good for the interleaved code at
   budget `B` is good for the base code at the *same* `B`.

   **What this does not give.** Because the forward leg changes the budget from `B` to `B^m`, these
   theorems do **not** show that the fixed-budget list threshold is the same for `C` and `C^{≡m}`.
   That equality is false in general. Take the binary repetition code of length 3, arity `m = 2` and
   budget `B = 2`. The base code has only 2 codewords, so every radius up to `1` is `2`-good. The
   interleaved code consists of the 4 constant pair-words. At `δ = 2/3` the received word
   `((0,0),(0,1),(1,0))` lists 3 distinct constants, so `δ = 2/3` is not `2`-good. Below `2/3`, any
   listed constant must occupy at least 2 of the 3 coordinates, so at most one is listed. The
   fixed-`B` good-radius supremum is therefore `2/3` for `C^{≡2}` against `1` for `C`. What
   does transfer, for fixed `m`, is the *existence of some polynomial list bound* (an asymptotic
   threshold notion). Nothing here defines or compares the repository's MCA threshold `mcaDeltaStar`, so this
   is also not a statement about the security-budget MCA `δ*`.

5. `gap_present_in_interleaved` — the convergent-wall confirmation: *any* base-code list-size lower
   bound at an interior radius `δ` propagates verbatim to the interleaved code
   (`L ≤ Λ(C,δ) ≤ Λ(C^{≡m},δ)`).  So every list-size obstruction known for `C` is also present in
   `C^{≡m}` at the same radius (the interleaved code may have additional ones). The list-recovery
   view inherits, rather than resolves, the wall.

## Honest scope (what is NOT done)

This is a verified **list-size sandwich**, not a closure and not a threshold equality.  It proves
that, for fixed `m`, a polynomial list bound exists for `C` iff one exists for `C^{≡m}`, with the
budget raised to the fixed `m`-th power in one direction. At a *fixed* budget the list thresholds of
`C` and `C^{≡m}` can differ (see the repetition-code example in item 4), and the MCA threshold
`mcaDeltaStar` is not addressed. The deep `m`-independent GGR11 bound (`lambda_le_ggr11`,
exponent `m → r`) is still gated on the external Erase-Decode-tree residual `GGR11TreeStructure`;
that improved exponent would only *tighten the budget transfer*.  The actual prize — a
matching interior upper bound for `Λ(C,δ)` itself on the smooth domain — is untouched; the
list-recovery reformulation provably reduces *to* it (this file), it does not *solve* it.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
- [GGR11] Gopalan, Guruswami, Raghavendra. *List Decoding Tensor Products and Interleaved Codes*. 2011.
-/

open ListDecodable Code InterleavedCode

namespace ArkLib.CodingTheory.Round2ListRecovery

open InterleavedCode.ListSize

variable {ι F : Type} [Fintype ι]

/-! ### 1. The two-sided interleaved list-size sandwich. -/

/-- **The interleaved list-size sandwich.** For a finite field `F`, a nonempty coordinate set, and
any fixed arity `m ≠ 0`, the maximised list size of the `m`-interleaved code `C^{≡m}` is squeezed
between the base list size and its `m`-th power:

  `Λ(C, δ) ≤ Λ(C^{≡m}, δ) ≤ (Λ(C, δ))^m`.

The lower bound is `Lambda_interleaved_ge` (diagonal embedding); the upper bound is
`Lambda_interleaved_le_pow` (column projection).  This is the structural heart of the ABF26 §5
collapse: interleaving moves the list size only *within* a fixed power band. -/
theorem Lambda_interleaved_sandwich [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ} [NeZero m]
    (C : Set (ι → F)) (δ : ℝ) :
    ListDecodable.Lambda C δ ≤ ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ ∧
      ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤ (ListDecodable.Lambda C δ) ^ m :=
  ⟨Lambda_interleaved_ge C δ, Lambda_interleaved_le_pow C δ⟩

/-! ### 2. Polynomial-threshold transfer (the collapse, in `≤ B` form). -/

/-- **Base bound ⟹ interleaved bound (with `m`-power on the threshold).** If the base-code list is
bounded by `B` at radius `δ`, then the interleaved list is bounded by `B^m`.  This is the forward
half of the `δ*`-collapse: a radius with a polynomial base list has a polynomial interleaved list. -/
theorem interleaved_poly_of_base_poly [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ}
    (C : Set (ι → F)) (δ : ℝ) {B : ℕ∞} (hB : ListDecodable.Lambda C δ ≤ B) :
    ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤ B ^ m :=
  le_trans (Lambda_interleaved_le_pow C δ) (pow_le_pow_left' hB m)

/-- **Interleaved bound ⟹ base bound (same threshold).** If the interleaved list is bounded by `B`
at radius `δ`, then the base list is bounded by the *same* `B`.  This is the backward half of the
`δ*`-collapse: the interleaved view can only *under*count the base list when measured against a fixed
threshold, so a polynomial interleaved list forces a polynomial base list. -/
theorem base_poly_of_interleaved_poly [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ} [NeZero m]
    (C : Set (ι → F)) (δ : ℝ) {B : ℕ∞}
    (hB : ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤ B) :
    ListDecodable.Lambda C δ ≤ B :=
  le_trans (Lambda_interleaved_ge C δ) hB

/-! ### 3. Finiteness collapse. -/

/-- **Finiteness collapse.** The interleaved list is finite (`< ⊤`) iff the base list is finite.
Interleaving neither creates nor destroys an infinite decoding list at any fixed radius `δ`. -/
theorem interleaved_finite_iff_base_finite [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ}
    [NeZero m] (C : Set (ι → F)) (δ : ℝ) :
    ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ < ⊤ ↔ ListDecodable.Lambda C δ < ⊤ := by
  constructor
  · -- interleaved finite ⟹ base finite, via the (exact) lower bound `Λ C ≤ Λ C^{≡m}`.
    intro h
    exact lt_of_le_of_lt (Lambda_interleaved_ge C δ) h
  · -- base finite ⟹ interleaved finite, via `Λ C^{≡m} ≤ (Λ C)^m` and `x^m < ⊤` when `x < ⊤`.
    intro h
    refine lt_of_le_of_lt (Lambda_interleaved_le_pow C δ) ?_
    -- `(Λ C δ)^m < ⊤` because `Λ C δ < ⊤`.
    exact ENat.pow_lt_top_iff.2 (Or.inl h)

/-! ### 4. The `δ*`-collapse at a polynomial threshold. -/

/-- A radius `δ` is **`B`-good** for a code `D` if its maximised list size is `≤ B`.  This is a
list-size goodness notion only. It is not the repository's MCA threshold `mcaDeltaStar`, and no
theorem here relates the two. -/
def IsGood (D : Set (ι → F)) (δ : ℝ) (B : ℕ∞) : Prop := ListDecodable.Lambda D δ ≤ B

/-- **Budget-changing transfer, forward** (historical name `deltaStar_collapse_forward`). Every
radius that is `B`-good for the base code is `B^m`-good for the interleaved code.  The budget
changes from `B` to `B^m`, so this does not show that `B`-good radii of `C` are `B`-good for
`C^{≡m}`. -/
theorem deltaStar_collapse_forward [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ}
    (C : Set (ι → F)) (δ : ℝ) {B : ℕ∞} (h : IsGood C δ B) :
    IsGood (interleavedCodeSet (κ := Fin m) C) δ (B ^ m) :=
  interleaved_poly_of_base_poly C δ h

/-- **Budget-preserving transfer, backward** (historical name `deltaStar_collapse_backward`). Every
radius that is `B`-good for the interleaved code is `B`-good for the base code, at the *same*
budget `B`.  So the fixed-budget list threshold of `C^{≡m}` is at most that of `C`. Together with
`deltaStar_collapse_forward`, this transfers the *existence of a polynomial list bound* for fixed
`m`. It does **not** give equality of fixed-budget thresholds (binary repetition code of length 3,
`m = 2`, `B = 2`: suprema `1` for `C` and `2/3` for `C^{≡2}`), and it says nothing about the MCA
threshold `mcaDeltaStar`. -/
theorem deltaStar_collapse_backward [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ} [NeZero m]
    (C : Set (ι → F)) (δ : ℝ) {B : ℕ∞}
    (h : IsGood (interleavedCodeSet (κ := Fin m) C) δ B) :
    IsGood C δ B :=
  base_poly_of_interleaved_poly C δ h

/-- **The collapse, packaged as a biconditional bracket.** For fixed `m ≠ 0`:
`Λ(C,δ) ≤ B` implies `Λ(C^{≡m},δ) ≤ B^m`, and `Λ(C^{≡m},δ) ≤ B` implies `Λ(C,δ) ≤ B`.  These two
implications bracket the interleaved list size by the base list size at every radius. For fixed `m`,
a radius admits *some* polynomial list bound for `C` iff it does for `C^{≡m}`. At a fixed budget the
two good-radius suprema can differ, and the MCA threshold `mcaDeltaStar` is not compared. -/
theorem deltaStar_collapse_bracket [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ} [NeZero m]
    (C : Set (ι → F)) (δ : ℝ) (B : ℕ∞) :
    (IsGood C δ B → IsGood (interleavedCodeSet (κ := Fin m) C) δ (B ^ m)) ∧
      (IsGood (interleavedCodeSet (κ := Fin m) C) δ B → IsGood C δ B) :=
  ⟨deltaStar_collapse_forward C δ, deltaStar_collapse_backward C δ⟩

/-! ### 5. The convergent wall is inherited by the interleaved code. -/

/-- **The open gap is present inside the interleaved code.** Any list-size *lower* bound `L ≤ Λ(C,δ)`
for the base code at an interior radius `δ` propagates verbatim to the interleaved code:
`L ≤ Λ(C,δ) ≤ Λ(C^{≡m},δ)`.  In particular the verified interior data points (e.g. the F₇
`6`-element list at `δ = 4/7`, see `ListInteriorDataPointF7`) lift to the interleaved code at the
*same* interior radius.  So the list-recovery reformulation **inherits** the round-1 convergent
wall — it does not provide a route around the `(1-√ρ, 1-ρ)` gap. -/
theorem gap_present_in_interleaved [Finite F] [Nonempty ι] {m : ℕ} [NeZero m]
    (C : Set (ι → F)) (δ : ℝ) {L : ℕ∞} (hL : L ≤ ListDecodable.Lambda C δ) :
    L ≤ ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ := by
  classical
  cases nonempty_fintype F
  exact le_trans hL (Lambda_interleaved_ge C δ)

/-! ## Axiom audit -/

#print axioms Lambda_interleaved_sandwich
#print axioms interleaved_poly_of_base_poly
#print axioms base_poly_of_interleaved_poly
#print axioms interleaved_finite_iff_base_finite
#print axioms deltaStar_collapse_forward
#print axioms deltaStar_collapse_backward
#print axioms deltaStar_collapse_bracket
#print axioms gap_present_in_interleaved

end ArkLib.CodingTheory.Round2ListRecovery
