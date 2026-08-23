/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.StructuredUncertaintySharpFloor

/-!
# list-at-extremal-k2 : the `k = 2` list at the binomial-extremal word is EXACTLY `2` (#407/#444)

`UncertaintyTwoPowerExtremal.lean` records the single-line / list-decoding SEPARATION: the
subgroup-binomial extremal achieves single-line agreement `s* = n/2` (`≫ √(kn)`), but the prize
`δ*` is a LIST radius, and the in-tree Prop `SingleLineNotList` discharges the conflation *only by
taking* `listAtExtremal ≤ 2` as a machine-checked numeric HYPOTHESIS (`/tmp/up_extremal.py`,
"`list = 2` at `δ = 0.5`").

This file UPGRADES that numeric hypothesis to a PROVEN theorem for the `k = 2` (affine / degree-`<2`)
case — the actual codeword degree of the in-tree binomial extremal. It is a clean, axiom-clean,
NON-MOMENT structural fact: injectivity of nonconstant affine maps on the cyclic group `μ_n`.

## The setup (the REAL object, p-independent — probe `/tmp/probe_listatextremal.py`,
`/tmp/probe_list_k2_detail.py`)

`μ_n = ⟨ζ⟩`, `ζ` a primitive `2^μ`-th root of unity, `n = 2^μ`. The binomial-extremal WORD is the
value function `w(ζ^j) = (ζ^j)^{n/2} = (-1)^j` (since `ζ^{n/2} = -1`, reusing
`StructuredUncertainty.primRoot_pow_half_eq_neg_one`). It takes EXACTLY the two values `{+1, -1}`.
A `k = 2` codeword is an affine function `c(x) = α + β·x`.

* **The two constants reach `n/2`** (`const_one_agreement_card`, `const_negOne_agreement_card`):
  `c ≡ +1` agrees with `w` on the even powers `{ζ^j : j even}` (size `n/2`); `c ≡ -1` agrees on the
  odd powers (size `n/2`).  (Counts via the in-tree `StructuredUncertainty.card_odd_range_two_mul`.)
* **Every NONCONSTANT affine codeword agrees on `≤ 2` points** (`nonconstant_affine_agreement_le_two`):
  `x ↦ α + β·x` with `β ≠ 0` is INJECTIVE on `F`, hence on the distinct points `ζ^j`
  (`j < 2^μ`, primitive root); the word `w` takes only `2` values, so the agreement set (where `c`
  equals one of `≤ 2` word-values) has size `≤ 2`. For `n ≥ 6` this is `< n/2`, so no nonconstant
  codeword joins the list.

## Honest scope (rule-3 / rule-6)

This is the `k = 2` case ONLY. The list is NOT uniformly `≤ 2` for `k ≥ 3` (machine-checked:
`k = 3, n = 8` gives list `= 6`, dropping to `2` only at `n = 16` — `/tmp/probe_listatextremal.py`),
so this does NOT generalize to a `k`-uniform list bound and is NOT a CORE/prize closure. It discharges
exactly the `k = 2` hypothesis the in-tree separation rested on, by a real injectivity argument.
Thinness enters via `ζ^{n/2} = -1` (the `2`-power structure giving the `±1`-valued word). CORE
(`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

All results `sorry`-free; intended audit `[propext, Classical.choice, Quot.sound]`. Issues #407/#444.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.ListAtBinomialExtremalTwo

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The `±1`-valued word `w(ζ^j) = (-1)^j`. -/

/-- The **word value** at `ζ^j`: `w(ζ^j) = (ζ^j)^{n/2} = (-1)^j` (the binomial-extremal word
`x ↦ x^{n/2}`), which takes only the two values `±1`. -/
def wordVal (μ : ℕ) (ζ : F) (j : ℕ) : F := (ζ ^ j) ^ (2 ^ (μ - 1))

/-- `wordVal = (-1)^j`, using the in-tree half-power identity `ζ^{2^{μ-1}} = -1`. -/
theorem wordVal_eq_neg_one_pow {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (j : ℕ) :
    wordVal μ ζ j = (-1 : F) ^ j := by
  unfold wordVal
  rw [← pow_mul, mul_comm, pow_mul,
    ProximityGap.StructuredUncertainty.primRoot_pow_half_eq_neg_one hμ hζ]

/-- The word takes value `+1` on EVEN `j`. -/
theorem wordVal_even {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    {j : ℕ} (hj : Even j) : wordVal μ ζ j = 1 := by
  rw [wordVal_eq_neg_one_pow hμ hζ, hj.neg_one_pow]

/-- The word takes value `-1` on ODD `j`. -/
theorem wordVal_odd {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    {j : ℕ} (hj : Odd j) : wordVal μ ζ j = -1 := by
  rw [wordVal_eq_neg_one_pow hμ hζ, hj.neg_one_pow]

/-! ### The two constant codewords each reach `n/2` agreement. -/

/-- `2^μ = 2 * 2^{μ-1}` for `μ ≥ 1` (to reuse the `range (2 * m)` counting lemmas). -/
theorem two_pow_eq_two_mul {μ : ℕ} (hμ : 1 ≤ μ) : 2 ^ μ = 2 * 2 ^ (μ - 1) := by
  rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩
  subst ht; rw [show 1 + t = t + 1 from by omega, Nat.add_sub_cancel, pow_succ]; ring

/-- **`c ≡ -1` agrees with the word on exactly `n/2` points** (the ODD powers).  Its agreement set
is `{j ∈ range (2^μ) | wordVal = -1} = {j | j odd}`, of size `2^{μ-1} = n/2`. -/
theorem const_negOne_agreement_card {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    ((range (2 ^ μ)).filter (fun j => wordVal μ ζ j = -1)).card = 2 ^ (μ - 1) := by
  have hne : (-1 : F) ≠ 1 := ProximityGap.StructuredUncertainty.neg_one_ne_one_of_primRoot hμ hζ
  have hcongr :
      ((range (2 ^ μ)).filter (fun j => wordVal μ ζ j = -1))
        = ((range (2 ^ μ)).filter (fun j => Odd j)) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · intro h
      by_contra hodd
      rw [Nat.not_odd_iff_even] at hodd
      rw [wordVal_even hμ hζ hodd] at h
      exact hne h.symm
    · intro hodd; exact wordVal_odd hμ hζ hodd
  rw [hcongr, two_pow_eq_two_mul hμ]
  exact ProximityGap.StructuredUncertainty.card_odd_range_two_mul _

/-- `#{ j ∈ range (2^μ) | j even } = 2^{μ-1}` (the count complementary to the odd one). -/
theorem card_even_range {μ : ℕ} (hμ : 1 ≤ μ) :
    ((range (2 ^ μ)).filter (fun j => Even j)).card = 2 ^ (μ - 1) := by
  classical
  -- total = even-count + (¬even)-count, and ¬even = odd
  have htot := Finset.filter_card_add_filter_neg_card_eq_card
    (s := range (2 ^ μ)) (p := fun j => Even j)
  rw [Finset.card_range] at htot
  have hodd_eq :
      ((range (2 ^ μ)).filter (fun j => ¬ Even j)).card
        = ((range (2 ^ μ)).filter (fun j => Odd j)).card := by
    apply Finset.card_nbij' id id <;> intro j hj <;>
      simp_all [Finset.mem_filter, Nat.not_even_iff_odd]
  rw [hodd_eq] at htot
  have hodd :
      ((range (2 ^ μ)).filter (fun j => Odd j)).card = 2 ^ (μ - 1) := by
    rw [two_pow_eq_two_mul hμ]
    exact ProximityGap.StructuredUncertainty.card_odd_range_two_mul _
  rw [hodd] at htot
  have h2 : 2 ^ μ = 2 ^ (μ - 1) + 2 ^ (μ - 1) := by
    rw [two_pow_eq_two_mul hμ]; ring
  omega

/-- **`c ≡ +1` agrees with the word on exactly `n/2` points** (the EVEN powers).  Its agreement set
is `{j ∈ range (2^μ) | wordVal = 1} = {j | j even}`, of size `2^{μ-1} = n/2`. -/
theorem const_one_agreement_card {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    ((range (2 ^ μ)).filter (fun j => wordVal μ ζ j = 1)).card = 2 ^ (μ - 1) := by
  have hne : (-1 : F) ≠ 1 := ProximityGap.StructuredUncertainty.neg_one_ne_one_of_primRoot hμ hζ
  have hcongr :
      ((range (2 ^ μ)).filter (fun j => wordVal μ ζ j = 1))
        = ((range (2 ^ μ)).filter (fun j => Even j)) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · intro h
      by_contra heven
      rw [Nat.not_even_iff_odd] at heven
      rw [wordVal_odd hμ hζ heven] at h
      exact hne h
    · intro heven; exact wordVal_even hμ hζ heven
  rw [hcongr, card_even_range hμ]

/-! ### The injectivity bound: a NONCONSTANT affine codeword agrees on `≤ 2` points. -/

/-- A nonconstant affine map `x ↦ α + β·x` (`β ≠ 0`) is injective on `F`. -/
theorem affine_injective {α β : F} (hβ : β ≠ 0) :
    Function.Injective (fun x : F => α + β * x) := by
  intro x y hxy
  simp only at hxy
  have h : β * x = β * y := by
    have := add_left_cancel hxy
    exact this
  exact mul_left_cancel₀ hβ h

/-- **The key agreement bound.**  Let `c(x) = α + β·x` be a NONCONSTANT (`β ≠ 0`) affine codeword.
The set of `j ∈ range (2^μ)` at which `c` agrees with the word — i.e. `c(ζ^j) ∈ {+1, -1}` (the two
word values) — has cardinality `≤ 2`.  Reason: `c` is injective on `F`, the points `ζ^j` are distinct
for `j ∈ range (2^μ)` (primitive root), so `j ↦ c(ζ^j)` is injective on the agreement set, whose image
lands in the `2`-element set `{1, -1}`. -/
theorem nonconstant_affine_agreement_le_two {μ : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {α β : F} (hβ : β ≠ 0) :
    ((range (2 ^ μ)).filter
        (fun j => α + β * (ζ ^ j) = 1 ∨ α + β * (ζ ^ j) = -1)).card ≤ 2 := by
  classical
  set S := (range (2 ^ μ)).filter
      (fun j => α + β * (ζ ^ j) = 1 ∨ α + β * (ζ ^ j) = -1) with hS
  have hinj : Set.InjOn (fun j => α + β * (ζ ^ j)) (S : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    have hζeq : ζ ^ a = ζ ^ b := affine_injective (α := α) (β := β) hβ hab
    have haR : a < 2 ^ μ := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbR : b < 2 ^ μ := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    exact hζ.pow_inj haR hbR hζeq
  have himg : S.image (fun j => α + β * (ζ ^ j)) ⊆ ({1, -1} : Finset F) := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hjS, rfl⟩ := hv
    rcases (Finset.mem_filter.mp hjS).2 with h | h
    · simp [h]
    · simp [h]
  have hpair : ({1, -1} : Finset F).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  calc S.card = (S.image (fun j => α + β * (ζ ^ j))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ({1, -1} : Finset F).card := Finset.card_le_card himg
    _ ≤ 2 := hpair

/-- **The `k = 2` list at the binomial-extremal word is `≤ 2`, with a strict gap to `n/2`.**
For `μ ≥ 3` (`n = 2^μ ≥ 8`): a nonconstant affine codeword agrees on `≤ 2 < 2^{μ-1} = n/2` points,
so it CANNOT be in the radius-`n/2` list, while the two constants `±1` each agree on exactly `n/2`.
Hence the deg-`<2` codewords reaching `n/2` agreement are exactly the `2` constants — discharging
the `listAtExtremal ≤ 2` numeric hypothesis of `SingleLineNotList` for `k = 2`. -/
theorem nonconstant_below_half {μ : ℕ} (hμ : 3 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {α β : F} (hβ : β ≠ 0) :
    ((range (2 ^ μ)).filter
        (fun j => α + β * (ζ ^ j) = 1 ∨ α + β * (ζ ^ j) = -1)).card < 2 ^ (μ - 1) := by
  refine lt_of_le_of_lt (nonconstant_affine_agreement_le_two hζ hβ) ?_
  have : (2 : ℕ) ^ 2 ≤ 2 ^ (μ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa using lt_of_lt_of_le (by norm_num : (2 : ℕ) < 4) (by simpa using this)

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only — NO sorryAx)
#print axioms wordVal_eq_neg_one_pow
#print axioms wordVal_even
#print axioms wordVal_odd
#print axioms const_one_agreement_card
#print axioms const_negOne_agreement_card
#print axioms affine_injective
#print axioms nonconstant_affine_agreement_le_two
#print axioms nonconstant_below_half

end ProximityGap.ListAtBinomialExtremalTwo
