/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-! # An odd antipodally isolated class in the half-rate four-fiber patterns

The first four labels denote the private sets. The next five denote the marked
sites a, b, c, d, f. The last label collects marks with zero divisor signature.
Each line records the divisors of the protected ratios at the indicated private
color. -/

namespace ProximityGap.HalfFourFiberParity

abbrev Shape := Fin 3
abbrev Label := Fin 10
abbrev Head := Fin 4
abbrev Heavy := Head → Bool

private def flag (b : Bool) : ℤ := if b then 1 else 0

/-- The two divisor-coordinate signatures belonging to a three-center color.
Shapes are complete, five double sites, and one triple site in that order. -/
def signature (s : Shape) (h : Head) (i : Label) : ℤ × ℤ :=
  let z := flag (i == 0 || (s != 2 && i == 5))
  let p := flag (i == 1 || i == 7)
  let u := flag (i == 2 || (s == 0 && i == 8))
  let z' := flag (i == 0 || (s != 2 && i == 4))
  let p' := flag (i == 1 || i == 6)
  let u' := flag (i == 3 || (s == 0 && i == 8))
  match h.val with
  | 0 => (u - p, u' - p')
  | 1 => (z - u, z' - u')
  | 2 => (z - p, 0)
  | _ => (z' - p', 0)

/-- The three bipartitions into two pairs of heavy private colors. -/
def pair (split : Fin 3) (side : Bool) : Head × Head :=
  match split.val, side with
  | 0, false => (0, 1)
  | 0, true => (2, 3)
  | 1, false => (0, 2)
  | 1, true => (1, 3)
  | _, false => (0, 3)
  | _, true => (1, 2)

/-- A single odd-size class isolated on both halves of a complementary split. -/
def isolated (s : Shape) (split : Fin 3) : Label :=
  if s = 0 then (if split = 0 then 4 else 8) else
  if s = 1 then (if split = 0 then 4 else 2) else 0

/-- Both heavy colors in either half of the split distinguish the odd class. -/
theorem signature_isolates : ∀ (s : Shape) (split : Fin 3) (side : Bool) (i : Label),
    signature s (pair split side).1 i = signature s (pair split side).1 (isolated s split) →
    signature s (pair split side).2 i = signature s (pair split side).2 (isolated s split) →
    i = isolated s split := by decide

/-- Two colors in each set and coverage of all four imply a complementary split. -/
theorem complementary_pairs : ∀ (e o : Heavy),
    (∃ i j, i ≠ j ∧ e i = true ∧ e j = true) →
    (∃ i j, i ≠ j ∧ o i = true ∧ o j = true) →
    (∀ i, e i = true ∨ o i = true) →
    ∃ (s : Fin 3) (side : Bool),
      e (pair s side).1 = true ∧ e (pair s side).2 = true ∧
      o (pair s (!side)).1 = true ∧ o (pair s (!side)).2 = true := by decide

/-- Each parity class has at least two three-center colors once the grid has 64 sites. -/
theorem two_heavy_of_mass (h threshold : ℕ) (v : Head → ℕ) (hh : 3 * threshold + 4 < h)
    (hv : ∀ i, v i ≤ h - 1) (hm : 2 * h ≤ v 0 + v 1 + v 2 + v 3 + 8) :
    ∃ i j, i ≠ j ∧ threshold ≤ v i ∧ threshold ≤ v j := by
  by_contra! hn
  have h01 := hn 0 1 (by decide)
  have h02 := hn 0 2 (by decide)
  have h03 := hn 0 3 (by decide)
  have h12 := hn 1 2 (by decide)
  have h13 := hn 1 3 (by decide)
  have h23 := hn 2 3 (by decide)
  have v0 := hv 0
  have v1 := hv 1
  have v2 := hv 2
  have v3 := hv 3
  omega

/-- When a private class has at least h−2 sites it is heavy on some parity. -/
theorem heavy_somewhere (h e o threshold : ℕ) (hh : 2 * threshold < h) (hv : h - 2 ≤ e + o) :
    threshold ≤ e ∨ threshold ≤ o := by omega

/-- A coordinate system pairs opposite sites by the second Boolean argument. -/
def population {ι : Type*} [Fintype ι] (color : ι → Bool → Label) (w : Label) : ℕ :=
  ∑ i, ((if color i false = w then 1 else 0) + (if color i true = w then 1 else 0))

/-- If either parity's heavy pair protects its signatures, the isolated class
has even cardinality across all antipodal pairs. -/
theorem even_isolated_population {ι : Type*} [Fintype ι] (s : Shape) (split : Fin 3)
    (color : ι → Bool → Label) (side : ι → Bool)
    (h₁ : ∀ i, signature s (pair split (side i)).1 (color i false) =
      signature s (pair split (side i)).1 (color i true))
    (h₂ : ∀ i, signature s (pair split (side i)).2 (color i false) =
      signature s (pair split (side i)).2 (color i true)) :
    Even (population color (isolated s split)) := by
  let w := isolated s split
  have eqv (i : ι) : color i false = w ↔ color i true = w := by
    constructor
    · intro hi
      exact signature_isolates s split (side i) _ ((h₁ i).symm.trans (congrArg _ hi))
        ((h₂ i).symm.trans (congrArg _ hi))
    · intro hi
      exact signature_isolates s split (side i) _ ((h₁ i).trans (congrArg _ hi))
        ((h₂ i).trans (congrArg _ hi))
  refine ⟨∑ i, if color i true = w then 1 else 0, ?_⟩
  unfold population
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (if color i false = w then 1 else 0) + (if color i true = w then 1 else 0) = _
  by_cases h : color i false = w
  · simp [h, (eqv i).mp h]
  · simp [h, mt (eqv i).mpr h]

/-- The change of population parity is impossible when the private counts and
marked singletons give the prescribed odd populations. The Boolean `source`
selects the opposite exponent parity which protects the given antipodal pair. -/
theorem no_protected_list {ι : Type*} [Fintype ι] (s : Shape) (h threshold : ℕ)
    (counts : Bool → Head → ℕ) (color : ι → Bool → Label) (source : ι → Bool)
    (hh : 3 * threshold + 4 < h) (hmax : ∀ t i, counts t i ≤ h - 1)
    (hmass : ∀ t, 2 * h ≤ counts t 0 + counts t 1 + counts t 2 + counts t 3 + 8)
    (hcover : ∀ i, h - 2 ≤ counts false i + counts true i)
    (hprotect : ∀ i j, threshold ≤ counts (source i) j →
      signature s j (color i false) = signature s j (color i true))
    (hodd : ∀ split, Odd (population color (isolated s split))) : False := by
  let heavy (t : Bool) (j : Head) := decide (threshold ≤ counts t j)
  have two (t : Bool) : ∃ i j, i ≠ j ∧ heavy t i = true ∧ heavy t j = true := by
    simpa [heavy] using two_heavy_of_mass h threshold (counts t) hh (hmax t) (hmass t)
  have both (i : Head) : heavy false i = true ∨ heavy true i = true := by
    simpa [heavy] using
      heavy_somewhere h (counts false i) (counts true i) threshold (by omega) (hcover i)
  obtain ⟨split, side, h₁, h₂, h₃, h₄⟩ := complementary_pairs _ _ (two false) (two true) both
  let sideAt (i : ι) := if source i then !side else side
  have hit (i : ι) : heavy (source i) (pair split (sideAt i)).1 = true ∧
      heavy (source i) (pair split (sideAt i)).2 = true := by
    cases hi : source i <;> simp only [sideAt, hi, Bool.false_eq_true, ite_false, ite_true]
    · exact ⟨h₁, h₂⟩
    · exact ⟨h₃, h₄⟩
  have he := even_isolated_population s split color sideAt
    (fun i => hprotect i _ (of_decide_eq_true (hit i).1))
    (fun i => hprotect i _ (of_decide_eq_true (hit i).2))
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hodd split
  omega

/-- A first-prime candidate has an antipodal change of a protected signature on
a center class with at least 89,478,483 sites on one exponent parity. -/
theorem production_unprotected {ι : Type*} [Fintype ι] (s : Shape)
    (counts : Bool → Head → ℕ) (color : ι → Bool → Label) (source : ι → Bool)
    (hmax : ∀ t i, counts t i ≤ 268435456 - 1)
    (hmass : ∀ t, 536870912 ≤ counts t 0 + counts t 1 + counts t 2 + counts t 3 + 8)
    (hcover : ∀ i, 268435456 - 2 ≤ counts false i + counts true i)
    (hodd : ∀ split, Odd (population color (isolated s split))) :
    ∃ i j, 89478483 ≤ counts (source i) j ∧
      signature s j (color i false) ≠ signature s j (color i true) := by
  by_contra! hn
  exact no_protected_list s 268435456 89478483 counts color source (by decide)
    hmax hmass hcover hn hodd

/-- At most two centers per complex value force at least 44,739,242 different
values in the single named-field residue class. -/
theorem production_distinct_values {α β : Type*} [DecidableEq β]
    (sites : Finset α) (f : α → β) (h : 89478483 ≤ sites.card)
    (hf : ∀ y ∈ sites.image f, (sites.filter fun x => f x = y).card ≤ 2) :
    44739242 ≤ (sites.image f).card := by
  by_contra! cap
  have ht : (sites.image f).card * 2 < sites.card := by omega
  obtain ⟨y, hy, hbig⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun a ha => Finset.mem_image_of_mem f ha) ht
  exact (Nat.not_lt_of_ge (hf y hy)) hbig

end ProximityGap.HalfFourFiberParity
