/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Issue #232 — the threshold `δ*` is WELL-DEFINED (the prize statement's presupposition)

The Grand Challenges ask to "determine the **largest** `δ*_C` such that `|Λ(C, δ*_C)| ≤ ε*·|F|`…
*assuming `|F|` is large enough that such a `δ*_C` exists*."  This file removes the presupposition:
for **every** finite code `C ⊆ Fⁿ` and **every** list budget `B ≥ 1`, the agreement threshold

  `a*(C, B) = min { a : maxList(C, a) ≤ B }`

**exists and is unique**, where `maxList(C, a) = max_w #{c ∈ C : agree(c, w) ≥ a}` is the worst-case
list size at agreement `a` (relative radius `δ = 1 − a/n`).  The three ingredients:

* `maxList_antitone` — the worst-case list size is antitone in the agreement demand (each word's
  list shrinks, hence so does the max).
* `maxList_top_le_one` — at full agreement `a = n` the list is at most a single codeword
  (`agree(c, w) ≥ n` forces `c = w` pointwise) — for **any** code, no distance assumption.
* `threshold_exists_unique` — hence `{a : maxList ≤ B}` is upward-closed, nonempty (it contains
  `n` whenever `B ≥ 1`), and has a unique minimum: the threshold the prize asks to determine.

So `δ*_C = 1 − a*(C,B)/n` is a well-defined object for every prize-admissible configuration; what
is open is its **value** in the gap interior, not its existence.  All results are `sorry`-free and
axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset

namespace ArkLib.CodingTheory.ListThresholdWellDefined

variable {n : ℕ} {F : Type*} [DecidableEq F] [Fintype F]

/-- The agreement count of a codeword `c` with a received word `w`. -/
def agree (c w : Fin n → F) : ℕ :=
  (Finset.univ.filter fun i : Fin n => c i = w i).card

/-- The worst-case list size of the code `C` at agreement demand `a`:
`maxList(C, a) = max_w #{c ∈ C : agree(c, w) ≥ a}`. -/
def maxList (C : Finset (Fin n → F)) (a : ℕ) : ℕ :=
  Finset.sup Finset.univ fun w : Fin n → F => (C.filter fun c => a ≤ agree c w).card

/-- **Antitonicity:** demanding more agreement can only shrink the worst-case list. -/
theorem maxList_antitone (C : Finset (Fin n → F)) : Antitone (maxList C) := by
  intro a a' haa'
  apply Finset.sup_le
  intro w _
  calc (C.filter fun c => a' ≤ agree c w).card
      ≤ (C.filter fun c => a ≤ agree c w).card := by
        apply Finset.card_le_card
        intro c hc
        rw [Finset.mem_filter] at hc ⊢
        exact ⟨hc.1, le_trans haa' hc.2⟩
    _ ≤ maxList C a :=
        Finset.le_sup (f := fun w => (C.filter fun c => a ≤ agree c w).card)
          (Finset.mem_univ w)

/-- **Full agreement pins the codeword:** `agree(c, w) ≥ n` forces `c = w`. -/
theorem eq_of_agree_ge (c w : Fin n → F) (h : n ≤ agree c w) : c = w := by
  have hcard : (Finset.univ.filter fun i : Fin n => c i = w i).card
      = (Finset.univ : Finset (Fin n)).card := by
    have h1 : (Finset.univ.filter fun i : Fin n => c i = w i).card ≤ n := by
      calc (Finset.univ.filter fun i : Fin n => c i = w i).card
          ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_univ, Fintype.card_fin]
    exact le_antisymm h1 h
  have hfeq : (Finset.univ.filter fun i : Fin n => c i = w i) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hcard.symm)
  funext i
  have hi : i ∈ Finset.univ.filter fun i : Fin n => c i = w i := by
    rw [hfeq]; exact Finset.mem_univ i
  exact (Finset.mem_filter.mp hi).2

/-- **The top is trivial for ANY code:** at full agreement `a = n` the worst-case list has at most
one element (the word itself, if it is a codeword) — no distance assumption needed. -/
theorem maxList_top_le_one (C : Finset (Fin n → F)) : maxList C n ≤ 1 := by
  apply Finset.sup_le
  intro w _
  apply Finset.card_le_one.mpr
  intro c₁ h₁ c₂ h₂
  rw [Finset.mem_filter] at h₁ h₂
  rw [eq_of_agree_ge c₁ w h₁.2, eq_of_agree_ge c₂ w h₂.2]

/-- **THE THRESHOLD EXISTS AND IS UNIQUE (the prize's presupposition, discharged).**
For every finite code `C` and every list budget `B ≥ 1`, there is a unique minimal agreement
threshold `a*` with `maxList(C, a*) ≤ B`; moreover everything above it also satisfies the budget
(`∀ a ≥ a*`), and everything below strictly violates it (`∀ a < a*, B < maxList(C, a)`).
The prize's `δ*_C` is `1 − a*/n`: a well-defined object whose *value* is the open question. -/
theorem threshold_exists_unique (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) :
    ∃! a : ℕ, maxList C a ≤ B ∧ ∀ a' < a, B < maxList C a' := by
  have hne : maxList C n ≤ B := le_trans (maxList_top_le_one C) hB
  have hex : ∃ a, maxList C a ≤ B := ⟨n, hne⟩
  classical
  set a₀ := Nat.find hex with ha₀
  refine ⟨a₀, ⟨Nat.find_spec hex, ?_⟩, ?_⟩
  · intro a' ha'
    have := Nat.find_min hex (by omega : a' < a₀)
    omega
  · rintro a ⟨hle, hmin⟩
    by_contra hne'
    rcases Nat.lt_or_ge a a₀ with hlt | hge
    · have := Nat.find_min hex hlt
      omega
    · have hgt : a₀ < a := by omega
      have h1 := hmin a₀ hgt
      have h2 := Nat.find_spec hex
      rw [← ha₀] at h2
      omega

/-- **Monotone consequence:** above the threshold the budget holds everywhere (the threshold is a
genuine crossing point, not an isolated dip) — from antitonicity. -/
theorem budget_holds_above (C : Finset (Fin n → F)) (B a a' : ℕ)
    (h : maxList C a ≤ B) (haa' : a ≤ a') : maxList C a' ≤ B :=
  le_trans (maxList_antitone C haa') h

/-- **Non-vacuity** (`ZMod 3`, `n = 2`, the full code, `B = 1`): the threshold machinery is genuine —
`maxList` at `a = 2` is `1` (≤ B) while at `a = 0` it is `9 > 1`, so the unique threshold lies in
`{1, 2}` and the existence theorem applies with real content. -/
theorem nonvacuous_zmod3 :
    maxList (Finset.univ : Finset (Fin 2 → ZMod 3)) 2 ≤ 1 ∧
    1 < maxList (Finset.univ : Finset (Fin 2 → ZMod 3)) 0 := by
  constructor
  · exact maxList_top_le_one _
  · have h9 : ((Finset.univ : Finset (Fin 2 → ZMod 3)).filter
        fun c => 0 ≤ agree c (fun _ => 0)).card = 9 := by
      rw [Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _), Finset.card_univ,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num
    have hle : ((Finset.univ : Finset (Fin 2 → ZMod 3)).filter
        fun c => 0 ≤ agree c (fun _ => 0)).card
        ≤ maxList (Finset.univ : Finset (Fin 2 → ZMod 3)) 0 :=
      Finset.le_sup (f := fun w => ((Finset.univ : Finset (Fin 2 → ZMod 3)).filter
        fun c => 0 ≤ agree c w).card) (Finset.mem_univ _)
    omega


/-! ## `δ*` as a first-class object: `aStar`, with the crossing characterizations.

`aStar C B hB` is THE threshold the prize asks to determine (in agreement form;
`δ* = 1 − aStar/n`).  The two iffs below are the **bracket API**: any verified list bound
`maxList C a₀ ≤ B` pins `aStar ≤ a₀`, and any verified violation `B < maxList C a₁` pins
`a₁ < aStar`. -/

/-- The budget set is nonempty (it contains `n`). -/
theorem maxList_budget_ex (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) :
    ∃ a, maxList C a ≤ B :=
  ⟨n, le_trans (maxList_top_le_one C) hB⟩

/-- **The threshold, as a named object:** the minimal agreement demand meeting the budget. -/
noncomputable def aStar (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) : ℕ :=
  Nat.find (maxList_budget_ex C B hB)

/-- The threshold meets the budget. -/
theorem aStar_spec (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) :
    maxList C (aStar C B hB) ≤ B :=
  Nat.find_spec (maxList_budget_ex C B hB)

/-- **Crossing characterization, upper form:** `aStar ≤ a ↔ maxList C a ≤ B`.
Any verified list bound at agreement `a` pins the threshold from above. -/
theorem aStar_le_iff (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) (a : ℕ) :
    aStar C B hB ≤ a ↔ maxList C a ≤ B := by
  constructor
  · intro h
    exact budget_holds_above C B _ a (aStar_spec C B hB) h
  · intro h
    unfold aStar
    exact Nat.find_le h

/-- **Crossing characterization, lower form:** `a < aStar ↔ B < maxList C a`.
Any verified budget violation at agreement `a` pins the threshold strictly from below. -/
theorem lt_aStar_iff (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) (a : ℕ) :
    a < aStar C B hB ↔ B < maxList C a := by
  rw [← not_le, ← not_le, ← aStar_le_iff C B hB a]

/-- **The bracket combinator:** a list bound at `a₁` and a violation at `a₀` confine the
threshold to the half-open window `(a₀, a₁]` — the form in which all in-tree two-sided results
(prize-scale Johnson instance above, averaging violation below) translate into statements about
the prize's `δ*` itself. -/
theorem aStar_mem_window (C : Finset (Fin n → F)) (B : ℕ) (hB : 1 ≤ B) {a₀ a₁ : ℕ}
    (hupper : maxList C a₁ ≤ B) (hlower : B < maxList C a₀) :
    a₀ < aStar C B hB ∧ aStar C B hB ≤ a₁ :=
  ⟨(lt_aStar_iff C B hB a₀).mpr hlower, (aStar_le_iff C B hB a₁).mpr hupper⟩

end ArkLib.CodingTheory.ListThresholdWellDefined

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.maxList_antitone
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.maxList_top_le_one
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.threshold_exists_unique
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.budget_holds_above
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.nonvacuous_zmod3
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.aStar_le_iff
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.lt_aStar_iff
#print axioms ArkLib.CodingTheory.ListThresholdWellDefined.aStar_mem_window
