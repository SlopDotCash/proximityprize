/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowedFoldingBelowJohnson

/-!
# Issue #232 — the POSITIVE windowed transfer (route 4's constructive half, completing the story)

`WindowedFoldingBelowJohnson` proved the windowed-folding route cannot reach the Johnson radius
(the factor-`s` shrinkage `δ ↦ s·δ` puts its ceiling `(1−ρ)/s` strictly below `1−√ρ` at every rate).
This file proves the matching **positive direction** for a fixed code `C`: a window-metric list
bound for codewords of `C` yields a plain list bound for codewords of `C` at the shrunk radius:

* `disagree_card_le` — agreement `≥ t` means at most `n − t` disagreements.
* `windowAgree_count_ge_of_agree` — hence (via `agreeing_windows_ge`) every word with
  `≥ t` plain agreements has `≥ n − s·(n−t)` fully-agreeing windows.
* `windowed_list_transfer` (HEADLINE) — if every set `M ⊆ C` of codewords with `≥ τ` agreeing
  windows has `|M| ≤ B`, and `τ ≤ n − s·(n−t)`, then every set `L ⊆ C` of codewords with plain
  agreement `≥ t` has `|L| ≤ B`.  Both lists carry the membership constraint, so a list bound
  that only controls codewords of `C` is a valid input; no bound on arbitrary ambient words is
  needed.
* `windowed_list_transfer_ambient` — the special case `C = univ` (all words), where the input
  hypothesis quantifies over every set of ambient words.

What is **not** proved here: that the window-metric list for `C` coincides with an ordinary
list for a folded code (the folded code lives over the alphabet `F^s`, and its list counts
folded codewords, not codewords of `C`); that identification is a separate step a user must
supply when instantiating `hfold`.

Together with `WindowedFoldingBelowJohnson`, this describes what the worst-case
agreement-to-window conversion (`agreeing_windows_ge`) gives: plain list bounds for
`δ ≤ (1−ρ_f)/s`.  It does not show that every folding route is limited to that radius;
structured error patterns can leave many more windows agreeing than the worst-case count.
All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset

namespace ArkLib.CodingTheory.WindowedFoldingTransfer

open ArkLib.CodingTheory.WindowedFoldingBelowJohnson

variable {F : Type*} [DecidableEq F] {n s : ℕ}

/-- Agreement `≥ t` bounds the disagreement count by `n − t`. -/
theorem disagree_card_le (c w : Fin n → F) (t : ℕ)
    (h : t ≤ (Finset.univ.filter fun i : Fin n => c i = w i).card) :
    (Finset.univ.filter fun i : Fin n => c i ≠ w i).card ≤ n - t := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => c i = w i)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hconv : (Finset.univ.filter fun i : Fin n => c i ≠ w i)
      = Finset.univ.filter fun i : Fin n => ¬ c i = w i := by
    apply Finset.filter_congr
    intro i _
    simp [ne_eq]
  rw [hconv]
  omega

/-- **Window count from plain agreement:** a word with `≥ t` plain agreements has
`≥ n − s·(n−t)` fully-agreeing windows (monotone composition with `agreeing_windows_ge`). -/
theorem windowAgree_count_ge_of_agree (c w : Fin n → F) (hs : s ≤ n) (t : ℕ)
    (h : t ≤ (Finset.univ.filter fun i : Fin n => c i = w i).card) :
    n - s * (n - t) ≤ (Finset.univ.filter fun i : Fin n => windowAgrees c w s hs i).card := by
  classical
  set e := (Finset.univ.filter fun i : Fin n => c i ≠ w i).card with he
  have hge := agreeing_windows_ge c w hs e he.symm
  have hle : e ≤ n - t := disagree_card_le c w t h
  have hmul : s * e ≤ s * (n - t) := Nat.mul_le_mul_left s hle
  omega

/-- **THE POSITIVE WINDOWED TRANSFER (route 4's constructive half), code-relative.**
Fix a code `C`.  If window-metric lists of codewords are bounded — every set `M ⊆ C` of
codewords, each with `≥ τ` fully-agreeing windows against `w`, has `|M| ≤ B` — then every
plain list `L ⊆ C` of codewords at plain agreement `≥ t` is bounded by the same `B`, provided
the shrunk threshold suffices: `τ ≤ n − s·(n−t)`.

The input `hfold` only constrains codewords of `C`, so a code-specific window-metric list bound
is a legitimate instantiation.  (With `t = (1−δ)n` and `τ = ρ_f·n` the radius condition reads
`δ ≤ (1−ρ_f)/s`; see `WindowedFoldingBelowJohnson` for how this worst-case conversion compares
with the Johnson radius.  Identifying the window-metric list of `C` with a list of an actual
folded code is not done here.) -/
theorem windowed_list_transfer (C : Set (Fin n → F)) (w : Fin n → F) (hs : s ≤ n)
    (t τ B : ℕ) (hτ : τ ≤ n - s * (n - t))
    (hfold : ∀ M : Finset (Fin n → F), (∀ c ∈ M, c ∈ C) →
      (∀ c ∈ M, τ ≤ (Finset.univ.filter fun i : Fin n => windowAgrees c w s hs i).card) →
      M.card ≤ B)
    (L : Finset (Fin n → F)) (hLC : ∀ c ∈ L, c ∈ C)
    (hagree : ∀ c ∈ L, t ≤ (Finset.univ.filter fun i : Fin n => c i = w i).card) :
    L.card ≤ B := by
  apply hfold L hLC
  intro c hc
  calc τ ≤ n - s * (n - t) := hτ
    _ ≤ (Finset.univ.filter fun i : Fin n => windowAgrees c w s hs i).card :=
        windowAgree_count_ge_of_agree c w hs t (hagree c hc)

/-- **Ambient special case** (`C = univ`): a window-metric bound on every set of ambient words
transfers to every plain list of ambient words.  This input is much stronger than a list bound
for a particular code, which only controls codewords. -/
theorem windowed_list_transfer_ambient (w : Fin n → F) (hs : s ≤ n) (t τ B : ℕ)
    (hτ : τ ≤ n - s * (n - t))
    (hfold : ∀ M : Finset (Fin n → F),
      (∀ c ∈ M, τ ≤ (Finset.univ.filter fun i : Fin n => windowAgrees c w s hs i).card) →
      M.card ≤ B)
    (L : Finset (Fin n → F))
    (hagree : ∀ c ∈ L, t ≤ (Finset.univ.filter fun i : Fin n => c i = w i).card) :
    L.card ≤ B :=
  windowed_list_transfer Set.univ w hs t τ B hτ (fun M _ hM => hfold M hM) L
    (fun _ _ => Set.mem_univ _) hagree

/-- The binary repetition code of length `4`: the two constant words. -/
def repCode4 : Set (Fin 4 → ZMod 2) := {c | ∃ a : ZMod 2, c = fun _ => a}

/-- **Code-specific non-vacuity** (`ZMod 2`, `n = 4`, `s = 2`, `t = 4`, `τ = 4`, `w = 0`):
for the repetition code, the only codeword with all `4` windows agreeing with `0` is `0` itself,
so the code-specific window-metric list bound is `B = 1` (far below the ambient count `16`), and
the transfer bounds every plain list of repetition codewords at full agreement by `1`. -/
theorem nonvacuous_transfer :
    ∀ L : Finset (Fin 4 → ZMod 2), (∀ c ∈ L, c ∈ repCode4) →
      (∀ c ∈ L, 4 ≤ (Finset.univ.filter fun i : Fin 4 => c i = (fun _ => 0) i).card) →
      L.card ≤ 1 := by
  intro L hLC hagree
  apply windowed_list_transfer (s := 2) repCode4 (fun _ => 0) (by norm_num) 4 4 1
    (by norm_num) _ L hLC hagree
  intro M hMC hMw
  have hzero : ∀ c ∈ M, c = fun _ => 0 := by
    intro c hc
    obtain ⟨a, rfl⟩ := hMC c hc
    have hw := hMw _ hc
    revert hw
    fin_cases a
    · intro _; rfl
    · intro hw
      exfalso
      revert hw
      decide
  exact Finset.card_le_one.mpr fun a ha b hb => (hzero a ha).trans (hzero b hb).symm

end ArkLib.CodingTheory.WindowedFoldingTransfer

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.disagree_card_le
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.windowAgree_count_ge_of_agree
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.windowed_list_transfer
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.windowed_list_transfer_ambient
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.nonvacuous_transfer
