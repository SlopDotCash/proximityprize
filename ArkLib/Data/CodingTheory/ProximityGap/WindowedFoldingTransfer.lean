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
This file proves the matching **positive direction**: the transfer DOES work below that ceiling —
any list bound in the folded (window) metric yields a plain list bound at the shrunk radius:

* `disagree_card_le` — agreement `≥ t` means at most `n − t` disagreements.
* `windowAgree_count_ge_of_agree` — hence (via `agreeing_windows_ge`) every plain codeword with
  `≥ t` agreements has `≥ n − s·(n−t)` fully-agreeing windows.
* `windowed_list_transfer` (HEADLINE) — therefore **any** bound `B` on lists in the window metric
  at folded threshold `τ ≤ n − s·(n−t)` bounds the plain list at plain agreement `t` by the same
  `B`.

Together with the no-go, route 4 of the issue's §6 is now characterized on both sides:
the windowed transfer is **exactly** as strong as the factor-`s` shrinkage allows — it delivers
plain list bounds for `δ ≤ (1−ρ_f)/s` (below Johnson at every rate, per the no-go), and nothing
more.  All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
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

/-- **THE POSITIVE WINDOWED TRANSFER (route 4's constructive half).**
If lists in the **window metric** are bounded — every set `M` of words, each with `≥ τ`
fully-agreeing windows against `w`, has `|M| ≤ B` — then the **plain** list at plain agreement
`t` is bounded by the same `B`, provided the shrunk threshold suffices: `τ ≤ n − s·(n−t)`.

(With `t = (1−δ)n` and `τ = ρ_f·n` this is exactly: a folded-metric bound at folded rate `ρ_f`
gives a plain bound at radius `δ ≤ (1−ρ_f)/s` — which `windowed_folding_below_johnson` proves is
strictly below the Johnson radius at every rate and window size.  The transfer is therefore
characterized: it works exactly up to the factor-`s` shrinkage, and no further.) -/
theorem windowed_list_transfer (w : Fin n → F) (hs : s ≤ n) (t τ B : ℕ)
    (hτ : τ ≤ n - s * (n - t))
    (hfold : ∀ M : Finset (Fin n → F),
      (∀ c ∈ M, τ ≤ (Finset.univ.filter fun i : Fin n => windowAgrees c w s hs i).card) →
      M.card ≤ B)
    (L : Finset (Fin n → F))
    (hagree : ∀ c ∈ L, t ≤ (Finset.univ.filter fun i : Fin n => c i = w i).card) :
    L.card ≤ B := by
  apply hfold
  intro c hc
  calc τ ≤ n - s * (n - t) := hτ
    _ ≤ (Finset.univ.filter fun i : Fin n => windowAgrees c w s hs i).card :=
        windowAgree_count_ge_of_agree c w hs t (hagree c hc)

/-- **Non-vacuity** (`ZMod 2`, `n = 4`, `s = 2`, `t = 4`, `τ = 4`): full agreement gives all `4`
windows agreeing (`4 ≤ n − s·(n−t) = 4`), so the transfer fires with genuine hypotheses — e.g. the
trivial folded bound `B = 16` (all words) transfers. -/
theorem nonvacuous_transfer :
    ∀ L : Finset (Fin 4 → ZMod 2),
      (∀ c ∈ L, 4 ≤ (Finset.univ.filter fun i : Fin 4 => c i = (fun _ => 0) i).card) →
      L.card ≤ 16 := by
  intro L hagree
  apply windowed_list_transfer (s := 2) (fun _ => 0) (by norm_num) 4 4 16 (by norm_num)
    _ L hagree
  intro M _
  calc M.card ≤ (Finset.univ : Finset (Fin 4 → ZMod 2)).card := Finset.card_le_card
        (Finset.subset_univ M)
    _ = 16 := by
        rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        norm_num

end ArkLib.CodingTheory.WindowedFoldingTransfer

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.disagree_card_le
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.windowAgree_count_ge_of_agree
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.windowed_list_transfer
#print axioms ArkLib.CodingTheory.WindowedFoldingTransfer.nonvacuous_transfer
