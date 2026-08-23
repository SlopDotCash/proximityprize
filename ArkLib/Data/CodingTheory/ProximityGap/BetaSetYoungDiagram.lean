/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BetaSetSize
import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# The β-set Young diagram: `area = number of cells` (#389)

The geometric bridge connecting the β-set area theory (`RimHookArea`, `BetaSetSize`) to Mathlib's
`YoungDiagram`. We associate to a bead set `B` the Young diagram whose row lengths are the
partition parts `β_j - j` (decreasing), and prove its cell count equals `area B`. This grounds the
rim-hook size law as a literal statement about Young-diagram cells.

* **`cellsOfRowLens_card`** — `(cellsOfRowLens w).card = w.sum` (general, reusable).
-/

open Finset

namespace ArkLib.ProximityGap.BetaSetYoungDiagram

/-- The number of cells of the Young diagram built from a row-length list is the list sum. -/
theorem cellsOfRowLens_card : ∀ w : List ℕ, (YoungDiagram.cellsOfRowLens w).card = w.sum
  | [] => by simp [YoungDiagram.cellsOfRowLens]
  | (w :: ws) => by
      rw [YoungDiagram.cellsOfRowLens]
      rw [Finset.card_union_of_disjoint, Finset.card_map, cellsOfRowLens_card ws,
        Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul, List.sum_cons]
      · -- disjointness: row-0 cells vs shifted (row ≥ 1) cells
        rw [Finset.disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        simp only [Finset.mem_product, Finset.mem_singleton] at h1
        simp only [Finset.mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
          Prod.exists] at h2
        obtain ⟨x, y, _, hxy⟩ := h2
        simp only [Prod.map_apply, Function.Embedding.refl_apply, Prod.mk.injEq] at hxy
        obtain ⟨ha0, _⟩ := h1
        omega

open ArkLib.ProximityGap.RimHookArea ArkLib.ProximityGap.BetaSetSize

variable {B : Finset ℕ} {n : ℕ}

/-- The `k`-th smallest element of `B` is at least `k` (strict monotonicity of the enumeration). -/
theorem orderEmbOfFin_le (h : B.card = n) :
    ∀ (k : ℕ) (hk : k < n), k ≤ B.orderEmbOfFin h ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
      intro hk
      have hm : m < n := by omega
      have hstep : B.orderEmbOfFin h ⟨m, hm⟩ < B.orderEmbOfFin h ⟨m + 1, hk⟩ :=
        (B.orderEmbOfFin h).strictMono (Fin.mk_lt_mk.mpr (by omega))
      have hih := ih hm
      omega

/-- The parts `β_j - j` are weakly increasing (since the β's are strictly increasing). -/
theorem parts_monotone (h : B.card = n) :
    Monotone (fun j : Fin n => B.orderEmbOfFin h j - (j : ℕ)) := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      have hlt : B.orderEmbOfFin h (Fin.castSucc i) < B.orderEmbOfFin h i.succ :=
        (B.orderEmbOfFin h).strictMono (by rw [Fin.lt_def]; simp)
      simp only [Fin.coe_castSucc, Fin.val_succ]
      omega

/-- The Young diagram associated to a bead set `B`: row lengths are the parts `β_j - j` in
decreasing order. -/
noncomputable def youngDiagramOfBeta (h : B.card = n) : YoungDiagram :=
  YoungDiagram.ofRowLens
    (List.ofFn (fun j : Fin n => B.orderEmbOfFin h (Fin.rev j) - ((Fin.rev j : Fin n) : ℕ)))
    (by
      rw [List.sortedGE_ofFn_iff]
      exact (parts_monotone h).comp_antitone Fin.rev_anti)

/-- **The geometric bridge.** The number of cells of the Young diagram of `B` equals `area B`:
the rim-hook size law is literally about Young-diagram cells. -/
theorem card_youngDiagramOfBeta (h : B.card = n) :
    ((youngDiagramOfBeta h).card : ℤ) = area B := by
  classical
  have hcard : (youngDiagramOfBeta h).card
      = ∑ j : Fin n, (B.orderEmbOfFin h j - (j : ℕ)) := by
    unfold youngDiagramOfBeta YoungDiagram.card
    rw [YoungDiagram.ofRowLens]
    dsimp only
    rw [cellsOfRowLens_card, List.sum_ofFn]
    exact Equiv.sum_comp (Fin.revPerm) (fun j => B.orderEmbOfFin h j - (j : ℕ))
  rw [hcard, area_eq_sum_parts h]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hle2 : (j : ℕ) ≤ B.orderEmbOfFin h j := orderEmbOfFin_le h j.val j.isLt
  omega


/-- **Geometric rim-hook size law.** Removing a rim `n`-hook removes exactly `n` cells from the
Young diagram: `card (YD of B') + n = card (YD of B)`. Combined with `card_youngDiagramOfBeta`
this realizes the abacus bead-move as the removal of `n` genuine Young-diagram cells. -/
theorem youngDiagram_card_removeRimHook {B B' : Finset ℕ} {n : ℕ}
    (hB : B.card = n) (hstep : RemovesRimHook B B' n) :
    (youngDiagramOfBeta (show B'.card = n from (card_removeRimHook hstep).trans hB)).card + n
      = (youngDiagramOfBeta hB).card := by
  have hB' : B'.card = n := (card_removeRimHook hstep).trans hB
  have h1 : ((youngDiagramOfBeta hB').card : ℤ) = area B' := card_youngDiagramOfBeta hB'
  have h2 : ((youngDiagramOfBeta hB).card : ℤ) = area B := card_youngDiagramOfBeta hB
  have h3 : area B' = area B - n := area_removeRimHook hstep
  omega


end ArkLib.ProximityGap.BetaSetYoungDiagram
