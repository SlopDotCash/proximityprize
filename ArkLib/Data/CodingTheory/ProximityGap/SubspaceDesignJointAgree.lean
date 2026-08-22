/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignFullVanish


/-!
# Joint agreement against a subspace design is small (B2 list-decoding ingredient) (#389, #334)

The open producer step (proving the explicit code is curve-decodable) is bounding the list of
codeword-curves via the subspace-design property the fleet proved for folded RS.  This file supplies
the core list-decoding ingredient: `subspaceDesign_jointAgree_card_le` — if `r+1` codewords with
linearly independent differences all agree with a word `y` on a set `S`, then `|S| ≤ τ(r)·n`.

On `S` every difference vanishes, so the dimension-`r` span of the differences fully vanishes on
`S`, and `subspaceDesign_fullVanish_card_le` caps such coordinates at `τ(r)·n`.  This is exactly the
mechanism that prevents many codeword-curves from sharing a large agreement region: a fresh codeword
extends a joint agreement on at most a `τ(r)`-fraction of coordinates, which is what forces the
close-set list onto few curves in the GG25 / Guruswami–Xing argument.  Axiom-clean.
-/
open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {F : Type} [Field F]

omit [DecidableEq ι] in
/-- **Joint agreement against a subspace design is small.**  If `r+1` codewords of a
`τ`-subspace-design `C` have linearly independent differences `c_{j+1} − c₀` (so they span a
dimension-`r` subspace of `C`) and they *all* agree with a word `y` on a set `S`, then
`|S| ≤ τ(r)·n`.  On `S` every difference vanishes, so the dimension-`r` span fully vanishes on `S`,
and the subspace-design bound `subspaceDesign_fullVanish_card_le` caps such coordinates at `τ(r)·n`.
This is the list-decoding ingredient: a fresh codeword can extend a joint agreement only on a
`τ(r)`-fraction of coordinates, which is what forces the list onto few curves. -/
theorem subspaceDesign_jointAgree_card_le {s : ℕ} {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) (c : Fin (r + 1) → (ι → Fin s → F)) (hc : ∀ j, c j ∈ C)
    (hindep : LinearIndependent F (fun j : Fin r => c j.succ - c 0))
    (y : ι → Fin s → F) (S : Finset ι) (hS : ∀ i ∈ S, ∀ j, c j i = y i) :
    (S.card : ℝ) ≤ τ r * Fintype.card ι := by
  classical
  set A := Submodule.span F (Set.range (fun j : Fin r => c j.succ - c 0)) with hA
  have hAC : A ≤ C := by
    rw [hA, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact C.sub_mem (hc j.succ) (hc 0)
  have hrank : Module.finrank F A = r := by
    rw [hA, finrank_span_eq_card hindep, Fintype.card_fin]
  have hSsub : S ⊆ univ.filter (fun i : ι => A ≤ LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) := by
    intro i hi
    rw [mem_filter]
    refine ⟨mem_univ i, ?_⟩
    rw [hA, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    change (c j.succ - c 0) i = 0
    rw [Pi.sub_apply, hS i hi j.succ, hS i hi 0, sub_self]
  calc (S.card : ℝ)
      ≤ ((univ.filter (fun i : ι => A ≤ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSsub
    _ ≤ τ r * Fintype.card ι := subspaceDesign_fullVanish_card_le h hr hAC hrank

end ProximityGap
