/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Line ⊕ hyperplane decomposition of a subspace

A nonzero `𝔽`-subspace `W ⊆ K` decomposes as `span 𝔽 {u} ⊔ W'` for some `u ∈ W` and a hyperplane
`W' ≤ W` with `u ∉ W'`, the two summands disjoint.  The structural input to the
subspace-polynomial recursion (`V = V' ⊕ 𝔽_q·u`).
-/

open BigOperators

namespace BKR06

variable {F : Type*} [Field F] {K : Type*} [Field K] [Module F K]

/-- **Line ⊕ hyperplane decomposition.** For a nonzero `𝔽`-subspace `W ⊆ K`, there is `u ∈ W` and
a subspace `W' ≤ W` with `u ∉ W'`, `W = span 𝔽 {u} ⊔ W'`, and `span 𝔽 {u}` disjoint from `W'`. -/
lemma exists_line_decomp (W : Submodule F K) (hW : W ≠ ⊥) :
    ∃ (W' : Submodule F K) (u : K), u ∈ W ∧ W' ≤ W ∧ u ∉ W' ∧
      W = Submodule.span F {u} ⊔ W' ∧ Disjoint (Submodule.span F {u}) W' := by
  obtain ⟨u, hu_mem, hu_ne⟩ := (Submodule.ne_bot_iff W).mp hW
  set L := Submodule.span F {u} with hL
  have hLW : L ≤ W := by rw [hL, Submodule.span_le]; simpa using hu_mem
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl L
  refine ⟨W ⊓ Q, u, hu_mem, inf_le_left, ?_, ?_, ?_⟩
  · intro hcon
    have hmem : u ∈ L ⊓ Q := ⟨Submodule.mem_span_singleton_self u, hcon.2⟩
    rw [hQ.inf_eq_bot] at hmem
    exact hu_ne (by simpa using hmem)
  · -- W = L ⊔ (W ⊓ Q), by element chasing using L ⊔ Q = ⊤
    refine le_antisymm ?_ (sup_le hLW inf_le_left)
    intro x hx
    have hxLQ : x ∈ L ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨l, hl, q, hq, rfl⟩ := Submodule.mem_sup.mp hxLQ
    have hqW : q ∈ W := by
      have heq : l + q - l = q := by abel
      rw [← heq]; exact W.sub_mem hx (hLW hl)
    exact Submodule.mem_sup.mpr ⟨l, hl, q, ⟨hqW, hq⟩, rfl⟩
  · exact hQ.disjoint.mono_right inf_le_right

end BKR06

-- Axiom audit.
#print axioms BKR06.exists_line_decomp
