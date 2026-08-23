/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.AGL24AgreementHypergraph

/-!
# [AGL24] the list-decoding notion bridge (issue #346, brick 7)

The average-radius ⟹ plain list-decodability bridge that wires the composed deterministic
chain (brick 6) into the in-tree `listDecodable` surface: a failure of `(r, L)`-list
decodability yields `L+1` *distinct* codewords whose total distance to the witness word is at
most `(L+1)·r·n` — a bad average-radius configuration whenever `(L+1)·r·n ≤ L(n−k)` (the
[AGL24] radius `r = L/(L+1)·(1−R−ε)` satisfies this with room `εn`).

* `exists_distinct_close_codewords_of_not_listDecodable` — the extraction: `L+1` distinct
  close codewords from a list-decoding failure;
* `exists_bad_config_of_not_listDecodable` — **the bridge**: the bad average-radius
  configuration in exactly the shape `bad_list_gives_wpc_rank_deficit` consumes
  (an injective `Fin (L+1)`-family in `C` with the integer total-distance bound).
-/

open Finset ListDecodable

namespace AGL24

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- A failure of `(r, L)`-list decodability yields `L + 1` **distinct** codewords within
relative radius `r` of a common word. -/
theorem exists_distinct_close_codewords_of_not_listDecodable
    {C : Set (ι → F)} {r : ℝ} {L : ℕ}
    (h : ¬ listDecodable C r (L : ℝ)) :
    ∃ y : ι → F, ∃ c : Fin (L + 1) → ι → F, Function.Injective c ∧
      (∀ j, c j ∈ C) ∧ ∀ j, (Code.relHammingDist y (c j) : ℝ) ≤ r := by
  classical
  unfold listDecodable at h
  push Not at h
  obtain ⟨y, hy⟩ := h
  -- The close-codeword set is finite; extract an (L+1)-subset.
  set S := closeCodewordsRel C y r with hS
  have hfin : S.Finite := Set.toFinite S
  have hcard : L + 1 ≤ hfin.toFinset.card := by
    have hgt : (L : ℝ) < (S.ncard : ℝ) := hy
    have hL : L < S.ncard := by exact_mod_cast hgt
    have heq : S.ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card S hfin
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  -- Enumerate the subset.
  let e : ↥T ≃ Fin (L + 1) := T.equivFinOfCardEq hTcard
  refine ⟨y, fun j => (e.symm j : ι → F), ?_, ?_, ?_⟩
  · intro j j' hjj'
    have : e.symm j = e.symm j' := Subtype.ext hjj'
    simpa using congrArg e this
  · intro j
    have hmem : ((e.symm j : ↥T) : ι → F) ∈ T := (e.symm j).property
    have := hTsub hmem
    rw [Set.Finite.mem_toFinset] at this
    exact this.1
  · intro j
    have hmem : ((e.symm j : ↥T) : ι → F) ∈ T := (e.symm j).property
    have hball := (Set.Finite.mem_toFinset hfin |>.mp (hTsub hmem)).2
    rw [relHammingBall, Set.mem_setOf_eq] at hball
    show (Code.relHammingDist y ((e.symm j : ↥T) : ι → F) : ℝ) ≤ r
    convert hball using 3

/-- **The notion bridge**: a failure of `(r, L)`-list decodability with
`(L+1)·r·n ≤ L·(n−k)` yields a bad average-radius configuration — `L+1` pairwise-distinct
codewords with integer total distance at most `L(n−k)`, exactly the input shape of the
composed deterministic chain. -/
theorem exists_bad_config_of_not_listDecodable
    {C : Set (ι → F)} {r : ℝ} {L k : ℕ} (hr : 0 ≤ r)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    (h : ¬ listDecodable C r (L : ℝ)) :
    ∃ y : ι → F, ∃ c : Fin (L + 1) → ι → F, Function.Injective c ∧
      (∀ j, c j ∈ C) ∧
      ∑ j, hammingDist y (c j) ≤ L * (Fintype.card ι - k) := by
  obtain ⟨y, c, hinj, hmem, hclose⟩ :=
    exists_distinct_close_codewords_of_not_listDecodable h
  refine ⟨y, c, hinj, hmem, ?_⟩
  -- Per-codeword: hammingDist ≤ r·n (from the relative bound).
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hper : ∀ j, (hammingDist y (c j) : ℝ) ≤ r * (Fintype.card ι : ℝ) := by
    intro j
    have hrel := hclose j
    rw [show (Code.relHammingDist y (c j) : ℝ)
        = (hammingDist y (c j) : ℝ) / (Fintype.card ι : ℝ) from ?_] at hrel
    · exact (div_le_iff₀ hn).mp hrel
    · unfold Code.relHammingDist
      push_cast
      rfl
  -- Sum and cast back to ℕ.
  have hsum : ((∑ j, hammingDist y (c j) : ℕ) : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ) := by
    calc ((∑ j, hammingDist y (c j) : ℕ) : ℝ)
        = ∑ j, (hammingDist y (c j) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _j : Fin (L + 1), r * (Fintype.card ι : ℝ) :=
        Finset.sum_le_sum fun j _ => hper j
    _ = (L + 1 : ℝ) * r * (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
    _ ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ) := hrad
  exact_mod_cast hsum

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.exists_distinct_close_codewords_of_not_listDecodable
#print axioms AGL24.exists_bad_config_of_not_listDecodable
