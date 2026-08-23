/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingGeometryProducers

/-! Scratch: Hab25 S5 elementary half — the discriminant bad-set supply. -/

namespace ArkLib.Match304

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The polynomial non-vanishing locus is large** (the elementary half of Hab25 S5):
a nonzero `disc : F[X]` vanishes on at most `natDegree disc` points, so whenever
`N + natDegree disc < |F|` the non-vanishing locus exceeds `N`. This supplies the `bad`-set
input of `card_gt_of_compl_subset` with `bad = disc.roots.toFinset`. -/
theorem card_nonvanishing_gt {disc : F[X]} (hdisc : disc ≠ 0) {N : ℕ}
    (hbig : N + disc.natDegree < Fintype.card F) :
    N < (Finset.univ.filter (fun z : F => disc.eval z ≠ 0)).card := by
  classical
  refine card_gt_of_compl_subset (bad := disc.roots.toFinset) ?_ ?_
  · intro z hz
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun hzero => hz ?_⟩
    rw [Multiset.mem_toFinset, mem_roots hdisc]
    exact hzero
  · calc N + disc.roots.toFinset.card
        ≤ N + Multiset.card disc.roots := by
          have := Multiset.toFinset_card_le disc.roots
          omega
      _ ≤ N + disc.natDegree := by
          have := card_roots' disc
          omega
      _ < Fintype.card F := hbig

/-- **The S5-shaped matching-set supply**: any matching set containing the non-vanishing locus
of a nonzero discriminant inherits the cardinality bound `N < #matchingSet` whenever
`N + natDegree disc < |F|`. The exact bad-set form `hcardFin_of_badSet` consumes. -/
theorem card_matching_gt_of_disc {disc : F[X]} (hdisc : disc ≠ 0)
    {matchingSet : Finset F}
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    {N : ℕ} (hbig : N + disc.natDegree < Fintype.card F) :
    N < matchingSet.card := by
  classical
  refine card_gt_of_compl_subset (bad := disc.roots.toFinset) ?_ ?_
  · intro z hz
    refine hcover z (fun hzero => hz ?_)
    rw [Multiset.mem_toFinset, mem_roots hdisc]
    exact hzero
  · calc N + disc.roots.toFinset.card
        ≤ N + Multiset.card disc.roots := by
          have := Multiset.toFinset_card_le disc.roots
          omega
      _ ≤ N + disc.natDegree := by
          have := card_roots' disc
          omega
      _ < Fintype.card F := hbig

end ArkLib.Match304

#print axioms ArkLib.Match304.card_nonvanishing_gt
#print axioms ArkLib.Match304.card_matching_gt_of_disc
