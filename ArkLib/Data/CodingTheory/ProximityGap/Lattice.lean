/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Lattice-form Grand-Challenge statements (the faithful encodings)

Companion to `GrandChallengeCollapse.lean` (Finding F6). The collapse file shows the
real-threshold existence encodings of the §1 Grand Challenges degenerate to radius-one
statements. This file supplies the *faithful* lattice encodings and proves that, in them,
**existence of the maximal threshold is trivial** — a finite, monotone-downward-closed,
nonempty set of lattice radii has a maximum. Together the two files make the
formalization-level situation precise:

* real-threshold existence form: collapses (F6) — cannot carry the prize content;
* lattice existence form: trivially true whenever any threshold works at all
  (`mcaLatticeThreshold_spec`, `listLatticeThreshold_spec`);
* therefore the prize content is exactly the **value** `δ*_C = (max j)/n` — the
  "determine" in ABF26 §1 — which is what the `MCALowerWitness`/`MCAUpperWitness`
  bracketing framework in `GrandChallenges.lean` tracks. No existence-form `Prop` can
  encode an open "determine" problem over a finite search space.

The nonemptiness hypotheses (`epsMCA C 0 ≤ ε*`, resp. the radius-zero list bound) are the
paper's "assuming `|F|` is sufficiently large so that such a `δ*_C` exists".

## Relationship to `GrandChallengesLattice.lean`

There are two lattice encodings in this directory, and they are **complementary, not
duplicate** — keep both:

* This file (`GrandChallengeLattice`, singular) indexes the lattice by `Finset ℕ`
  (`Finset.range (n+1) |>.filter …`) and lives in namespace `ProximityGap.GrandChallenges`.
  Its `listLatticeSet` / `listLatticeThreshold` are the **canonical objects the
  downstream Grand-Challenge LD-threshold files consume**
  (`GrandChallengeLDThreshold`, `…Elias`, `…JohnsonSq`, `…HalfDist`): those files prove
  capacity/Johnson/Elias/half-distance brackets on `GrandChallenges.listLatticeThreshold`
  by `rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]`, i.e. they
  depend on the `Finset ℕ` representation here.
* `GrandChallengesLattice.lean` (plural) indexes the lattice by `Finset (Fin (n+1))`
  (`Finset.univ.filter …`) in namespace `ProximityGap.GrandChallengesLattice`. It adds the
  step-function bridge to the real-valued `MCALowerWitness`/`MCAUpperWitness`/
  `ListLowerWitness`/`ListUpperWitness` framework (`latticeIndexOf`, `*_bracketed`,
  uniqueness), which this file does not.

The bridge API in `GrandChallengesLattice.lean`
(`*_val_eq_*LatticeThreshold`, `val_mem_*LatticeSet_iff_*Satisfies`, and
`*PrizeLatticeResolved_of_canonical_*LatticeThreshold_eq`) proves that the two
representations agree under `Fin.val`. The MCA-side definitions of this file
(`mcaLatticeSet`, `mcaLatticeThreshold`, `mcaLatticeThreshold_spec`) are the `Finset ℕ`-form
analogue of the plural file's `mcaThreshold`; they are kept proven and green for symmetry
with the list-decoding side that downstream LD-threshold files consume.

## Main definitions and results

* `mcaLatticeSet` — the set of lattice radii `j ≤ n` with `ε_mca(C, j/n) ≤ ε*`.
* `mcaLatticeThreshold` — its maximum (the genuine `δ*_C`, as data).
* `mcaLatticeThreshold_spec` — the maximum is a *bona fide* maximal threshold: the bound
  holds at it and fails at every strictly larger lattice radius.
* `listLatticeSet`, `listLatticeThreshold`, `listLatticeThreshold_spec` — the
  list-decoding mirror (the objects consumed by the downstream LD-threshold files).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace GrandChallenges

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- Lattice radii `j ∈ {0, …, n}` at which the MCA bound holds. Relative Hamming
distances live on `{j/n}`, so these are the only radii that matter
(`epsMCA_eq_of_floor_eq`). -/
noncomputable def mcaLatticeSet (C : Set (ι → F)) (ε_star : ℝ≥0) : Finset ℕ :=
  (Finset.range (Fintype.card ι + 1)).filter
    (fun j => epsMCA (F := F) (A := F) C ((j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤
      (ε_star : ENNReal))

/-- Radius zero belongs to the lattice set as soon as the radius-zero bound holds — the
paper's "`|F|` sufficiently large" hypothesis. -/
lemma zero_mem_mcaLatticeSet {C : Set (ι → F)} {ε_star : ℝ≥0}
    (h0 : epsMCA (F := F) (A := F) C 0 ≤ (ε_star : ENNReal)) :
    0 ∈ mcaLatticeSet C ε_star := by
  classical
  unfold mcaLatticeSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
  simpa using h0

open Classical in
/-- **The genuine `δ*_C` (MCA side), as data**: the largest lattice radius with the
bound. Defined whenever the lattice set is nonempty. -/
noncomputable def mcaLatticeThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : (mcaLatticeSet C ε_star).Nonempty) : ℕ :=
  (mcaLatticeSet C ε_star).max' hne

/-- **Existence of the maximal lattice threshold is trivial** (finite nonempty set):
the bound holds at `δ* = (max j)/n ≤ 1` and fails at every strictly larger lattice
radius. This is the faithful statement shape of the §1 Grand MCA Challenge; its open
content is *computing* the value, not the existence proved here. -/
theorem mcaLatticeThreshold_spec (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : (mcaLatticeSet C ε_star).Nonempty) :
    (mcaLatticeThreshold C ε_star hne : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ 1 ∧
    epsMCA (F := F) (A := F) C
      ((mcaLatticeThreshold C ε_star hne : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤
        (ε_star : ENNReal) ∧
    ∀ j : ℕ, j ≤ Fintype.card ι → mcaLatticeThreshold C ε_star hne < j →
      epsMCA (F := F) (A := F) C ((j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) >
        (ε_star : ENNReal) := by
  classical
  have hcard : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hmem := (mcaLatticeSet C ε_star).max'_mem hne
  unfold mcaLatticeSet at hmem
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hrange, hbound⟩ := hmem
  refine ⟨?_, hbound, ?_⟩
  · -- `j ≤ n` so `j/n ≤ 1`.
    rw [div_le_one hcard]
    exact_mod_cast Nat.lt_succ_iff.mp hrange
  · intro j hj hgt
    by_contra hnot
    push Not at hnot
    have hjmem : j ∈ mcaLatticeSet C ε_star := by
      unfold mcaLatticeSet
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hj, hnot⟩
    exact absurd (Finset.le_max' _ j hjmem) (not_le.mpr hgt)

open Classical ListDecodable in
/-- Lattice radii at which the interleaved list-size bound holds (list-decoding side). -/
noncomputable def listLatticeSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Finset ℕ :=
  (Finset.range (Fintype.card ι + 1)).filter
    (fun j => (Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) :
        ENNReal) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))

open Classical in
/-- **The genuine `δ*_C` (list-decoding side), as data.** -/
noncomputable def listLatticeThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : (listLatticeSet C m ε_star).Nonempty) : ℕ :=
  (listLatticeSet C m ε_star).max' hne

open ListDecodable in
/-- **Existence of the maximal lattice list-decoding threshold is trivial**: the mirror
of `mcaLatticeThreshold_spec`. -/
theorem listLatticeThreshold_spec (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : (listLatticeSet C m ε_star).Nonempty) :
    (listLatticeThreshold C m ε_star hne : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ 1 ∧
    (Lambda (C^⋈ (Fin m))
        (((listLatticeThreshold C m ε_star hne : ℝ≥0) / (Fintype.card ι : ℝ≥0) :
          ℝ≥0) : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) ∧
    ∀ j : ℕ, j ≤ Fintype.card ι → listLatticeThreshold C m ε_star hne < j →
      (Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) :
        ENNReal) > (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
  classical
  have hcard : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hmem := (listLatticeSet C m ε_star).max'_mem hne
  unfold listLatticeSet at hmem
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hrange, hbound⟩ := hmem
  refine ⟨?_, hbound, ?_⟩
  · rw [div_le_one hcard]
    exact_mod_cast Nat.lt_succ_iff.mp hrange
  · intro j hj hgt
    by_contra hnot
    push Not at hnot
    have hjmem : j ∈ listLatticeSet C m ε_star := by
      unfold listLatticeSet
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hj, hnot⟩
    exact absurd (Finset.le_max' _ j hjmem) (not_le.mpr hgt)

end GrandChallenges

end ProximityGap
