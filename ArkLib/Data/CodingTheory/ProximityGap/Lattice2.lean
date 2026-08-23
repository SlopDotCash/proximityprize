/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Core
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Witnesses
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.ListThreshold
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Spec

/-!
# Faithful lattice encodings of the §1 Grand Challenges (after Finding F6)

`GrandChallengeCollapse.lean` proves that the real-valued, strict-failure encodings
`grandMCAChallenge` / `grandListDecodingChallenge` of `GrandChallenges.lean` **collapse**:
because `ε_mca C δ` and `Λ(C^⋈m, δ)` are step functions of `δ` through `⌊δ·n⌋`
(`epsMCA_eq_of_floor_eq`, `Lambda_eq_of_floor_eq`), no maximal *real* threshold `δ* < 1` can
satisfy a strict-failure-above clause, so the encodings degenerate to radius-one statements
and `listDecodingPrize` is provably false as encoded.

The paper [ABF26] §1 actually asks to **determine the largest *lattice* threshold**
`δ* ∈ {0, 1/n, …, 1}`: relative Hamming distances live on the `1/n`-lattice, so the only
meaningful thresholds are the lattice points `j/n` for `j : Fin (n+1)`, where
`n := |ι|`. On this lattice the maximal threshold is a *well-defined finite quantity*
whenever it exists at all — a finite, nonempty, (by monotonicity) downward-closed subset of
`Fin (n+1)` has a maximum — and **determining its value is the open $1M problem**; the
one-sided witnesses of `GrandChallenges.lean` *bound* it.

This file builds that faithful encoding:

* `mcaLatticePoint n j := j/n : ℝ≥0` — the lattice radii.
* `mcaSatisfies C ε* j` (a `DecidablePred`) — `ε_mca(C, j/n) ≤ ε*`; downward closed in `j`
  by `epsMCA_mono` (`mcaSatisfies_downward_closed`).
* `mcaThreshold C ε* hne : Fin (n+1)` — the lattice threshold, `Finset.max'` of the
  satisfying set under a nonemptiness hypothesis `hne`
  (the paper's "`|F|` sufficiently large so that `δ*` exists").
* `mcaThreshold_spec` / `mcaThreshold_unique` — existence and uniqueness: the threshold
  satisfies the bound and is the **unique greatest** lattice point that does.
* `mcaThresholdLattice_bracketed` — a lattice lower witness and a lattice upper witness
  bracket `mcaThreshold`, mirroring `mca_threshold_bracketed`.
* the list-decoding analogues `listThreshold`, `listThreshold_spec`, … ,
  `listThresholdLattice_bracketed`.

Nothing here resolves the prize: it makes the prize *quantity* `mcaThreshold` / `listThreshold`
a real Lean object that the witnesses can be proved to bracket, replacing the collapse-broken
existence predicate.

## Relationship to `GrandChallengeLattice.lean` (singular)

There are two lattice encodings in this directory, and they are **complementary, not
duplicate** — both are kept and both are fully proven (axiom-clean):

* This file (`GrandChallengesLattice`, plural, namespace `ProximityGap.GrandChallengesLattice`)
  indexes the lattice by `Finset (Fin (n+1))` (`Finset.univ.filter …`) and supplies the
  step-function bridge to the real-valued witness framework
  (`MCALowerWitness`/`MCAUpperWitness`, `ListLowerWitness`/`ListUpperWitness`):
  `latticeIndexOf`, the `*_bracketed` lemmas, the `*_unique` lemmas, and the
  per-rate prize-resolution predicates. `Hab25Core.lean` consumes these objects.
* `GrandChallengeLattice.lean` (singular, namespace `ProximityGap.GrandChallenges`)
  indexes the lattice by `Finset ℕ` (`Finset.range (n+1) |>.filter …`). Its
  `listLatticeSet` / `listLatticeThreshold` are the canonical objects the downstream
  Grand-Challenge LD-threshold bracket files consume
  (`GrandChallengeLDThreshold{,Elias,JohnsonSq,HalfDist}.lean`), which rewrite by
  `GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range` and therefore
  depend on that `Finset ℕ` representation.

This file also contains the canonical bridge API back to the singular `Finset ℕ`
representation: `val_mem_*LatticeSet_iff_*Satisfies`, nonemptiness equivalences,
`*_val_eq_*LatticeThreshold`, and the MCA/list
`*PrizeLatticeResolved_of_canonical_*LatticeThreshold_eq` transport lemmas. These show that
the two retained representations agree under `Fin.val` while allowing downstream proofs to
keep whichever shape is most convenient.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

