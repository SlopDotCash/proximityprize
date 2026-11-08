/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Commitments.Functional.MerkleTree.Extraction
import VCVio
import ToMathlib.Data.IndexedBinaryTree.Equiv

/-!
# Hiding for inductive Merkle-tree commitments (salted leaves)

A plain Merkle commitment is *not* hiding: the root and an opening can leak information about the
committed leaf (e.g. a low-entropy leaf can be brute-forced through the public hash). The standard
fix (SNARGs book §18) is to commit to *salted* leaves: each leaf `v` is replaced by a leaf
commitment `leafCommit r v` using fresh randomness (salt) `r`, and the Merkle tree is built over the
salted leaves. Opening reveals `(v, r)` together with the authentication path.

This file provides:

* `leafCommit` / `saltedLeaves` / `buildSaltedTree` — the salted-leaf commitment construction over
  the VCVio inductive Merkle tree.
* `salted_completeness` — a **fully proven** correctness lemma: the salted construction is itself an
  honest Merkle tree over the commitment leaves, so single-index completeness transports verbatim.
* `simulatorTranscript` — the simulator-facing transcript generator that keeps opened leaves and
  replaces unopened leaves by a fixed filler before sampling salts and building the transcript.
* `SimulationBasedHiding` / `simulationBasedHiding_implies_Hiding` — the hybrid proof skeleton:
  if every real transcript *program* equals its simulator program, then the existing `Hiding`
  predicate follows.
* `outputLaw`, `DistHiding`, `DistSimulationBasedHiding` — the output-law (perfect
  distributional) versions, with `Hiding.distHiding`, `SimulationBasedHiding.dist`,
  `distSimulationBasedHiding_implies_DistHiding`, and the resampling example
  `distHiding_resample_prefix` / `Hiding.distHiding_resample_prefix`.

## Program equality versus output-law equality

`Hiding` and `SimulationBasedHiding` equate raw `OracleComp (spec α)` terms. That is *program
equivalence*: strictly stronger than equality of output distributions (for example, prefixing the
salt sampler with a discarded sampling step changes the program but not its output law). It is
therefore not the advertised perfect-distribution hiding notion and can rule out legitimate
simulator or hybrid steps. The distributional notion is `DistHiding`, which compares
`outputLaw` (the `evalDist` measure of the transcript experiment, with the discrete σ-algebra,
under the chosen `UniformAnswerMeasure (spec α)` interpretation). Program-equality hiding implies
it (`Hiding.distHiding`). No compiled counterexample separating the two notions is included here.

Scope of `outputLaw`: each oracle query in `sampleSalts` is interpreted as a fresh independent
uniform answer (no shared cache), and `hashFn` is a fixed public function. This is perfect salted
hiding with respect to a fixed compression function, not the shared-random-oracle hiding
experiment in which `hashFn` itself is the lazily sampled oracle.

## Scope of the global no-collision premise

The deterministic binding/uniqueness lemmas in this file take the *global* injectivity premise
`∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d`, which is unsatisfiable for a finite digest
type with at least two elements (`not_global_hash_injective_of_finite` in `Extraction.lean`).
They are meaningful only for abstract or infinite digest types and are not the good event of a
birthday argument. The finite-digest form is `salted_opening_binding_pair_of_queryInjectiveOn`,
which assumes injectivity only on the two leaf-commitment pairs and the child pairs hashed by the
two openings (cf. `opening_binding_of_queryInjectiveOn` / `opening_conflict_collision`).

## What remains probabilistic

The simulator/hybrid layer below proves the exact logical discharge of `Hiding` (resp.
`DistHiding`) from a real-to-ideal transcript equality premise. In the random-oracle model, that
premise is the usual salting/programming argument: unopened salted leaves are replaced by fresh
random digest values, with loss bounded by salt/query collisions. That argument is **not**
formalized here, and changing program equality to output-law equality does not discharge it.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/-- A salted leaf commitment: combine a leaf value `v` with salt `r` via the compression function.
Using the same two-to-one `hashFn` keeps the construction inside the single-oracle model. -/
def leafCommit (hashFn : α → α → α) (r v : α) : α := hashFn r v

/-- Replace every leaf `v` of the data tree by its salted commitment, given a salt tree `salts`
of the same shape. -/
def saltedLeaves {s : Skeleton} (hashFn : α → α → α)
    (salts : LeafData α s) (leaves : LeafData α s) : LeafData α s :=
  match salts, leaves with
  | LeafData.leaf r, LeafData.leaf v => LeafData.leaf (leafCommit hashFn r v)
  | LeafData.internal sl sr, LeafData.internal ll lr =>
    LeafData.internal (saltedLeaves hashFn sl ll) (saltedLeaves hashFn sr lr)

/-- Build the salted Merkle tree: hash the salted leaves into a tree using `hashFn`. -/
def buildSaltedTree {s : Skeleton} (hashFn : α → α → α)
    (salts : LeafData α s) (leaves : LeafData α s) : FullData α s :=
  buildMerkleTreeWithHash (saltedLeaves hashFn salts leaves) hashFn

/-- The leaf value used in a salted opening at index `idx` is the salted commitment of the
underlying leaf with its salt. -/
theorem saltedLeaves_get {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    (saltedLeaves hashFn salts leaves).get idx
      = leafCommit hashFn (salts.get idx) (leaves.get idx) := by
  induction idx with
  | ofLeaf =>
    cases salts; cases leaves; rfl
  | ofLeft idxLeft ih =>
    cases salts with
    | internal sl sr =>
      cases leaves with
      | internal ll lr =>
        simp only [saltedLeaves, LeafData.get_internal_ofLeft]
        exact ih sl ll
  | ofRight idxRight ih =>
    cases salts with
    | internal sl sr =>
      cases leaves with
      | internal ll lr =>
        simp only [saltedLeaves, LeafData.get_internal_ofRight]
        exact ih sr lr

/-- **Salted-construction completeness** (fully proven): an honest opening of the salted tree —
the salted leaf commitment at `idx` plus the honest path — verifies against the salted root.
The salted construction is just a Merkle tree over the commitment leaves, so the single-index
`functional_completeness` applies directly. -/
theorem salted_completeness {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    getPutativeRootWithHash idx
      ((saltedLeaves hashFn salts leaves).get idx)
      (generateProof (buildSaltedTree hashFn salts leaves) idx) hashFn
      = (buildSaltedTree hashFn salts leaves).getRootValue := by
  unfold buildSaltedTree
  exact functional_completeness idx (saltedLeaves hashFn salts leaves) hashFn

/-- **Same-salt deterministic binding for salted openings.** If the compression function is
collision-free, two openings at the same index with the same salt, sibling path, and root cannot
reveal different underlying leaf values. This is still the deterministic core only: the
random-oracle collision-probability step remains a separate probabilistic statement.

The global premise `hinj` is unsatisfiable for finite nontrivial `α`; see the module docstring and
`salted_opening_binding_pair_of_queryInjectiveOn` for the query-local form. -/
theorem salted_opening_binding_value {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salt value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt value₂) proof hashFn
      = rootValue) :
    value₁ = value₂ := by
  have hcommit :
      leafCommit hashFn salt value₁ = leafCommit hashFn salt value₂ :=
    opening_binding idx hashFn hinj
      (leafCommit hashFn salt value₁) (leafCommit hashFn salt value₂) rootValue proof h₁ h₂
  exact (hinj salt value₁ salt value₂ hcommit).2

/-- **Pair-level deterministic binding for salted openings.** If the compression function is
collision-free, two openings at the same index with the same sibling path and root determine the
entire salted opening pair: both the salt and the underlying leaf value are equal.

This is still only the deterministic no-collision implication. The global premise `hinj` is
unsatisfiable for finite nontrivial `α`, so it is not the event whose failure a random-oracle
birthday bound controls; that role is played by the query-local premise of
`salted_opening_binding_pair_of_queryInjectiveOn`. -/
theorem salted_opening_binding_pair {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salt₁ salt₂ value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt₁ value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt₂ value₂) proof hashFn
      = rootValue) :
    salt₁ = salt₂ ∧ value₁ = value₂ := by
  have hcommit :
      leafCommit hashFn salt₁ value₁ = leafCommit hashFn salt₂ value₂ :=
    opening_binding idx hashFn hinj
      (leafCommit hashFn salt₁ value₁) (leafCommit hashFn salt₂ value₂) rootValue proof h₁ h₂
  exact hinj salt₁ value₁ salt₂ value₂ hcommit

/-- **Query-local pair-level binding for salted openings.** Two openings at the same index with
the same sibling path and root determine the salted pair, assuming only that `hashFn` is injective
on the two leaf-commitment inputs `(salt₁, value₁)`, `(salt₂, value₂)` and on the child pairs hashed
while recomputing the two roots. Unlike `salted_opening_binding_pair`, this premise is satisfiable
for finite digest types. -/
theorem salted_opening_binding_pair_of_queryInjectiveOn {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (salt₁ salt₂ value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (hinj : HashInjectiveOnQueries hashFn
      ([(salt₁, value₁), (salt₂, value₂)] ++
        (openingHashQueries hashFn idx (leafCommit hashFn salt₁ value₁) proof ++
          openingHashQueries hashFn idx (leafCommit hashFn salt₂ value₂) proof)))
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt₁ value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt₂ value₂) proof hashFn
      = rootValue) :
    salt₁ = salt₂ ∧ value₁ = value₂ := by
  have hpaths := hinj.mono (fun p hp => List.mem_append_right _ hp)
  have hcommit :
      leafCommit hashFn salt₁ value₁ = leafCommit hashFn salt₂ value₂ :=
    (getPutativeRootWithHash_unique_of_queryInjectiveOn hashFn _ hpaths idx proof proof
      (leafCommit hashFn salt₁ value₁) (leafCommit hashFn salt₂ value₂)
      (fun _ hp => List.mem_append_left _ hp) (fun _ hp => List.mem_append_right _ hp)
      (h₁.trans h₂.symm)).1
  have hpair := hinj (salt₁, value₁) (by simp) (salt₂, value₂) (by simp) hcommit
  exact Prod.mk.inj hpair

/-- **Honest salted-opening uniqueness.** If a candidate salted pair verifies against the honest
salted root using the honest authentication path, then it is the honest salt and leaf at that
index, assuming the compression function is collision-free.

This is the salted analogue of the deterministic extractor soundness in `Extraction.lean`: the
honest salted tree and path pin down the opened `(salt, value)` pair. -/
theorem salted_opening_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s)
    (salt value : α)
    (h : getPutativeRootWithHash idx (leafCommit hashFn salt value)
        (generateProof (buildSaltedTree hashFn salts leaves) idx) hashFn
        = (buildSaltedTree hashFn salts leaves).getRootValue) :
    salt = salts.get idx ∧ value = leaves.get idx := by
  apply salted_opening_binding_pair idx hashFn hinj salt (salts.get idx) value (leaves.get idx)
    (buildSaltedTree hashFn salts leaves).getRootValue
    (generateProof (buildSaltedTree hashFn salts leaves) idx) h
  simpa [saltedLeaves_get] using salted_completeness hashFn salts leaves idx

/-- **Multi-opening deterministic uniqueness for honest salted trees.** Every accepting salted
opening in a finite list, checked against the honest salted root with the honest path for its index,
reveals the honest salt and leaf value at that index.

This is the salted analogue of `multi_instance_extracted_leaves_unique`; it is still a deterministic
no-collision statement, not the probabilistic random-oracle binding theorem. -/
theorem multi_salted_openings_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s)
    (openings : List ((_ : SkeletonLeafIndex s) × α × α))
    (hver : ∀ o ∈ openings,
      getPutativeRootWithHash o.1 (leafCommit hashFn o.2.1 o.2.2)
        (generateProof (buildSaltedTree hashFn salts leaves) o.1) hashFn
        = (buildSaltedTree hashFn salts leaves).getRootValue) :
    ∀ o ∈ openings, o.2.1 = salts.get o.1 ∧ o.2.2 = leaves.get o.1 := by
  intro o ho
  exact salted_opening_unique_against_honest_tree hashFn hinj salts leaves o.1 o.2.1 o.2.2
    (hver o ho)

/-- The transcript an honest committer publishes when opening a set of indices: the salted root
together with, for each opened index, the salt, the underlying leaf, and the authentication path. -/
def openTranscript {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) :=
  let tree := buildSaltedTree hashFn salts leaves
  (tree.getRootValue,
    idxs.map (fun i => ⟨i, salts.get i, leaves.get i, generateProof tree i⟩))

/-- Project a salted opening transcript to the public opened payloads: index, salt, and leaf value.
The transcript root and authentication paths are intentionally discarded. -/
def openTranscriptPayloads {s : Skeleton}
    (transcript : α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)) :
    List (SkeletonLeafIndex s × α × α) :=
  transcript.2.map (fun o => (o.1, o.2.1, o.2.2.1))

@[simp] theorem openTranscriptPayloads_length {s : Skeleton}
    (transcript : α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)) :
    (openTranscriptPayloads transcript).length = transcript.2.length := by
  simp [openTranscriptPayloads]

/-- Projecting payloads back to their indices recovers the transcript-entry indices. -/
@[simp] theorem openTranscriptPayloads_indices {s : Skeleton}
    (transcript : α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)) :
    (openTranscriptPayloads transcript).map (fun payload => payload.1) =
      transcript.2.map (fun entry => entry.1) := by
  simp [openTranscriptPayloads, Function.comp_def]

/-- The honest salted transcript root is the root of the salted Merkle tree. -/
theorem openTranscript_root_eq {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscript hashFn salts leaves idxs).1 =
      (buildSaltedTree hashFn salts leaves).getRootValue := by
  simp [openTranscript]

/-- The honest salted transcript entries are exactly the requested indices mapped to their honest
salt, leaf value, and authentication path. -/
theorem openTranscript_entries_eq {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscript hashFn salts leaves idxs).2 =
      idxs.map
        (fun i =>
          ⟨i, salts.get i, leaves.get i,
            generateProof (buildSaltedTree hashFn salts leaves) i⟩) := by
  simp [openTranscript]

/-- The payload projection of an honest salted transcript is exactly the requested indices mapped
to their honest salt and leaf value. -/
theorem openTranscriptPayloads_openTranscript_eq {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    openTranscriptPayloads (openTranscript hashFn salts leaves idxs) =
      idxs.map (fun i => (i, salts.get i, leaves.get i)) := by
  simp [openTranscriptPayloads, openTranscript]

/-- Honest transcript payloads have one payload per requested index. -/
theorem openTranscriptPayloads_openTranscript_length {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscriptPayloads (openTranscript hashFn salts leaves idxs)).length = idxs.length := by
  simp [openTranscriptPayloads_openTranscript_eq]

/-- Projecting honest transcript payloads to indices recovers the requested index list. -/
theorem openTranscriptPayloads_openTranscript_indices {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscriptPayloads (openTranscript hashFn salts leaves idxs)).map
        (fun payload => payload.1) = idxs := by
  simp [openTranscriptPayloads_openTranscript_eq, Function.comp_def]

/-- Bounded lookup in the honest payload projection returns the requested index with its honest
salt and leaf value. -/
@[simp] theorem openTranscriptPayloads_openTranscript_getElem {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) (n : ℕ)
    (h : n < idxs.length) :
    (openTranscriptPayloads (openTranscript hashFn salts leaves idxs))[n]'(by
      rw [openTranscriptPayloads_openTranscript_length]
      exact h) =
      (idxs[n]'h, salts.get (idxs[n]'h), leaves.get (idxs[n]'h)) := by
  simp [openTranscriptPayloads_openTranscript_eq]

/-- Membership in the honest payload projection is exactly membership of the corresponding opened
index, paired with its honest salt and leaf value. -/
theorem openTranscriptPayloads_openTranscript_mem_iff {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (payload : SkeletonLeafIndex s × α × α) :
    payload ∈ openTranscriptPayloads (openTranscript hashFn salts leaves idxs) ↔
      ∃ i ∈ idxs, (i, salts.get i, leaves.get i) = payload := by
  rw [openTranscriptPayloads_openTranscript_eq]
  simp

/-- Every requested index contributes its honest salt and leaf to the honest payload projection. -/
theorem openTranscriptPayloads_openTranscript_mem {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (i : SkeletonLeafIndex s) (hi : i ∈ idxs) :
    (i, salts.get i, leaves.get i) ∈
      openTranscriptPayloads (openTranscript hashFn salts leaves idxs) := by
  rw [openTranscriptPayloads_openTranscript_mem_iff]
  exact ⟨i, hi, rfl⟩

/-- Every honest payload carries an index from the requested opened-index list. -/
theorem openTranscriptPayloads_openTranscript_index_mem {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ payload ∈ openTranscriptPayloads (openTranscript hashFn salts leaves idxs),
      payload.1 ∈ idxs := by
  intro payload hpayload
  rw [openTranscriptPayloads_openTranscript_mem_iff] at hpayload
  obtain ⟨i, hi, hpayload⟩ := hpayload
  subst payload
  exact hi

/-- Every honest payload carries the honest salt and leaf value for its own index. -/
theorem openTranscriptPayloads_openTranscript_eq_honest_pair {s : Skeleton}
    (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ payload ∈ openTranscriptPayloads (openTranscript hashFn salts leaves idxs),
      payload.2.1 = salts.get payload.1 ∧ payload.2.2 = leaves.get payload.1 := by
  intro payload hpayload
  rw [openTranscriptPayloads_openTranscript_mem_iff] at hpayload
  obtain ⟨i, _hi, hpayload⟩ := hpayload
  subst payload
  simp

/-- Universal quantification over honest payloads is the same as quantification over requested
indices with their honest salt and leaf values. -/
theorem openTranscriptPayloads_openTranscript_forall {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (P : SkeletonLeafIndex s × α × α → Prop) :
    (∀ payload ∈ openTranscriptPayloads (openTranscript hashFn salts leaves idxs), P payload) ↔
      ∀ i ∈ idxs, P (i, salts.get i, leaves.get i) := by
  rw [openTranscriptPayloads_openTranscript_eq]
  simp

/-- Existential quantification over honest payloads is the same as existence of a requested index
with its honest salt and leaf values. -/
theorem openTranscriptPayloads_openTranscript_exists {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (P : SkeletonLeafIndex s × α × α → Prop) :
    (∃ payload ∈ openTranscriptPayloads (openTranscript hashFn salts leaves idxs), P payload) ↔
      ∃ i ∈ idxs, P (i, salts.get i, leaves.get i) := by
  rw [openTranscriptPayloads_openTranscript_eq]
  simp

/-- Duplicate-free requested indices give duplicate-free honest transcript payloads. -/
theorem openTranscriptPayloads_openTranscript_nodup {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hidxs : idxs.Nodup) :
    (openTranscriptPayloads (openTranscript hashFn salts leaves idxs)).Nodup := by
  rw [openTranscriptPayloads_openTranscript_eq]
  exact hidxs.map (by
    intro i j h
    exact congrArg (fun payload => payload.1) h)

/-- If two leaf assignments agree on the requested opened indices under the same salts, then the
honest transcripts reveal the same opened payloads `(index, salt, value)`. This is the
deterministic payload projection used by hiding simulators; roots and authentication paths still
depend on the unopened leaves and are not compared here. -/
theorem openTranscript_entries_payload_eq_of_agree {s : Skeleton} (hashFn : α → α → α)
    (salts leaves₁ leaves₂ : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hagree : ∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) :
    ((openTranscript hashFn salts leaves₁ idxs).2.map
        (fun o => (o.1, o.2.1, o.2.2.1))) =
      ((openTranscript hashFn salts leaves₂ idxs).2.map
        (fun o => (o.1, o.2.1, o.2.2.1))) := by
  simp [openTranscript, Function.comp_def]
  exact hagree

/-- Named-payload form of `openTranscript_entries_payload_eq_of_agree`. -/
theorem openTranscriptPayloads_eq_of_agree {s : Skeleton} (hashFn : α → α → α)
    (salts leaves₁ leaves₂ : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hagree : ∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) :
    openTranscriptPayloads (openTranscript hashFn salts leaves₁ idxs) =
      openTranscriptPayloads (openTranscript hashFn salts leaves₂ idxs) := by
  simpa [openTranscriptPayloads] using
    openTranscript_entries_payload_eq_of_agree hashFn salts leaves₁ leaves₂ idxs hagree

/-- If two salt assignments and two leaf assignments agree on the requested opened indices, then
the honest transcripts reveal the same opened payloads `(index, salt, value)`. Roots and
authentication paths are still intentionally not compared, since they may depend on unopened
leaves or salts. -/
theorem openTranscript_entries_payload_eq_of_agree_on_opened {s : Skeleton}
    (hashFn : α → α → α)
    (salts₁ salts₂ leaves₁ leaves₂ : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hsalts : ∀ i ∈ idxs, salts₁.get i = salts₂.get i)
    (hleaves : ∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) :
    ((openTranscript hashFn salts₁ leaves₁ idxs).2.map
        (fun o => (o.1, o.2.1, o.2.2.1))) =
      ((openTranscript hashFn salts₂ leaves₂ idxs).2.map
        (fun o => (o.1, o.2.1, o.2.2.1))) := by
  simp [openTranscript, Function.comp_def]
  intro i hi
  exact ⟨hsalts i hi, hleaves i hi⟩

/-- Named-payload form of `openTranscript_entries_payload_eq_of_agree_on_opened`. -/
theorem openTranscriptPayloads_eq_of_agree_on_opened {s : Skeleton}
    (hashFn : α → α → α)
    (salts₁ salts₂ leaves₁ leaves₂ : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hsalts : ∀ i ∈ idxs, salts₁.get i = salts₂.get i)
    (hleaves : ∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) :
    openTranscriptPayloads (openTranscript hashFn salts₁ leaves₁ idxs) =
      openTranscriptPayloads (openTranscript hashFn salts₂ leaves₂ idxs) := by
  simpa [openTranscriptPayloads] using
    openTranscript_entries_payload_eq_of_agree_on_opened hashFn salts₁ salts₂ leaves₁ leaves₂
      idxs hsalts hleaves

/-- The honest salted transcript emits exactly one opening entry for each requested index. -/
theorem openTranscript_entries_length {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscript hashFn salts leaves idxs).2.length = idxs.length := by
  simp [openTranscript]

/-- Projecting honest salted transcript entries to their indices recovers the requested index list.
This names the basic transcript-shape invariant used by simulators and deterministic extractors. -/
theorem openTranscript_entries_indices {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ((openTranscript hashFn salts leaves idxs).2.map (fun o => o.1)) = idxs := by
  simp [openTranscript, Function.comp_def]

/-- If the requested opened indices are duplicate-free, then the honest salted transcript entries
are duplicate-free too. This is transcript-shape bookkeeping for simulator/extractor arguments:
each entry carries its requested index as the first field. -/
theorem openTranscript_entries_nodup {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hidxs : idxs.Nodup) :
    (openTranscript hashFn salts leaves idxs).2.Nodup := by
  simpa [openTranscript] using hidxs.map (by
    intro i j h
    exact congrArg (fun o => o.1) h)

/-- Every opening emitted by the honest salted transcript carries the honest salt and leaf value
for its own index. This exposes the transcript data invariant used by deterministic extraction and
future simulator/hybrid arguments. -/
theorem openTranscript_entry_eq_honest_pair {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ o ∈ (openTranscript hashFn salts leaves idxs).2,
      o.2.1 = salts.get o.1 ∧ o.2.2.1 = leaves.get o.1 := by
  intro o ho
  simp [openTranscript] at ho ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  simp

/-- Every opening emitted by the honest salted transcript carries the honest authentication path
for its own index. This completes the transcript-shape invariants for index, salt/value, and path
fields. -/
theorem openTranscript_entry_path_eq_honest_proof {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ o ∈ (openTranscript hashFn salts leaves idxs).2,
      o.2.2.2 = generateProof (buildSaltedTree hashFn salts leaves) o.1 := by
  intro o ho
  simp [openTranscript] at ho ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  simp

/-- Every opening emitted by the honest salted transcript verifies against the transcript root. This
is the list-level packaging of `salted_completeness` used by future simulator/hybrid arguments. -/
theorem openTranscript_entry_verifies {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ o ∈ (openTranscript hashFn salts leaves idxs).2,
      getPutativeRootWithHash o.1 (leafCommit hashFn o.2.1 o.2.2.1) o.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1 := by
  intro o ho
  simp [openTranscript] at ho ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  simpa [saltedLeaves_get] using salted_completeness hashFn salts leaves i

/-- Any candidate salted pair that verifies against the transcript root using an honest transcript
entry's path equals the pair carried by that entry. This packages deterministic extraction for
individual entries of `openTranscript`. -/
theorem openTranscript_entry_unique_against_candidate {s : Skeleton} (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (o : (i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)
    (ho : o ∈ (openTranscript hashFn salts leaves idxs).2)
    (salt value : α)
    (h : getPutativeRootWithHash o.1 (leafCommit hashFn salt value) o.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    salt = o.2.1 ∧ value = o.2.2.1 := by
  simp [openTranscript] at ho h ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  exact salted_opening_unique_against_honest_tree hashFn hinj salts leaves i salt value (by
    simpa [openTranscript] using h)

/-- Any candidate salted pair that verifies against an honest transcript entry's path equals the
honest salt and leaf at that entry's index. This is the transcript-facing form of
`salted_opening_unique_against_honest_tree`, useful for deterministic extraction statements that
want the honest tree values rather than the pair stored in the transcript entry. -/
theorem openTranscript_candidate_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (o : (i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)
    (ho : o ∈ (openTranscript hashFn salts leaves idxs).2)
    (salt value : α)
    (h : getPutativeRootWithHash o.1 (leafCommit hashFn salt value) o.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    salt = salts.get o.1 ∧ value = leaves.get o.1 := by
  simp [openTranscript] at ho h ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  exact salted_opening_unique_against_honest_tree hashFn hinj salts leaves i salt value (by
    simpa [openTranscript] using h)

/-- Batch transcript-entry deterministic extraction. For any finite list of candidate salted
opening pairs attached to honest transcript entries, if each candidate verifies against the honest
transcript root using the attached path, then every candidate pair equals the salt and leaf pair
stored in that transcript entry. -/
theorem openTranscript_candidates_unique_against_entries {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (attempts :
      List (((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) × α × α))
    (hmem : ∀ a ∈ attempts, a.1 ∈ (openTranscript hashFn salts leaves idxs).2)
    (hver : ∀ a ∈ attempts,
      getPutativeRootWithHash a.1.1 (leafCommit hashFn a.2.1 a.2.2) a.1.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    ∀ a ∈ attempts, a.2.1 = a.1.2.1 ∧ a.2.2 = a.1.2.2.1 := by
  intro a ha
  exact openTranscript_entry_unique_against_candidate hashFn hinj salts leaves idxs
    a.1 (hmem a ha) a.2.1 a.2.2 (hver a ha)

/-- Batch transcript-facing deterministic extraction. For any finite list of candidate salted
opening pairs attached to honest transcript entries, if each candidate verifies against the honest
transcript root using the attached path, then every candidate pair is the honest salt and leaf at
that entry's index. -/
theorem openTranscript_candidates_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (attempts :
      List (((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) × α × α))
    (hmem : ∀ a ∈ attempts, a.1 ∈ (openTranscript hashFn salts leaves idxs).2)
    (hver : ∀ a ∈ attempts,
      getPutativeRootWithHash a.1.1 (leafCommit hashFn a.2.1 a.2.2) a.1.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    ∀ a ∈ attempts, a.2.1 = salts.get a.1.1 ∧ a.2.2 = leaves.get a.1.1 := by
  intro a ha
  exact openTranscript_candidate_unique_against_honest_tree hashFn hinj salts leaves idxs
    a.1 (hmem a ha) a.2.1 a.2.2 (hver a ha)

section HidingDefinition

variable [DecidableEq α] [SampleableType α]

/-- **Hiding (indistinguishability definition, SNARGs book §18).** A salted Merkle commitment is
hiding for a fixed opened index set `idxs` if, for *any* two leaf assignments `leaves₁`, `leaves₂`
that agree on the opened positions, the transcript experiments over the salt sampler `sampleSalts`
coincide.

**Caveat: this is program equality, not distribution equality.** The two sides are compared as raw
`OracleComp (spec α)` terms, which is strictly stronger than equality of their output laws. The
perfect-distribution hiding notion is `DistHiding` (output-law equality), implied by this one via
`Hiding.distHiding`. A computational version would further replace `=` by an
indistinguishability relation.

The simulator/hybrid theorem below discharges this predicate from a real-to-simulator program
equality premise. -/
def Hiding {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) : Prop :=
  ∀ (leaves₁ leaves₂ : LeafData α s),
    (∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) →
    (sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves₁ idxs))
      = (sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves₂ idxs))

end HidingDefinition

section HidingSimulator

/-- Replace every unopened leaf by a fixed filler value, preserving only the leaves selected by
`opened`. This is the leaf assignment consumed by the hiding simulator: it depends on the real
witness only through the public opened positions. The predicate form avoids requiring decidable
equality for `SkeletonLeafIndex`. -/
noncomputable def openedLeafData {s : Skeleton} (filler : α)
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (leaves : LeafData α s) : LeafData α s :=
  LeafData.ofFun s fun idx => if opened idx then leaves.get idx else filler

@[simp]
theorem openedLeafData_get {s : Skeleton} (filler : α)
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    (openedLeafData filler opened leaves).get idx =
      if opened idx then leaves.get idx else filler := by
  simp [openedLeafData]

/-- The simulator's leaf assignment is insensitive to unopened leaves. If two leaf trees agree on
the opened predicate, replacing all unopened leaves by `filler` produces the same tree. -/
theorem openedLeafData_eq_of_agree {s : Skeleton} (filler : α)
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (leaves₁ leaves₂ : LeafData α s)
    (hagree : ∀ i, opened i → leaves₁.get i = leaves₂.get i) :
    openedLeafData filler opened leaves₁ = openedLeafData filler opened leaves₂ := by
  apply (LeafData.equivIndexFun s).injective
  funext idx
  change (openedLeafData filler opened leaves₁).get idx =
    (openedLeafData filler opened leaves₂).get idx
  by_cases hidx : opened idx
  · rw [openedLeafData_get, openedLeafData_get]
    simp only [hidx, ite_true]
    exact hagree idx hidx
  · rw [openedLeafData_get, openedLeafData_get]
    simp only [hidx, ite_false]

/-- **Salted Merkle hiding simulator.** Given only the opened leaves (represented by
`openedLeaves`) and public parameters, fill every unopened position with `filler`, sample the salts,
and emit the ordinary honest transcript for that hybrid leaf assignment.

The theorem `simulatorTranscript_eq_of_agree` below formalizes that this simulator depends on its
leaf input only through the opened positions. -/
noncomputable def simulatorTranscript {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) (filler : α)
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (openedLeaves : LeafData α s) :
    OracleComp (spec α)
      (α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)) :=
  sampleSalts >>= fun salts =>
    pure (openTranscript hashFn salts (openedLeafData filler opened openedLeaves) idxs)

/-- The simulator program (hence also its output distribution) is identical for any two witnesses
that agree on the opened positions; this is the formal "simulator uses only opened leaves"
statement. -/
theorem simulatorTranscript_eq_of_agree {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) (filler : α)
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (leaves₁ leaves₂ : LeafData α s)
    (hagree : ∀ i, opened i → leaves₁.get i = leaves₂.get i) :
    simulatorTranscript hashFn sampleSalts idxs filler opened leaves₁ =
      simulatorTranscript hashFn sampleSalts idxs filler opened leaves₂ := by
  unfold simulatorTranscript
  rw [openedLeafData_eq_of_agree filler opened leaves₁ leaves₂ hagree]

/-- Real salted transcript experiment, factored out to keep the simulator/hybrid theorem
readable. -/
def realTranscriptExperiment {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) (leaves : LeafData α s) :
    OracleComp (spec α)
      (α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)) :=
  sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves idxs)

/-- Simulation-based hiding premise for salted Merkle transcripts, **program-equality form**.
There is a fixed filler such that every real transcript experiment equals, as a raw
`OracleComp (spec α)` term, the simulator experiment for the opened-only leaf assignment. This is
stronger than equality of output distributions; the distributional premise is
`DistSimulationBasedHiding`, implied via `SimulationBasedHiding.dist`. The salted-leaf
hybrid/programming argument that would discharge either premise is not formalized here. -/
def SimulationBasedHiding {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s))
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened] : Prop :=
  ∃ filler : α, ∀ leaves : LeafData α s,
    realTranscriptExperiment hashFn sampleSalts idxs leaves =
      simulatorTranscript hashFn sampleSalts idxs filler opened leaves

/-- **Hybrid discharge of `Hiding`.** If real transcript programs are equal to the opened-leaf
simulator program for every witness, then the two real transcript programs for any pair of
witnesses that agree on opened positions are equal. This is the formal simulator + hybrid argument
needed to connect the construction to the existing `Hiding` predicate. -/
theorem simulationBasedHiding_implies_Hiding {s : Skeleton}
    (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s))
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (hopened_subset : ∀ i, opened i → i ∈ idxs)
    (hsim : SimulationBasedHiding hashFn sampleSalts idxs opened) :
    Hiding hashFn sampleSalts idxs := by
  rcases hsim with ⟨filler, hreal_to_sim⟩
  intro leaves₁ leaves₂ hagree
  change realTranscriptExperiment hashFn sampleSalts idxs leaves₁ =
    realTranscriptExperiment hashFn sampleSalts idxs leaves₂
  rw [hreal_to_sim leaves₁, hreal_to_sim leaves₂]
  exact simulatorTranscript_eq_of_agree hashFn sampleSalts idxs filler opened leaves₁ leaves₂
    (fun i hi => hagree i (hopened_subset i hi))

end HidingSimulator

section HidingOutputLaw

open MeasureTheory

variable [UniformAnswerMeasure (spec α)]

/-- The output law of an oracle computation over `spec α`: its `evalDist` measure with the
discrete σ-algebra on the result type, under the chosen `UniformAnswerMeasure (spec α)`
interpretation (each query is answered by a fresh independent uniform value; no shared cache). -/
noncomputable def outputLaw {β : Type _} (mx : OracleComp (spec α) β) : @Measure β ⊤ :=
  @evalDist (OracleComp (spec α)) _ β ⊤ mx

/-- **Perfect distributional hiding (output-law form).** For any two leaf assignments agreeing
on the opened positions, the real transcript experiments have the same output law. This is the
perfect-hiding notion that `Hiding` describes; unlike `Hiding` it does not compare programs. -/
def DistHiding {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) : Prop :=
  ∀ (leaves₁ leaves₂ : LeafData α s),
    (∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) →
    outputLaw (realTranscriptExperiment hashFn sampleSalts idxs leaves₁) =
      outputLaw (realTranscriptExperiment hashFn sampleSalts idxs leaves₂)

/-- Program-equality hiding implies output-law hiding. -/
theorem Hiding.distHiding [DecidableEq α] [SampleableType α] {s : Skeleton}
    {hashFn : α → α → α} {sampleSalts : OracleComp (spec α) (LeafData α s)}
    {idxs : List (SkeletonLeafIndex s)} (h : Hiding hashFn sampleSalts idxs) :
    DistHiding hashFn sampleSalts idxs := fun leaves₁ leaves₂ hagree =>
  congrArg outputLaw (h leaves₁ leaves₂ hagree)

/-- Simulation-based hiding premise, **output-law form**: there is a filler such that every real
transcript experiment has the same output law as the opened-leaf simulator. -/
def DistSimulationBasedHiding {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s))
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened] : Prop :=
  ∃ filler : α, ∀ leaves : LeafData α s,
    outputLaw (realTranscriptExperiment hashFn sampleSalts idxs leaves) =
      outputLaw (simulatorTranscript hashFn sampleSalts idxs filler opened leaves)

/-- The program-equality simulation premise implies the output-law one. -/
theorem SimulationBasedHiding.dist {s : Skeleton} {hashFn : α → α → α}
    {sampleSalts : OracleComp (spec α) (LeafData α s)}
    {idxs : List (SkeletonLeafIndex s)}
    {opened : SkeletonLeafIndex s → Prop} [DecidablePred opened]
    (h : SimulationBasedHiding hashFn sampleSalts idxs opened) :
    DistSimulationBasedHiding hashFn sampleSalts idxs opened := by
  rcases h with ⟨filler, hsim⟩
  exact ⟨filler, fun leaves => congrArg outputLaw (hsim leaves)⟩

/-- **Hybrid discharge of `DistHiding`.** If every real transcript has the same output law as the
opened-leaf simulator, then any two witnesses agreeing on opened positions (with `opened ⊆ idxs`)
give real transcripts with the same output law. -/
theorem distSimulationBasedHiding_implies_DistHiding {s : Skeleton}
    (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s))
    (opened : SkeletonLeafIndex s → Prop) [DecidablePred opened]
    (hopened_subset : ∀ i, opened i → i ∈ idxs)
    (hsim : DistSimulationBasedHiding hashFn sampleSalts idxs opened) :
    DistHiding hashFn sampleSalts idxs := by
  rcases hsim with ⟨filler, hreal_to_sim⟩
  intro leaves₁ leaves₂ hagree
  rw [hreal_to_sim leaves₁, hreal_to_sim leaves₂,
    simulatorTranscript_eq_of_agree hashFn sampleSalts idxs filler opened leaves₁ leaves₂
      (fun i hi => hagree i (hopened_subset i hi))]

/-- Prefixing the salt sampler with a discarded computation does not change the output law of a
real transcript experiment (it does change the program). -/
theorem outputLaw_realTranscriptExperiment_resample_prefix {s : Skeleton} {γ : Type _}
    (hashFn : α → α → α) (pre : OracleComp (spec α) γ)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) (leaves : LeafData α s) :
    outputLaw (realTranscriptExperiment hashFn (pre >>= fun _ => sampleSalts) idxs leaves) =
      outputLaw (realTranscriptExperiment hashFn sampleSalts idxs leaves) := by
  unfold outputLaw realTranscriptExperiment
  rw [bind_assoc]
  let : MeasurableSpace
      (α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)) := ⊤
  exact OracleComp.evalDist_bind_const pre _

/-- **Resampling example accepted by the distributional predicate.** `DistHiding` is invariant
under prefixing the salt sampler with any discarded computation `pre` (for instance, an extra
independent salt draw that is thrown away): the two samplers are different programs with the same
output law. -/
theorem distHiding_resample_prefix {s : Skeleton} {γ : Type _}
    (hashFn : α → α → α) (pre : OracleComp (spec α) γ)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) :
    DistHiding hashFn (pre >>= fun _ => sampleSalts) idxs ↔
      DistHiding hashFn sampleSalts idxs := by
  unfold DistHiding
  simp only [outputLaw_realTranscriptExperiment_resample_prefix]

/-- Concrete instance: if `sampleSalts` satisfies program-equality `Hiding`, then the resampled
sampler `pre >>= fun _ => sampleSalts` satisfies the distributional `DistHiding`, even though no
program-equality `Hiding` statement for the resampled sampler is derived here. -/
theorem Hiding.distHiding_resample_prefix [DecidableEq α] [SampleableType α]
    {s : Skeleton} {γ : Type _} {hashFn : α → α → α} (pre : OracleComp (spec α) γ)
    {sampleSalts : OracleComp (spec α) (LeafData α s)}
    {idxs : List (SkeletonLeafIndex s)} (h : Hiding hashFn sampleSalts idxs) :
    DistHiding hashFn (pre >>= fun _ => sampleSalts) idxs :=
  (InductiveMerkleTree.distHiding_resample_prefix hashFn pre sampleSalts idxs).2 h.distHiding

end HidingOutputLaw

end InductiveMerkleTree

/-! ### Axiom audit (issue #119 salted Merkle construction / hiding-definition front doors) -/

#print axioms InductiveMerkleTree.saltedLeaves_get
#print axioms InductiveMerkleTree.salted_completeness
#print axioms InductiveMerkleTree.salted_opening_binding_value
#print axioms InductiveMerkleTree.salted_opening_binding_pair
#print axioms InductiveMerkleTree.salted_opening_binding_pair_of_queryInjectiveOn
#print axioms InductiveMerkleTree.salted_opening_unique_against_honest_tree
#print axioms InductiveMerkleTree.multi_salted_openings_unique_against_honest_tree
#print axioms InductiveMerkleTree.openTranscript
#print axioms InductiveMerkleTree.openTranscriptPayloads
#print axioms InductiveMerkleTree.openTranscriptPayloads_length
#print axioms InductiveMerkleTree.openTranscriptPayloads_indices
#print axioms InductiveMerkleTree.openTranscript_root_eq
#print axioms InductiveMerkleTree.openTranscript_entries_eq
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_eq
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_length
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_indices
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_getElem
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_mem_iff
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_mem
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_index_mem
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_eq_honest_pair
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_forall
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_exists
#print axioms InductiveMerkleTree.openTranscriptPayloads_openTranscript_nodup
#print axioms InductiveMerkleTree.openTranscript_entries_payload_eq_of_agree
#print axioms InductiveMerkleTree.openTranscriptPayloads_eq_of_agree
#print axioms InductiveMerkleTree.openTranscript_entries_payload_eq_of_agree_on_opened
#print axioms InductiveMerkleTree.openTranscriptPayloads_eq_of_agree_on_opened
#print axioms InductiveMerkleTree.openTranscript_entries_length
#print axioms InductiveMerkleTree.openTranscript_entries_indices
#print axioms InductiveMerkleTree.openTranscript_entries_nodup
#print axioms InductiveMerkleTree.openTranscript_entry_eq_honest_pair
#print axioms InductiveMerkleTree.openTranscript_entry_path_eq_honest_proof
#print axioms InductiveMerkleTree.openTranscript_entry_verifies
#print axioms InductiveMerkleTree.openTranscript_entry_unique_against_candidate
#print axioms InductiveMerkleTree.openTranscript_candidate_unique_against_honest_tree
#print axioms InductiveMerkleTree.openTranscript_candidates_unique_against_entries
#print axioms InductiveMerkleTree.openTranscript_candidates_unique_against_honest_tree
#print axioms InductiveMerkleTree.Hiding
#print axioms InductiveMerkleTree.openedLeafData_eq_of_agree
#print axioms InductiveMerkleTree.simulatorTranscript_eq_of_agree
#print axioms InductiveMerkleTree.simulationBasedHiding_implies_Hiding
#print axioms InductiveMerkleTree.Hiding.distHiding
#print axioms InductiveMerkleTree.SimulationBasedHiding.dist
#print axioms InductiveMerkleTree.distSimulationBasedHiding_implies_DistHiding
#print axioms InductiveMerkleTree.outputLaw_realTranscriptExperiment_resample_prefix
#print axioms InductiveMerkleTree.distHiding_resample_prefix
#print axioms InductiveMerkleTree.Hiding.distHiding_resample_prefix
