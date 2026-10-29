/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio
import VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability

/-!
# Position binding / collision core for inductive Merkle trees (towards extractability)

This file develops the *deterministic, collision-free core* of Merkle-tree extractability and
position binding, building on the VCVio inductive Merkle tree definitions
(`VCVio.CryptoFoundations.MerkleTree.Inductive`).

The VCVio package proves single-index *completeness* and now also exposes the random-oracle
extractability theorem from SNARGs §18.5. This file keeps ArkLib's deterministic,
function-facing API and adds an ArkLib-facing bridge to the upstream probabilistic theorem:

* `getPutativeRootWithHash_injective_of_hash_injective` — the **collision lemma** (SNARGs §18.3):
  if the compression function is injective, the leaf value is uniquely determined by an opening
  (index + sibling path) and the recomputed root.
* `opening_binding` — **single-instance position binding**: two openings of the *same* index with
  the *same* sibling path that verify against the *same* root must open to the *same* leaf, whenever
  the hash function is collision-free. This is the deterministic heart of single-instance
  extractability.
* `extractLeaf` / `extractLeaf_eq_opened` — a concrete extractor reading the committed leaf from
  the data tree, with the consistency lemma that it agrees with the leaf carried by an honest
  opening.

## Random-oracle bridge

The theorem `randomOracle_extractability_rom_bound` below re-exports the upstream VCVio
query-log extractor and birthday-bound result in ArkLib's Merkle namespace. For any bounded
two-phase adversary, the probability of accepting an opening that disagrees with the extractor is
bounded by the canonical stopping-time numerator divided by `|α|`. The experiment uses the current
shared-cache random-oracle semantics; its sampling law is explicit in `UniformAnswerMeasure`.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/-- **Collision lemma** (SNARGs book §18.3), deterministic form: if the compression function
`hashFn` is injective (collision-free), then the recomputed root `getPutativeRootWithHash` is
injective in the leaf value for a fixed index and sibling path. Equivalently: a leaf is uniquely
pinned down by its authentication path and the root it produces. -/
theorem getPutativeRootWithHash_injective_of_hash_injective {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (leaf1 leaf2 : α) (proof : List.Vector α idx.depth)
    (h : getPutativeRootWithHash idx leaf1 proof hashFn
        = getPutativeRootWithHash idx leaf2 proof hashFn) :
    leaf1 = leaf2 := by
  induction idx generalizing leaf1 leaf2 with
  | ofLeaf => simpa [getPutativeRootWithHash] using h
  | ofLeft idxLeft ih =>
    simp only [getPutativeRootWithHash] at h
    exact ih leaf1 leaf2 proof.tail (hinj _ _ _ _ h).1
  | ofRight idxRight ih =>
    simp only [getPutativeRootWithHash] at h
    exact ih leaf1 leaf2 proof.tail (hinj _ _ _ _ h).2

/-- **Single-instance position binding.** If the compression function is collision-free, two
openings of the same index `idx` sharing the same sibling path `proof` and both verifying against
the same `rootValue` must open to the same leaf. This is the deterministic core of single-instance
extractability: an accepting opening determines its leaf. -/
theorem opening_binding {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (leaf1 leaf2 rootValue : α) (proof : List.Vector α idx.depth)
    (h1 : getPutativeRootWithHash idx leaf1 proof hashFn = rootValue)
    (h2 : getPutativeRootWithHash idx leaf2 proof hashFn = rootValue) :
    leaf1 = leaf2 :=
  getPutativeRootWithHash_injective_of_hash_injective idx hashFn hinj leaf1 leaf2 proof
    (h1.trans h2.symm)

/-- A concrete extractor: from the committed leaf-data tree, the extracted leaf value at an index
is simply the value stored there. (The honest committer's data *is* the committed data.) -/
def extractLeaf {s : Skeleton} (leaf_data_tree : LeafData α s)
    (idx : SkeletonLeafIndex s) : α :=
  leaf_data_tree.get idx

/-- **Extractor consistency** (honest case): the value recovered by `extractLeaf` from the data
tree is exactly the leaf value carried by the honestly generated opening at that index. -/
theorem extractLeaf_eq_opened {s : Skeleton} (leaf_data_tree : LeafData α s)
    (idx : SkeletonLeafIndex s) :
    extractLeaf leaf_data_tree idx = leaf_data_tree.get idx := rfl

/-- **Extractor soundness against binding.** If a leaf value `v` verifies (over a collision-free
hash) against the honest root with the honest sibling path at index `idx`, then `v` equals the
extracted committed leaf. Thus any accepting opening must open to the committed value — there is no
way to open the same index to a different leaf without finding a hash collision. -/
theorem extracted_leaf_unique {s : Skeleton}
    (leaf_data_tree : LeafData α s) (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (v : α)
    (hv : getPutativeRootWithHash idx v
        (generateProof (buildMerkleTreeWithHash leaf_data_tree hashFn) idx) hashFn
        = (buildMerkleTreeWithHash leaf_data_tree hashFn).getRootValue) :
    v = extractLeaf leaf_data_tree idx := by
  apply opening_binding idx hashFn hinj v (leaf_data_tree.get idx)
    ((buildMerkleTreeWithHash leaf_data_tree hashFn).getRootValue)
    (generateProof (buildMerkleTreeWithHash leaf_data_tree hashFn) idx) hv
  exact functional_completeness idx leaf_data_tree hashFn

/-- **Multi-instance extractability core.** Given a list of openings — each an index, a claimed
leaf value, and the honest sibling path for that index — that all verify against the honest root of
a single committed tree, every claimed leaf equals the committed (extracted) leaf at its index,
provided the hash is collision-free. A multi-instance adversary cannot open *any* of the requested
positions to anything other than the committed value. -/
theorem multi_instance_extracted_leaves_unique {s : Skeleton}
    (leaf_data_tree : LeafData α s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (openings : List ((_ : SkeletonLeafIndex s) × α))
    (hver : ∀ o ∈ openings,
      getPutativeRootWithHash o.1 o.2
        (generateProof (buildMerkleTreeWithHash leaf_data_tree hashFn) o.1) hashFn
        = (buildMerkleTreeWithHash leaf_data_tree hashFn).getRootValue) :
    ∀ o ∈ openings, o.2 = extractLeaf leaf_data_tree o.1 := by
  intro o ho
  exact extracted_leaf_unique leaf_data_tree o.1 hashFn hinj o.2 (hver o ho)

section RandomOracleBinding

/-- **Random-oracle Merkle extractability / probabilistic binding bound.**

This is the ArkLib-facing form of VCVio's SNARGs §18.5 theorem. A two-phase adversary first
commits to a claimed root, then opens one position. If the combined adversary has total query bound
`qb`, the probability that verification accepts while the query-log extractor disagrees with the
opened `(leaf, proof)` pair is bounded by the current stopping-time error numerator:

`extractabilityROMErrorNumerator s qb / |α|`.

The upstream `extractability_rom_bound_quadratic` gives a birthday-shaped specialization under
its explicit query-dominance and depth hypotheses. This general wrapper does not assume them. -/
theorem randomOracle_extractability_rom_bound [DecidableEq α] [Fintype α]
    [UniformAnswerMeasure (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h_IsQueryBound_qb : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr{let z ← extractabilityExperiment 𝒜}[OpeningExtractionFailure z] ≤
      (extractabilityROMErrorNumerator s qb : ENNReal) *
        (Fintype.card α : ENNReal)⁻¹ :=
  extractability_rom_bound 𝒜 qb h_IsQueryBound_qb

/-- The former birthday-plus-guessing numerical expression is a valid corollary for the current
ROM experiment under the canonical query-dominance and depth conditions. This does not restore
the retired unconditional wrapper or its former probability experiment. -/
theorem randomOracle_extractability_rom_birthday_bound [DecidableEq α] [Fintype α]
    [UniformAnswerMeasure (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hdominance : 2 * (2 * s.leafCount - 1) + 1 ≤ qb)
    (hdepth : 2 * (2 * s.leafCount - 1) * s.depth ≤ qb) :
    Pr{let z ← extractabilityExperiment 𝒜}[OpeningExtractionFailure z] ≤
      (((qb + s.depth : ℕ) : ENNReal) ^ 2) / (2 * Fintype.card α)
        + 1 / (Fintype.card α) := by
  have hbudget : (qb : ENNReal) ≤ ((qb + s.depth : ℕ) : ENNReal) := by
    exact_mod_cast Nat.le_add_right qb s.depth
  have hnum := pow_le_pow_left' hbudget 2
  calc
    _ ≤ (qb : ENNReal) ^ 2 / (2 * Fintype.card α) :=
      extractability_rom_bound_quadratic 𝒜 qb h hdominance hdepth
    _ ≤ (((qb + s.depth : ℕ) : ENNReal) ^ 2) / (2 * Fintype.card α) :=
      mul_le_mul hnum le_rfl zero_le zero_le
    _ ≤ _ := le_add_of_nonneg_right zero_le

end RandomOracleBinding

end InductiveMerkleTree

/-! ### Axiom audit (issue #119 deterministic Merkle binding/extraction core) -/

#print axioms InductiveMerkleTree.getPutativeRootWithHash_injective_of_hash_injective
#print axioms InductiveMerkleTree.opening_binding
#print axioms InductiveMerkleTree.extractLeaf_eq_opened
#print axioms InductiveMerkleTree.extracted_leaf_unique
#print axioms InductiveMerkleTree.multi_instance_extracted_leaves_unique
#print axioms InductiveMerkleTree.randomOracle_extractability_rom_bound
#print axioms InductiveMerkleTree.randomOracle_extractability_rom_birthday_bound
