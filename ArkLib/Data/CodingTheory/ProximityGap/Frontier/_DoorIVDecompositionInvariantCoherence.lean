/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Convex.StrictConvexSpace
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVComplexRayCoherence

/-!
# Door (iv): piece-decomposition coherence is partition-INVARIANT under common-ray terms

## Why this file exists (the named-but-unprobed surviving Lane-1 direction)

The raw index-2 coset-half split of the thin 2-power subgroup `μ_n` is *negation-stable*: every
nontrivial subgroup of the cyclic 2-group `μ_n` contains the unique order-2 element `-1 = g^{n/2}`,
so both half-period sums are real and the worst-frequency coherence
`ρ(b) = ‖Σ pieces‖ / Σ‖pieces‖` saturates to `1` on same-sign halves
(`DoorIVCosetHalfCoherence`, DISPROOF `door-iv-coset-half-degeneracy`). The recorded VERDICT there
was: *"Any surviving door-(iv) theorem must use a finer / NON-negation-stable decomposition or a
different arithmetic statistic of `{b·x^m}`; the two-half coherence by itself cannot be bounded
below 1."*

That surviving hope — "break the `x ↦ -x` symmetry of the partition to force GENUINELY COMPLEX
piece-sums, where `ρ < 1` is geometrically possible" — was the last unprobed Lane-1 lever. The
probes `scripts/probes/probe_dooriv_nonneg_split_coherence{,_b}.py` tested it directly in the prize
regime (PROPER thin `μ_n`, `n = 2^a`, `p ≡ 1 (mod n)`, `p ≫ n³`, NEVER `n = q-1`, exact `ℂ`):
contiguous arc splits (`ARC2/4/8`), non-contiguous splits (`BIT1`, gray-code), and an
asymmetric-cardinality split (`|P₀| = n/2 - 1`), at generic AND structured Fermat-type primes
(incl. `p = 65537 = F₄`, `v₂(p-1) = 16`). In EVERY case the worst-`b` coherence saturated to
`ρ = 1.000000`, with the slack `1 - ρ` at the numerical noise floor and NOT growing with `n` for any
split. Breaking the negation symmetry supplied no usable slack.

## The mechanism this file formalizes (the load-bearing reason)

The empirical saturation has a clean partition-independent cause: at the adversarial frequency the
underlying *period terms* `e_p(b·x)` already lie (up to the worst-case alignment) on a common
nonnegative ray, and **any** grouping of common-ray terms produces piece-sums that lie on that SAME
ray, so the grouped (multi-piece) coherence is `1` for EVERY partition — finer, coarser, contiguous,
non-contiguous, negation-stable or not. Hence "choose a cleverer / non-negation-stable partition" is
not a lever: partition choice is irrelevant once the terms co-ray at the worst `b`. A useful
Door-IV piece-split anti-concentration theorem must prove the *terms themselves* are not commonly
rayed at the adversarial `b` — which is exactly the original sup-norm (CORE) statement, not a new
handle.

No Gauss-period cancellation is claimed. These are partition-invariance / triangle-equality
bookkeeping lemmas for the localized Door-IV coherence object. CORE (`M ≤ C√(n log(p/n))`) stays open.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence

open ProximityGap.Frontier.DoorIVComplexRayCoherence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Common-ray terms group to common-ray pieces.**
If every term `f i` (over the whole index set `t`) lies on a common nonnegative ray `ℝ_{≥0} • u`,
then for any partition map `g : ι → κ` and any block `k`, the block-sum `Σ_{i ∈ t, g i = k} f i`
ALSO lies on that ray, with nonnegative scalar `Σ c i`. The partition is arbitrary; the ray is the
same. -/
theorem block_sum_common_ray {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (f : ι → E) (u : E) (c : ι → ℝ)
    (hf : ∀ i ∈ t, f i = c i • u) (hc : ∀ i ∈ t, 0 ≤ c i)
    (g : ι → κ) (k : κ) :
    (∑ i ∈ t.filter (fun i => g i = k), f i)
      = (∑ i ∈ t.filter (fun i => g i = k), c i) • u
    ∧ 0 ≤ (∑ i ∈ t.filter (fun i => g i = k), c i) := by
  refine ⟨?_, ?_⟩
  · calc
      (∑ i ∈ t.filter (fun i => g i = k), f i)
          = ∑ i ∈ t.filter (fun i => g i = k), c i • u := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hf i (Finset.mem_of_mem_filter i hi)
      _ = (∑ i ∈ t.filter (fun i => g i = k), c i) • u := by rw [Finset.sum_smul]
  · refine Finset.sum_nonneg ?_
    intro i hi
    exact hc i (Finset.mem_of_mem_filter i hi)

/-- **Partition-invariant saturation (the headline).**
Let the terms `f` over `t` lie on a common nonnegative ray with positive total mass, `u ≠ 0`. Then
for ANY partition `g : ι → κ` indexed by a block set `s` that covers `t` (every term's block is in
`s`), the resulting multi-piece coherence over the blocks equals `1`. The choice of partition —
arity, contiguity, or negation-symmetry — is irrelevant: subdividing common-ray terms never lowers
coherence below `1`. -/
theorem multiPieceNormCoherence_block_eq_one_of_common_ray {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) (u : E) (c : ι → ℝ)
    (hf : ∀ i ∈ t, f i = c i • u) (hc : ∀ i ∈ t, 0 ≤ c i)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s)
    (hmass : 0 < ∑ i ∈ t, c i) (hu : u ≠ 0) :
    multiPieceNormCoherence s (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) = 1 := by
  -- The block-sum vector field: A k := Σ_{i∈t, g i = k} f i.
  set A : κ → E := fun k => ∑ i ∈ t.filter (fun i => g i = k), f i with hA
  -- Block scalar field: d k := Σ_{i∈t, g i = k} c i; each block lies on ray u with scalar d k.
  set d : κ → ℝ := fun k => ∑ i ∈ t.filter (fun i => g i = k), c i with hd
  have hAk : ∀ k ∈ s, A k = d k • u := by
    intro k _; exact (block_sum_common_ray t f u c hf hc g k).1
  have hdk : ∀ k ∈ s, 0 ≤ d k := by
    intro k _; exact (block_sum_common_ray t f u c hf hc g k).2
  -- Total block mass equals total term mass (cover by blocks in s), hence positive.
  have hmass_blocks : (∑ k ∈ s, d k) = ∑ i ∈ t, c i := by
    have : (∑ k ∈ s, ∑ i ∈ t.filter (fun i => g i = k), c i) = ∑ i ∈ t, c i := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := g) (s := t) (t := s) hcover (fun i => c i)]
    simpa [hd] using this
  have hmass_pos : 0 < ∑ k ∈ s, d k := by rw [hmass_blocks]; exact hmass
  -- Apply the existing common-nonneg-ray saturation lemma to the block field.
  exact multiPieceNormCoherence_eq_one_of_common_nonneg_ray s A u d hAk hdk hmass_pos hu

/-- **Constraint lemma (the door-(iv) consequence).**
If, at the adversarial frequency, the underlying terms lie on a common nonnegative ray with positive
mass, then NO partition `g` — however clever, non-negation-stable, or finely refined — can certify a
strict coherence drop `≤ θ < 1`. The negation-stable degeneracy is not special to subgroup splits:
it is forced for every partition by term-level co-ray alignment. A useful piece-split
anti-concentration theorem must therefore break the common-ray alignment of the TERMS at the worst
`b` (the original sup-norm/CORE problem), not merely re-partition them. -/
theorem no_partition_beats_one_of_common_ray_terms {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) {θ : ℝ}
    (hθ : θ < 1)
    (hray : ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ t, f i = c i • u) ∧ (∀ i ∈ t, 0 ≤ c i) ∧
      0 < (∑ i ∈ t, c i) ∧ u ≠ 0)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s) :
    ¬ multiPieceNormCoherence s (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) ≤ θ := by
  rintro hcoh
  obtain ⟨u, c, hf, hc, hmass, hu⟩ := hray
  have hone : multiPieceNormCoherence s
      (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) = 1 :=
    multiPieceNormCoherence_block_eq_one_of_common_ray t s f u c hf hc g hcover hmass hu
  linarith

/-- **Epsilon-drop form.** Common-ray terms forbid any positive `1 - ε` piece-coherence saving for
every partition. -/
theorem common_ray_terms_no_partition_le_one_sub {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) {ε : ℝ}
    (hε : 0 < ε)
    (hray : ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ t, f i = c i • u) ∧ (∀ i ∈ t, 0 ≤ c i) ∧
      0 < (∑ i ∈ t, c i) ∧ u ≠ 0)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s) :
    ¬ multiPieceNormCoherence s (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) ≤ 1 - ε := by
  exact no_partition_beats_one_of_common_ray_terms t s f (sub_lt_self 1 hε) hray g hcover

end ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence

#print axioms ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.block_sum_common_ray
#print axioms ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.multiPieceNormCoherence_block_eq_one_of_common_ray
#print axioms ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.no_partition_beats_one_of_common_ray_terms
#print axioms ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.common_ray_terms_no_partition_le_one_sub
