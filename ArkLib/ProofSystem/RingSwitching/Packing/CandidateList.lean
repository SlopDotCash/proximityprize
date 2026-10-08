/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Batching
import ArkLib.ToVCVio.EvalDist.ProbabilityBounds

/-!
# Batching a candidate list fixed before the challenge

Adapted from ArkLib PR #1289 at `2dcb25437a4b59e59b4434a2c6f802ca6008debc`.
The candidate list is chosen before sampling. Correct candidates are excluded
from the bad event; an adaptive list chosen after sampling is not covered.
-/
set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ProbabilityTheory
namespace RingSwitching.Packing.BatchingStrategy

/-- Some incorrect member of a pre-challenge list of size at most `L` collides
with probability at most `L` times the batching strategy's separation error. -/
theorem separates_finset {P W : Type} [CommRing P] [Fintype W] (bat : BatchingStrategy P W)
    (s : W → P) (S : Finset (W → P)) {L : ℕ} (hS : S.card ≤ L) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ s' ∈ S, s' ≠ s ∧
      ∑ u, bat.weight c u * s' u = ∑ u, bat.weight c u * s u] ≤ L * (bat.error : ℝ≥0∞) :=
  prEvent_exists_mem_and_le_mul ($ᵗ bat.Challenge) (fun s' => s' ≠ s)
    (fun s' c => ∑ u, bat.weight c u * s' u = ∑ u, bat.weight c u * s u) S
    (fun s' _ hne => bat.separates s' s hne) hS

end RingSwitching.Packing.BatchingStrategy
end
