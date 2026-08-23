/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LDFourRate
import ArkLib.Data.CodingTheory.EntropyVolumeBound

/-!
# Elias-volume upper certificates from q-entropy exponent inequalities (issue #102)

`ListEliasVolumeUpperCore C j ε*` (in `GrandChallengeLDFourRate.lean`) is the upper-side
list-decoding certificate `ε*·|F| < Vol_q(j/n, n) / q^(n−k)` used by the four-rate
faithful list-lattice frontier (`PostRIMListThresholdFrontier.hvol`). Discharging it
directly forces evaluating the raw binomial `hammingBallVolume` sum, which is intractable at
the abstract prize-rate instances.

This file supplies the missing **bridge brick**: the proven entropy/volume lower bound
`CodingTheory.hammingBallVolume_ge_qEntropy` (`Vol ≥ q^{n·H_q(j/n)}/(n+1)`, ABF26 Cor 3.8)
reduces `ListEliasVolumeUpperCore` to a single *checkable real exponent inequality*

  `ε*·q·(n+1) < q^{n·H_q(j/n) − (n−k)}`,

i.e. the Elias ceiling beats the budget once the entropy mass clears `(n−k) + log_q(ε*·q·(n+1))`.
The four-rate wrapper packages the per-rate form directly into the shape the frontier's
`hvol` field consumes, leaving only the per-rate entropy arithmetic to each instance.

Both declarations are `sorry`/`axiom`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

open scoped NNReal ENNReal

namespace ProximityGap

open ListDecodable GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Elias-volume upper certificate from a q-entropy exponent inequality.**
Reduces the abstract `ListEliasVolumeUpperCore` to a checkable real exponent inequality by
chaining the proven volume lower bound `hammingBallVolume_ge_qEntropy`. -/
theorem ListEliasVolumeUpperCore_of_qEntropy
    (C : Submodule F (ι → F)) (j : ℕ) (ε_star : ℝ≥0)
    (hq : 2 ≤ Fintype.card F) (hj0 : 0 < j) (hjn : j < Fintype.card ι)
    (hexp : (ε_star : ℝ) * (Fintype.card F : ℝ) * ((Fintype.card ι : ℝ) + 1)
        < (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
            * CodingTheory.qEntropy (Fintype.card F) ((j : ℝ) / (Fintype.card ι : ℝ))
            - ((Fintype.card ι : ℝ) - (Module.finrank F C : ℝ)))) :
    ListEliasVolumeUpperCore C j ε_star := by
  set q := Fintype.card F with hqdef
  set n := Fintype.card ι with hndef
  set k := Module.finrank F C with hkdef
  have hn0 : 0 < n := lt_trans hj0 hjn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hδeq : (((j : ℝ≥0) / (n : ℝ≥0) : ℝ≥0) : ℝ) = (j : ℝ) / (n : ℝ) := by push_cast; ring
  have hfloor : ⌊(((j : ℝ≥0) / (n : ℝ≥0) : ℝ≥0) : ℝ) * (n : ℝ)⌋₊ = j := by
    rw [hδeq, div_mul_cancel₀ (j : ℝ) (ne_of_gt hnR)]; exact Nat.floor_natCast j
  have hvol := CodingTheory.hammingBallVolume_ge_qEntropy (q := q) hq
    (((j : ℝ≥0) / (n : ℝ≥0) : ℝ≥0) : ℝ) n
    (by rw [hfloor]; exact hj0) (by rw [hfloor]; exact hjn)
  rw [hfloor] at hvol
  set Vol : ℝ := (CodingTheory.hammingBallVolume q (((j : ℝ≥0) / (n : ℝ≥0) : ℝ≥0) : ℝ) n : ℝ)
    with hVoldef
  set H : ℝ := CodingTheory.qEntropy q ((j : ℝ) / (n : ℝ)) with hHdef
  have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) := Real.rpow_pos_of_pos hqR _
  have hnp1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hexp2 : (ε_star : ℝ) * (q : ℝ) * ((n : ℝ) + 1) * (q : ℝ) ^ ((n : ℝ) - (k : ℝ))
      < (q : ℝ) ^ ((n : ℝ) * H) := by
    have h := hexp
    rw [Real.rpow_sub hqR] at h
    rw [lt_div_iff₀ hqpow_pos] at h
    exact h
  have hreal : (ε_star : ℝ) * (q : ℝ) < Vol / (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
    rw [lt_div_iff₀ hqpow_pos]
    nlinarith [hexp2, hvol, hnp1, hqpow_pos, mul_pos hnp1 hqpow_pos]
  have hreal_nonneg : (0 : ℝ) ≤ (ε_star : ℝ) * (q : ℝ) := by positivity
  unfold ListEliasVolumeUpperCore
  have hlhs : (ε_star : ENNReal) * (q : ENNReal)
      = ENNReal.ofReal ((ε_star : ℝ) * (q : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    · exact (ENNReal.ofReal_coe_nnreal).symm
    · exact (ENNReal.ofReal_natCast q).symm
  rw [hlhs]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hreal_nonneg hreal)).mpr hreal

/-- **Four-rate Elias-volume certificates from per-rate q-entropy exponent inequalities.**
Packages `ListEliasVolumeUpperCore_of_qEntropy` into the exact `∀ r : Fin 4` shape the
faithful list-lattice frontier's `hvol` field consumes (issue #102): each rate's abstract
Elias certificate follows from a per-rate entropy-exponent inequality. -/
theorem listEliasVolumeUpperCore_fourRate_of_qEntropy
    (domain : ι ↪ F) (τ_hi : Fin 4 → ℕ)
    (hq : 2 ≤ Fintype.card F)
    (hj0 : ∀ r : Fin 4, 0 < τ_hi r)
    (hjn : ∀ r : Fin 4, τ_hi r < Fintype.card ι)
    (hexp : ∀ r : Fin 4,
      (epsStar : ℝ) * (Fintype.card F : ℝ) * ((Fintype.card ι : ℝ) + 1)
        < (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
            * CodingTheory.qEntropy (Fintype.card F) ((τ_hi r : ℝ) / (Fintype.card ι : ℝ))
            - ((Fintype.card ι : ℝ)
              - (Module.finrank F
                  (ReedSolomon.code domain
                    ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Submodule F (ι → F)) : ℝ)))) :
    ∀ r : Fin 4,
      ListEliasVolumeUpperCore
        (ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
        (τ_hi r) epsStar := fun r =>
  ListEliasVolumeUpperCore_of_qEntropy _ (τ_hi r) epsStar hq (hj0 r) (hjn r) (hexp r)

end ProximityGap
