/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The pointwise representation-count route cannot beat the `8/3` energy exponent (#389)

`GVHBKEnergyReduction.lean` proves, from the Garcia–Voloch pointwise input
`GVRepBound G M` (`∀ t ≠ 0, repCount G t ≤ M`, with `M³ ≤ 64·|G|²` i.e. `M = 4·|G|^{2/3}`),
the energy bound `E(G) ≤ (1+M)·|G|²`, hence `E(G) ≲ |G|^{8/3}`.  The literature
(`HBKEnergySupplyBound.lean`, recorded as a named residual) gives the strictly stronger
`E(G) ≪ |G|^{5/2}` for proper subgroups, and a fresh literature sweep
(`docs/kb/deltastar-literature-findings-2026-06-13.md` §0.A) suggested the `5/2` follows
from "summing the `4·|G|^{2/3}` shifted-intersection bound over all shifts — no cube-root
loss".  **That derivation is invalid**, and this file proves it so, machine-checked.

The obstruction is information-theoretic, not about any particular subgroup (real
multiplicative subgroups genuinely have `E ≈ |G|^{5/2}`, *below* `8/3`).  The point is that
the pointwise hypotheses — `r i ≤ M` and `∑ r = S` (here `S = |G|²`) — are *by themselves*
consistent with an energy proxy `∑ r²` of order `M·S ≈ |G|^{8/3}`.  Concretely the
saturated profile (`S/M` slots at the cap `M`, one remainder slot) realizes

  `M·S − M² ≤ ∑ r² ≤ M·S`        (`pointwise_method_bound_tight`)

so the pointwise upper bound `M·S` is **tight up to an additive `M²` (lower order)**.  Any
energy bound proved using only the pointwise cap and the total mass is therefore `≥ M·S −
M² ≈ 4·|G|^{8/3}`, and cannot reach `|G|^{5/2}` (since `5/2 < 8/3`).  Reaching `5/2`
genuinely requires the deeper second-moment / sum-product input ([SV11] Thm 1.1;
`AddEnergyMulHomogeneous.lean` lands its honest first reduction `E ≪ |G|^{5/2} ⟸
N ≪ |G|^{3/2}`), **not** summing the cap — exactly as `GVHBKEnergyReduction.lean`'s own
docstring (lines 44–46) and `GVRepBoundFromEnergy.lean` ("no elementary proof") already
flag.  A `NoGo` brick in the project's documented-refutation convention.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.PointwiseEnergyCeilingNoGo

/-- The saturated shift-count profile witnessing tightness: `S / M` slots hold the cap `M`,
the final slot holds the remainder `S % M`.  Defined on all of `ℕ` (only `range (S/M+1)` is
summed); off-support indices coincide with the remainder slot and stay `≤ M`. -/
def satProfile (M S : ℕ) (i : ℕ) : ℕ := if i < S / M then M else S % M

theorem satProfile_le_all (M S : ℕ) (hM : 1 ≤ M) (i : ℕ) : satProfile M S i ≤ M := by
  unfold satProfile
  split
  · exact le_refl M
  · exact le_of_lt (Nat.mod_lt S hM)

/-- The profile sums to `S` over `range (S/M + 1)` (holds for `M = 0` too, by
`Nat.div_add_mod`). -/
theorem satProfile_sum (M S : ℕ) :
    ∑ i ∈ range (S / M + 1), satProfile M S i = S := by
  rw [Finset.sum_range_succ]
  have h1 : ∑ i ∈ range (S / M), satProfile M S i = (S / M) * M := by
    rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, card_range, smul_eq_mul]
    · unfold satProfile; rw [if_pos (Finset.mem_range.mp hi)]
  have h2 : satProfile M S (S / M) = S % M := by
    unfold satProfile; rw [if_neg (lt_irrefl _)]
  rw [h1, h2, Nat.mul_comm]
  exact Nat.div_add_mod S M

/-- The profile's sum of squares in closed form. -/
theorem satProfile_sumSq (M S : ℕ) :
    ∑ i ∈ range (S / M + 1), (satProfile M S i) ^ 2 = (S / M) * M ^ 2 + (S % M) ^ 2 := by
  rw [Finset.sum_range_succ]
  congr 1
  · rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, card_range, smul_eq_mul]
    · unfold satProfile; rw [if_pos (Finset.mem_range.mp hi)]
  · unfold satProfile; rw [if_neg (lt_irrefl _)]

/-- Lower tightness: the energy proxy is at least `M·S − M²`. -/
theorem satProfile_sumSq_ge (M S : ℕ) :
    M * S - M ^ 2 ≤ ∑ i ∈ range (S / M + 1), (satProfile M S i) ^ 2 := by
  rcases Nat.eq_zero_or_pos M with h0 | hM
  · simp [h0]
  rw [satProfile_sumSq]
  have hmod : S % M < M := Nat.mod_lt S hM
  have hdiv : (S / M) * M + S % M = S := by rw [Nat.mul_comm]; exact Nat.div_add_mod S M
  -- (S/M)*M² = ((S/M)*M)*M; from hdiv, (S/M)*M = S - S%M, and (S%M)*M ≤ M²
  have key : M * S ≤ (S / M) * M ^ 2 + (S % M) ^ 2 + M ^ 2 := by
    nlinarith [hdiv, hmod, Nat.mul_le_mul_right M (le_of_lt hmod), Nat.zero_le ((S % M) ^ 2)]
  omega

/-- Upper bound: the energy proxy is at most `M·S` (this is the pointwise method's own
bound, recast — every term is `≤ M·r i`). -/
theorem satProfile_sumSq_le (M S : ℕ) (hM : 1 ≤ M) :
    ∑ i ∈ range (S / M + 1), (satProfile M S i) ^ 2 ≤ M * S := by
  calc ∑ i ∈ range (S / M + 1), (satProfile M S i) ^ 2
      ≤ ∑ i ∈ range (S / M + 1), M * satProfile M S i := by
        apply Finset.sum_le_sum
        intro i _
        have h := satProfile_le_all M S hM i
        nlinarith [h, Nat.zero_le (satProfile M S i)]
    _ = M * ∑ i ∈ range (S / M + 1), satProfile M S i := by rw [Finset.mul_sum]
    _ = M * S := by rw [satProfile_sum M S]

/-- **The pointwise method is tight — the `NoGo` for a sub-`8/3` energy bound from the
pointwise cap alone.**  There is a feasible representation-count profile meeting the
pointwise hypotheses (`r i ≤ M`, `∑ r = S`) whose additive-energy proxy `∑ r²` is pinned to
`M·S` up to an additive `M²`:

  `M·S − M² ≤ ∑ r² ≤ M·S`.

With the Garcia–Voloch cap `M = 4·|G|^{2/3}` and total mass `S = |G|²` the leading term is
`M·S ≈ 4·|G|^{8/3}`, so the pointwise hypothesis is consistent with energy of order
`|G|^{8/3}`.  Hence **no energy bound proved from the pointwise cap and the total mass can
reach `|G|^{5/2}`** (`5/2 < 8/3`); the lit-note §0.A "sum the cap → 5/2" derivation is
invalid.  The genuine `5/2` needs the deeper second-moment input, not this one. -/
theorem pointwise_method_bound_tight (M S : ℕ) (hM : 1 ≤ M) :
    ∃ r : ℕ → ℕ, (∀ i, r i ≤ M) ∧ (∑ i ∈ range (S / M + 1), r i = S) ∧
      M * S - M ^ 2 ≤ (∑ i ∈ range (S / M + 1), r i ^ 2) ∧
      (∑ i ∈ range (S / M + 1), r i ^ 2) ≤ M * S :=
  ⟨satProfile M S, satProfile_le_all M S hM, satProfile_sum M S,
    satProfile_sumSq_ge M S, satProfile_sumSq_le M S hM⟩

#print axioms pointwise_method_bound_tight

end ArkLib.ProximityGap.PointwiseEnergyCeilingNoGo
