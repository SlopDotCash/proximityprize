/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoAdicMomentAnnihilation

/-!
# Stall-locator for the depth-ℓ 2-adic graded tower (#444)

The proven depth-ℓ gate biconditional
`signedSum_mem_idealPow_iff_gradedTower` reads
`D ∈ I^ℓ ⟺ G_ℓ ∈ I^ℓ`, where `D = Σ_{i∈s} c_i·(1+t)^{a_i}` is the signed cyclotomic
wraparound sum and `G_ℓ = Σ_{j<ℓ} σ_j·t^j` is its depth-`ℓ` graded Taylor vector
(`σ_j = Σ_i c_i·C(a_i,j)`). The forward consumer
`signedSum_mem_idealPow_of_moments_zero` covers `(∀ j<ℓ, σ_j = 0) ⟹ D ∈ I^ℓ`.

This file packages the two **structural** corollaries of that biconditional that the
moment-vanishing consumer does NOT give:

* `signedSum_notMem_idealPow_of_gradedTower_notMem` — the all-depth **contrapositive**:
  if the graded vector misses `I^ℓ` then so does `D`. (This generalizes the `ℓ = 1`
  parity-gate `signedSum_notMem_of_weight_notMem` to every depth.)

* `signedSum_mem_idealPow_succ_iff_newGraded_of_lower_clears` — the **incremental
  stall-locator**: once the depth-`ℓ` graded vector already clears the *next* level
  (`G_ℓ ∈ I^{ℓ+1}`), advancing the wraparound from `I^ℓ` to `I^{ℓ+1}` is governed
  by the *single new* graded coordinate `σ_ℓ·t^ℓ`:
  `D ∈ I^{ℓ+1} ⟺ σ_ℓ·t^ℓ ∈ I^{ℓ+1}`.
  This is the exact recursion step of the 2-adic phase-alignment tower: to gain one
  unit of valuation you must kill exactly the next graded coordinate modulo `I^{ℓ+1}`.

Probe-verified (integer 2-adic shadow `R = ℤ`, `I = (2)`, `t = 2`, `1+t = 3`):
the biconditional held over 120k random instances (0 failures), and the incremental
stall form held over ~60k instances where the lower-vector premise fires (0 failures).

This is only the algebraic tower substrate. It does **not** prove the integer parity
criterion at general depth, any char-`p` transfer, BGK, CORE, or a capacity/growth-law
claim. It is a reusable structural consumer locating *where* the 2-adic tower stalls.
-/

namespace ProximityGap.Frontier.TwoAdicStallLocator

open Finset
open ProximityGap.Frontier.TwoAdicGradedTower

variable {ι R : Type*} [CommRing R]

/-- **All-depth non-membership gate (contrapositive of the tower biconditional).**
If the depth-`ℓ` graded Taylor vector `G_ℓ = Σ_{j<ℓ} σ_j·t^j` is *not* in `I^ℓ`, then the
signed wraparound sum `D = Σ_i c_i·(1+t)^{a_i}` is *not* in `I^ℓ`. For `I = (λ)`,
`t = ζ − 1`: a graded vector with `v_λ(G_ℓ) < ℓ` forces `v_λ(D) < ℓ` — the obstruction to
depth-`ℓ` divisibility is detectable purely in the low binomial moments. This generalizes
the parity-gate `ℓ = 1` non-divisibility gate to every depth. -/
theorem signedSum_notMem_idealPow_of_gradedTower_notMem
    (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hG : (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) ∉ I ^ ℓ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∉ I ^ ℓ :=
  fun hD => hG ((signedSum_mem_idealPow_iff_gradedTower I t ht ℓ s c a).1 hD)

/-- **The depth-`ℓ` graded vector splits off its top coordinate.**
`G_{ℓ+1} = G_ℓ + σ_ℓ·t^ℓ`, where `σ_ℓ = Σ_i c_i·C(a_i,ℓ)`. -/
theorem gradedTower_succ_eq
    (t : R) (ℓ : ℕ) (s : Finset ι) (c : ι → R) (a : ι → ℕ) :
    (∑ j ∈ range (ℓ + 1), (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
      = (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
        + (∑ i ∈ s, c i * ((a i).choose ℓ : R)) * t ^ ℓ :=
  Finset.sum_range_succ _ ℓ

/-- **Incremental stall-locator.** Suppose the depth-`ℓ` graded vector already clears the
*next* level, `G_ℓ ∈ I^{ℓ+1}`. Then advancing the signed wraparound from `I^ℓ` to `I^{ℓ+1}`
is governed by the single new graded coordinate:
`D ∈ I^{ℓ+1} ⟺ σ_ℓ·t^ℓ ∈ I^{ℓ+1}`, where `σ_ℓ = Σ_i c_i·C(a_i,ℓ)`.

For `I = (λ)`, `t = ζ − 1`: once the lower moments have driven `v_λ(G_ℓ) ≥ ℓ+1`, the
2-adic tower stalls exactly on the next moment — `λ^{ℓ+1} ∣ D ⟺ λ^{ℓ+1} ∣ σ_ℓ·λ^ℓ`. This
is the recursion step of the 2-adic phase-alignment tower: each extra unit of valuation
costs exactly one graded coordinate. -/
theorem signedSum_mem_idealPow_succ_iff_newGraded_of_lower_clears
    (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hlow : (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) ∈ I ^ (ℓ + 1)) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ (ℓ + 1)
      ↔ (∑ i ∈ s, c i * ((a i).choose ℓ : R)) * t ^ ℓ ∈ I ^ (ℓ + 1) := by
  -- Bridge D ∈ I^{ℓ+1} to the full graded vector G_{ℓ+1} ∈ I^{ℓ+1} via the proven tower biconditional.
  rw [signedSum_mem_idealPow_iff_gradedTower I t ht (ℓ + 1) s c a,
    gradedTower_succ_eq t ℓ s c a]
  -- Now: G_ℓ + σ_ℓ·t^ℓ ∈ I^{ℓ+1} ⟺ σ_ℓ·t^ℓ ∈ I^{ℓ+1}, using G_ℓ ∈ I^{ℓ+1}.
  constructor
  · intro hsum
    -- σ_ℓ·t^ℓ = (G_ℓ + σ_ℓ·t^ℓ) − G_ℓ.
    have hrw : (∑ i ∈ s, c i * ((a i).choose ℓ : R)) * t ^ ℓ
        = ((∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
            + (∑ i ∈ s, c i * ((a i).choose ℓ : R)) * t ^ ℓ)
          - (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) := by ring
    rw [hrw]; exact (I ^ (ℓ + 1)).sub_mem hsum hlow
  · intro hnew
    exact (I ^ (ℓ + 1)).add_mem hlow hnew

end ProximityGap.Frontier.TwoAdicStallLocator

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicStallLocator.signedSum_notMem_idealPow_of_gradedTower_notMem
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicStallLocator.gradedTower_succ_eq
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicStallLocator.signedSum_mem_idealPow_succ_iff_newGraded_of_lower_clears
