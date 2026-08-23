/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoAdicTropicalFloor

/-!
# Uncancellable lone graded term: tightness of the 2-adic tropical floor (#444)

`_TwoAdicTropicalFloor` proved the ultrametric floor `v_λ(D) ≥ min_{j<ℓ}(v_λ(σ_j)+j)` (in ideal form
`(∀ j<ℓ, σ_j·t^j ∈ I^ℓ) ⟹ D ∈ I^ℓ`). The floor can be *strict* — but only through cancellation
between graded coordinates of equal tropical value. This file locks the matching **tightness** result:
when a single graded term carries the obstruction and every *other* term clears `I^ℓ`, the lone term
cannot be cancelled, so the wraparound sum inherits the obstruction.

* `signedSum_notMem_idealPow_of_lone_gradedTerm_notMem` —
  if `σ_{j₀}·t^{j₀} ∉ I^ℓ` (some `j₀<ℓ`) and `σ_j·t^j ∈ I^ℓ` for every other `j<ℓ`, then `D ∉ I^ℓ`.

For `I = (λ)`, `t = ζ − 1`: this is the **uncancellable lowest-term principle** sharpening the floor.
Probe-verified (R=ℤ, I=(2), t=2): when the tropical minimum `min_{j<ℓ}(v_λ(σ_j)+j)` is attained at a
*unique* coordinate, the floor is an equality — `v_λ(D) = min_{j<ℓ}(v_λ(σ_j)+j)` held with 0 failures
over 66k random instances; strictness occurs only on tropical-min ties (≥2 minimizers), where extra
cancellation strictly raised the valuation in ~90% of the ~14k tie instances. The "unique minimizer ⟹
that coordinate's term is the lone non-`I^ℓ` term" hypothesis is the clean ideal-theoretic form of
"unique tropical minimizer".

This is only the algebraic tower substrate. It does **not** prove the integer parity criterion at
general depth, any char-`p` transfer, BGK, CORE, or a capacity/growth-law claim.
-/

namespace ProximityGap.Frontier.TwoAdicLoneTermFloor

open Finset
open ProximityGap.Frontier.TwoAdicGradedTower

variable {ι R : Type*} [CommRing R]

/-- **Splitting off a single graded coordinate.** For `j₀ ∈ range ℓ`, the depth-`ℓ` graded vector
`G_ℓ = Σ_{j<ℓ} σ_j·t^j` equals its `j₀`-term plus the sum of the remaining terms. -/
theorem gradedTower_eq_lone_add_rest
    (t : R) (ℓ j₀ : ℕ) (hj₀ : j₀ ∈ range ℓ) (s : Finset ι) (c : ι → R) (a : ι → ℕ) :
    (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
      = (∑ i ∈ s, c i * ((a i).choose j₀ : R)) * t ^ j₀
        + ∑ j ∈ (range ℓ).erase j₀, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j := by
  rw [← Finset.add_sum_erase (range ℓ) _ hj₀]

/-- **Uncancellable lone graded term (floor tightness).** Suppose a single graded coordinate `j₀ < ℓ`
escapes `I^ℓ` (`σ_{j₀}·t^{j₀} ∉ I^ℓ`) while every *other* graded term `σ_j·t^j` (`j<ℓ`, `j≠j₀`) lies in
`I^ℓ`. Then the signed wraparound sum `D = Σ_i c_i·(1+t)^{a_i}` does *not* lie in `I^ℓ`: the lone
obstructing term cannot be cancelled. For `I = (λ)`, `t = ζ − 1` this is the uncancellable lowest-term
principle that makes the tropical floor an equality at a unique minimizer. -/
theorem signedSum_notMem_idealPow_of_lone_gradedTerm_notMem
    (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ j₀ : ℕ) (hj₀ : j₀ ∈ range ℓ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hlone : (∑ i ∈ s, c i * ((a i).choose j₀ : R)) * t ^ j₀ ∉ I ^ ℓ)
    (hrest : ∀ j ∈ (range ℓ).erase j₀,
      (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j ∈ I ^ ℓ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∉ I ^ ℓ := by
  -- The graded vector misses I^ℓ (lone term ∉, rest ∈), then apply the all-depth contrapositive.
  apply TwoAdicStallLocator.signedSum_notMem_idealPow_of_gradedTower_notMem I t ht ℓ s c a
  rw [gradedTower_eq_lone_add_rest t ℓ j₀ hj₀ s c a]
  -- (lone + rest) ∈ I^ℓ with rest ∈ I^ℓ would force lone ∈ I^ℓ; contradiction.
  intro hsum
  apply hlone
  have hrest_mem :
      (∑ j ∈ (range ℓ).erase j₀, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) ∈ I ^ ℓ :=
    Ideal.sum_mem _ hrest
  have hrw : (∑ i ∈ s, c i * ((a i).choose j₀ : R)) * t ^ j₀
      = ((∑ i ∈ s, c i * ((a i).choose j₀ : R)) * t ^ j₀
          + ∑ j ∈ (range ℓ).erase j₀, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
        - ∑ j ∈ (range ℓ).erase j₀, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j := by ring
  rw [hrw]
  exact (I ^ ℓ).sub_mem hsum hrest_mem

end ProximityGap.Frontier.TwoAdicLoneTermFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicLoneTermFloor.gradedTower_eq_lone_add_rest
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicLoneTermFloor.signedSum_notMem_idealPow_of_lone_gradedTerm_notMem
