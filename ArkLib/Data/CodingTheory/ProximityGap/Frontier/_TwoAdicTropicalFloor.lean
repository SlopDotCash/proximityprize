/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoAdicStallLocator

/-!
# Ultrametric / tropical floor for the depth-ℓ 2-adic graded tower (#444)

The proven depth-`ℓ` gate biconditional `signedSum_mem_idealPow_iff_gradedTower`
reads `D ∈ I^ℓ ⟺ G_ℓ ∈ I^ℓ`, where `D = Σ_i c_i·(1+t)^{a_i}` is the signed cyclotomic
wraparound sum and `G_ℓ = Σ_{j<ℓ} σ_j·t^j` (`σ_j = Σ_i c_i·C(a_i,j)`). The moment-vanishing
consumer `signedSum_mem_idealPow_of_moments_zero` needs the *strong* hypothesis `σ_j = 0`
for `j < ℓ`.

This file packages the strictly weaker, **termwise** (ultrametric) consumer: it is enough that
each graded *term* `σ_j·t^j` already lies in `I^ℓ`.

* `signedSum_mem_idealPow_of_gradedTerms_mem` —
  `(∀ j<ℓ, σ_j·t^j ∈ I^ℓ) ⟹ D ∈ I^ℓ`.

For `I = (λ)`, `t = ζ − 1` this is the ideal-theoretic shadow of the **tropical valuation
floor**
```
    v_λ(D) ≥ min_{j<ℓ} ( v_λ(σ_j) + j ),
```
the non-Archimedean lower bound on the wraparound valuation: `D` cannot beat the best graded
coordinate's valuation. (Probe-verified over R=ℤ, I=(2), t=2: the inequality
`v_2(D) ≥ min_j (v_2(σ_j)+j)` held with 0 failures over 60k random instances; the matching
*equality* FAILS exactly when the tropical minimum is attained at ≥2 coordinates — ties allow
cancellation — so only the floor inequality, not the equality, is a theorem.)

The consumer is strictly more general than the moment-vanishing one: `σ_j = 0 ⟹ σ_j·t^j = 0 ∈ I^ℓ`,
but the converse can hold with `σ_j ≠ 0` whenever `σ_j` itself carries enough `I`-divisibility
(`v(σ_j) ≥ ℓ − j`). Re-deriving the moment-vanishing consumer from it is `signedSum_mem_idealPow_of_moments_zero'`.

This is only the algebraic tower substrate. It does **not** prove the integer parity criterion at
general depth, any char-`p` transfer, BGK, CORE, or a capacity/growth-law claim.
-/

namespace ProximityGap.Frontier.TwoAdicTropicalFloor

open Finset
open ProximityGap.Frontier.TwoAdicGradedTower

variable {ι R : Type*} [CommRing R]

/-- **Termwise (ultrametric) consumer.** If every graded term `σ_j·t^j` lies in `I^ℓ` for `j < ℓ`,
then the signed wraparound sum `D = Σ_i c_i·(1+t)^{a_i}` lies in `I^ℓ`. This is the ideal-theoretic
shadow of the tropical valuation floor `v_λ(D) ≥ min_{j<ℓ}(v_λ(σ_j)+j)`: the sum cannot have smaller
valuation than its best graded coordinate. Strictly weaker hypothesis than moment-vanishing. -/
theorem signedSum_mem_idealPow_of_gradedTerms_mem
    (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hterms : ∀ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j ∈ I ^ ℓ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ ℓ := by
  apply (signedSum_mem_idealPow_iff_gradedTower I t ht ℓ s c a).2
  exact Ideal.sum_mem _ hterms

/-- **Moment-vanishing as a special case of the termwise floor.** Recovering
`signedSum_mem_idealPow_of_moments_zero` from the strictly-weaker termwise consumer: each vanishing
moment makes its graded term `0 ∈ I^ℓ`. -/
theorem signedSum_mem_idealPow_of_moments_zero'
    (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hzero : ∀ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) = 0) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ ℓ := by
  apply signedSum_mem_idealPow_of_gradedTerms_mem I t ht ℓ s c a
  intro j hj
  rw [hzero j hj, zero_mul]
  exact (I ^ ℓ).zero_mem

end ProximityGap.Frontier.TwoAdicTropicalFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicTropicalFloor.signedSum_mem_idealPow_of_gradedTerms_mem
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicTropicalFloor.signedSum_mem_idealPow_of_moments_zero'
