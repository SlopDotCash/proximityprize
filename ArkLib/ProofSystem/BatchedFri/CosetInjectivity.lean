/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.BatchedFri.Security

/-!
# Batched FRI coset-bijection injectivity (issue #303)

Named standalone forms of the coset-enumeration bijection facts underlying the Batched FRI
query-round analysis: injectivity of `cosetEnum` (the map enumerating the `2 ^ (s i)`-element
folding coset through a point `s₀` of the round-`i` evaluation domain), and the resulting coset
cardinalities `|cosetG n s s₀| = 2 ^ (s i)`.  These are extracted from the in-file bijection
`fin_equiv_coset` (`BatchedFri/Security.lean`), which is the coset-bijection input to the
Vandermonde interpolation step (`VDM`/`VDMInv`) of the batched-to-base FRI query-round lift:
injectivity is what makes the Vandermonde matrix over the coset nodes invertible
(`invertibleDomain`), hence the folded value `f_succ'` well-defined.
-/

namespace Fri

open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
variable (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+)
variable {i : Fin (k + 1)} {ω : SmoothCosetFftDomain n 𝔽}

omit [Fintype 𝔽] in
/-- **Coset-bijection injectivity.**  The coset enumeration `cosetEnum n s s₀ k_le_n` of the
`2 ^ (s i)`-element folding coset through `s₀` is injective.  This is the named standalone form
of the injectivity half of `fin_equiv_coset`. -/
theorem cosetEnum_injective (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n) :
    Function.Injective (cosetEnum n s s₀ k_le_n) := by
  intro a b h
  exact (fin_equiv_coset n s s₀ k_le_n).injective (Subtype.ext h)

omit [Fintype 𝔽] in
/-- **Coset cardinality (Finset form).**  The folding coset through `s₀` has exactly
`2 ^ (s i)` elements. -/
theorem cosetG_card (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n) :
    (cosetG n s s₀).card = 2 ^ (s i).1 := by
  unfold cosetG
  rw [dif_pos k_le_n,
    Finset.card_image_of_injective _ (cosetEnum_injective n s s₀ k_le_n)]
  simp

omit [Fintype 𝔽] in
/-- **Coset cardinality (Fintype form).**  The subtype of the folding coset through `s₀` has
exactly `2 ^ (s i)` elements; this is the cardinality consequence of the full bijection
`fin_equiv_coset`. -/
theorem card_coe_cosetG (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n) :
    Fintype.card {x // x ∈ cosetG n s s₀} = 2 ^ (s i).1 := by
  rw [← Fintype.card_congr (fin_equiv_coset n s s₀ k_le_n)]
  exact Fintype.card_fin _

end Fri

/-! ### Axiom audit (issue #303 coset-bijection injectivity) -/

#print axioms Fri.cosetEnum_injective
#print axioms Fri.cosetG_card
#print axioms Fri.card_coe_cosetG
