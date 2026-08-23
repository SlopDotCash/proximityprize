/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilCauchySchwarzFisher
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrelation

/-!
# The Cauchy-Schwarz / Fisher pencil bound, discharged to multiplicative autocorrelation (#407/#444)

`PencilCauchySchwarzFisher.pencil_cs_fisher` proved the abstract block bound
`r·(r−1) ≤ (M+1)·(N−1)` from a *punctured pairwise* hypothesis on `(Bᵢ).erase p ∩ (Bⱼ).erase p`.
This file wires that hypothesis to the actual **multiplicative autocorrelation** of the root set `S`
(via `PencilAutocorrelation.inter_dilate_eq_autocorr`), exactly as
`PencilAutocorrRootBound.pencil_card_bound_of_autocorr_le_one` did for the `M = 1` extreme, but now
in the sharp Cauchy-Schwarz form valid for **every** `M`:

> `pencil_cs_autocorr_bound` :  `M(S) ≤ M` over the order-`n` subgroup `μ ⊆ G` with `S ⊆ μ`,
> `|S| = r ≥ 1`, ⟹ `r·(r−1) ≤ (M+1)·(n−1)`,

and its `√` extraction

> `pencil_cs_autocorr_sqrt_bound` :  `(r−1)² < (M+1)·n`   (`r ≤ 1 + √((M+1)n)`).

Here `M(S) ≤ M` means every nontrivial multiplicative shift `ρ ≠ 1` overlaps `S` in `≤ M` points
(`∀ ρ ≠ 1, |S ∩ ρ·S| ≤ M`). We build the `Fin r`-indexed pencil-block family `pencil_cs_fisher`
consumes, with apex `1` and universe `μ`, and discharge its punctured-pairwise hypothesis from the
autocorrelation bridge: the punctured intersection is a subset of the full pencil overlap, which the
bridge identifies with `|S ∩ ρ·S| ≤ M`.

## Honest scope (rules 1,3,4,6 + ASYMPTOTIC GUARD)

This is the **end-to-end autocorrelation form** of the sharp Cauchy-Schwarz pencil count, NOT a
closure. Field- and thickness-universal combinatorics. Rule-4 Johnson collapse: for the
prize-relevant general `t = k+2` worst case `S = (coset of size n/2) ∪ {straggler}` the
autocorrelation is `M ≍ n/2` (`PencilAutocorrelation.autocorr_ge_coset_core`), so the hypothesis
holds only with `M ≍ n/2`, and the bound gives `r·(r−1) ≤ (n/2)(n−1)`, i.e. `r ≲ n` (**Johnson**,
not sub-Johnson). The Cauchy-Schwarz pencil double-count **collapses to Johnson** at the prize core,
exactly as the cliff-at-n/2 guard demands. The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**
(the beyond-Johnson `√(log)` cancellation lives in the agreement-sharing / BGK contribution).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilCauchySchwarzAutocorr

open ProximityGap.Frontier.PencilCauchySchwarzFisher
open ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- The **punctured** pencil overlap is bounded by the full pencil overlap, hence by the
autocorrelation. For distinct roots `ζᵢ ≠ ζⱼ` with `M(S) ≤ M`,
`|(pencilBlock ζᵢ S).erase 1 ∩ (pencilBlock ζⱼ S).erase 1| ≤ M`. (The punctured intersection is a
subset of the full intersection `pencilBlock ζᵢ S ∩ pencilBlock ζⱼ S`, whose card is `≤ M` by
`pencil_overlap_le_of_autocorr`.) -/
theorem punctured_pencil_overlap_le_of_autocorr {S : Finset G} {M : ℕ}
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ M)
    {zi zj : G} (hne : zi ≠ zj) :
    ((pencilBlock zi S).erase 1 ∩ (pencilBlock zj S).erase 1).card ≤ M := by
  classical
  have hsub : (pencilBlock zi S).erase 1 ∩ (pencilBlock zj S).erase 1
      ⊆ pencilBlock zi S ∩ pencilBlock zj S := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_erase, Finset.mem_erase] at hx
    exact Finset.mem_inter.mpr ⟨hx.1.2, hx.2.2⟩
  calc ((pencilBlock zi S).erase 1 ∩ (pencilBlock zj S).erase 1).card
      ≤ (pencilBlock zi S ∩ pencilBlock zj S).card := Finset.card_le_card hsub
    _ ≤ M := pencil_overlap_le_of_autocorr hM hne

/-- **The Cauchy-Schwarz pencil bound in autocorrelation language.** Let `μ ⊆ G` be the order-`n`
multiplicative subgroup (closed under `*` and `⁻¹`) and `S ⊆ μ` the root set with `|S| = r ≥ 1`. If
the multiplicative autocorrelation of `S` is `≤ M` at every nontrivial shift, then

  `r·(r−1) ≤ (M + 1)·(n − 1)`.

The sharp Cauchy-Schwarz form valid for every `M` (the `M = 1` case recovers the trinomial rung of
`PencilAutocorrRootBound`). We enumerate `S` by `S ≃ Fin r` to build the block family
`pencil_cs_fisher` consumes (apex `1`, universe `μ`), discharging its punctured-pairwise hypothesis
from `punctured_pencil_overlap_le_of_autocorr`. -/
theorem pencil_cs_autocorr_bound {μ S : Finset G} {n r M : ℕ}
    (hμcard : μ.card = n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ M) :
    r * (r - 1) ≤ (M + 1) * (n - 1) := by
  classical
  -- enumerate S by an equiv with Fin r
  let e : Fin r ≃ {x // x ∈ S} := (Fintype.equivFinOfCardEq (by simp [hr])).symm
  -- the block family with apex 1
  let B : Fin r → Finset G := fun i => pencilBlock (e i : G) S
  -- pencilBlock z S ⊆ μ for z ∈ μ
  have hBμ : ∀ i, B i ⊆ μ := by
    intro i x hx
    have hzμ : (e i : G) ∈ μ := hSμ (e i).2
    rw [mem_pencilBlock] at hx
    have hzx : (e i : G) * x ∈ μ := hSμ hx
    have : (e i : G)⁻¹ * ((e i : G) * x) ∈ μ := hμmul _ (hμinv _ hzμ) _ hzx
    simpa [inv_mul_cancel_left] using this
  -- apply pencil_cs_fisher with univ = μ, apex 1
  have key : r * (r - 1) ≤ (M + 1) * (μ.card - 1) := by
    apply pencil_cs_fisher μ r M hr1 B (1 : G) hBμ
    · -- each block has card r
      intro i
      change (pencilBlock (e i : G) S).card = r
      rw [card_pencilBlock, hr]
    · -- every block contains the apex 1
      intro i; exact one_mem_pencilBlock (e i).2
    · -- punctured pairwise ≤ M (from autocorrelation)
      intro i j hij
      have hzij : (e i : G) ≠ (e j : G) := by
        intro h
        apply hij
        exact e.injective (Subtype.ext h)
      change ((pencilBlock (e i : G) S).erase 1 ∩ (pencilBlock (e j : G) S).erase 1).card ≤ M
      exact punctured_pencil_overlap_le_of_autocorr hM hzij
  rwa [hμcard] at key

/-- **The `√` extraction in autocorrelation language.** From `pencil_cs_autocorr_bound`,

  `(r − 1)² < (M + 1)·n`,

i.e. `r − 1 < √((M+1)n)`, `r ≤ 1 + √((M+1)n)`. At `M = 0` this is `(r−1)² < n` (the order-`n`
Johnson radius `√n`); at the prize core `M ≍ n/2` the radius is `√((n/2)n)`, the Johnson-scale
ceiling. -/
theorem pencil_cs_autocorr_sqrt_bound {μ S : Finset G} {n r M : ℕ}
    (hμcard : μ.card = n) (hn : 1 ≤ n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ M) :
    (r - 1) * (r - 1) < (M + 1) * n := by
  have hcount : r * (r - 1) ≤ (M + 1) * (n - 1) :=
    pencil_cs_autocorr_bound hμcard hSμ hμmul hμinv hr hr1 hM
  have hsq : (r - 1) * (r - 1) ≤ r * (r - 1) := Nat.mul_le_mul_right _ (by omega)
  have hstrict : (M + 1) * (n - 1) < (M + 1) * n :=
    (Nat.mul_lt_mul_left (by omega : 0 < M + 1)).mpr (by omega)
  omega

end ProximityGap.Frontier.PencilCauchySchwarzAutocorr

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
open ProximityGap.Frontier.PencilCauchySchwarzAutocorr in
#print axioms punctured_pencil_overlap_le_of_autocorr
open ProximityGap.Frontier.PencilCauchySchwarzAutocorr in
#print axioms pencil_cs_autocorr_bound
open ProximityGap.Frontier.PencilCauchySchwarzAutocorr in
#print axioms pencil_cs_autocorr_sqrt_bound
