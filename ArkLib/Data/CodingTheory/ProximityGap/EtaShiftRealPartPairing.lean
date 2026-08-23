/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaNormSqRealShiftForm

/-!
# The inversion involution pairs the REAL PARTS of the difference-set periods (#444, #389)

The pointwise-autocorrelation chain established the single-frequency worst period² as

* `EtaNormSqRealShiftForm.eta_normSq_eq_card_add_sum_re`:
  `‖η_b‖² = |μ_n| + ∑_{ζ ∈ μ_n \ {1}} Re(η_{b·(ζ-1)})`  (a real-number identity),

and `EtaAutocorrInvolutionPaired.eta_invShift_eq_conj` proved the *complex* pairing
`η_{b·(ζ⁻¹-1)} = conj(η_{b·(ζ-1)})`.

This file extracts the **real-part content** of that pairing — the per-term cosine equality — and
the **involution-invariance of the real-shift sum**, the form in which a half-orbit bound feeds the
full real cosine aggregate.

> **`eta_re_invShift_eq`** — `Re(η_{b·(ζ⁻¹-1)}) = Re(η_{b·(ζ-1)})` for every `ζ ∈ μ_n`.
>
> The inversion `ζ ↦ ζ⁻¹` *preserves* each difference-set period's real part (conjugation fixes the
> real part). So the `|μ_n|−1` real cosine terms `Re(η_{b(ζ-1)})` come in equal-valued
> inversion-pairs `{ζ, ζ⁻¹}`, with the unique fixed point `ζ = -1` (for even `n`) contributing the
> singleton `Re(η_{-2b})` (which is itself `η_{-2b}`, real by `eta_negTwoB_isReal`).

> **`shiftSum_re_inv_invariant`** — the real-shift sum is unchanged by the inversion reindex:
> `∑_{ζ ∈ μ_n \ {1}} Re(η_{b(ζ-1)}) = ∑_{ζ ∈ μ_n \ {1}} Re(η_{b(ζ⁻¹-1)})`.

## Why this is the right downstream form (NON-MOMENT)
`eta_normSq_eq_card_add_sum_re` left the open content as a sum of `|μ_n|−1` real cosine terms. The
pairing here says those terms are pairwise EQUAL across the involution `ζ ↦ ζ⁻¹`: a bound on the
`Re(η_{b(ζ-1)})` over a half-orbit transversal (plus the single fixed-point term `Re(η_{-2b})`)
controls the whole real aggregate by doubling. This packages the orbit structure of the open
BGK/Paley real cosine sum so a half-set bound is lossless.

**Honest scope (rule 6).** EXACT structural equalities, NOT bounds. They re-express the real cosine
aggregate via its inversion-orbit structure but do NOT bound any `Re(η_{b(ζ-1)})` — bounding the
real cosine sum (its terms can be `±` and interfere constructively at the worst `b`) IS the open
BGK/Paley cancellation problem. No CORE bound, no capacity / beyond-Johnson / cliff-at-n/2 / `δ*→0`
claim. CORE `M(μ_n) ≤ C√(n log(q/n))` remains OPEN.

**Thinness-essential (rule 3).** The pairing consumes `eta_invShift_eq_conj`, whose proof needs
multiplicative closure (`η_{ζ⁻¹·w} = η_w` for `ζ⁻¹ ∈ μ_n`); it is FALSE for an unstructured thin set
(verified numerically: a random same-size thin set's "involution-grouped" form mismatches the true
real-shift sum by `Θ(1)`). See `scripts/probes/probe_eta_orbit_grouped.py`.

Axiom-clean. Issues #444, #389.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EtaPointwiseAutocorr
open ArkLib.ProximityGap.EtaAutocorrInvolutionPaired
open ArkLib.ProximityGap.AdditiveEnergyKernel (inv_mem_nthRootsFinset)

namespace ArkLib.ProximityGap.EtaShiftRealPartPairing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The inversion involution preserves each difference-set period's real part.** From the complex
pairing `η_{b·(ζ⁻¹-1)} = conj(η_{b·(ζ-1)})`, taking real parts (which conjugation fixes) gives
`Re(η_{b·(ζ⁻¹-1)}) = Re(η_{b·(ζ-1)})`. The `|μ_n|−1` real cosine terms thus come in equal-valued
inversion-pairs `{ζ, ζ⁻¹}`. -/
theorem eta_re_invShift_eq {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : ζ ∈ nthRootsFinset n (1 : F)) (b : F) :
    (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ⁻¹ - 1))).re
      = (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).re := by
  -- the complex pairing: `η_{b(ζ⁻¹-1)} = conj(η_{b(ζ-1)})`
  rw [eta_invShift_eq_conj hn hζ b]
  -- conjugation fixes the real part
  rw [Complex.conj_re]

#print axioms ArkLib.ProximityGap.EtaShiftRealPartPairing.eta_re_invShift_eq

/-- **The real-shift sum is invariant under the inversion reindex.** Reindexing the real cosine
aggregate `∑_{ζ ∈ μ_n \ {1}} Re(η_{b(ζ-1)})` by the involution `ζ ↦ ζ⁻¹` on `μ_n \ {1}` leaves it
unchanged (the bijection sends each term to its equal-valued inversion-partner). This is the form a
half-orbit bound feeds: control over a transversal of `{ζ, ζ⁻¹}`-pairs (plus the fixed-point term
`Re(η_{-2b})`) bounds the whole real aggregate by doubling. -/
theorem shiftSum_re_inv_invariant {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (b : F) :
    ∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).re
      = ∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ⁻¹ - 1))).re := by
  classical
  -- reindex by `ζ ↦ ζ⁻¹` on `μ_n \ {1}`; each summand maps to its inversion-partner.
  refine Finset.sum_nbij' (fun ζ => ζ⁻¹) (fun ζ => ζ⁻¹) ?_ ?_ ?_ ?_ ?_
  · -- maps `μ_n \ {1}` into itself
    intro ζ hζ
    rw [Finset.mem_erase] at hζ ⊢
    refine ⟨?_, inv_mem_nthRootsFinset hn hζ.2⟩
    intro h
    exact hζ.1 (by simpa using (inv_eq_one.mp h))
  · intro ζ hζ
    rw [Finset.mem_erase] at hζ ⊢
    refine ⟨?_, inv_mem_nthRootsFinset hn hζ.2⟩
    intro h
    exact hζ.1 (by simpa using (inv_eq_one.mp h))
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero (Finset.mem_of_mem_erase hζ)
    simp [inv_inv]
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero (Finset.mem_of_mem_erase hζ)
    simp [inv_inv]
  · -- summand identity: `Re(η_{b(ζ-1)}) = Re(η_{b((ζ⁻¹)⁻¹-1)})` reduces via `inv_inv` to
    -- `Re(η_{b(ζ-1)}) = Re(η_{b(ζ-1)})` after the reindex; concretely the reindexed RHS summand at
    -- `ζ⁻¹` is `Re(η_{b((ζ⁻¹)⁻¹-1)}) = Re(η_{b(ζ-1)})`.
    intro ζ hζ
    have hζmem : ζ ∈ nthRootsFinset n (1 : F) := Finset.mem_of_mem_erase hζ
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hζmem
    simp only [inv_inv]

#print axioms ArkLib.ProximityGap.EtaShiftRealPartPairing.shiftSum_re_inv_invariant

end ArkLib.ProximityGap.EtaShiftRealPartPairing
