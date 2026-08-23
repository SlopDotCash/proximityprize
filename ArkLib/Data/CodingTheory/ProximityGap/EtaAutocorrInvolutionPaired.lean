/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaPointwiseAutocorr
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031DilationOrbitReduction
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyResultantProduct

/-!
# The inversion involution on the pointwise autocorrelation shift-spectrum (#444, #389)

This EXTENDS the just-landed pointwise (single-frequency) autocorrelation identity
`EtaPointwiseAutocorr.eta_normSq_eq_card_add_nontrivial`:

> `‖η_b‖² = |μ_n| + ∑_{ζ ∈ μ_n \ {1}} η_{b·(ζ-1)}`,

which re-expresses the worst period² as a sum of periods at the **difference-set frequencies**
`b·(ζ-1)`, `ζ ∈ μ_n`. The open content is the cancellation among those `|μ_n|-1` shift periods (the
BGK/Paley wall). This file pins a *structural symmetry* of that shift-spectrum that the
second-moment / energy framework is blind to: the **inversion involution** `ζ ↦ ζ⁻¹` on `μ_n` pairs
each shift period with the conjugate of its partner.

## The mechanism (thinness-essential, NON-MOMENT)
For `ζ ∈ μ_n` the inverse `ζ⁻¹ ∈ μ_n` (a subgroup), and the difference-set frequency of the inverse
is the *negated, coset-rotated* frequency of `ζ`:
`b·(ζ⁻¹ - 1) = -(b·(ζ-1))·ζ⁻¹`. Now:
* `η_{-c} = conj(η_c)` (negating the frequency conjugates the period — true for any `G`);
* `η_{c·ζ⁻¹} = η_c` for `ζ⁻¹ ∈ μ_n` (the **frequency coset-invariance** `eta_dilation_invariant`,
  thinness-essential: it needs `μ_n` closed under multiplication).
Composing:

> **`eta_invShift_eq_conj`** — `η_{b·(ζ⁻¹-1)} = conj(η_{b·(ζ-1)})`  for every `ζ ∈ μ_n`.

So the inversion involution acts on the shift-spectrum `{η_{b(ζ-1)}}` as complex conjugation. Hence
the nontrivial shift-sum `∑_{ζ ≠ 1} η_{b(ζ-1)}` is invariant under conjugation, i.e.

> **`pointwise_autocorr_shiftSum_isReal`** — `∑_{ζ ∈ μ_n \ {1}} η_{b(ζ-1)}` is REAL (equals its
> own conjugate), and (`pointwise_autocorr_shiftSum_eq_self_conj`) the worst period² minus `|μ_n|` is
> carried entirely by this real, inversion-symmetric shift sum.

**Why thinness-essential (rule 3).** The pairing uses (a) `ζ⁻¹ ∈ μ_n` (inverse-closure of the
subgroup) and (b) the coset-invariance `η_{c·ζ⁻¹} = η_c` for `ζ⁻¹ ∈ μ_n`. Both FAIL for an
unstructured thin set `S` (a random `S` has `ζ⁻¹ ∉ S` and `η_{c·u} ≠ η_c`); probe
`probe_eta_involution_pairing.py` confirms the pairing on PROPER `μ_n` (`m=(p-1)/n ≥ 4`, incl.
Fermat `257, 65537`, `pair_err ≤ 1.2e-14`) and the coset-invariance control set fails by `~7-19`.

**Honest scope (rule 6).** This is a structural SYMMETRY of the shift-spectrum, NOT a bound. The
reality / inversion-pairing reduces the `|μ_n|-1` complex shift terms to `~|μ_n|/2` real cosine
pairs but does NOT bound their (constructive) sum — bounding `∑_{ζ≠1} η_{b(ζ-1)}` is exactly the
open BGK/Paley cancellation problem. No CORE bound, no capacity / beyond-Johnson / cliff-at-n/2
claim. CORE `M(μ_n) ≤ C√(n log(q/n))` remains OPEN. The value: the worst period² is `|μ_n|` plus a
manifestly REAL, inversion-symmetric difference-set period sum — the non-moment phase content that
`∑_b ‖η_b‖² = q|μ_n|` averages away is here pinned to an involution-paired real form.

Axiom-clean. Issues #444, #389.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EtaPointwiseAutocorr
open ArkLib.ProximityGap.I031DilationOrbitReduction

open ArkLib.ProximityGap.AdditiveEnergyKernel (inv_mem_nthRootsFinset)

namespace ArkLib.ProximityGap.EtaAutocorrInvolutionPaired

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Negating the frequency conjugates the period.** For any `G : Finset F` and frequency `c`,
`η_{-c} = conj(η_c)`. Pure character algebra: `ψ(-c y) = conj(ψ(c y))`. -/
theorem eta_neg_eq_conj {ψ : AddChar F ℂ} (G : Finset F) (c : F) :
    eta ψ G (-c) = (starRingEnd ℂ) (eta ψ G c) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- Expand `conj(η_c) = ∑_y conj(ψ(c y)) = ∑_y ψ(-(c y)) = ∑_y ψ((-c) y) = η_{-c}`.
  have hrhs : (starRingEnd ℂ) (eta ψ G c) = ∑ y ∈ G, ψ ((-c) * y) := by
    rw [show eta ψ G c = ∑ y ∈ G, ψ (c * y) from rfl, _root_.map_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hconj (c * y)]
    congr 1
    ring
  rw [hrhs]
  show (∑ y ∈ G, ψ ((-c) * y)) = ∑ y ∈ G, ψ ((-c) * y)
  rfl

/-- **The inversion involution acts on the shift-spectrum as conjugation.** For `ζ ∈ μ_n` the
difference-set frequency of `ζ⁻¹` is `-(b·(ζ-1))·ζ⁻¹`, and since `ζ⁻¹ ∈ μ_n` the coset-invariance
absorbs the `·ζ⁻¹` factor, leaving the negation. Hence

> `η_{b·(ζ⁻¹ - 1)} = conj(η_{b·(ζ - 1)})`.

Thinness-essential: uses `ζ⁻¹ ∈ μ_n` and `eta_dilation_invariant` (both need the subgroup). -/
theorem eta_invShift_eq_conj {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : ζ ∈ nthRootsFinset n (1 : F)) (b : F) :
    eta ψ (nthRootsFinset n (1 : F)) (b * (ζ⁻¹ - 1))
      = (starRingEnd ℂ) (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))) := by
  have hζinv : ζ⁻¹ ∈ nthRootsFinset n (1 : F) := inv_mem_nthRootsFinset hn hζ
  have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hζ
  -- Key field identity: `b·(ζ⁻¹ - 1) = ζ⁻¹ · (-(b·(ζ - 1)))`.
  have hfreq : b * (ζ⁻¹ - 1) = ζ⁻¹ * (-(b * (ζ - 1))) := by
    field_simp
    ring
  rw [hfreq]
  -- absorb the `ζ⁻¹` coset factor: `η_{ζ⁻¹ · w} = η_w` for `ζ⁻¹ ∈ μ_n`.
  rw [eta_dilation_invariant hζinv (-(b * (ζ - 1)))]
  -- negation conjugates.
  rw [eta_neg_eq_conj]

/-- **The nontrivial shift-sum is invariant under conjugation (hence REAL).** The inversion
involution `ζ ↦ ζ⁻¹` is a bijection of `μ_n \ {1}` (it fixes the set, swaps each `ζ` with `ζ⁻¹`),
and by `eta_invShift_eq_conj` it sends each shift period to the conjugate of its partner. Summing,
the difference-set period sum equals its own complex conjugate:

> `conj(∑_{ζ ∈ μ_n \ {1}} η_{b(ζ-1)}) = ∑_{ζ ∈ μ_n \ {1}} η_{b(ζ-1)}`,

so the sum is real. -/
theorem pointwise_autocorr_shiftSum_eq_self_conj {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (b : F) :
    (starRingEnd ℂ) (∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
        eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1)))
      = ∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
        eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1)) := by
  classical
  rw [map_sum]
  -- reindex the sum by the inversion involution `ζ ↦ ζ⁻¹` on `μ_n \ {1}`.
  refine Finset.sum_nbij' (fun ζ => ζ⁻¹) (fun ζ => ζ⁻¹) ?_ ?_ ?_ ?_ ?_
  · -- maps μ_n\{1} into itself
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
  · -- the summand identity: `conj(η_{b(ζ-1)}) = η_{b(ζ⁻¹-1)}`.
    intro ζ hζ
    have hζmem : ζ ∈ nthRootsFinset n (1 : F) := Finset.mem_of_mem_erase hζ
    exact (eta_invShift_eq_conj hn hζmem b).symm

/-- **The nontrivial shift-sum is REAL.** Restated via `Complex.conj_eq_iff_im`: the difference-set
period sum has zero imaginary part. The single-frequency worst period² is therefore `|μ_n|` plus a
*real*, inversion-symmetric sum over the difference-set spectrum. -/
theorem pointwise_autocorr_shiftSum_isReal {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (b : F) :
    (∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
        eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).im = 0 := by
  have h := pointwise_autocorr_shiftSum_eq_self_conj hn (ψ := ψ) b
  -- conj z = z ↔ im z = 0
  rwa [Complex.conj_eq_iff_im] at h

end ArkLib.ProximityGap.EtaAutocorrInvolutionPaired

#print axioms ArkLib.ProximityGap.EtaAutocorrInvolutionPaired.eta_neg_eq_conj
#print axioms ArkLib.ProximityGap.EtaAutocorrInvolutionPaired.eta_invShift_eq_conj
#print axioms ArkLib.ProximityGap.EtaAutocorrInvolutionPaired.pointwise_autocorr_shiftSum_eq_self_conj
#print axioms ArkLib.ProximityGap.EtaAutocorrInvolutionPaired.pointwise_autocorr_shiftSum_isReal
