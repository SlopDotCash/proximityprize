/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaAutocorrInvolutionPaired

/-!
# The inversion-involution FIXED POINT pins an exactly REAL difference-set period (#444, #389)

This EXTENDS the just-landed inversion-involution file
`EtaAutocorrInvolutionPaired`, which proved that the inversion `ζ ↦ ζ⁻¹` on `μ_n` acts on the
pointwise-autocorrelation shift-spectrum `{η_{b(ζ-1)}}` as complex conjugation
(`eta_invShift_eq_conj`: `η_{b(ζ⁻¹-1)} = conj(η_{b(ζ-1)})`), so the nontrivial shift-sum
`∑_{ζ≠1} η_{b(ζ-1)}` is REAL.

A free involution on a finite set has no statement about individual terms; but the inversion
`ζ ↦ ζ⁻¹` is **not** free — when `n` is even it has the FIXED POINT `ζ = -1` (since `(-1)⁻¹ = -1`
and `(-1)^n = 1`). At a fixed point the conjugation-pairing forces the corresponding shift period to
equal *its own conjugate*, i.e. to be exactly REAL:

> **`eta_negTwoB_isReal`** — for even `n` and any frequency `b`,
> `η_{-2·b} = η_{b·((-1)-1)}` (the `ζ=-1` term of the shift-spectrum) is REAL:
> `(η_{-2b}).im = 0`.

This is the diagonal companion of the off-diagonal pairing: the involution splits the `|μ_n|-1`
nontrivial shift periods into `(|μ_n|-2)/2` conjugate-paired off-diagonal terms PLUS this one
real fixed-point term `η_{-2b}` (the `ζ=-1` term). It localizes the single real *singleton* of the
shift-spectrum to the explicit difference-set frequency `-2b`.

## Mechanism (thinness-essential, NON-MOMENT)
`ζ = -1 ∈ μ_n` requires `(-1)^n = 1`, i.e. `n` even (the subgroup contains the order-2 element).
Then `eta_invShift_eq_conj` at `ζ = -1` gives `η_{b((-1)⁻¹-1)} = conj(η_{b((-1)-1)})`; since
`(-1)⁻¹ = -1`, both sides are `η_{b·(-2)} = η_{-2b}`, so `η_{-2b} = conj(η_{-2b})` ⟹ real.

**Why thinness-essential (rule 3).** It inherits the thinness-essential ingredients of
`eta_invShift_eq_conj` — inverse-closure `(-1)⁻¹ ∈ μ_n` and the coset-invariance
`eta_dilation_invariant`, both FALSE for an unstructured thin set. Probe
`scripts/probes/probe_eta_invol_fixedpt_real.py` confirms `η_{-2b}` is exactly real on PROPER thin
`μ_n` (`m=(p-1)/n ≥ 4`, `n=2^a`, incl. Fermat `4129, 32801, 65537, …`, never `n=q-1`; `real-fails=0`
for the worst `b` and several `b`) while for a random same-size thin set the corresponding sum has
`|im| ≈ 0.2 – 5.1` (NOT forced real).

**Honest scope (rule 6).** This is an EXACT structural reality statement about ONE shift period,
NOT a bound. It does not bound `|η_{-2b}|` or the shift-sum; bounding the (constructive) shift-sum is
the open BGK/Paley cancellation problem. No CORE bound, no capacity / beyond-Johnson / cliff-at-n/2 /
`δ*→0` claim. CORE `M(μ_n) ≤ C√(n log(q/n))` remains OPEN. The value: it identifies the *fixed-point
diagonal* of the inversion involution as the explicit real singleton `η_{-2b}` of the difference-set
shift-spectrum, completing the involution's orbit structure (off-diagonal conjugate pairs + this one
fixed real term).

Axiom-clean. Issues #444, #389.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EtaPointwiseAutocorr
open ArkLib.ProximityGap.EtaAutocorrInvolutionPaired

namespace ArkLib.ProximityGap.EtaInvolutionFixedPointReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedSectionVars false in
/-- **`-1` is the inversion fixed point in `μ_n` when `n` is even.** Since `(-1)^n = 1` for even `n`,
`-1 ∈ nthRootsFinset n 1`. -/
theorem neg_one_mem_nthRootsFinset {n : ℕ} (hn : 0 < n) (hne : Even n) :
    (-1 : F) ∈ nthRootsFinset n (1 : F) := by
  rw [mem_nthRootsFinset hn]
  exact hne.neg_one_pow

/-- **The inversion fixed point pins a REAL difference-set period.** For even `n` the inversion
`ζ ↦ ζ⁻¹` on `μ_n` fixes `ζ = -1`; applying `eta_invShift_eq_conj` at this fixed point yields
`η_{-2b} = conj(η_{-2b})`, so `η_{-2b}` is REAL. (`-2b = b·((-1)-1)` is the `ζ=-1` term of the
pointwise-autocorrelation shift-spectrum.) -/
theorem eta_negTwoB_isReal {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (hne : Even n) (b : F) :
    (eta ψ (nthRootsFinset n (1 : F)) (-2 * b)).im = 0 := by
  have hmem : (-1 : F) ∈ nthRootsFinset n (1 : F) := neg_one_mem_nthRootsFinset hn hne
  -- `eta_invShift_eq_conj` at ζ = -1.
  have h := eta_invShift_eq_conj (ψ := ψ) hn hmem b
  -- `(-1)⁻¹ = -1`, so both `b·((-1)⁻¹-1)` and `b·((-1)-1)` equal `-2*b`.
  have hinv : ((-1 : F)⁻¹ - 1) = ((-1 : F) - 1) := by
    rw [inv_neg, inv_one]
  have harg : b * ((-1 : F) - 1) = -2 * b := by ring
  rw [hinv, harg] at h
  -- now `h : η_{-2b} = conj(η_{-2b})`, i.e. conj fixes it ⟹ im = 0.
  have h' : (starRingEnd ℂ) (eta ψ (nthRootsFinset n (1 : F)) (-2 * b))
      = eta ψ (nthRootsFinset n (1 : F)) (-2 * b) := h.symm
  rwa [Complex.conj_eq_iff_im] at h'

end ArkLib.ProximityGap.EtaInvolutionFixedPointReal

#print axioms ArkLib.ProximityGap.EtaInvolutionFixedPointReal.neg_one_mem_nthRootsFinset
#print axioms ArkLib.ProximityGap.EtaInvolutionFixedPointReal.eta_negTwoB_isReal
