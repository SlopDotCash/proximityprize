/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaAutocorrInvolutionPaired

/-!
# The worst period² as `|μ_n|` plus a REAL cosine shift-sum (#444, #389)

This combines the two just-landed pointwise-autocorrelation results into the directly-usable closed
form for the single-frequency worst period²:

* `EtaPointwiseAutocorr.eta_normSq_eq_card_add_nontrivial`:
  `(‖η_b‖² : ℂ) = |μ_n| + ∑_{ζ≠1} η_{b(ζ-1)}`  (the difference-set fixed-point form);
* `EtaAutocorrInvolutionPaired.pointwise_autocorr_shiftSum_isReal`:
  the nontrivial shift-sum `∑_{ζ≠1} η_{b(ζ-1)}` is REAL.

Since the shift-sum is real, it equals the sum of the *real parts* of its terms, giving the
**real-shift closed form**:

> **`eta_normSq_eq_card_add_sum_re`** —
> `‖η_b‖² = |μ_n| + ∑_{ζ ∈ μ_n \ {1}} Re(η_{b·(ζ-1)})`  (a real-number identity),

lossless because `sum_im_shift_eq_zero`: `∑_{ζ≠1} Im(η_{b(ζ-1)}) = 0` (the involution reality).

Each `Re(η_{b(ζ-1)}) = ∑_{x∈μ_n} cos(2π·b(ζ-1)x / p)` is a cosine sum, so the worst period² is `|μ_n|`
plus a genuine **sum of cosine sums** over the difference-set spectrum — the form in which any
prospective `‖η_b‖²`-bound must be proved (a real-valued aggregate, not a complex one). This packages
the involution's reality result into the shape future bounds will consume.

## Why this is the right downstream form (NON-MOMENT)
The pointwise identity alone leaves `‖η_b‖²` equal to a *complex-valued* sum `∑ η_{b(ζ-1)}` whose
realness is non-obvious; bounding a complex sum requires handling its (a priori nonzero) imaginary
part. The involution kills the imaginary part exactly, so the operative object is the REAL sum
`∑_{ζ≠1} Re η_{b(ζ-1)}`. The remaining open problem — the BGK/Paley cancellation — is now a statement
purely about this real cosine sum (its terms can be `±` and interfere constructively at the worst `b`).

**Honest scope (rule 6).** EXACT identity, NOT a bound. It re-expresses `‖η_b‖²` as `|μ_n|` plus a real
cosine sum but does NOT bound that sum; bounding it is the open BGK/Paley cancellation problem. No CORE
bound, no capacity / beyond-Johnson / cliff-at-n/2 / `δ*→0` claim. CORE `M(μ_n) ≤ C√(n log(q/n))` remains
OPEN. Thinness-essential: inherits the subgroup hypotheses of both consumed theorems (the realness fails
for an unstructured thin set — see `EtaAutocorrInvolutionPaired`).

Axiom-clean. Issues #444, #389.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EtaPointwiseAutocorr
open ArkLib.ProximityGap.EtaAutocorrInvolutionPaired

namespace ArkLib.ProximityGap.EtaNormSqRealShiftForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The worst period² as `|μ_n|` plus a REAL cosine shift-sum.** Combining the pointwise
fixed-point form `‖η_b‖² = |G| + ∑_{ζ≠1} η_{b(ζ-1)}` with the involution reality of the shift-sum,
the (real) worst period² equals `|G|` plus the sum of the REAL PARTS of the difference-set periods:

> `‖η_b‖² = |μ_n| + ∑_{ζ ∈ μ_n \ {1}} Re(η_{b·(ζ-1)})`.

This is the directly-usable downstream form: a real-valued aggregate (a sum of cosine sums) rather
than a complex one. (Stated with `(μ_n.card : ℝ)`; for a proper thin subgroup `μ_n.card = n`.) -/
theorem eta_normSq_eq_card_add_sum_re {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n)
    (hbij : ∀ u ∈ nthRootsFinset n (1 : F),
      (nthRootsFinset n (1 : F)).image (fun z => u * z) = nthRootsFinset n (1 : F))
    (h0 : (0 : F) ∉ nthRootsFinset n (1 : F)) (b : F) :
    (‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2 : ℝ)
      = ((nthRootsFinset n (1 : F)).card : ℝ)
        + ∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
            (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).re := by
  classical
  set G := nthRootsFinset n (1 : F) with hG
  have h1 : (1 : F) ∈ G := one_mem_nthRootsFinset hn
  -- The complex fixed-point identity:
  have hC : ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = (G.card : ℂ) + ∑ ζ ∈ G.erase 1, eta ψ G (b * (ζ - 1)) :=
    eta_normSq_eq_card_add_nontrivial hbij h0 h1 b
  -- Take real parts of the complex identity; LHS is already a real cast, `Re(z+w)=Re z+Re w`,
  -- `Re (G.card : ℂ) = G.card`, `Re (∑ ..) = ∑ Re ..`.
  have hre := congrArg Complex.re hC
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
    Complex.re_sum] using hre

#print axioms ArkLib.ProximityGap.EtaNormSqRealShiftForm.eta_normSq_eq_card_add_sum_re

/-- **The dropped imaginary parts cancel exactly.** The real-shift form
`eta_normSq_eq_card_add_sum_re` keeps only the real parts of the difference-set periods; this is
lossless precisely because the involution forces `∑_{ζ≠1} Im(η_{b(ζ-1)}) = 0`
(`pointwise_autocorr_shiftSum_isReal`). Without the subgroup structure this would be false (the
imaginary parts do NOT cancel for an unstructured thin set), so the real-shift form is
thinness-essential. -/
theorem sum_im_shift_eq_zero {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (b : F) :
    ∑ ζ ∈ (nthRootsFinset n (1 : F)).erase 1,
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).im = 0 := by
  have h := pointwise_autocorr_shiftSum_isReal (ψ := ψ) hn b
  rwa [Complex.im_sum] at h

#print axioms ArkLib.ProximityGap.EtaNormSqRealShiftForm.sum_im_shift_eq_zero

end ArkLib.ProximityGap.EtaNormSqRealShiftForm
