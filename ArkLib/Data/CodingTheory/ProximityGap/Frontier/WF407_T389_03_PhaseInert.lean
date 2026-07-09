/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# WF407 / T389-03 — Phase alignment is the WORST-CASE branch (structural inertness)

Companion to `Sweep_A12_PhaseAlignmentTower.lean`. That file lands the exact 2-adic recursion
(split + twist + parallelogram + the alignment ⟺ cross-term-nonneg characterization). This file
adds the ONE sharper named lemma that settles part (3) of the actionable for thread **T389-03**:

> Can the exact `cos = 1` phase alignment at the worst frequency `b*` be combined with a
> *non-moment* input to bound `B = max_{b≠0} ‖η_b(μ_n)‖`, or is it structurally inert?

**Verdict (formalized below): structurally inert as a downward lever.** At the worst frequency
the two half-coset periods `A := η_{b*}(μ_{n/2})`, `B := η_{b*z}(μ_{n/2})` are aligned, so the
worst-case period sits at the *upper* parallelogram branch `η_{b*}(μ_n) = A + B` with
`‖A+B‖ ≥ √(‖A‖²+‖B‖²)` (Cauchy–Schwarz, with equality only at `A=0` or `B=0`). Alignment selects
the **maximal** of the two branches `{‖A+B‖, ‖A−B‖}` — it makes `B(μ_n)` as *large* as the
magnitudes `‖A‖,‖B‖` permit. So combining alignment with any magnitude-only fact (the proven
`E_2`/Parseval pins) can only *raise* the bound: it never beats the trivial `‖A+B‖ ≤ ‖A‖+‖B‖`
Cauchy–Schwarz ceiling. The downward force on `B` must come from a bound on the magnitudes
themselves (equidistribution / additive energy of `μ_{n/2}` = the W2/BGK/Paley wall), which is
exactly the input alignment does **not** supply.

This is the dual of the refuted descent: the parallelogram is an exact equality, alignment
fixes the cross-term **sign** (`+`), but its **size** `Re(A·conj B) = ‖A‖‖B‖·cos` (`= +‖A‖‖B‖`
at `cos=1`) is the open quantity, governed by the same analytic wall.

Numerics: `scripts/probes/wf407_T389-03-phase_inertness.py` (exact, full coset scan, n=8,16,32,
both `p~n²` and prize-shaped `p~n⁴`): in ALL cases `B(μ_n)` realizes the UPPER branch `‖A‖+‖B‖`
(LEVER3), the cross inflation `(‖A‖+‖B‖)²/(‖A‖²+‖B‖²)∈[1.52,2.00]` (size open, sign fixed,
LEVER2), and the doubling ceiling `B(n)/B(n/2)<2` towers to `2^μ ≫ √(n log n)` (LEVER1, useless).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- DISPROOF_LOG `[#407] 2026-06-13 (2)`: the descent USE of this alignment is refuted; this is the
  STRUCTURAL fact + the inertness statement, not a descent.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.WF407_T389_03

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Reindexing the `z`-coset** (inlined from `Sweep_A12`): `η_b` over `z·G_half` equals
`η_{b·z}` over `G_half`. Pure `Finset.sum_image` + `b·(z·y) = (b·z)·y`. -/
theorem eta_over_smul_coset (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F) (hz : z ≠ 0) :
    eta ψ (Ghalf.image (fun y => z * y)) b = eta ψ Ghalf (b * z) := by
  unfold eta
  rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel₀ hz h)]
  exact Finset.sum_congr rfl (fun y _ => by rw [mul_assoc])

/-- **The untwisted half-coset split** (inlined from `Sweep_A12`): for `G = G_half ⊔ z·G_half`,
`η_b(G) = η_b(G_half) + η_{b·z}(G_half) = A + B`. -/
theorem eta_split_coset (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F) (hz : z ≠ 0)
    (hdisj : Disjoint Ghalf (Ghalf.image (fun y => z * y))) :
    eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b
      = eta ψ Ghalf b + eta ψ Ghalf (b * z) := by
  have hsplit : eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b
      = eta ψ Ghalf b + eta ψ (Ghalf.image (fun y => z * y)) b := by
    unfold eta; exact Finset.sum_union hdisj
  rw [hsplit, eta_over_smul_coset ψ Ghalf b z hz]

/-- **The alignment characterization** (inlined from `Sweep_A12`): `‖A−B‖² ≤ ‖A+B‖²` iff the
cross term `Re(A·conj B) ≥ 0`. -/
theorem untwisted_ge_twisted_iff_align (A B : ℂ) :
    ‖A - B‖ ^ 2 ≤ ‖A + B‖ ^ 2 ↔ 0 ≤ (A * (starRingEnd ℂ) B).re := by
  have hcross : ‖A + B‖ ^ 2 - ‖A - B‖ ^ 2 = 4 * (A * (starRingEnd ℂ) B).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]; ring
  rw [← sub_nonneg, hcross]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The aligned (untwisted) branch dominates the RMS of its two children.** For ANY two complex
values `A, B` with nonnegative cross term `0 ≤ Re(A·conj B)` (the alignment condition, exactly
`cos ≥ 0` and at the worst frequency `cos = 1`), the untwisted norm satisfies
`‖A‖² + ‖B‖² ≤ ‖A + B‖²`.

This is the structural-inertness core: alignment makes `‖A+B‖` (the worst-case period at `b*`)
at least the **root-mean-square** `√(‖A‖²+‖B‖²)` of the two half-periods — the maximal of the two
parallelogram branches. Alignment therefore pushes `B(μ_n)` UP toward `‖A‖+‖B‖`; it can never be
the source of a downward bound on `B`. (Proof: `‖A+B‖² = ‖A‖²+‖B‖²+2·Re(A·conj B)` and the cross
term is `≥ 0`.) -/
theorem aligned_branch_ge_rms (A B : ℂ) (halign : 0 ≤ (A * (starRingEnd ℂ) B).re) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ ‖A + B‖ ^ 2 := by
  have hsum : ‖A + B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * (A * (starRingEnd ℂ) B).re := by
    have h1 : ‖A + B‖ ^ 2 = Complex.normSq (A + B) := Complex.sq_norm (A + B)
    have h2 : ‖A‖ ^ 2 = Complex.normSq A := Complex.sq_norm A
    have h3 : ‖B‖ ^ 2 = Complex.normSq B := Complex.sq_norm B
    rw [h1, h2, h3, Complex.normSq_add]
  rw [hsum]; linarith

/-- **Alignment selects the MAXIMAL parallelogram branch.** With `0 ≤ Re(A·conj B)`, the untwisted
branch `‖A+B‖` is `≥` the twisted branch `‖A−B‖`. Combined with `aligned_branch_ge_rms`, the
worst-case Gauss period at `b*` is the *largest* value compatible with the two child magnitudes
`‖A‖, ‖B‖`: `√(‖A‖²+‖B‖²) ≤ ‖A+B‖`, and the twisted companion is the *smaller* branch. There is no
inequality direction here that lowers `‖A+B‖` from the magnitudes — that is the inertness. -/
theorem aligned_is_max_branch (A B : ℂ) (halign : 0 ≤ (A * (starRingEnd ℂ) B).re) :
    ‖A - B‖ ≤ ‖A + B‖ ∧ ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ ‖A + B‖ ^ 2 := by
  refine ⟨?_, aligned_branch_ge_rms A B halign⟩
  have hsq : ‖A - B‖ ^ 2 ≤ ‖A + B‖ ^ 2 := (untwisted_ge_twisted_iff_align A B).mpr halign
  exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq

/-- **The Cauchy–Schwarz ceiling is never beaten by alignment (inertness, top-level form).** At the
worst frequency `b*`, with `A = η_{b*}(G_half)`, `B = η_{b*z}(G_half)` aligned, the worst-case
Gauss period `η_{b*}(μ_n) = A + B` is squeezed between the RMS floor and the `ℓ¹` ceiling:
`√(‖A‖²+‖B‖²) ≤ ‖η_{b*}(μ_n)‖ ≤ ‖A‖ + ‖B‖`. Both ends are *magnitude-only* — alignment fixes the
position WITHIN this band (at the top, `‖A‖+‖B‖`, when `cos = 1`) but supplies no force pulling the
band's endpoints down. Any improvement on `B` must lower `‖A‖, ‖B‖` (the half-period magnitudes =
the equidistribution / additive-energy wall), NOT the alignment. -/
theorem worst_period_squeezed_of_align (ψ : AddChar F ℂ) (Ghalf : Finset F) (b z : F)
    (hz : z ≠ 0) (hdisj : Disjoint Ghalf (Ghalf.image (fun y => z * y)))
    (halign : 0 ≤ (eta ψ Ghalf b * (starRingEnd ℂ) (eta ψ Ghalf (b * z))).re) :
    Real.sqrt (‖eta ψ Ghalf b‖ ^ 2 + ‖eta ψ Ghalf (b * z)‖ ^ 2)
        ≤ ‖eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b‖
      ∧ ‖eta ψ (Ghalf ∪ Ghalf.image (fun y => z * y)) b‖
        ≤ ‖eta ψ Ghalf b‖ + ‖eta ψ Ghalf (b * z)‖ := by
  rw [eta_split_coset ψ Ghalf b z hz hdisj]
  set A := eta ψ Ghalf b
  set B := eta ψ Ghalf (b * z)
  refine ⟨?_, norm_add_le A B⟩
  have hge : ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ ‖A + B‖ ^ 2 := aligned_branch_ge_rms A B halign
  rw [show ‖A + B‖ = Real.sqrt (‖A + B‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hge

/-
**VERDICT (T389-03 — phase alignment, structural inertness).**
Probe `scripts/probes/wf407_T389-03-phase_inertness.py` (exact, full coset scan):
- LEVER3 (the decisive one, formalized above as `aligned_is_max_branch`/`worst_period_squeezed`):
  at `b*` the worst-case period is ALWAYS the UPPER branch `‖A‖+‖B‖ ≥ √(‖A‖²+‖B‖²)` — alignment
  is the worst-case OBSTRUCTION, not a downward lever; it never beats Cauchy–Schwarz.
- LEVER2: alignment fixes the cross-term SIGN (`+`); its SIZE `‖A‖‖B‖` is the open quantity,
  governed by `E_2`/equidistribution = the W2/BGK/Paley wall.
- LEVER1: the doubling ceiling `B(n) ≤ 2·B(n/2)` holds (const `<2`, `→2` at `β=4`) but towers to
  `2^μ ≫ √(n log n)` — the dual of the refuted descent.

CONCLUSION: the exact phase alignment is STRUCTURALLY INERT as a bound on `B` absent an external
analytic (equidistribution / additive-energy) input. It is a precise statement of the worst-vs-
average coherent-addition mechanism — a clean structural fact, NOT a closure. Axiom-clean, no
fabricated input.
-/

end ArkLib.ProximityGap.WF407_T389_03

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.WF407_T389_03.eta_split_coset
#print axioms ArkLib.ProximityGap.WF407_T389_03.untwisted_ge_twisted_iff_align
#print axioms ArkLib.ProximityGap.WF407_T389_03.aligned_branch_ge_rms
#print axioms ArkLib.ProximityGap.WF407_T389_03.aligned_is_max_branch
#print axioms ArkLib.ProximityGap.WF407_T389_03.worst_period_squeezed_of_align
