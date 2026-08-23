/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.Pigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.GoodCoeffs
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Strict-Johnson RS proximity gap, reduced to a single curve list-size residual ([BCIKS20] §5–6)

This file states the *one* remaining research-grade input of the strict-Johnson Reed–Solomon
proximity gap as an explicit named hypothesis — `RSCurveListSizeResidual`, a transparent bound on
the number of distinct codewords a degree-`k` curve is close to — and proves
`RS_jointAgreement_of_curveListSizeResidual`: every elementary/structural component (the
agreement-count pigeonhole + heavy-codeword dichotomy of `AgreementCount`/`Pigeonhole`) is
discharged, so the proximity gap follows from this single residual.

Establishing the residual itself is the trivariate Guruswami–Sudan construction over `ι × F`
([BCIKS20] §5), giving the curve list size `L ≤ deg²/((2·min(1-√ρ-δ, √ρ/20))⁷·|ι|)`; it is the
genuine multi-paper kernel and is left as the named hypothesis.
-/


open Finset BigOperators ReedSolomon
open scoped NNReal

namespace ProximityGap

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **RS-curve list-size residual.** The single research-grade input remaining for the
strict-Johnson Reed–Solomon proximity gap, stated transparently as a *curve list-size* bound:
along the good-coefficient curve, choosing for each good parameter `z` a code-codeword `cw z` that
the curve agrees with on `≥ |ι| - e` coordinates, the number of *distinct* such codewords
(`(G.image cw).card`, the curve list size `L`) times `k·|ι|` stays below `|G|`. Equivalently
`L ≤ |G| / (k·|ι|)`; together with `|G| > k·errorBound·|F|` this is the BCIKS bound
`L ≤ deg²/((2·min(1-√ρ-δ, √ρ/20))⁷·|ι|)`. Establishing it is the trivariate Guruswami–Sudan
construction (BCIKS20 §5). -/
def RSCurveListSizeResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (e : ℕ) : Prop :=
  ∀ (u : Fin (k + 1) → ι → F) (cw : F → ι → F),
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      cw z ∈ ReedSolomon.code domain deg) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = cw z i)).card) →
    ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).image cw).card
        * (k * Fintype.card ι)
      < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card

/-- **Strict-Johnson RS proximity gap, reduced to the single curve list-size residual.** Every
elementary and structural component is discharged: from the list-size residual (the only remaining
research input), the agreement-count pigeonhole + heavy-codeword dichotomy yield joint agreement of
the word stack with the Reed–Solomon code. `0 ∈ code` is automatic (submodule); `k < |F|` and the
`(1-δ)|ι| ≤ |ι|-e` size match are the standard regime hypotheses. -/
theorem RS_jointAgreement_of_curveListSizeResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (e : ℕ)
    (hk : k < Fintype.card F)
    (hsize : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((Fintype.card ι - e : ℕ) : ℝ≥0))
    (hres : RSCurveListSizeResidual (k := k) (deg := deg) (domain := domain) (δ := δ) e)
    (u : Fin (k + 1) → ι → F) (cw : F → ι → F)
    (hcw_mem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      cw z ∈ ReedSolomon.code domain deg)
    (hcw_agree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = cw z i)).card) :
    Code.jointAgreement (κ := Fin (k + 1))
      (↑(ReedSolomon.code domain deg) : Set (ι → F)) δ u :=
  jointAgreement_of_close_codeword_pigeonhole u e
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) cw hk
    (Submodule.zero_mem _) hsize hcw_mem hcw_agree (hres u cw hcw_mem hcw_agree)

end ProximityGap
