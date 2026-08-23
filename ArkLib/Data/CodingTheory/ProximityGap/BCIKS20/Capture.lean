/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.SliceAffine
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AffineCapture

/-!
# Affine capture from the heavy pencil — the hlin ⟹ dichotomy hand-off (#302)

The terminal assembly of the geometric hlin lane: the pencil identity
(`slice_eq_affinePencil_of_heavy`) composed with the per-scalar §5 **proximity data** (the
fold agrees with the decoded slice on a large set `S` with no joint agreement — the
`mcaEvent` shape) produces `AffineCaptured` for every captured bad scalar — the exact input
of `affineCaptured_improve` (the dichotomy `hImprove`) and
`exists_algebraicData_of_affine_capture`/`johnsonNumericBound_of_affine_capture`.

## Main results

* `affineCaptured_of_pencil_proximity` — **the capture**: pencil identity + per-scalar
  proximity ⟹ `AffineCaptured` at the explicit pencil pair.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.8 (Step 8).
* [Hab25] ePrint 2025/2110 — Claim 1 / Lemma 1.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open BCIKS20.Claim510SliceAffine
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open _root_.ProximityGap Code
open CodingTheory
open scoped NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510Capture

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]}

/-- **Affine capture from the heavy pencil.**  For a bad scalar `z` whose §5 proximity
witness set `S` (large, fold-agreeing with the decoded slice, no joint agreement) lies over
a matching place, the pencil identity captures `z` at the explicit pair
`(affinePencil x₀ a n, affinePencil x₀ b n)`. -/
theorem affineCaptured_of_pencil_proximity
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]} {n : ℕ} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    -- the place data at the bad scalar
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    -- the §5 proximity data at `z`: a large witness set, fold agreement with the decoded
    -- slice, and no joint agreement (the `mcaEvent` shape)
    (domain : ι₀ ↪ F) (k : ℕ) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι₀)
    (S : Finset ι₀)
    (hScard : ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀))
    (hSagree : ∀ i ∈ S, (w.eval (Polynomial.C (domain i))).eval z = u 0 i + z • u 1 i)
    (hSnoJoint : ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code domain k : Set (ι₀ → F))) S (u 0) (u 1)) :
    AffineCaptured domain k δ u z
      (affinePencil x₀ a n, affinePencil x₀ b n) := by
  refine ⟨S, hScard, fun i hi => ?_, hSnoJoint⟩
  have hpencil := slice_eq_affinePencil_of_heavy hHyp hξ hlc hlin hwn hdvd hR z root hx
    hbase (domain i)
  have hagree := hSagree i hi
  rw [hpencil] at hagree
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hagree]

end BCIKS20.Claim510Capture

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Capture.affineCaptured_of_pencil_proximity
