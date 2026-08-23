/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffinePair

/-!
# The slice affine form — decoded slices ARE one affine pencil (#302)

The polynomial-level packaging of the affine-pair extraction: on a heavy monic branch with
ground streams `a b` (the Claim 5.9 output, vanishing past `n`), the decoded surface slice
at EVERY matching place is the fixed affine pencil

`w(ω)(z) = v₀(ω) + z·v₁(ω)`  for all `ω : F`,  where
`v₀ := ∑_{t<n} a t·(X − x₀)^t`, `v₁ := ∑_{t<n} b t·(X − x₀)^t` (degree < n).

This is the exact value shape `AffineCaptured` consumes (`ab.1 + C γ·ab.2` evaluated on the
agreement set), completing the bridge from the hlin discharge to the
`Hab25AffineCapture`/dichotomy machinery: per bad scalar, the §5 proximity data + this
pencil identity + the non-joint-agreement produce `AffineCaptured`, whence
`affineCaptured_improve` gives the dichotomy `hImprove`.

## Main results

* `affinePencil₀`/`affinePencil₁` — the recentred pair, `natDegree < n`.
* `slice_eq_affinePencil_of_heavy` — **the pencil identity** at every matching place.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.7–5.2.8.
* [Hab25] ePrint 2025/2110 — Claim 1 / Lemma 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open BCIKS20.Claim510AffinePair

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510SliceAffine

variable {F : Type} [Field F]

/-- The recentred affine-pencil component: `∑_{t<n} c t·(X − x₀)^t`. -/
noncomputable def affinePencil (x₀ : F) (c : ℕ → F) (n : ℕ) : F[X] :=
  ∑ t ∈ Finset.range n, Polynomial.C (c t) * (Polynomial.X - Polynomial.C x₀) ^ t

/-- The pencil has degree `< n` (for `0 < n`). -/
theorem affinePencil_natDegree_lt (x₀ : F) (c : ℕ → F) {n : ℕ} (hn : 0 < n) :
    (affinePencil x₀ c n).natDegree < n := by
  rw [affinePencil]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_lt]
  refine ⟨hn, fun t ht => ?_⟩
  rw [Finset.mem_range] at ht
  calc (Polynomial.C (c t) * (Polynomial.X - Polynomial.C x₀) ^ t).natDegree
      ≤ (Polynomial.C (c t)).natDegree
          + ((Polynomial.X - Polynomial.C x₀) ^ t).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + t := by
        refine add_le_add (le_of_eq (Polynomial.natDegree_C _)) ?_
        refine le_trans (Polynomial.natDegree_pow_le) ?_
        have hXC : (Polynomial.X - Polynomial.C x₀ : F[X]).natDegree ≤ 1 :=
          Polynomial.natDegree_X_sub_C_le x₀
        calc t * (Polynomial.X - Polynomial.C x₀ : F[X]).natDegree
            ≤ t * 1 := Nat.mul_le_mul_left _ hXC
          _ = t := Nat.mul_one t
    _ < n := by omega

/-- The pencil evaluates as the coefficient sum: `(affinePencil x₀ c n).eval ω
= ∑_{t<n} c t·(ω−x₀)^t`. -/
theorem affinePencil_eval (x₀ : F) (c : ℕ → F) (n : ℕ) (ω : F) :
    (affinePencil x₀ c n).eval ω = ∑ t ∈ Finset.range n, c t * (ω - x₀) ^ t := by
  rw [affinePencil, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]}

/-- **The pencil identity** ([BCIKS20] Step 7→8 hand-off): at every matching place of a
heavy monic branch, the decoded surface slice IS the fixed affine pencil:
`w(ω)(z) = v₀(ω) + z·v₁(ω)` for every `ω : F`. -/
theorem slice_eq_affinePencil_of_heavy
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]} {n : ℕ} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (ω : F) :
    (w.eval (Polynomial.C ω)).eval z
      = (affinePencil x₀ a n).eval ω + z * (affinePencil x₀ b n).eval ω := by
  -- the Taylor reconstruction of the slice value
  set T : F[X][Y] := Polynomial.taylor (Polynomial.C x₀) w with hT
  have hTdeg : T.natDegree < n := by rw [hT, Polynomial.natDegree_taylor]; exact hwn
  have heval : T.eval (Polynomial.C (ω - x₀))
      = ∑ t ∈ Finset.range n, T.coeff t * (Polynomial.C (ω - x₀)) ^ t :=
    Polynomial.eval_eq_sum_range' hTdeg _
  have hslice : (w.eval (Polynomial.C ω)).eval z
      = ∑ t ∈ Finset.range n, (T.coeff t).eval z * (ω - x₀) ^ t := by
    have h1 : T.eval (Polynomial.C (ω - x₀)) = w.eval (Polynomial.C ω) := by
      rw [hT, Polynomial.taylor_eval, ← Polynomial.C_add]
      congr 2
      ring
    rw [← h1, heval, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
  -- substitute the affine coefficient streams
  rw [hslice,
    Finset.sum_congr rfl fun t _ => by
      rw [show (T.coeff t).eval z = a t + z * b t from
        taylor_coeff_eq_affine_of_heavy hHyp hξ hlc hlin hdvd hR z root hx hbase t]]
  rw [affinePencil_eval, affinePencil_eval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end BCIKS20.Claim510SliceAffine

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510SliceAffine.affinePencil_natDegree_lt
#print axioms BCIKS20.Claim510SliceAffine.affinePencil_eval
#print axioms BCIKS20.Claim510SliceAffine.slice_eq_affinePencil_of_heavy
