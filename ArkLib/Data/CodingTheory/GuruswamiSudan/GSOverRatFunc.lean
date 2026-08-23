/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Guruswami–Sudan interpolation over the rational-function field `K = F(Z)`

This file discharges **Step S2** of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`), which was previously recorded as a
genuinely-deep residual with the note *"no algebraic-function-field interpolation API in tree"*.

The observation is that the in-tree single-function existence theorem
`GuruswamiSudan.gs_existence` is stated over an **arbitrary field** `(F : Type) [Field F]
[DecidableEq F]` with purely numeric hypotheses (`1 < k`, `n ≠ 0`, `1 ≤ m`). Mathlib's
`RatFunc F` is itself a field whenever `F` is, so instantiating `gs_existence` at the field
`K := RatFunc F` *is* the algebraic-function-field interpolation API: it produces, for the
**generic fold** `f₀ + Z·f₁` (with `Z = RatFunc.X`) over the lifted evaluation domain, a nonzero
Guruswami–Sudan interpolant `Q(X, Y) ∈ K[X][Y]` of bounded `(1, k-1)`-weighted degree vanishing
to multiplicity `≥ m` at every point `(ω_i, f₀ i + Z·f₁ i)`.

This is the §3 generalisation of `[BCIKS20 §5]` from `F` to `K = F(Z)` (paper Step S2). No
`sorry`, no `axiom`: the entire content is a single instantiation of the proven `gs_existence`
at `RatFunc F`, together with the (classical) decidable-equality instance on `RatFunc F`.

The downstream deep steps S3–S6 (degree bounds over `K`, factorisation, discriminant
non-vanishing, the Hensel lift producing the *unique affine pairs*) remain; this file supplies the
GS interpolant they all start from.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

-- `RatFunc F` (a field of fractions) carries no computable `DecidableEq`; the GS `Conditions`
-- structure and `hammingDist` require one, so we supply the classical instance file-locally.
attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- The injective field embedding `F ↪ F(Z) = RatFunc F` (the structure map of `F`-algebra
`RatFunc F`, which is injective since it is a homomorphism of fields). -/
noncomputable def coeFieldEmb : F ↪ RatFunc F :=
  ⟨algebraMap F (RatFunc F), (algebraMap F (RatFunc F)).injective⟩

@[simp] lemma coeFieldEmb_apply (x : F) : coeFieldEmb x = algebraMap F (RatFunc F) x := rfl

/-- The **generic fold** `f₀ + Z·f₁ : Fin n → F(Z)` of two received words `f₀, f₁ : Fin n → F`,
with the formal variable `Z := RatFunc.X`. This is the word over `K = F(Z)` whose
Guruswami–Sudan interpolant simultaneously decodes every scalar fold `f₀ + z·f₁` (`z ∈ F`). -/
noncomputable def genericFold {n : ℕ} (f₀ f₁ : Fin n → F) : Fin n → RatFunc F :=
  fun i => algebraMap F (RatFunc F) (f₀ i) + RatFunc.X * algebraMap F (RatFunc F) (f₁ i)

/-- The evaluation domain `ωs : Fin n ↪ F`, transported along `coeFieldEmb` into `K = F(Z)`. -/
noncomputable def liftedDomain {n : ℕ} (ωs : Fin n ↪ F) : Fin n ↪ RatFunc F :=
  ωs.trans coeFieldEmb

/-- **Hab25 §3, Step S2 — Guruswami–Sudan interpolation over `K = F(Z)`, discharged.**

For received words `f₀, f₁ : Fin n → F`, an evaluation domain `ωs : Fin n ↪ F`, parameters
`1 < k`, `n ≠ 0`, `1 ≤ m`, there exists a nonzero bivariate polynomial
`Q ∈ (RatFunc F)[X][Y]` satisfying the Guruswami–Sudan `Conditions` over the field `K = F(Z)`:
* `Q ≠ 0`;
* its `(1, k-1)`-weighted degree is `≤ gs_degree_bound k n m`;
* every lifted interpolation point `(ω_i, f₀ i + Z·f₁ i)` is a root of multiplicity `≥ m`.

This is the generic-fold interpolant the paper's Steps S3–S6 factor and Hensel-lift. The proof is
a direct instantiation of the in-tree, field-generic `GuruswamiSudan.gs_existence` at the field
`RatFunc F`; the only nonconstructive ingredient is decidable equality on `RatFunc F`. -/
theorem gs_existence_over_ratfunc {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q := by
  classical
  exact GuruswamiSudan.gs_existence (m := m) k n (liftedDomain ωs) (genericFold f₀ f₁) hk hn hm

/-- **Divisibility consequence over `K = F(Z)` (Step S1 at the generic level).**

If a degree-`< k` codeword polynomial `p ∈ K[X]` (here `K = RatFunc F`) is within the
Guruswami–Sudan Johnson radius of the generic fold — measured by the Hamming distance over the
lifted domain — then `X - C p` divides the interpolant `Q`. This is `GuruswamiSudan.gs_divisibility`
specialised to the rational-function field; it is the per-codeword factor extraction that Step S6
(Hensel) refines to the *unique affine pair*. -/
theorem gs_divisibility_over_ratfunc {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (p : ReedSolomon.code (liftedDomain ωs) k)
    {Q : (RatFunc F)[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (h_dist :
      (hammingDist (genericFold f₀ f₁)
          (fun i => (ReedSolomon.codewordToPoly p).eval ((liftedDomain ωs) i)) : ℝ) / n <
        gs_johnson k n m) :
    X - C (ReedSolomon.codewordToPoly p) ∣ Q := by
  classical
  exact GuruswamiSudan.gs_divisibility (m := m) hk hm p hQ h_dist

end GuruswamiSudan.OverRatFunc
