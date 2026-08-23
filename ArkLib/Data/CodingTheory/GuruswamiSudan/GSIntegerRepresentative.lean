/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSAffinePair
import Mathlib.RingTheory.Localization.Integer

/-!
# Hab25 §3 Step S10 bridge — integer representative of the GS interpolant and per-`z`
# specialization of the decoded divisibilities

The Theorem-2 union bound (S10) needs the **per-`z` cover**: the scalar folds' decoded
polynomials must arise from the `K = F(Z)`-level decoded list by specializing `Z := z`. The
obstruction is that `Q ∈ K[X][Y]` has rational-function coefficients, so `Z := z` is only a
partial map. This file removes the obstruction and proves the forward (divisibility) half of
the cover, fully residual-free:

* `exists_integer_representative` — **denominator clearing**: every `Q ∈ K[X][Y]` has an
  integer representative `Q₀ ∈ F[Z][X][Y]` with
  `Q₀ ↦ C(C(d)) · Q` for some nonzero `d ∈ F[Z]` (two-level common denominator via
  `IsLocalization.exist_integer_multiples_of_finset` on the doubly-finite coefficient set);

* `integer_representative_eval_eq_zero` — **root transfer**: a decoded root `eval p Q = 0`
  with `p` integral (`p = p₀ ↦ K`) forces `eval p₀ Q₀ = 0` *already over `F[Z][X]`*
  (evaluation commutes with the coefficient embedding, which is injective);

* `specialized_linear_divisibility` — **total specialization**: `eval p₀ Q₀ = 0` specializes
  at **every** `z ∈ F` (the `F[Z] → F` evaluation is a total ring hom):
  `(Y − C p₀(z)) ∣ Q₀|_{Z:=z}`. No bad set, no `d(z) ≠ 0` hypothesis for the divisibility;

* `affinePairLift` + `decoded_affine_pair_divides_specialization` — the **capstone**,
  composing with the proven S6 affine pair: for every decoded codeword `p = a + Z·b` of the
  generic fold, and every `z ∈ F`,

    `(Y − C (a + z·b)) ∣ Q₀|_{Z:=z}`.

  The per-`z` decoded polynomial `q_z = a + z·b` of **every** scalar fold divides the
  specialized integer interpolant — the forward half of the S10 cover `E = ⋃ E_{i,j}`,
  with the factor index supplied by the S4 factorization of `Q₀|_{Z:=z}`.

What remains of S10 after this file is only the *converse* inclusion (every close scalar
fold's decoded polynomial appears in the `K`-level list), which needs the specialized
`Conditions` (the `d(z) ≠ 0` finitely-bad-`z` argument) + per-`z` GS divisibility.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-! ## Denominator clearing: the integer representative -/

/-- **Two-level denominator clearing.** Every bivariate polynomial over `K = F(Z)` has an
integer representative over `F[Z]`: there are `d ∈ F[Z] \ {0}` and `Q₀ ∈ F[Z][X][Y]` with
`Q₀ ↦ C(C(d))·Q` under the coefficientwise embedding `F[Z] → F(Z)`. The common denominator
is produced by `IsLocalization.exist_integer_multiples_of_finset` on the (doubly finite)
set of coefficients of `Q`. -/
theorem exists_integer_representative (Q : (RatFunc F)[X][Y]) :
    ∃ (d : F[X]) (Q₀ : (F[X])[X][Y]), d ≠ 0 ∧
      Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
        Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q := by
  classical
  set φ := algebraMap F[X] (RatFunc F) with hφ
  set s : Finset (RatFunc F) :=
    Q.support.biUnion (fun i => (Q.coeff i).support.image fun j => (Q.coeff i).coeff j)
    with hs
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors F[X]) s
  have hd0 : (b : F[X]) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hex : ∀ i j : ℕ, ∃ q : F[X], φ q = (b : F[X]) • ((Q.coeff i).coeff j) := by
    intro i j
    by_cases hc : (Q.coeff i).coeff j = 0
    · exact ⟨0, by rw [hc, smul_zero, map_zero]⟩
    · have hi : i ∈ Q.support := by
        rw [Polynomial.mem_support_iff]
        intro h0
        rw [h0, Polynomial.coeff_zero] at hc
        exact hc rfl
      have hj : j ∈ (Q.coeff i).support := Polynomial.mem_support_iff.mpr hc
      exact hb _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩)
  set cf : ℕ → ℕ → F[X] := fun i j => (hex i j).choose with hcfdef
  have hcf : ∀ i j, φ (cf i j) = (b : F[X]) • ((Q.coeff i).coeff j) :=
    fun i j => (hex i j).choose_spec
  set Q₀ : (F[X])[X][Y] :=
    ∑ i ∈ Q.support, Polynomial.monomial i
      (∑ j ∈ (Q.coeff i).support, Polynomial.monomial j (cf i j)) with hQ₀
  refine ⟨b, Q₀, hd0, ?_⟩
  -- the outer coefficients of `Q₀`
  have h1 : ∀ i, Q₀.coeff i =
      ∑ j ∈ (Q.coeff i).support, Polynomial.monomial j (cf i j) := by
    intro i
    rw [hQ₀, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' Q.support i]
    split_ifs with hi
    · rfl
    · have h0 : Q.coeff i = 0 := by
        by_contra hne
        exact hi (Polynomial.mem_support_iff.mpr hne)
      rw [h0]
      simp
  -- the inner coefficients of `Q₀`
  have h2 : ∀ i j, (Q₀.coeff i).coeff j = cf i j := by
    intro i j
    rw [h1, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Q.coeff i).support j]
    split_ifs with hj
    · rfl
    · have hc : (Q.coeff i).coeff j = 0 := by
        by_contra hne
        exact hj (Polynomial.mem_support_iff.mpr hne)
      have : φ (cf i j) = 0 := by rw [hcf, hc, smul_zero]
      exact ((map_eq_zero_iff φ (RatFunc.algebraMap_injective F)).mp this).symm
  -- coefficientwise comparison
  refine Polynomial.ext fun i => Polynomial.ext fun j => ?_
  rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map, h2,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, hcf, Algebra.smul_def]

/-! ## Root transfer down to `F[Z][X]` and total specialization at every `z` -/

/-- **Root transfer.** If `p` is a decoded root of `Q` over `K` (`eval p Q = 0`) and `p` is
integral (`p₀ ↦ p`), then the integer representative `Q₀` already has the root `p₀` over
`F[Z][X]`: evaluation commutes with the (injective) coefficient embedding, and the
denominator factor `C(C d)` evaluates to a constant. -/
theorem integer_representative_eval_eq_zero
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    {p₀ : (F[X])[X]} {p : (RatFunc F)[X]}
    (hp : p₀.map (algebraMap F[X] (RatFunc F)) = p)
    (hroot : Polynomial.eval p Q = 0) :
    Polynomial.eval p₀ Q₀ = 0 := by
  set φ := algebraMap F[X] (RatFunc F) with hφ
  have hinj : Function.Injective (Polynomial.map φ) :=
    Polynomial.map_injective φ (RatFunc.algebraMap_injective F)
  apply hinj
  rw [Polynomial.map_zero]
  -- evaluation commutes with the coefficient embedding
  have h2 := Polynomial.eval₂_at_apply (p := Q₀) (Polynomial.mapRingHom φ) p₀
  rw [Polynomial.coe_mapRingHom] at h2
  calc (Polynomial.eval p₀ Q₀).map φ
      = Polynomial.eval₂ (Polynomial.mapRingHom φ) (p₀.map φ) Q₀ := h2.symm
    _ = Polynomial.eval (p₀.map φ)
          (Q₀.map (Polynomial.mapRingHom φ)) := (Polynomial.eval_map _ _).symm
    _ = Polynomial.eval p (Polynomial.C (Polynomial.C (φ d)) * Q) := by rw [hp, hrep]
    _ = Polynomial.C (φ d) * Polynomial.eval p Q := by
          rw [Polynomial.eval_mul, Polynomial.eval_C]
    _ = 0 := by rw [hroot, mul_zero]

/-- **Total specialization.** A root over `F[Z][X]` specializes at **every** `z ∈ F` —
the evaluation `F[Z] → F` is a total ring hom, so there is no bad set:
`(Y − C p₀(z)) ∣ Q₀|_{Z:=z}` for all `z`. -/
theorem specialized_linear_divisibility
    {Q₀ : (F[X])[X][Y]} {p₀ : (F[X])[X]}
    (hroot : Polynomial.eval p₀ Q₀ = 0) (z : F) :
    (Polynomial.X - Polynomial.C (p₀.map (Polynomial.evalRingHom z))) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  have h2 := Polynomial.eval₂_at_apply (p := Q₀)
    (Polynomial.mapRingHom (Polynomial.evalRingHom z)) p₀
  rw [Polynomial.coe_mapRingHom] at h2
  calc Polynomial.eval (p₀.map (Polynomial.evalRingHom z))
        (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
      = Polynomial.eval₂ (Polynomial.mapRingHom (Polynomial.evalRingHom z))
          (p₀.map (Polynomial.evalRingHom z)) Q₀ := Polynomial.eval_map _ _
    _ = (Polynomial.eval p₀ Q₀).map (Polynomial.evalRingHom z) := h2
    _ = 0 := by rw [hroot, Polynomial.map_zero]

/-! ## The affine-pair lift and the S10 forward cover -/

/-- The integral lift of an affine pair: `a + Z·b ∈ F[Z][X]` (coefficients in `F[Z]`). -/
noncomputable def affinePairLift (a b : F[X]) : (F[X])[X] :=
  a.map (Polynomial.C : F →+* F[X]) +
    Polynomial.C (Polynomial.X : F[X]) * b.map (Polynomial.C : F →+* F[X])

/-- The affine-pair lift maps to the `K = F(Z)`-level affine pair. -/
theorem affinePairLift_map (a b : F[X]) :
    (affinePairLift a b).map (algebraMap F[X] (RatFunc F)) =
      a.map (algebraMap F (RatFunc F)) +
        Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)) := by
  have hcomp : (algebraMap F[X] (RatFunc F)).comp (Polynomial.C : F →+* F[X]) =
      algebraMap F (RatFunc F) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply F F[X] (RatFunc F),
      Polynomial.algebraMap_eq]
  rw [affinePairLift, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_map,
    Polynomial.map_map, hcomp, Polynomial.map_C, RatFunc.algebraMap_X]

/-- The affine-pair lift specializes at `Z := z` to the scalar fold's decoded polynomial
`a + z·b`. -/
theorem affinePairLift_specialize (a b : F[X]) (z : F) :
    (affinePairLift a b).map (Polynomial.evalRingHom z) = a + Polynomial.C z * b := by
  have hcomp : (Polynomial.evalRingHom z).comp (Polynomial.C : F →+* F[X]) =
      RingHom.id F := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C, RingHom.id_apply]
  rw [affinePairLift, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_map,
    Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_id, Polynomial.map_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_X]

/-- **Hab25 §3 — the S10 forward cover, fully residual-free.**

Let `p` be a decoded codeword of the `K = F(Z)`-level list (`(Y − C p) ∣ Q`) with affine
pair `p = a + Z·b` (supplied by the proven S6 kernel `affine_pair_of_hammingDist`), and let
`(d, Q₀)` be an integer representative of `Q`. Then for **every** scalar `z ∈ F`, the
scalar fold's decoded polynomial `q_z = a + z·b` divides the specialized integer
interpolant:

  `(Y − C (a + z·b)) ∣ Q₀|_{Z:=z}`.

The factorization of `Q₀|_{Z:=z}` (S4) then indexes the per-`z` exceptional sets `E_{i,j}`,
giving the forward half of the Theorem-2 cover `E = ⋃ E_{i,j}` with zero residual
hypotheses — no bad-`z` set is needed on this side. -/
theorem decoded_affine_pair_divides_specialization
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    {p : (RatFunc F)[X]} (hdvd : (Polynomial.X - Polynomial.C p) ∣ Q)
    {a b : F[X]}
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)))
    (z : F) :
    (Polynomial.X - Polynomial.C (a + Polynomial.C z * b)) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  have hroot : Polynomial.eval p Q = 0 := Polynomial.dvd_iff_isRoot.mp hdvd
  have hp : (affinePairLift a b).map (algebraMap F[X] (RatFunc F)) = p := by
    rw [affinePairLift_map, haffine]
  have h0 : Polynomial.eval (affinePairLift a b) Q₀ = 0 :=
    integer_representative_eval_eq_zero hrep hp hroot
  have hspec := specialized_linear_divisibility h0 z
  rwa [affinePairLift_specialize] at hspec

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.exists_integer_representative
#print axioms GuruswamiSudan.OverRatFunc.integer_representative_eval_eq_zero
#print axioms GuruswamiSudan.OverRatFunc.specialized_linear_divisibility
#print axioms GuruswamiSudan.OverRatFunc.affinePairLift_map
#print axioms GuruswamiSudan.OverRatFunc.affinePairLift_specialize
#print axioms GuruswamiSudan.OverRatFunc.decoded_affine_pair_divides_specialization
