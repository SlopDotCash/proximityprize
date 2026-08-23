/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSOverRatFunc
import Mathlib.LinearAlgebra.Lagrange

/-!
# Hab25 §3 Step S6 deep kernel — the unique affine pair, by Lagrange descent

The deepest remaining node of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`) was S6: every decoded codeword of
the **generic fold** `f₀ + Z·f₁` over `K = F(Z)` is an **affine pair**
`p = a + Z·b` with `a, b ∈ F[X]` of degree `< k` — the paper packages this inside the Hensel
lift (`R_{i,j} = (Y − (a+Zb))^{p^f}`). This file proves the affine-pair extraction itself by a
direct **Lagrange descent**, with no Hensel machinery and no residual hypotheses:

> A decoded `p ∈ K[X]` of degree `< k` agrees with the generic fold on some agreement set
> `A` of evaluation points. The fold **values** are affine in `Z` (`f₀ᵢ + Z·f₁ᵢ`) and the
> **nodes** `ωᵢ` are `F`-rational. If `|A| ≥ k`, then `p` is the Lagrange interpolation of
> affine values through `F`-rational nodes; the Lagrange basis is defined over `F`, and
> `interpolate` is *linear in the values*, so
> `p = interpolate(f₀-values) + Z · interpolate(f₁-values) = a + Z·b` with
> `a, b ∈ F[X]`, `deg < k`.

Main results:

* `Lagrange.map_interpolate` (with `map_basisDivisor`, `map_basis`) — Lagrange interpolation
  commutes with field embeddings (Mathlib-ready);
* `affine_pair_of_agreement` — the extraction: `≥ k` agreements with the generic fold force
  `p = a + Z·b`, `a, b ∈ F[X]`, `deg < k`;
* `affine_pair_unique` — the pair `(a, b)` is unique (`1, Z` are `F[X]`-independent in `K`);
* `affine_pair_of_hammingDist` — the distance form: `Δ(p|_D, f₀ + Z·f₁) ≤ n − k` suffices,
  so **every GS-decoded codeword of the generic fold in the Johnson regime carries a unique
  affine pair** — the S6 payload `(a_{i,j}, b_{i,j})` of `Hab25JohnsonAlgebraicData`, whose
  `Z`-specializations `a + z·b` are the per-`z` decoded polynomials the S7/S8 combinatorics
  consume.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial

/-! ## Lagrange interpolation commutes with field embeddings (Mathlib-ready) -/

namespace Lagrange

variable {F K : Type*} [Field F] [Field K]

theorem map_basisDivisor (φ : F →+* K) (x y : F) :
    (basisDivisor x y).map φ = basisDivisor (φ x) (φ y) := by
  simp [basisDivisor, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, map_inv₀, map_sub]

theorem map_basis {ι : Type*} [DecidableEq ι] (φ : F →+* K)
    (s : Finset ι) (v : ι → F) (i : ι) :
    (Lagrange.basis s v i).map φ = Lagrange.basis s (φ ∘ v) i := by
  simp [Lagrange.basis, Polynomial.map_prod, map_basisDivisor, Function.comp]

/-- **Lagrange interpolation commutes with field embeddings**: interpolating the mapped
values through the mapped nodes is the map of the interpolant. -/
theorem map_interpolate {ι : Type*} [DecidableEq ι] (φ : F →+* K)
    (s : Finset ι) (v : ι → F) (r : ι → F) :
    (interpolate s v r).map φ = interpolate s (φ ∘ v) (φ ∘ r) := by
  rw [interpolate_apply, interpolate_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, map_basis]
  rfl

end Lagrange

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-! ## `1, Z` independence: the affine pair is unique -/

/-- `1` and `Z` are independent over `F` inside `K = F(Z)`: an `F`-affine combination
vanishes only trivially. (Transport along the injective `F[Z] → F(Z)`.) -/
lemma affine_scalar_eq_zero {x y : F}
    (h : algebraMap F (RatFunc F) x + RatFunc.X * algebraMap F (RatFunc F) y = 0) :
    x = 0 ∧ y = 0 := by
  have hC : ∀ z : F, algebraMap F (RatFunc F) z =
      algebraMap F[X] (RatFunc F) (Polynomial.C z) := by
    intro z
    rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), Polynomial.algebraMap_eq]
  have hX : (RatFunc.X : RatFunc F) = algebraMap F[X] (RatFunc F) Polynomial.X :=
    RatFunc.algebraMap_X.symm
  have h' : algebraMap F[X] (RatFunc F) (Polynomial.C x + Polynomial.X * Polynomial.C y) = 0 := by
    rw [map_add, map_mul, ← hC, ← hC, ← hX]
    exact h
  have h0 : (Polynomial.C x + Polynomial.X * Polynomial.C y : F[X]) = 0 :=
    RatFunc.algebraMap_injective F (by rw [map_zero]; exact h')
  constructor
  · have := congrArg (fun q : F[X] => q.coeff 0) h0
    simpa using this
  · have := congrArg (fun q : F[X] => q.coeff 1) h0
    simpa using this

/-- **Uniqueness of the affine pair**: `a + Z·b` determines `(a, b)` (coefficientwise
`1, Z`-independence). -/
theorem affine_pair_unique {a b a' b' : F[X]}
    (h : a.map (algebraMap F (RatFunc F)) +
        Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)) =
      a'.map (algebraMap F (RatFunc F)) +
        Polynomial.C RatFunc.X * b'.map (algebraMap F (RatFunc F))) :
    a = a' ∧ b = b' := by
  have hcoeff : ∀ j : ℕ,
      algebraMap F (RatFunc F) (a.coeff j - a'.coeff j) +
        RatFunc.X * algebraMap F (RatFunc F) (b.coeff j - b'.coeff j) = 0 := by
    intro j
    have hj := congrArg (fun q : (RatFunc F)[X] => q.coeff j) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map] at hj
    rw [map_sub, map_sub]
    linear_combination hj
  constructor
  · ext j
    have h2 := (affine_scalar_eq_zero (hcoeff j)).1
    exact sub_eq_zero.mp h2
  · ext j
    have h2 := (affine_scalar_eq_zero (hcoeff j)).2
    exact sub_eq_zero.mp h2

/-! ## The affine-pair extraction (S6 deep kernel) -/

/-- **Hab25 §3 S6 deep kernel — the affine pair, by Lagrange descent.**

If `p ∈ K[X]` (`K = F(Z)`) has degree `< k` and agrees with the generic fold `f₀ + Z·f₁`
on an agreement set `A` of at least `k` lifted evaluation points, then `p` **is** an affine
pair: `p = a + Z·b` with `a, b ∈ F[X]` of degree `< k`. The nodes are `F`-rational and the
fold values are affine in `Z`, so Lagrange interpolation (linear in the values, basis defined
over `F`) splits `p` into its `F`-rational constant and `Z`-parts. No Hensel lift, no
separability, no characteristic hypothesis. -/
theorem affine_pair_of_agreement {n k : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {p : (RatFunc F)[X]} (hdeg : p.degree < k)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, p.eval (liftedDomain ωs i) = genericFold f₀ f₁ i)
    (hk : k ≤ A.card) :
    ∃ a b : F[X], a.degree < k ∧ b.degree < k ∧
      p = a.map (algebraMap F (RatFunc F)) +
        Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)) := by
  classical
  obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hk
  set φ := algebraMap F (RatFunc F) with hφ
  set v : Fin n → F := fun i => ωs i with hv
  have hinjF : Set.InjOn v S := fun i _ j _ hij => ωs.injective hij
  have hinjK : Set.InjOn (φ ∘ v) S := fun i hi j hj hij =>
    hinjF hi hj ((algebraMap F (RatFunc F)).injective hij)
  -- `p` interpolates the affine fold values through the lifted nodes
  have hp : p = Lagrange.interpolate S (φ ∘ v) (fun i => genericFold f₀ f₁ i) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hinjK (by rw [hScard]; exact hdeg) ?_
    intro i hi
    exact hA i (hSA hi)
  -- the fold values are an affine combination of the `F`-rational value vectors
  have hvals : (fun i => genericFold f₀ f₁ i) =
      (⇑φ ∘ f₀) + (RatFunc.X : RatFunc F) • (⇑φ ∘ f₁) := by
    funext i
    simp [genericFold, hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨Lagrange.interpolate S v f₀, Lagrange.interpolate S v f₁, ?_, ?_, ?_⟩
  · rw [← hScard]
    exact_mod_cast Lagrange.degree_interpolate_lt _ hinjF
  · rw [← hScard]
    exact_mod_cast Lagrange.degree_interpolate_lt _ hinjF
  · calc p = Lagrange.interpolate S (⇑φ ∘ v) (fun i => genericFold f₀ f₁ i) := hp
      _ = Lagrange.interpolate S (⇑φ ∘ v)
            ((⇑φ ∘ f₀) + (RatFunc.X : RatFunc F) • (⇑φ ∘ f₁)) := by rw [hvals]
      _ = Lagrange.interpolate S (⇑φ ∘ v) (⇑φ ∘ f₀) +
            (RatFunc.X : RatFunc F) • Lagrange.interpolate S (⇑φ ∘ v) (⇑φ ∘ f₁) := by
          rw [map_add, LinearMap.map_smul]
      _ = (Lagrange.interpolate S v f₀).map φ +
            (RatFunc.X : RatFunc F) • (Lagrange.interpolate S v f₁).map φ := by
          rw [Lagrange.map_interpolate φ S v f₀, Lagrange.map_interpolate φ S v f₁]
      _ = (Lagrange.interpolate S v f₀).map φ +
            Polynomial.C RatFunc.X * (Lagrange.interpolate S v f₁).map φ := by
          rw [Polynomial.smul_eq_C_mul]

/-- **The affine pair in Hamming-distance form** — the shape the GS list-decoder produces.

If `p ∈ K[X]` has degree `< k` and its evaluation vector over the lifted domain is within
Hamming distance `n − k` of the generic fold, then `p` carries a (unique) affine pair
`p = a + Z·b`, `a, b ∈ F[X]`, `deg < k`. In the Johnson regime `δ < 1 − √ρ` one has
`δn ≤ n − k`, so **every decoded codeword of the generic fold is an affine pair** — the S6
output `(a_{i,j}, b_{i,j})` consumed by the Hab25 Theorem-2 combinatorics. -/
theorem affine_pair_of_hammingDist {n k : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {p : (RatFunc F)[X]} (hdeg : p.degree < k)
    (hdist : hammingDist (genericFold f₀ f₁)
        (fun i => p.eval (liftedDomain ωs i)) + k ≤ n) :
    ∃ a b : F[X], a.degree < k ∧ b.degree < k ∧
      p = a.map (algebraMap F (RatFunc F)) +
        Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)) := by
  classical
  set A : Finset (Fin n) :=
    Finset.univ.filter (fun i => p.eval (liftedDomain ωs i) = genericFold f₀ f₁ i) with hA
  have hAagree : ∀ i ∈ A, p.eval (liftedDomain ωs i) = genericFold f₀ f₁ i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  refine affine_pair_of_agreement ωs f₀ f₁ hdeg A hAagree ?_
  -- the complement of the agreement set is the disagreement set, of size `hammingDist`
  have hsplit : A.card +
      (Finset.univ.filter
        (fun i => ¬ p.eval (liftedDomain ωs i) = genericFold f₀ f₁ i)).card =
      n := by
    rw [hA, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have hdist' : (Finset.univ.filter
      (fun i => ¬ p.eval (liftedDomain ωs i) = genericFold f₀ f₁ i)).card ≤
      hammingDist (genericFold f₀ f₁) (fun i => p.eval (liftedDomain ωs i)) := by
    rw [hammingDist]
    refine Finset.card_le_card ?_
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, fun hne => hi.2 hne.symm⟩
  omega

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Lagrange.map_interpolate
#print axioms GuruswamiSudan.OverRatFunc.affine_scalar_eq_zero
#print axioms GuruswamiSudan.OverRatFunc.affine_pair_unique
#print axioms GuruswamiSudan.OverRatFunc.affine_pair_of_agreement
#print axioms GuruswamiSudan.OverRatFunc.affine_pair_of_hammingDist
