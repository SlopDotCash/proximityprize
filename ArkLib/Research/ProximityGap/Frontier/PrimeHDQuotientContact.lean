/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Translation
import ArkLib.Data.MvPolynomial.WeightedDegree
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

/-!
# Prime-Field Quotient-Contact Rank Identity & Combined Interpolation (`PrimeHDQuotientContact`)

Formalizes the exact prime-field (in fact, **arbitrary-characteristic**!) first-order (`d = 1`)
quotient-contact rank identity and combined quotient interpolation engine from `#142` /
`B6402CombinedInterpolation`, built directly on ArkLib's canonical
`ReedSolomon.HiddenDerivative` framework.

## Main statements

1. **Abstract Quotient Existence (`exists_outside_multiples`, `exists_in_ker_outside_range`):**
   Direct linear-algebraic surplus lemmas (`B6402QuotientDimension` + subspace quotient form).
2. **Exact First-Order Weighted Space (`primeFirstOrderSpace`, `exactDimD1`,
   `finrank_primeFirstOrderSpace`, `globalPointTranslation_equiv_primeFirstOrderSpace`,
   `mul_mem_primeFirstOrderSpace_iff`):**
   The space `V_{D_cut}(s) = {X^a Y₀^{b₀} Y₁^{b₁} : b₁ ≤ s, a + w * b₀ + (w - 1) * b₁ < D_cut}`
   with exact dimension `exactDimD1 w D_cut s`, exact translation automorphism at every `(x₀, y₀)`,
   and exact divisibility characterization `f ∣ Q ↔ Q ∈ range (mulLeft f)` via strict additivity
   of weighted degree on the integral domain `DifferentialPolynomial F 1`.
3. **Vandermonde Pascal Determinant (`det_pascal_submatrix`) & Exact Local Rank
   (`exactRankD1`, `finrank_range_localConstraintAt_primeFirstOrderSpace`):**
   Using the Vandermonde LU factorization `[(L + c).choose b] = A * B` (`det = 1` in EVERY
   commutative ring and EVERY characteristic!), proves the EXACT equality
   `finrank F (range (localConstraintAt m x₀ y₀ |_{V_{D_cut}(s)})) = exactRankD1 m s w D_cut`.
4. **Integral-Domain Kernel Shift & Exact Quotient-Contact Rank Identity
   (`localConstraintAt_mul_eq_zero_iff`, `finrank_range_localConstraintAt_mul_eq`,
   `finrank_range_localConstraintAt_mul_primeFirstOrderSpace`):**
   For any nonzero `f` of exact local contact order `k` at `(x₀, y₀)`:
   - `ker (localConstraintAt m x₀ y₀ ∘ (· f)) = ker (localConstraintAt (m - k) x₀ y₀)` (via
     non-vanishing of the product of leading contact-homogeneous forms in the integral domain
     `LocalPolynomial R d`),
   - hence **`finrank F (range (localConstraintAt m x₀ y₀ ∘ (· f) |_{V_{D_cut - W_f}(s - d_f)}))
     = exactRankD1 (m - k) (s - d_f) w (D_cut - W_f)`** identically in EVERY field `F`!
5. **Prime-Field Quotient-Contact Interpolant (`exists_quotient_contact_interpolant`):**
   Whenever
   `∑ i, (exactRankD1 m s w D_cut - exactRankD1 (m - k i) (s - d_f) w (D_cut - W_f))
     + exactDimD1 w (D_cut - W_f) (s - d_f) < exactDimD1 w D_cut s`,
   produces `Q ∈ V_{D_cut}(s)` with `¬ f ∣ Q` such that **every** codeword `S` of degree `≤ w`
   on `f(X, S, S') = 0` agreeing on `≥ H` sites (`D_cut ≤ m * H.card`) satisfies `Q(X, S, S') = 0`!
6. **Direct Bridge from `BiPoly F` (`contactLinearDiff A B`):**
   Embeds `f = A(X, Y₀) * Y₁ + B(X, Y₀)` into `DifferentialPolynomial F 1` for zero-friction
   integration with `@drdos-engine`'s `DrdosDiscriminantBarrier`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArkLib.ProximityGap.Frontier.PrimeHDQuotientContact

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative Matrix
open scoped BigOperators

/-! ### Part 1: Abstract Quotient Existence (`B6402QuotientDimension`) -/

/-- `B6402QuotientDimension.exists_outside_multiples`: if `rows u = 0 ∧ output u = 0 → u = 0`
and `finrank E + finrank C < finrank U`, there exists `u ∈ ker rows` with
`output u ∉ range multiples`. -/
theorem exists_outside_multiples {K U E Z C : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup Z] [Module K Z]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    (rows : U →ₗ[K] E) (output : U →ₗ[K] Z) (multiples : C →ₗ[K] Z)
    (unique : ∀ u, rows u = 0 → output u = 0 → u = 0)
    (surplus : Module.finrank K E + Module.finrank K C < Module.finrank K U) :
    ∃ u : U, rows u = 0 ∧ output u ∉ LinearMap.range multiples := by
  classical
  by_contra! closed
  let embed : LinearMap.ker rows →ₗ[K] LinearMap.range multiples :=
    (output.comp (LinearMap.ker rows).subtype).codRestrict _ (fun x => closed x.1 x.2)
  have hinj : Function.Injective embed := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hz : output x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (unique x.1 x.2 hz)
  have hsize := LinearMap.finrank_le_finrank_of_injective hinj
  have hnull := LinearMap.finrank_range_add_finrank_ker rows
  have h1 := LinearMap.finrank_range_le multiples
  have h2 := Submodule.finrank_le (LinearMap.range rows)
  omega

/-- Direct subspace-quotient form: if `finrank (range rows) + finrank C < finrank U`, there exists
`u ∈ ker rows` outside `range multiples`. -/
theorem exists_in_ker_outside_range {K U E C : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup E] [Module K E]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    (rows : U →ₗ[K] E) (multiples : C →ₗ[K] U)
    (surplus : Module.finrank K (LinearMap.range rows) + Module.finrank K C <
      Module.finrank K U) :
    ∃ u : U, rows u = 0 ∧ u ∉ LinearMap.range multiples := by
  classical
  by_contra! hsub
  have hle : LinearMap.ker rows ≤ LinearMap.range multiples := fun u hu => hsub u hu
  have h1 : Module.finrank K (LinearMap.ker rows) ≤ Module.finrank K (LinearMap.range multiples) :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank K (LinearMap.range multiples) ≤ Module.finrank K C :=
    LinearMap.finrank_range_le multiples
  have hnull := LinearMap.finrank_range_add_finrank_ker rows
  omega

/-! ### Part 2: Exact First-Order Weighted Space `V_{D_cut}(s)` -/

noncomputable section

/-- Exponent vector for `X^a Y₀^{b₀} Y₁^{b₁}` in `JetVariable 1 →₀ ℕ`. -/
def d1Exp (a b₀ b₁ : ℕ) : JetVariable 1 →₀ ℕ :=
  Finsupp.single none a + Finsupp.single (some 0) b₀ + Finsupp.single (some 1) b₁

@[simp] theorem d1Exp_none (a b₀ b₁ : ℕ) : d1Exp a b₀ b₁ none = a := by simp [d1Exp]
@[simp] theorem d1Exp_some_zero (a b₀ b₁ : ℕ) : d1Exp a b₀ b₁ (some 0) = b₀ := by simp [d1Exp]
@[simp] theorem d1Exp_some_one (a b₀ b₁ : ℕ) : d1Exp a b₀ b₁ (some 1) = b₁ := by simp [d1Exp]

theorem d1Exp_eta (u : JetVariable 1 →₀ ℕ) :
    d1Exp (u none) (u (some 0)) (u (some 1)) = u := by
  ext v
  rcases v with _ | j
  · simp
  · fin_cases j <;> simp

theorem weight_differentialWeight_d1 (w : ℕ) (u : JetVariable 1 →₀ ℕ) :
    u.weight (differentialWeight w) = u none + w * u (some 0) + (w - 1) * u (some 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_option, Fin.sum_univ_two]
  simp only [differentialWeight, Fin.val_zero, Fin.val_one,
    Nat.sub_zero, smul_eq_mul, mul_one, Nat.mul_comm]
  ring

/-- Exact dimension formula for `V_{D_cut}(s)` with weights `(1, w, w - 1)`. -/
def exactDimD1 (w D_cut s : ℕ) : ℕ :=
  ∑ b₁ ∈ Finset.range (s + 1),
    ∑ b₀ ∈ Finset.range (if (w - 1) * b₁ < D_cut then (D_cut - 1 - (w - 1) * b₁) / w + 1 else 0),
      (D_cut - w * b₀ - (w - 1) * b₁)

/-- Coordinate triples `⟨⟨b₁, b₀⟩, a⟩` for the basis monomials of `V_{D_cut}(s)`. -/
def d1Coords (w D_cut s : ℕ) : Finset (Σ _ : (Σ _ : ℕ, ℕ), ℕ) :=
  ((Finset.range (s + 1)).sigma fun b₁ =>
    Finset.range (if (w - 1) * b₁ < D_cut then (D_cut - 1 - (w - 1) * b₁) / w + 1 else 0)).sigma
      fun p => Finset.range (D_cut - w * p.2 - (w - 1) * p.1)

theorem card_d1Coords (w D_cut s : ℕ) : (d1Coords w D_cut s).card = exactDimD1 w D_cut s := by
  simp [d1Coords, exactDimD1, Finset.card_sigma, Finset.sum_sigma]

private def coordToExp (p : Σ _ : (Σ _ : ℕ, ℕ), ℕ) : JetVariable 1 →₀ ℕ :=
  d1Exp p.2 p.1.2 p.1.1

private theorem coordToExp_injective : Function.Injective coordToExp := by
  rintro ⟨⟨b₁, b₀⟩, a⟩ ⟨⟨b₁', b₀'⟩, a'⟩ h
  have h1 := congrArg (fun u : JetVariable 1 →₀ ℕ => u none) h
  have h2 := congrArg (fun u : JetVariable 1 →₀ ℕ => u (some 0)) h
  have h3 := congrArg (fun u : JetVariable 1 →₀ ℕ => u (some 1)) h
  simp [coordToExp] at h1 h2 h3
  subst h1; subst h2; subst h3; rfl

/-- Explicit finite set of exponents `{X^a Y₀^{b₀} Y₁^{b₁} : b₁ ≤ s, a + w*b₀ + (w-1)*b₁ < D_cut}`. -/
def primeExponents (w D_cut s : ℕ) : Finset (JetVariable 1 →₀ ℕ) :=
  (d1Coords w D_cut s).image coordToExp

theorem card_primeExponents (w D_cut s : ℕ) :
    (primeExponents w D_cut s).card = exactDimD1 w D_cut s := by
  rw [primeExponents, Finset.card_image_of_injective _ coordToExp_injective, card_d1Coords]

theorem mem_primeExponents_iff {w D_cut s : ℕ} (hw : 2 ≤ w) {u : JetVariable 1 →₀ ℕ} :
    u ∈ primeExponents w D_cut s ↔
      u (some 1) ≤ s ∧ u.weight (differentialWeight w) < D_cut := by
  rw [primeExponents, Finset.mem_image, weight_differentialWeight_d1]
  constructor
  · rintro ⟨⟨⟨b₁, b₀⟩, a⟩, hp, rfl⟩
    simp only [d1Coords, Finset.mem_sigma, Finset.mem_range] at hp
    rcases hp with ⟨⟨hb₁, hb₀⟩, ha⟩
    simp only [coordToExp, d1Exp_none, d1Exp_some_zero, d1Exp_some_one]
    have hlt : (w - 1) * b₁ < D_cut := by
      by_contra hge
      rw [ite_eq_right hge] at hb₀; omega
    rw [ite_eq_left hlt] at hb₀
    have hwb0 : w * b₀ ≤ D_cut - 1 - (w - 1) * b₁ := by
      have h1 : b₀ ≤ (D_cut - 1 - (w - 1) * b₁) / w := by omega
      have h2 := Nat.mul_le_mul_left w h1
      have h3 := Nat.mul_div_le (D_cut - 1 - (w - 1) * b₁) w
      omega
    exact ⟨by omega, by omega⟩
  · rintro ⟨hs, hwt⟩
    refine ⟨⟨⟨u (some 1), u (some 0)⟩, u none⟩, ?_, d1Exp_eta u⟩
    simp only [d1Coords, Finset.mem_sigma, Finset.mem_range]
    have hlt : (w - 1) * u (some 1) < D_cut := by omega
    have hb₀ : u (some 0) ≤ (D_cut - 1 - (w - 1) * u (some 1)) / w := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < w)]
      rw [Nat.mul_comm]
      omega
    exact ⟨⟨by omega, by rw [ite_eq_left hlt]; omega⟩, by omega⟩

/-- The first-order weighted interpolation space `V_{D_cut}(s)` over `F`. -/
def primeFirstOrderSpace (F : Type*) [CommSemiring F] (w D_cut s : ℕ) :
    Submodule F (DifferentialPolynomial F 1) :=
  MvPolynomial.restrictSupport F (↑(primeExponents w D_cut s) : Set (JetVariable 1 →₀ ℕ))

theorem mem_primeFirstOrderSpace_iff {F : Type*} [CommSemiring F] {w D_cut s : ℕ} (hw : 2 ≤ w)
    {Q : DifferentialPolynomial F 1} :
    Q ∈ primeFirstOrderSpace F w D_cut s ↔
      ∀ u ∈ Q.support, u (some 1) ≤ s ∧ u.weight (differentialWeight w) < D_cut := by
  rw [primeFirstOrderSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_primeExponents_iff hw]

instance primeFirstOrderSpace_finite {F : Type*} [CommSemiring F] (w D_cut s : ℕ) :
    Module.Finite F (primeFirstOrderSpace F w D_cut s) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport (R := F)
    (↑(primeExponents w D_cut s) : Set (JetVariable 1 →₀ ℕ)))

theorem finrank_primeFirstOrderSpace {F : Type*} [Field F] (w D_cut s : ℕ) :
    Module.finrank F (primeFirstOrderSpace F w D_cut s) = exactDimD1 w D_cut s := by
  let b : Module.Basis ↥(primeExponents w D_cut s) F
      (MvPolynomial.restrictSupport F (↑(primeExponents w D_cut s) : Set (JetVariable 1 →₀ ℕ))) :=
    MvPolynomial.basisRestrictSupport (R := F)
      (↑(primeExponents w D_cut s) : Set (JetVariable 1 →₀ ℕ))
  change Module.finrank F
    (MvPolynomial.restrictSupport F (↑(primeExponents w D_cut s) : Set (JetVariable 1 →₀ ℕ))) = _
  rw [Module.finrank_eq_card_basis b, Fintype.card_coe, card_primeExponents]

private theorem weight_jetFirstWeight_d1 (u : JetVariable 1 →₀ ℕ) :
    u.weight (jetFirstWeight (d := 1)) = u (some 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_option, Fin.sum_univ_two]
  simp [jetFirstWeight, smul_eq_mul]

/-- Global point translation `(X, Y₀) ↦ (X + center, Y₀ + received)` preserves `V_{D_cut}(s)`. -/
theorem globalPointTranslation_mem_primeFirstOrderSpace {R : Type*} [CommRing R]
    {w D_cut s : ℕ} (hw : 2 ≤ w) (center received : R) {Q : DifferentialPolynomial R 1}
    (hQ : Q ∈ primeFirstOrderSpace R w D_cut s) :
    globalPointTranslation center received Q ∈ primeFirstOrderSpace R w D_cut s := by
  rw [mem_primeFirstOrderSpace_iff hw] at hQ ⊢
  intro e he
  have hQne : Q ≠ 0 := by intro h; simp [h] at he
  obtain ⟨u₀, hu₀⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hDpos : 0 < D_cut := (Nat.zero_le _).trans_lt (hQ u₀ hu₀).2
  have hfirst := globalPointTranslation_mem_restrictWeightAtMost
    (w := jetFirstWeight (d := 1)) (by simp [jetFirstWeight]) (by simp [jetFirstWeight])
    center received (a := s)
    (mem_restrictWeightAtMost.mpr fun u hu => by
      rw [weight_jetFirstWeight_d1]; exact (hQ u hu).1)
  have hdeg := globalPointTranslation_mem_restrictWeightAtMost
    (w := differentialWeight w) (by simp [differentialWeight]) (by simp [differentialWeight])
    center received (a := D_cut - 1)
    (mem_restrictWeightAtMost.mpr fun u hu => by have := (hQ u hu).2; omega)
  have h1 := mem_restrictWeightAtMost.mp hfirst e he
  have h2 := mem_restrictWeightAtMost.mp hdeg e he
  rw [weight_jetFirstWeight_d1] at h1
  exact ⟨h1, by omega⟩

/-- `globalPointTranslation center received` restricts to an `F`-linear automorphism of
`primeFirstOrderSpace F w D_cut s`. -/
def globalPointTranslation_equiv_primeFirstOrderSpace {R : Type*} [CommRing R]
    {w D_cut s : ℕ} (hw : 2 ≤ w) (center received : R) :
    primeFirstOrderSpace R w D_cut s ≃ₗ[R] primeFirstOrderSpace R w D_cut s :=
  LinearEquiv.ofLinearMap
    ((globalPointTranslation center received).toLinearMap.restrict
      (fun _ h => globalPointTranslation_mem_primeFirstOrderSpace hw center received h))
    ((globalPointTranslation (-center) (-received)).toLinearMap.restrict
      (fun _ h => globalPointTranslation_mem_primeFirstOrderSpace hw (-center) (-received) h))
    (by
      apply LinearMap.ext; intro Q; apply Subtype.ext
      change (globalPointTranslation center received)
        (globalPointTranslation (-center) (-received) Q.1) = Q.1
      have h := AlgHom.congr_fun
        (globalPointTranslation_comp (d := 1) center received (-center) (-received)) Q.1
      simpa [neg_add_cancel] using h)
    (by
      apply LinearMap.ext; intro Q; apply Subtype.ext
      change (globalPointTranslation (-center) (-received))
        (globalPointTranslation center received Q.1) = Q.1
      have h := AlgHom.congr_fun (globalPointTranslation_neg_comp (d := 1) center received) Q.1
      simpa using h)

private def wdEmbedQ {σ : Type*} (wt : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun d := d.optionElim (Finsupp.weight wt d)
  map_zero' := by ext i; cases i <;> simp
  map_add' d e := by ext i; cases i <;> simp

private theorem wdEmbedQ_injective {σ : Type*} (wt : σ → ℕ) : Function.Injective (wdEmbedQ wt) := by
  intro d e h
  have := congrArg Finsupp.some h
  simpa [wdEmbedQ] using this

private def wdLiftQ {σ R : Type*} [CommSemiring R] (wt : σ → ℕ) :
    MvPolynomial σ R →+* MvPolynomial (Option σ) R :=
  AddMonoidAlgebra.mapDomainRingHom R (wdEmbedQ wt)

private theorem wdLiftQ_injective {σ R : Type*} [CommSemiring R] (wt : σ → ℕ) :
    Function.Injective (wdLiftQ (R := R) wt) :=
  AddMonoidAlgebra.mapDomain_injective (wdEmbedQ_injective wt)

private theorem degreeOf_wdLiftQ {σ R : Type*} [CommSemiring R] (wt : σ → ℕ)
    (p : MvPolynomial σ R) :
    (wdLiftQ wt p).degreeOf none = MvPolynomial.weightedTotalDegree wt p := by
  classical
  have hs : (wdLiftQ wt p).support = p.support.image (wdEmbedQ wt) :=
    Finsupp.mapDomain_support_of_injective (wdEmbedQ_injective wt) _
  rw [MvPolynomial.degreeOf_eq_sup, hs, Finset.sup_image]
  simp [Function.comp_def, wdEmbedQ, MvPolynomial.weightedTotalDegree]

private theorem wdeg_mul_eq {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (wt : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    MvPolynomial.weightedTotalDegree wt (p * q) =
      MvPolynomial.weightedTotalDegree wt p + MvPolynomial.weightedTotalDegree wt q := by
  have hp' : wdLiftQ wt p ≠ 0 := fun h => hp (wdLiftQ_injective wt (h.trans (map_zero _).symm))
  have hq' : wdLiftQ wt q ≠ 0 := fun h => hq (wdLiftQ_injective wt (h.trans (map_zero _).symm))
  rw [← degreeOf_wdLiftQ wt (p * q), map_mul, MvPolynomial.degreeOf_mul_eq hp' hq',
    degreeOf_wdLiftQ, degreeOf_wdLiftQ]

/-- Multiplication by `f` maps `V_{D_cut - W_f}(s - d_f)` linearly into `V_{D_cut}(s)`. -/
def mulLeftInSpace {R : Type*} [CommRing R] {w D_cut s : ℕ} (hw : 2 ≤ w)
    (f : DifferentialPolynomial R 1)
    (W_f d_f : ℕ)
    (hWf : MvPolynomial.weightedTotalDegree (differentialWeight w) f ≤ W_f)
    (hdf : f.degreeOf (some 1) ≤ d_f) (hd_le : d_f ≤ s) :
    primeFirstOrderSpace R w (D_cut - W_f) (s - d_f) →ₗ[R] primeFirstOrderSpace R w D_cut s :=
  LinearMap.codRestrict (primeFirstOrderSpace R w D_cut s)
    ((LinearMap.mulLeft R f).comp (primeFirstOrderSpace R w (D_cut - W_f) (s - d_f)).subtype)
    fun G => by
      rw [mem_primeFirstOrderSpace_iff hw]
      intro u hu
      have hG := (mem_primeFirstOrderSpace_iff hw).mp G.2
      have hGne : G.1 ≠ 0 := by
        intro h0
        have : f * G.1 = 0 := by simp [h0]
        simp [this] at hu
      obtain ⟨v0, hv0⟩ := MvPolynomial.support_nonempty.mpr hGne
      have hD_pos : 0 < D_cut - W_f := (Nat.zero_le _).trans_lt (hG v0 hv0).2
      have h1 : u (some 1) ≤ s := by
        have hdeg : u (some 1) ≤ (f * G.1).degreeOf (some 1) :=
          MvPolynomial.le_degreeOf_of_mem_support (some 1) hu
        have hmul := MvPolynomial.degreeOf_mul_le (some 1) f G.1
        have hGdeg : G.1.degreeOf (some 1) ≤ s - d_f :=
          MvPolynomial.degreeOf_le_iff.mpr fun v hv => (hG v hv).1
        omega
      have h2 : u.weight (differentialWeight w) < D_cut := by
        have hsup : u.weight (differentialWeight w) ≤
            MvPolynomial.weightedTotalDegree (differentialWeight w) (f * G.1) :=
          Finset.le_sup (f := fun e => e.weight (differentialWeight w)) hu
        have hmul := MvPolynomial.weightedTotalDegree_mul_le (differentialWeight w) f G.1
        have hGw : MvPolynomial.weightedTotalDegree (differentialWeight w) G.1 < D_cut - W_f := by
          unfold MvPolynomial.weightedTotalDegree
          rw [Finset.sup_lt_iff hD_pos]
          exact fun v hv => (hG v hv).2
        omega
      exact ⟨h1, h2⟩

/-- Over an integral domain `R`, if `W_f = wdeg f` and `d_f = deg_{Y₁}(f) ≤ s`, then an element
`Q ∈ V_{D_cut}(s)` is divisible by `f` in `DifferentialPolynomial R 1` IF AND ONLY IF
`Q` lies in the range of `mulLeftInSpace f : V_{D_cut - W_f}(s - d_f) → V_{D_cut}(s)`. -/
theorem mul_mem_primeFirstOrderSpace_iff {R : Type*} [CommRing R] [IsDomain R]
    {w D_cut s : ℕ} (hw : 2 ≤ w)
    (f : DifferentialPolynomial R 1) (hf : f ≠ 0)
    (hd_le : f.degreeOf (some 1) ≤ s)
    (Q : primeFirstOrderSpace R w D_cut s) :
    f ∣ Q.1 ↔
      Q ∈ LinearMap.range
        (mulLeftInSpace hw f (MvPolynomial.weightedTotalDegree (differentialWeight w) f)
          (f.degreeOf (some 1)) le_rfl le_rfl hd_le) := by
  constructor
  · rintro ⟨G, hG⟩
    have hGmem : G ∈ primeFirstOrderSpace R w
        (D_cut - MvPolynomial.weightedTotalDegree (differentialWeight w) f)
        (s - f.degreeOf (some 1)) := by
      by_cases hG0 : G = 0
      · subst hG0; exact Submodule.zero_mem _
      · rw [mem_primeFirstOrderSpace_iff hw]
        have hQ := (mem_primeFirstOrderSpace_iff hw).mp Q.2
        have hQne : Q.1 ≠ 0 := by rw [hG]; exact mul_ne_zero hf hG0
        obtain ⟨u0, hu0⟩ := MvPolynomial.support_nonempty.mpr hQne
        have hDpos : 0 < D_cut := (Nat.zero_le _).trans_lt (hQ u0 hu0).2
        have hQd : Q.1.degreeOf (some 1) ≤ s :=
          MvPolynomial.degreeOf_le_iff.mpr fun u hu => (hQ u hu).1
        have hQw : MvPolynomial.weightedTotalDegree (differentialWeight w) Q.1 < D_cut := by
          unfold MvPolynomial.weightedTotalDegree
          rw [Finset.sup_lt_iff hDpos]
          exact fun u hu => (hQ u hu).2
        rw [hG, MvPolynomial.degreeOf_mul_eq hf hG0] at hQd
        rw [hG, wdeg_mul_eq (differentialWeight w) f G hf hG0] at hQw
        intro u hu
        have hu1 := MvPolynomial.le_degreeOf_of_mem_support (some 1) hu
        have hu2 : u.weight (differentialWeight w) ≤
            MvPolynomial.weightedTotalDegree (differentialWeight w) G :=
          Finset.le_sup (f := fun v => v.weight (differentialWeight w)) hu
        exact ⟨by omega, by omega⟩
    exact ⟨⟨G, hGmem⟩, Subtype.ext hG.symm⟩
  · rintro ⟨G, hG⟩
    exact ⟨G.1, (congrArg Subtype.val hG).symm⟩

/-! ### Part 3: Vandermonde Pascal Determinant & Exact Local Rank Formula `exactRankD1` -/

/-- **Universal Vandermonde Pascal Determinant Theorem (ANY commutative ring `R`, ANY char!):**
For all `L, r : ℕ`, the `r × r` matrix `M[b, c] = (L + c).choose b` has determinant `1`. -/
theorem det_pascal_submatrix {R : Type*} [CommRing R] (L r : ℕ) :
    (Matrix.of fun b c : Fin r => ((L + c.val).choose b.val : R)).det = 1 := by
  let A : Matrix (Fin r) (Fin r) R :=
    Matrix.of fun b t => if t.val ≤ b.val then (L.choose (b.val - t.val) : R) else 0
  let B : Matrix (Fin r) (Fin r) R :=
    Matrix.of fun t c => if t.val ≤ c.val then (c.val.choose t.val : R) else 0
  have hAB : A * B = Matrix.of fun b c : Fin r => ((L + c.val).choose b.val : R) := by
    ext b c
    rw [Matrix.mul_apply, Matrix.of_apply]
    have hvand : ((L + c.val).choose b.val : R) =
        ∑ t ∈ Finset.range (b.val + 1), (L.choose (b.val - t) : R) * (c.val.choose t : R) := by
      have hN := Nat.add_choose_eq L c.val b.val
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => L.choose x * c.val.choose y)
        b.val] at hN
      have hsymm : ∑ t ∈ Finset.range (b.val + 1), L.choose (b.val - t) * c.val.choose t =
          ∑ t ∈ Finset.range (b.val + 1), L.choose t * c.val.choose (b.val - t) := by
        rw [← Finset.sum_range_reflect (fun t => L.choose t * c.val.choose (b.val - t)) (b.val + 1)]
        apply Finset.sum_congr rfl; intro t ht
        have hlt : t ≤ b.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
        have h1 : b.val + 1 - 1 - t = b.val - t := by omega
        have h2 : b.val - (b.val - t) = t := by omega
        rw [h1, h2]
      rw [hN, ← hsymm]
      push_cast
      rfl
    rw [hvand]
    have hsplit : ∑ t : Fin r, A b t * B t c =
        ∑ t ∈ Finset.univ.filter (fun t : Fin r => t.val ≤ b.val),
          (L.choose (b.val - t.val) : R) * (c.val.choose t.val : R) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro t _
      dsimp only [A, B, Matrix.of_apply]
      by_cases htb : t.val ≤ b.val
      · rw [ite_eq_left htb, ite_eq_left htb]
        by_cases htc : t.val ≤ c.val
        · rw [ite_eq_left htc]
        · rw [ite_eq_right htc, mul_zero, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge htc),
            Nat.cast_zero, mul_zero]
      · rw [ite_eq_right htb, ite_eq_right htb, zero_mul]
    rw [hsplit]
    refine Finset.sum_bij (fun t _ => t.val) ?_ ?_ ?_ ?_
    · intro t ht
      have hle := (Finset.mem_filter.mp ht).2
      exact Finset.mem_range.mpr (by omega)
    · intro t₁ _ t₂ _ h; exact Fin.ext h
    · intro k hk
      have hkb : k ≤ b.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact ⟨⟨k, by have := b.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkb⟩, rfl⟩
    · intro _ _; rfl
  have hdetA : A.det = 1 := by
    have htri : Aᵀ.BlockTriangular id := by
      intro i j hij
      change j.val < i.val at hij
      dsimp only [A, Matrix.transpose_apply, Matrix.of_apply]
      exact ite_eq_right (by omega)
    rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular htri]
    apply Finset.prod_eq_one; intro i _
    dsimp only [A, Matrix.transpose_apply, Matrix.of_apply]
    simp
  have hdetB : B.det = 1 := by
    have htri : B.BlockTriangular id := by
      intro i j hij
      change j.val < i.val at hij
      dsimp only [B, Matrix.of_apply]
      exact ite_eq_right (by omega)
    rw [Matrix.det_of_isUpperTriangular htri]
    apply Finset.prod_eq_one; intro i _
    dsimp only [B, Matrix.of_apply]
    simp [Nat.choose_self]
  rw [← hAB, Matrix.det_mul, hdetA, hdetB, one_mul]

/-- Exact first-order local constraint rank formula `rank₁(m, s, w, D_cut)` from `#142`
(matches `verify_d1_breakthrough.py`'s `exact_ld_rank_d1` bit-for-bit!). -/
def exactRankD1 (m s w D_cut : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m,
    ∑ j ∈ Finset.range (i + s + 1),
      if i + (w - 1) * j < D_cut then
        min (min (m - 1 - i) j + 1) (min i j + 1 - (j - s))
      else 0

/-- Local exponent `T^i E^b Y₁^c` in `LocalVariable 1 →₀ ℕ`. -/
private def locExp (i b c : ℕ) : LocalVariable 1 →₀ ℕ :=
  Finsupp.single (localT 1) i + Finsupp.single (localE 1) b + Finsupp.single (localY 0) c

@[simp] private theorem locExp_T (i b c : ℕ) : locExp i b c (localT 1) = i := by
  simp [locExp, localT, localE, localAux, localY]
@[simp] private theorem locExp_E (i b c : ℕ) : locExp i b c (localE 1) = b := by
  simp [locExp, localT, localE, localAux, localY]
@[simp] private theorem locExp_Y (i b c : ℕ) : locExp i b c (localY 0) = c := by
  simp [locExp, localT, localE, localAux, localY]

private theorem localContactOrder_locExp (i b c : ℕ) :
    localContactOrder 1 (locExp i b c) = i + b := by
  have h := localContactOrder_eq (d := 1) (locExp i b c)
  simpa [locExp_T, locExp_E] using h

private theorem localConstraintAt_zero_monomial_d1 {F : Type*} [CommRing F] (m a b₀ b₁ : ℕ) :
    localConstraintAt (R := F) (d := 1) m 0 0 (MvPolynomial.monomial (d1Exp a b₀ b₁) 1) =
      ∑ b ∈ Finset.range (b₀ + 1),
        if a + b₀ + b < m then
          MvPolynomial.monomial (locExp (a + b₀) b (b₀ - b + b₁)) (b₀.choose b : F)
        else 0 := by
  have hsub : unscaledLocalSubstitution (R := F) 1 0 0
      (MvPolynomial.monomial (d1Exp a b₀ b₁) 1) =
      ∑ b ∈ Finset.range (b₀ + 1),
        MvPolynomial.monomial (locExp (a + b₀) b (b₀ - b + b₁)) (b₀.choose b : F) := by
    have hmon : (MvPolynomial.monomial (d1Exp a b₀ b₁) (1 : F) : DifferentialPolynomial F 1) =
        MvPolynomial.X none ^ a * MvPolynomial.X (some 0) ^ b₀ * MvPolynomial.X (some 1) ^ b₁ := by
      simp only [d1Exp, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]
    rw [hmon, map_mul, map_mul, map_pow, map_pow, map_pow]
    rw [unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
      show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
      unscaledLocalSubstitution_Y_succ (R := F) (d := 1) (j := (0 : Fin 1))]
    simp only [map_zero, map_one, zero_add, localCorrection, Fin.sum_univ_one, Fin.val_zero,
      pow_zero, pow_one, one_mul]
    have hfact : (MvPolynomial.X (localT 1) * MvPolynomial.X (localY (0 : Fin 1)) +
        MvPolynomial.X (localT 1) * MvPolynomial.X (localE 1) : LocalPolynomial F 1) =
        MvPolynomial.X (localT 1) *
          (MvPolynomial.X (localE 1) + MvPolynomial.X (localY (0 : Fin 1))) := by ring
    rw [hfact, mul_pow, add_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _
    rw [show (b₀.choose b : LocalPolynomial F 1) = MvPolynomial.monomial 0 (b₀.choose b : F) by
      rw [MvPolynomial.monomial_zero', map_natCast]]
    simp only [MvPolynomial.X_pow_eq_monomial, locExp, MvPolynomial.monomial_mul_monomial,
      one_mul, mul_one]
    refine congrArg (fun e => MvPolynomial.monomial e (b₀.choose b : F)) ?_
    ext v
    simp only [Finsupp.add_apply, Finsupp.zero_apply, Finsupp.single_apply]
    split_ifs <;> omega
  change projectLowContact m (unscaledLocalSubstitution (R := F) 1 0 0 _) = _
  rw [hsub, map_sum]
  apply Finset.sum_congr rfl; intro b _
  ext e
  rw [coeff_projectLowContact]
  by_cases hlt : a + b₀ + b < m
  · rw [ite_eq_left hlt, MvPolynomial.coeff_monomial]
    by_cases he : locExp (a + b₀) b (b₀ - b + b₁) = e
    · subst he; rw [ite_eq_left rfl, ite_eq_left (by rw [localContactOrder_locExp]; exact hlt)]
    · rw [ite_eq_right he]; split_ifs <;> rfl
  · rw [ite_eq_right hlt, MvPolynomial.coeff_monomial]
    by_cases he : locExp (a + b₀) b (b₀ - b + b₁) = e
    · subst he; rw [ite_eq_right (by rw [localContactOrder_locExp]; exact hlt)]; simp
    · rw [ite_eq_right he]; split_ifs <;> simp

private theorem biSup_insert_eq {K V ι : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    [DecidableEq ι] (a : ι) (t : Finset ι) (M : ι → Submodule K V) :
    (⨆ i ∈ insert a t, M i) = M a ⊔ (⨆ i ∈ t, M i) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    rcases Finset.mem_insert.mp hi with rfl | hit
    · exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le i hit le_rfl)
  · refine sup_le (le_iSup₂_of_le a (Finset.mem_insert_self a t) le_rfl) ?_
    exact iSup₂_le fun i hi => le_iSup₂_of_le i (Finset.mem_insert_of_mem hi) le_rfl

private theorem finrank_biSup_of_disjoint {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι] (s : Finset ι) (M : ι → Submodule K V)
    (hfin : ∀ i ∈ s, Module.Finite K (M i))
    (hind : ∀ i ∈ s, Disjoint (M i) (⨆ j ∈ s.erase i, M j)) :
    Module.finrank K ↥(⨆ i ∈ s, M i) = ∑ i ∈ s, Module.finrank K (M i) := by
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ι), M i) = ⊥ := by simp
    rw [hbot, finrank_bot, Finset.sum_empty]
  | insert a t ha ih =>
    have hfin_a : Module.Finite K (M a) := hfin a (Finset.mem_insert_self a t)
    have hfin_t : ∀ i ∈ t, Module.Finite K (M i) := fun i hi => hfin i (Finset.mem_insert_of_mem hi)
    have hfin_sup : Module.Finite K ↥(⨆ i ∈ t, M i) := by
      clear ih hind hfin hfin_a ha
      induction t using Finset.induction_on with
      | empty =>
        have hbot : (⨆ i ∈ (∅ : Finset ι), M i) = ⊥ := by simp
        rw [hbot]; infer_instance
      | insert b u hb ihu =>
        rw [biSup_insert_eq]
        have : Module.Finite K (M b) := hfin_t b (Finset.mem_insert_self b u)
        have : Module.Finite K ↥(⨆ i ∈ u, M i) :=
          ihu (fun i hi => hfin_t i (Finset.mem_insert_of_mem hi))
        infer_instance
    have hsup_eq : (⨆ i ∈ insert a t, M i) = M a ⊔ (⨆ i ∈ t, M i) := biSup_insert_eq a t M
    have hdisj_a : Disjoint (M a) (⨆ i ∈ t, M i) := by
      have := hind a (Finset.mem_insert_self a t)
      rwa [Finset.erase_insert ha] at this
    have hind_t : ∀ i ∈ t, Disjoint (M i) (⨆ j ∈ t.erase i, M j) := by
      intro i hi
      have h1 := hind i (Finset.mem_insert_of_mem hi)
      refine h1.mono_right (iSup₂_le fun j hj => ?_)
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      have hjt : j ∈ t := (Finset.mem_erase.mp hj).2
      exact le_iSup₂_of_le j (Finset.mem_erase.mpr ⟨hne, Finset.mem_insert_of_mem hjt⟩) le_rfl
    rw [hsup_eq, Finset.sum_insert ha]
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq (M a) (⨆ i ∈ t, M i)
    rw [disjoint_iff.mp hdisj_a, finrank_bot, add_zero] at hadd
    rw [hadd, ih hfin_t hind_t]

/-- Exact rank of `localConstraintAt m 0 0` restricted to `primeFirstOrderSpace F w D_cut s`:
equals `exactRankD1 m s w D_cut` over **EVERY** field `F` of **EVERY** characteristic! -/
theorem finrank_range_localConstraintAt_zero_primeFirstOrderSpace {F : Type*} [Field F]
    {w : ℕ} (hw : 2 ≤ w) (m D_cut s : ℕ) :
    Module.finrank F
      (LinearMap.range ((localConstraintAt (R := F) (d := 1) m 0 0).domRestrict
        (primeFirstOrderSpace F w D_cut s))) = exactRankD1 m s w D_cut := by
  classical
  let φ : primeFirstOrderSpace F w D_cut s →ₗ[F] LocalPolynomial F 1 :=
    (localConstraintAt (R := F) (d := 1) m 0 0).domRestrict (primeFirstOrderSpace F w D_cut s)
  -- Active block index set B = {(i, j) : i < m, j ≤ i + s, i + (w - 1) * j < D_cut}.
  let blocks : Finset (ℕ × ℕ) :=
    ((Finset.range m).sigma fun i => Finset.range (i + s + 1)).filter
      (fun p => p.1 + (w - 1) * p.2 < D_cut) |>.image (fun p => (p.1, p.2))
  -- For each block (i, j), domain exponents and codomain exponents.
  let domExp (ij : ℕ × ℕ) : Finset (JetVariable 1 →₀ ℕ) :=
    (Finset.Icc (ij.2 - s) (min ij.1 ij.2)).image fun b₀ => d1Exp (ij.1 - b₀) b₀ (ij.2 - b₀)
  let codExp (ij : ℕ × ℕ) : Finset (LocalVariable 1 →₀ ℕ) :=
    (Finset.range (min (m - 1 - ij.1) ij.2 + 1)).image fun b => locExp ij.1 b (ij.2 - b)
  let blockIm (ij : ℕ × ℕ) : Submodule F (LocalPolynomial F 1) :=
    Submodule.span F
      (↑((domExp ij).image fun u =>
        localConstraintAt (R := F) (d := 1) m 0 0 (MvPolynomial.monomial u 1)) :
        Set (LocalPolynomial F 1))
  -- Every block image lies inside the codomain support `codExp ij`.
  have hblock_le_cod (ij : ℕ × ℕ) (hij : ij ∈ blocks) :
      blockIm ij ≤ MvPolynomial.restrictSupport F (↑(codExp ij) : Set (LocalVariable 1 →₀ ℕ)) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    rcases hx with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨b₀, hb₀, rfl⟩
    rcases Finset.mem_Icc.mp hb₀ with ⟨hlo, hhi⟩
    have hij' : ij.1 < m ∧ ij.2 ≤ ij.1 + s ∧ ij.1 + (w - 1) * ij.2 < D_cut := by
      rcases Finset.mem_image.mp hij with ⟨p, hp, hpeq⟩
      rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hp
      cases hpeq; exact ⟨hp.1.1, by omega, hp.2⟩
    rw [localConstraintAt_zero_monomial_d1]
    apply Submodule.sum_mem
    intro b hb
    have hbb₀ : b ≤ b₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    by_cases hlt : ij.1 - b₀ + b₀ + b < m
    · rw [ite_eq_left hlt, MvPolynomial.monomial_mem_restrictSupport]
      left; rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨b, Finset.mem_range.mpr (by omega), ?_⟩
      have h1 : ij.1 - b₀ + b₀ = ij.1 := by omega
      have h2 : b₀ - b + (ij.2 - b₀) = ij.2 - b := by omega
      rw [h1, h2]
    · rw [ite_eq_right hlt]; exact Submodule.zero_mem _
  -- The codomain supports `codExp ij` are pairwise disjoint across distinct `ij`.
  have hcod_disj : Pairwise fun ij₁ ij₂ : ℕ × ℕ => Disjoint (codExp ij₁) (codExp ij₂) := by
    intro ij₁ ij₂ hne
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rcases Finset.mem_image.mp he₁ with ⟨b₁, hb₁, rfl⟩
    rcases Finset.mem_image.mp he₂ with ⟨b₂, hb₂, heq⟩
    have hT := congrArg (fun f : LocalVariable 1 →₀ ℕ => f (localT 1)) heq
    have hE := congrArg (fun f : LocalVariable 1 →₀ ℕ => f (localE 1)) heq
    have hY := congrArg (fun f : LocalVariable 1 →₀ ℕ => f (localY 0)) heq
    simp at hT hE hY
    have hb₁_le : b₁ ≤ ij₁.2 := by have := Finset.mem_range.mp hb₁; omega
    have hb₂_le : b₂ ≤ ij₂.2 := by have := Finset.mem_range.mp hb₂; omega
    exact hne (Prod.ext hT.symm (by omega))
  -- Hence each `blockIm ij` is disjoint from the span of all other `blockIm j`.
  have hdisj_biSup : ∀ ij ∈ blocks, Disjoint (blockIm ij) (⨆ j ∈ blocks.erase ij, blockIm j) := by
    intro ij hij
    let otherCod : Set (LocalVariable 1 →₀ ℕ) :=
      ⋃ j ∈ blocks.erase ij, (↑(codExp j) : Set (LocalVariable 1 →₀ ℕ))
    have hother_le : (⨆ j ∈ blocks.erase ij, blockIm j) ≤
        MvPolynomial.restrictSupport F otherCod :=
      iSup₂_le fun j hj => (hblock_le_cod j (Finset.mem_of_mem_erase hj)).trans
        (MvPolynomial.restrictSupport_mono F fun e he => Set.mem_iUnion₂.mpr ⟨j, hj, he⟩)
    refine Disjoint.mono (hblock_le_cod ij hij) hother_le ?_
    rw [Submodule.disjoint_def]
    intro p hp1 hp2
    ext e
    by_contra hne
    have hne' : p.coeff e ≠ 0 := by simpa using hne
    have he : e ∈ p.support := MvPolynomial.mem_support_iff.mpr hne'
    have he1 : e ∈ codExp ij := Finset.mem_coe.mp (hp1 he)
    have he2 : e ∈ otherCod := hp2 he
    rcases Set.mem_iUnion₂.mp he2 with ⟨j, hj, hej⟩
    have hne_ij : ij ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact Finset.disjoint_left.mp (hcod_disj hne_ij) he1 (Finset.mem_coe.mp hej)
  -- The range of `φ` equals `⨆ ij ∈ blocks, blockIm ij`.
  have hrange_eq : LinearMap.range φ = ⨆ ij ∈ blocks, blockIm ij := by
    apply le_antisymm
    · rintro _ ⟨Q, rfl⟩
      change localConstraintAt m 0 0 Q.1 ∈ _
      rw [Q.1.as_sum, map_sum]
      apply Submodule.sum_mem; intro u hu
      have hsmul : MvPolynomial.monomial u (Q.1.coeff u) =
          Q.1.coeff u • MvPolynomial.monomial u (1 : F) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hsmul, map_smul]
      apply Submodule.smul_mem
      have huMem := (mem_primeExponents_iff hw).mp (Q.2 hu)
      rw [weight_differentialWeight_d1] at huMem
      let i := u none + u (some 0)
      let j := u (some 0) + u (some 1)
      by_cases hi : i < m
      · have hij : (i, j) ∈ blocks := by
          refine Finset.mem_image.mpr ⟨⟨i, j⟩, ?_, rfl⟩
          rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
          have hwt : i + (w - 1) * j = u none + w * u (some 0) + (w - 1) * u (some 1) := by
            dsimp only [i, j]
            have : (w - 1) * u (some 0) + u (some 0) = w * u (some 0) := by
              rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ w)]
            rw [Nat.mul_add]; omega
          dsimp only
          exact ⟨⟨hi, by dsimp only [i, j]; omega⟩, by rw [hwt]; exact huMem.2⟩
        refine Submodule.mem_iSup_of_mem (i, j) (Submodule.mem_iSup_of_mem hij ?_)
        apply Submodule.subset_span
        rw [Finset.mem_coe]
        refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
        refine Finset.mem_image.mpr ⟨u (some 0), ?_, ?_⟩
        · rw [Finset.mem_Icc]; dsimp only [i, j]; omega
        · have h1 : i - u (some 0) = u none := by dsimp only [i]; omega
          have h2 : j - u (some 0) = u (some 1) := by dsimp only [j]; omega
          rw [h1, h2, d1Exp_eta]
      · have hzero : localConstraintAt (R := F) (d := 1) m 0 0 (MvPolynomial.monomial u 1) = 0 := by
          rw [← d1Exp_eta u, localConstraintAt_zero_monomial_d1]
          apply Finset.sum_eq_zero; intro b _
          exact ite_eq_right (by dsimp only [i] at hi; omega)
        rw [hzero]; exact Submodule.zero_mem _
    · refine iSup₂_le fun ij hij => ?_
      rw [Submodule.span_le]
      intro x hx
      rw [Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hu with ⟨b₀, hb₀, rfl⟩
      rcases Finset.mem_Icc.mp hb₀ with ⟨hlo, hhi⟩
      rcases Finset.mem_image.mp hij with ⟨p, hp, hpeq⟩
      rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hp
      have hij1 : ij.1 = p.1 := congrArg Prod.fst hpeq.symm
      have hij2 : ij.2 = p.2 := congrArg Prod.snd hpeq.symm
      have humem : MvPolynomial.monomial (d1Exp (ij.1 - b₀) b₀ (ij.2 - b₀)) (1 : F) ∈
          primeFirstOrderSpace F w D_cut s := by
        rw [primeFirstOrderSpace, MvPolynomial.monomial_mem_restrictSupport]
        left; rw [Finset.mem_coe, mem_primeExponents_iff hw, weight_differentialWeight_d1]
        simp only [d1Exp_none, d1Exp_some_zero, d1Exp_some_one]
        have h1 : (w - 1) * b₀ + b₀ = w * b₀ := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ w)]
        have h2 : (w - 1) * (ij.2 - b₀) + (w - 1) * b₀ = (w - 1) * ij.2 := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        have hp2 : ij.1 + (w - 1) * ij.2 < D_cut := by rw [hij1, hij2]; exact hp.2
        exact ⟨by omega, by omega⟩
      exact ⟨⟨_, humem⟩, rfl⟩
  -- Compute exact `finrank (blockIm ij)` for every `ij ∈ blocks`.
  have hblock_rank (ij : ℕ × ℕ) (hij : ij ∈ blocks) :
      Module.finrank F (blockIm ij) =
        min (min (m - 1 - ij.1) ij.2 + 1) (min ij.1 ij.2 + 1 - (ij.2 - s)) := by
    have hij' : ij.1 < m ∧ ij.2 ≤ ij.1 + s := by
      rcases Finset.mem_image.mp hij with ⟨p, hp, hpeq⟩
      rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hp
      cases hpeq; exact ⟨hp.1.1, by omega⟩
    let rows := min (m - 1 - ij.1) ij.2 + 1
    let cols := min ij.1 ij.2 + 1 - (ij.2 - s)
    let r := min rows cols
    apply le_antisymm
    · -- Upper bound: `≤ min rows cols` (from spanning set of size `≤ cols` and codomain dim `≤ rows`).
      apply le_min
      · let codSub : Submodule F (LocalPolynomial F 1) :=
          MvPolynomial.restrictSupport F (↑(codExp ij) : Set (LocalVariable 1 →₀ ℕ))
        let bCod : Module.Basis ↥(codExp ij) F codSub :=
          MvPolynomial.basisRestrictSupport (R := F) (↑(codExp ij) : Set (LocalVariable 1 →₀ ℕ))
        have : Module.Finite F codSub := Module.Finite.of_basis bCod
        have hle : Module.finrank F (blockIm ij) ≤ Module.finrank F codSub :=
          Submodule.finrank_mono (hblock_le_cod ij hij)
        have hcod_dim : Module.finrank F codSub = (codExp ij).card := by
          rw [Module.finrank_eq_card_basis bCod, Fintype.card_coe]
        have hcard : (codExp ij).card ≤ rows :=
          (Finset.card_image_le).trans (by simp [rows])
        omega
      · have hspan : Module.finrank F (blockIm ij) ≤ (domExp ij).card := by
          let imgs : Finset (LocalPolynomial F 1) :=
            (domExp ij).image (fun u => localConstraintAt (R := F) (d := 1) m 0 0
              (MvPolynomial.monomial u 1))
          have h1 : Module.finrank F (blockIm ij) ≤
              (↑imgs : Set (LocalPolynomial F 1)).toFinset.card :=
            finrank_span_le_card (R := F) (↑imgs : Set (LocalPolynomial F 1))
          have hcard_eq : (↑imgs : Set (LocalPolynomial F 1)).toFinset.card = imgs.card := by simp
          exact h1.trans (hcard_eq.le.trans Finset.card_image_le)
        have hcard : (domExp ij).card ≤ cols := by
          refine (Finset.card_image_le).trans ?_
          rw [Nat.card_Icc]
        omega
    · -- Lower bound: `r ≤ finrank (blockIm ij)` via Vandermonde Pascal `det = 1`!
      let L := ij.2 - s
      let vec (c : Fin r) : blockIm ij :=
        ⟨localConstraintAt m 0 0 (MvPolynomial.monomial (d1Exp (ij.1 - (L + c.val)) (L + c.val)
          (ij.2 - (L + c.val))) 1), by
          apply Submodule.subset_span
          rw [Finset.mem_coe]
          refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
          refine Finset.mem_image.mpr ⟨L + c.val, ?_, rfl⟩
          rw [Finset.mem_Icc]; have hc := c.isLt; dsimp only [r, cols, L] at hc ⊢; omega⟩
      let proj : blockIm ij →ₗ[F] (Fin r → F) :=
        LinearMap.pi fun b : Fin r =>
          (MvPolynomial.lcoeff F (locExp ij.1 b.val (ij.2 - b.val))).comp (blockIm ij).subtype
      -- Check `proj (vec c) b = ((L + c.val).choose b.val : F)`!
      have hentry (b c : Fin r) : proj (vec c) b = ((L + c.val).choose b.val : F) := by
        change (localConstraintAt (R := F) (d := 1) m 0 0
          (MvPolynomial.monomial (d1Exp (ij.1 - (L + c.val)) (L + c.val)
            (ij.2 - (L + c.val))) 1)).coeff (locExp ij.1 b.val (ij.2 - b.val)) = _
        rw [localConstraintAt_zero_monomial_d1, MvPolynomial.coeff_sum]
        have hc_le : L + c.val ≤ min ij.1 ij.2 := by
          have hc := c.isLt; dsimp only [r, cols, L] at hc ⊢; omega
        have hb_lt : b.val < rows := by have hb := b.isLt; dsimp only [r] at hb; omega
        have hb_m : ij.1 - (L + c.val) + (L + c.val) + b.val < m := by
          dsimp only [rows] at hb_lt; omega
        have h1 : ij.1 - (L + c.val) + (L + c.val) = ij.1 := by omega
        by_cases hbc : b.val ≤ L + c.val
        · rw [Finset.sum_eq_single b.val]
          · rw [ite_eq_left hb_m, h1, show L + c.val - b.val + (ij.2 - (L + c.val)) = ij.2 - b.val
              by omega, MvPolynomial.coeff_monomial, ite_eq_left rfl]
          · intro b' _ hne
            split_ifs with hlt
            · rw [MvPolynomial.coeff_monomial, ite_eq_right]
              intro heq
              have := congrArg (fun f : LocalVariable 1 →₀ ℕ => f (localE 1)) heq
              simp at this; exact hne this
            · simp
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
          apply Finset.sum_eq_zero; intro b' hb'
          have hb'le : b' ≤ L + c.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
          split_ifs with hlt
          · rw [MvPolynomial.coeff_monomial, ite_eq_right]
            intro heq
            have := congrArg (fun f : LocalVariable 1 →₀ ℕ => f (localE 1)) heq
            simp at this; omega
          · simp
      have hli : LinearIndependent F vec := by
        apply LinearIndependent.of_comp proj
        rw [Fintype.linearIndependent_iff]
        intro g hg
        let M : Matrix (Fin r) (Fin r) F :=
          Matrix.of fun b c => ((L + c.val).choose b.val : F)
        have hMg : M.mulVec g = 0 := by
          ext b
          have hgb := congrFun hg b
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgb
          change ∑ c : Fin r, M b c * g c = 0
          rw [← hgb]
          apply Finset.sum_congr rfl; intro c _
          dsimp only [M, Matrix.of_apply, Function.comp_apply]
          rw [hentry b c, mul_comm]
        have hdet : IsUnit M.det := by rw [det_pascal_submatrix L r]; exact isUnit_one
        have hg0 : g = 0 := by
          have := congrArg (fun v => M⁻¹.mulVec v) hMg
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hdet, Matrix.one_mulVec,
            Matrix.mulVec_zero] at this
          exact this
        intro c; exact congrFun hg0 c
      simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank
  -- Sum the independent block ranks!
  have hfin_block (ij : ℕ × ℕ) (_ : ij ∈ blocks) : Module.Finite F (blockIm ij) :=
    Module.Finite.span_of_finite F (Finset.finite_toSet _)
  rw [hrange_eq, finrank_biSup_of_disjoint blocks blockIm hfin_block hdisj_biSup]
  rw [Finset.sum_congr rfl fun ij hij => hblock_rank ij hij]
  -- Match the sum over `blocks` to `exactRankD1 m s w D_cut`!
  unfold exactRankD1
  have hinj_pair : Function.Injective (fun p : Σ _ : ℕ, ℕ => (p.1, p.2)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; cases h; rfl
  rw [Finset.sum_image (fun _ _ _ _ h => hinj_pair h), Finset.sum_filter, Finset.sum_sigma]

/-- **Exact First-Order Local Rank Theorem (at ANY `(center, received)` in ANY field `F`):**
`finrank F (range (localConstraintAt m center received |_{V_{D_cut}(s)})) = exactRankD1 m s w D_cut`. -/
theorem finrank_range_localConstraintAt_primeFirstOrderSpace {F : Type*} [Field F]
    {w : ℕ} (hw : 2 ≤ w) (m D_cut s : ℕ) (center received : F) :
    Module.finrank F
      (LinearMap.range ((localConstraintAt (R := F) (d := 1) m center received).domRestrict
        (primeFirstOrderSpace F w D_cut s))) = exactRankD1 m s w D_cut := by
  let e := globalPointTranslation_equiv_primeFirstOrderSpace (R := F) (D_cut := D_cut) (s := s)
    hw center received
  have hcomp : ((localConstraintAt (R := F) (d := 1) m 0 0).domRestrict
      (primeFirstOrderSpace F w D_cut s)).comp e.toLinearMap =
      (localConstraintAt (R := F) (d := 1) m center received).domRestrict
        (primeFirstOrderSpace F w D_cut s) := by
    apply LinearMap.ext; intro Q
    exact (localConstraintAt_eq_zero_globalPointTranslation (R := F) (d := 1) (m := m)
      center received Q.1).symm
  rw [← hcomp, LinearMap.range_comp_of_range_eq_top _ e.range]
  exact finrank_range_localConstraintAt_zero_primeFirstOrderSpace hw m D_cut s

/-! ### Part 4: Integral-Domain Kernel Identity & Exact Quotient-Contact Rank Identity -/

/-- Exact local contact order `k` of `f ∈ DifferentialPolynomial R d` at `(center, received)`:
all monomials of `unscaledLocalSubstitution d center received f` have contact order `≥ k`, and at
least one monomial has contact order `= k`. -/
def HasExactLocalContactOrder {R : Type*} [CommRing R] {d : ℕ}
    (center received : R) (f : DifferentialPolynomial R d) (k : ℕ) : Prop :=
  (∀ e ∈ (unscaledLocalSubstitution d center received f).support, k ≤ localContactOrder d e) ∧
  (∃ e ∈ (unscaledLocalSubstitution d center received f).support, localContactOrder d e = k)

/-- **Integral-Domain Kernel Shift Lemma (ANY integral domain `R`, ANY order `d`, ANY char!):**
If `f` has exact local contact order `k` at `(center, received)`, then for EVERY `G`:
`localConstraintAt m center received (f * G) = 0 ↔ localConstraintAt (m - k) center received G = 0`. -/
theorem localConstraintAt_mul_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (m k : ℕ) (center received : R) (f G : DifferentialPolynomial R d)
    (hf : HasExactLocalContactOrder center received f k) :
    localConstraintAt m center received (f * G) = 0 ↔
      localConstraintAt (m - k) center received G = 0 := by
  classical
  let L := unscaledLocalSubstitution (R := R) d center received
  let lf := L f
  let lG := L G
  change projectLowContact m (L (f * G)) = 0 ↔ projectLowContact (m - k) lG = 0
  rw [map_mul, projectLowContact_eq_zero_iff, projectLowContact_eq_zero_iff]
  constructor
  · intro hfg
    by_contra hnot
    push Not at hnot
    -- Let `r` be the minimum contact order among monomials in `lG.support`.
    obtain ⟨e₀, he₀_lt, he₀_ne⟩ := hnot
    let degs : Finset ℕ := lG.support.image (localContactOrder d)
    have hdegs_ne : degs.Nonempty :=
      ⟨localContactOrder d e₀, Finset.mem_image.mpr ⟨e₀, MvPolynomial.mem_support_iff.mpr he₀_ne, rfl⟩⟩
    let r := degs.min' hdegs_ne
    have hr_lt : r < m - k :=
      (Finset.min'_le degs _ (Finset.mem_image.mpr ⟨e₀, MvPolynomial.mem_support_iff.mpr he₀_ne, rfl⟩)).trans_lt
        he₀_lt
    have hr_le : ∀ e ∈ lG.support, r ≤ localContactOrder d e := fun e he =>
      Finset.min'_le degs _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    -- Leading contact-homogeneous components `hf_lead` (order `k`) and `hG_lead` (order `r`) are nonzero!
    let hf_lead := MvPolynomial.weightedHomogeneousComponent (localContactWeight d) k lf
    let hG_lead := MvPolynomial.weightedHomogeneousComponent (localContactWeight d) r lG
    have hf_lead_ne : hf_lead ≠ 0 := by
      obtain ⟨ef, hef_supp, hef_ord⟩ := hf.2
      intro h0
      have hc := congrArg (fun p : LocalPolynomial R d => p.coeff ef) h0
      simp only [hf_lead, MvPolynomial.coeff_weightedHomogeneousComponent,
        AddMonoidAlgebra.coeff_zero] at hc
      change (if localContactOrder d ef = k then lf.coeff ef else 0) = 0 at hc
      rw [ite_eq_left hef_ord] at hc
      exact MvPolynomial.mem_support_iff.mp hef_supp hc
    have hG_lead_ne : hG_lead ≠ 0 := by
      have hr_mem : r ∈ degs := Finset.min'_mem degs hdegs_ne
      rcases Finset.mem_image.mp hr_mem with ⟨eG, heG_supp, heG_ord⟩
      intro h0
      have hc := congrArg (fun p : LocalPolynomial R d => p.coeff eG) h0
      simp only [hG_lead, MvPolynomial.coeff_weightedHomogeneousComponent,
        AddMonoidAlgebra.coeff_zero] at hc
      change (if localContactOrder d eG = r then lG.coeff eG else 0) = 0 at hc
      rw [ite_eq_left heG_ord] at hc
      exact MvPolynomial.mem_support_iff.mp heG_supp hc
    have hprod_ne : hf_lead * hG_lead ≠ 0 := mul_ne_zero hf_lead_ne hG_lead_ne
    -- Every monomial in `(hf_lead * hG_lead).support` has contact order `k + r` and agrees with `lf * lG`!
    obtain ⟨e, he_supp⟩ := MvPolynomial.support_nonempty.mpr hprod_ne
    have hprod_hom : (hf_lead * hG_lead).IsWeightedHomogeneous (localContactWeight d) (k + r) :=
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous k lf).mul
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous r lG)
    have he_ord : localContactOrder d e = k + r := hprod_hom (MvPolynomial.mem_support_iff.mp he_supp)
    have hcoeff_eq : (lf * lG).coeff e = (hf_lead * hG_lead).coeff e := by
      rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
      apply Finset.sum_congr rfl
      intro uv huv
      have huv_eq : uv.1 + uv.2 = e := Finset.mem_antidiagonal.mp huv
      rw [MvPolynomial.coeff_weightedHomogeneousComponent,
        MvPolynomial.coeff_weightedHomogeneousComponent]
      change lf.coeff uv.1 * lG.coeff uv.2 =
        (if localContactOrder d uv.1 = k then lf.coeff uv.1 else 0) *
        (if localContactOrder d uv.2 = r then lG.coeff uv.2 else 0)
      by_cases h1 : uv.1 ∈ lf.support
      · by_cases h2 : uv.2 ∈ lG.support
        · have hk1 : k ≤ localContactOrder d uv.1 := hf.1 uv.1 h1
          have hr2 : r ≤ localContactOrder d uv.2 := hr_le uv.2 h2
          have hsum : localContactOrder d uv.1 + localContactOrder d uv.2 = k + r := by
            rw [← he_ord, ← huv_eq]
            exact (map_add (Finsupp.weight (localContactWeight d)) uv.1 uv.2).symm
          rw [ite_eq_left (by omega : localContactOrder d uv.1 = k),
            ite_eq_left (by omega : localContactOrder d uv.2 = r)]
        · have hz : lG.coeff uv.2 = 0 := MvPolynomial.notMem_support_iff.mp h2
          simp [hz]
      · have hz : lf.coeff uv.1 = 0 := MvPolynomial.notMem_support_iff.mp h1
        simp [hz]
    have he_zero : (lf * lG).coeff e = 0 := hfg e (by omega)
    rw [hcoeff_eq] at he_zero
    exact MvPolynomial.mem_support_iff.mp he_supp he_zero
  · intro hG e he
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero; intro uv huv
    have huv_eq : uv.1 + uv.2 = e := Finset.mem_antidiagonal.mp huv
    by_cases h1 : uv.1 ∈ lf.support
    · have hk1 : k ≤ localContactOrder d uv.1 := hf.1 uv.1 h1
      have hsum : localContactOrder d uv.1 + localContactOrder d uv.2 = localContactOrder d e := by
        rw [← huv_eq]
        exact (map_add (Finsupp.weight (localContactWeight d)) uv.1 uv.2).symm
      have hlt2 : localContactOrder d uv.2 < m - k := by omega
      rw [hG uv.2 hlt2, mul_zero]
    · rw [MvPolynomial.notMem_support_iff.mp h1, zero_mul]

/-- **General Rank-Shift Identity:** for ANY finite-dimensional subspace `C` and any `f` of exact
local contact order `k` at `(center, received)`,
`finrank (range (localConstraintAt m ∘ (· f) |_C)) = finrank (range (localConstraintAt (m - k) |_C))`. -/
theorem finrank_range_localConstraintAt_mul_eq {F : Type*} [Field F] {d : ℕ}
    (m k : ℕ) (center received : F) (f : DifferentialPolynomial F d)
    (hf : HasExactLocalContactOrder center received f k)
    (C : Submodule F (DifferentialPolynomial F d)) [Module.Finite F C] :
    Module.finrank F (LinearMap.range
      (((localConstraintAt (R := F) (d := d) m center received).comp
        (LinearMap.mulLeft F f)).domRestrict C)) =
    Module.finrank F (LinearMap.range
      ((localConstraintAt (R := F) (d := d) (m - k) center received).domRestrict C)) := by
  let L₁ : C →ₗ[F] LocalPolynomial F d :=
    ((localConstraintAt (R := F) (d := d) m center received).comp
      (LinearMap.mulLeft F f)).domRestrict C
  let L₂ : C →ₗ[F] LocalPolynomial F d :=
    (localConstraintAt (R := F) (d := d) (m - k) center received).domRestrict C
  have hker : LinearMap.ker L₁ = LinearMap.ker L₂ := by
    ext G
    simp only [LinearMap.mem_ker, L₁, L₂, LinearMap.domRestrict_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply]
    exact localConstraintAt_mul_eq_zero_iff m k center received f G.1 hf
  have h1 := LinearMap.finrank_range_add_finrank_ker L₁
  have h2 := LinearMap.finrank_range_add_finrank_ker L₂
  rw [hker] at h1
  change Module.finrank F (LinearMap.range L₁) = Module.finrank F (LinearMap.range L₂)
  omega

/-- **Crown-Jewel Prime-Field Quotient-Contact Rank Identity (`#142`):**
For ANY field `F` (any prime characteristic!), `w ≥ 2`, `D_cut, s, m`, `f` with exact local
contact order `k` at `(center, received)`:
`finrank F (range (localConstraintAt m center received ∘ (· f) |_{V_{D_cut - W_f}(s - d_f)}))
  = exactRankD1 (m - k) (s - d_f) w (D_cut - W_f)`. -/
theorem finrank_range_localConstraintAt_mul_primeFirstOrderSpace {F : Type*} [Field F]
    {w : ℕ} (hw : 2 ≤ w) (m k D_cut W_f s d_f : ℕ) (center received : F)
    (f : DifferentialPolynomial F 1) (hf : HasExactLocalContactOrder center received f k) :
    Module.finrank F (LinearMap.range
      (((localConstraintAt (R := F) (d := 1) m center received).comp
        (LinearMap.mulLeft F f)).domRestrict
        (primeFirstOrderSpace F w (D_cut - W_f) (s - d_f)))) =
    exactRankD1 (m - k) (s - d_f) w (D_cut - W_f) := by
  rw [finrank_range_localConstraintAt_mul_eq m k center received f hf]
  exact finrank_range_localConstraintAt_primeFirstOrderSpace hw (m - k) (D_cut - W_f) (s - d_f)
    center received

/-! ### Part 5: Prime-Field Quotient-Contact Interpolant (`B6402CombinedInterpolation` in char `p`) -/

/-- Degree bound on `differentialSpecialization Q S` for `Q ∈ primeFirstOrderSpace F w D_cut s`:
if `Q ≠ 0` and `S.natDegree ≤ w`, then `(differentialSpecialization Q S).natDegree < D_cut`. -/
theorem natDegree_differentialSpecialization_lt {F : Type*} [Field F]
    {w D_cut s : ℕ} (hw : 2 ≤ w) {Q : DifferentialPolynomial F 1}
    (hQ : Q ∈ primeFirstOrderSpace F w D_cut s) (hQne : Q ≠ 0)
    {S : Polynomial F} (hS : S.natDegree ≤ w) :
    (differentialSpecialization Q S).natDegree < D_cut := by
  have hQsupp := (mem_primeFirstOrderSpace_iff hw).mp hQ
  obtain ⟨u0, hu0⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hDpos : 0 < D_cut := (Nat.zero_le _).trans_lt (hQsupp u0 hu0).2
  have hdeg_le : (differentialSpecialization Q S).natDegree ≤ D_cut - 1 := by
    unfold differentialSpecialization differentialSpecializationHom
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro u hu
    have huw := (hQsupp u hu).2
    rw [weight_differentialWeight_d1] at huw
    refine Polynomial.natDegree_mul_le.trans ?_
    change (Polynomial.C (Q.coeff u)).natDegree + _ ≤ _
    rw [Polynomial.natDegree_C, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun v => differentialWeight w v * u v) fun v _ => ?_).trans ?_
    · refine Polynomial.natDegree_pow_le.trans ?_
      rw [Nat.mul_comm]
      apply Nat.mul_le_mul_right
      rcases v with _ | j
      · simp [differentialWeight]
      · fin_cases j
        · simp [differentialWeight, Polynomial.hasseDeriv_zero, hS]
        · simp only [differentialWeight]
          exact (Polynomial.natDegree_hasseDeriv_le S 1).trans (Nat.sub_le_sub_right hS 1)
    · have hsum_eq : ∑ v ∈ u.support, differentialWeight w v * u v =
          u none + w * u (some 0) + (w - 1) * u (some 1) := by
        rw [← weight_differentialWeight_d1 w u]
        simp [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm]
      omega
  omega

/-- **Prime-Field Quotient-Contact Interpolation Theorem (`#142` / `B6402CombinedInterpolation`):**
Given `f ∈ DifferentialPolynomial F 1` (`f ≠ 0`, `W_f = wdeg f`, `d_f = deg_{Y₁}(f) ≤ s`) with
exact local contact orders `k i` at injective nodes `(centers i, received i)`, whenever the
exact quotient-contact surplus holds:
```text
  ∑ i, (exactRankD1 m s w D_cut - exactRankD1 (m - k i) (s - d_f) w (D_cut - W_f))
    + exactDimD1 w (D_cut - W_f) (s - d_f) < exactDimD1 w D_cut s,
```
there exists `Q ∈ primeFirstOrderSpace F w D_cut s` such that:
1. `¬ f ∣ Q` (and `Q ≠ 0`),
2. at every site `i`, `∃ G_i ∈ primeFirstOrderSpace F w (D_cut - W_f) (s - d_f)` with
   `SatisfiesLocalConstraints m (centers i) (received i) (Q - f * G_i)`,
3. for EVERY codeword `S : F[X]` with `S.natDegree ≤ w`, `differentialSpecialization f S = 0`,
   and `H : Finset ι` with `∀ i ∈ H, S.eval (centers i) = received i` and `D_cut ≤ m * H.card`,
   we have `differentialSpecialization Q S = 0`! -/
theorem exists_quotient_contact_interpolant {F ι : Type*} [Field F] [Fintype ι]
    {w D_cut s m : ℕ} (hw : 2 ≤ w)
    (centers received : ι → F) (hcenters : Function.Injective centers)
    (f : DifferentialPolynomial F 1) (hf : f ≠ 0)
    (hd_le : f.degreeOf (some 1) ≤ s)
    (k : ι → ℕ)
    (hord : ∀ i, HasExactLocalContactOrder (centers i) (received i) f (k i))
    (hsurplus :
      (∑ i : ι, (exactRankD1 m s w D_cut -
        exactRankD1 (m - k i) (s - f.degreeOf (some 1)) w
          (D_cut - MvPolynomial.weightedTotalDegree (differentialWeight w) f))) +
      exactDimD1 w (D_cut - MvPolynomial.weightedTotalDegree (differentialWeight w) f)
        (s - f.degreeOf (some 1)) <
      exactDimD1 w D_cut s) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ∈ primeFirstOrderSpace F w D_cut s ∧
      ¬ f ∣ Q ∧
      (∀ i : ι, ∃ G : DifferentialPolynomial F 1,
        G ∈ primeFirstOrderSpace F w
          (D_cut - MvPolynomial.weightedTotalDegree (differentialWeight w) f)
          (s - f.degreeOf (some 1)) ∧
        SatisfiesLocalConstraints m (centers i) (received i) (Q - f * G)) ∧
      (∀ (S : Polynomial F) (H : Finset ι),
        S.natDegree ≤ w →
        differentialSpecialization f S = 0 →
        (∀ i ∈ H, S.eval (centers i) = received i) →
        D_cut ≤ m * H.card →
        differentialSpecialization Q S = 0) := by
  classical
  let W_f := MvPolynomial.weightedTotalDegree (differentialWeight w) f
  let d_f := f.degreeOf (some 1)
  let U := primeFirstOrderSpace F w D_cut s
  let C := primeFirstOrderSpace F w (D_cut - W_f) (s - d_f)
  let Mf : C →ₗ[F] U := mulLeftInSpace hw f W_f d_f le_rfl le_rfl hd_le
  let Φ (i : ι) : U →ₗ[F] LocalPolynomial F 1 :=
    (localConstraintAt (R := F) (d := 1) m (centers i) (received i)).domRestrict U
  let Im (i : ι) := LinearMap.range (Φ i)
  let Sub (i : ι) : Submodule F (Im i) :=
    (LinearMap.range ((Φ i).comp Mf)).comap (Im i).subtype
  let qMap (i : ι) : U →ₗ[F] (Im i ⧸ Sub i) :=
    (Submodule.mkQ (Sub i)).comp ((Φ i).rangeRestrict)
  let rows : U →ₗ[F] ((i : ι) → (Im i ⧸ Sub i)) := LinearMap.pi qMap
  -- Finite-dimensionality and exact rank of each quotient `Im i ⧸ Sub i`.
  have hIm_fin : ∀ i : ι, Module.Finite F (Im i) := fun i => Module.Finite.range (Φ i)
  have : ∀ i : ι, Module.Finite F (Im i ⧸ Sub i) := fun i => by
    have : Module.Finite F (Im i) := hIm_fin i
    infer_instance
  have : ∀ i : ι, Module.Free F (Im i ⧸ Sub i) := fun i =>
    Module.Free.of_divisionRing F (Im i ⧸ Sub i)
  have hSub_dim (i : ι) : Module.finrank F (Sub i) =
      exactRankD1 (m - k i) (s - d_f) w (D_cut - W_f) := by
    have hle : LinearMap.range ((Φ i).comp Mf) ≤ Im i := by
      rintro _ ⟨G, rfl⟩; exact ⟨Mf G, rfl⟩
    have heq : LinearMap.range ((Φ i).comp Mf) = (Sub i).map (Im i).subtype := by
      ext y; simp only [Sub, Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨fun hy => ⟨⟨y, hle hy⟩, hy, rfl⟩, fun ⟨⟨_, _⟩, hy, h⟩ => h ▸ hy⟩
    have hfin_eq : Module.finrank F (Sub i) = Module.finrank F (LinearMap.range ((Φ i).comp Mf)) := by
      rw [heq]
      exact (Submodule.equivMapOfInjective (Im i).subtype Subtype.val_injective (Sub i)).finrank_eq
    rw [hfin_eq]
    have hcomp_eq : (Φ i).comp Mf =
        ((localConstraintAt (R := F) (d := 1) m (centers i) (received i)).comp
          (LinearMap.mulLeft F f)).domRestrict C := by
      ext G; rfl
    rw [hcomp_eq]
    exact finrank_range_localConstraintAt_mul_primeFirstOrderSpace hw m (k i) D_cut W_f s d_f
      (centers i) (received i) f (hord i)
  have hQuot_dim (i : ι) : Module.finrank F (Im i ⧸ Sub i) =
      exactRankD1 m s w D_cut - exactRankD1 (m - k i) (s - d_f) w (D_cut - W_f) := by
    have : Module.Finite F (Im i) := hIm_fin i
    have h := Submodule.finrank_quotient_add_finrank (Sub i)
    have hIm := finrank_range_localConstraintAt_primeFirstOrderSpace hw m D_cut s
      (centers i) (received i)
    have hSub := hSub_dim i
    change Module.finrank F (Im i) = exactRankD1 m s w D_cut at hIm
    omega
  have hrange_le : Module.finrank F (LinearMap.range rows) ≤
      ∑ i : ι, (exactRankD1 m s w D_cut - exactRankD1 (m - k i) (s - d_f) w (D_cut - W_f)) := by
    have h1 : Module.finrank F (LinearMap.range rows) ≤
        Module.finrank F ((i : ι) → (Im i ⧸ Sub i)) := Submodule.finrank_le _
    rw [Module.finrank_pi_fintype (R := F)] at h1
    simpa only [hQuot_dim] using h1
  have hsurp' : Module.finrank F (LinearMap.range rows) + Module.finrank F C < Module.finrank F U := by
    have hU : Module.finrank F U = exactDimD1 w D_cut s := finrank_primeFirstOrderSpace w D_cut s
    have hC : Module.finrank F C = exactDimD1 w (D_cut - W_f) (s - d_f) :=
      finrank_primeFirstOrderSpace w (D_cut - W_f) (s - d_f)
    change (∑ i : ι, (exactRankD1 m s w D_cut -
      exactRankD1 (m - k i) (s - d_f) w (D_cut - W_f))) +
      exactDimD1 w (D_cut - W_f) (s - d_f) < exactDimD1 w D_cut s at hsurplus
    omega
  have hex : ∃ Q : U, rows Q = 0 ∧ Q ∉ LinearMap.range Mf := by
    by_contra! hsub
    have hle : LinearMap.ker rows ≤ LinearMap.range Mf := fun u hu => hsub u hu
    have h1 : Module.finrank F (LinearMap.ker rows) ≤ Module.finrank F (LinearMap.range Mf) :=
      Submodule.finrank_mono hle
    have h2 : Module.finrank F (LinearMap.range Mf) ≤ Module.finrank F C :=
      LinearMap.finrank_range_le Mf
    have hnull : Module.finrank F (LinearMap.range rows) + Module.finrank F (LinearMap.ker rows) =
        Module.finrank F U := by
      let φq : (U ⧸ LinearMap.ker rows) →ₗ[F] LinearMap.range rows :=
        { toFun := Quotient.lift (fun x : U => rows.rangeRestrict x) (fun x y h => by
            apply Subtype.ext
            have hxy : x - y ∈ LinearMap.ker rows :=
              (Submodule.Quotient.eq (LinearMap.ker rows)).mp (Quotient.sound h)
            funext i
            have hi : qMap i (x - y) = 0 := congrFun hxy i
            rw [map_sub, sub_eq_zero] at hi
            exact hi)
          map_add' := fun a b => by
            induction a using Submodule.Quotient.induction_on with
            | H x =>
              induction b using Submodule.Quotient.induction_on with
              | H y => exact map_add rows.rangeRestrict x y
          map_smul' := fun c a => by
            induction a using Submodule.Quotient.induction_on with
            | H x => exact map_smul rows.rangeRestrict c x }
      have hbij : Function.Bijective φq := by
        constructor
        · intro a b hab
          induction a using Submodule.Quotient.induction_on with
          | H x =>
            induction b using Submodule.Quotient.induction_on with
            | H y =>
              rw [Submodule.Quotient.eq]
              change rows (x - y) = 0
              funext i
              change qMap i (x - y) = 0
              rw [map_sub, sub_eq_zero]
              exact congrFun (congrArg Subtype.val hab) i
        · rintro ⟨y, x, rfl⟩
          exact ⟨Submodule.Quotient.mk x, rfl⟩
      rw [← (LinearEquiv.ofBijective φq hbij).finrank_eq]
      exact Submodule.finrank_quotient_add_finrank (LinearMap.ker rows)
    omega
  rcases hex with ⟨Q, hQker, hQout⟩
  have hndvd : ¬ f ∣ Q.1 := (mul_mem_primeFirstOrderSpace_iff hw f hf hd_le Q).not.mpr hQout
  have hlocal : ∀ i : ι, ∃ G : DifferentialPolynomial F 1,
      G ∈ C ∧ SatisfiesLocalConstraints m (centers i) (received i) (Q.1 - f * G) := by
    intro i
    have hqi : qMap i Q = 0 := congrFun hQker i
    have hmemSub : (Φ i).rangeRestrict Q ∈ Sub i := (Submodule.Quotient.mk_eq_zero (Sub i)).mp hqi
    dsimp only [Sub] at hmemSub
    rw [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range] at hmemSub
    rcases hmemSub with ⟨G, hG⟩
    refine ⟨G.1, G.2, ?_⟩
    change localConstraintAt m (centers i) (received i) (Q.1 - f * G.1) = 0
    rw [map_sub, sub_eq_zero]
    exact hG.symm
  refine ⟨Q.1, Q.2, hndvd, hlocal, ?_⟩
  intro S H hS hSf hH hcard
  -- For every `i ∈ H`, `(X - centers i)^m ∣ differentialSpecialization Q S`.
  have hdvd_i : ∀ i ∈ H,
      (Polynomial.X - Polynomial.C (centers i)) ^ m ∣ differentialSpecialization Q.1 S := by
    intro i hi
    rcases hlocal i with ⟨G, _, hGcon⟩
    have hd := X_sub_C_pow_dvd_differentialSpecialization_of_contact (Q.1 - f * G) S
      (centers i) (received i) (hH i hi) hGcon
    rw [← differentialSpecializationHom_apply, map_sub, map_mul,
      differentialSpecializationHom_apply, differentialSpecializationHom_apply,
      differentialSpecializationHom_apply, hSf, zero_mul, sub_zero] at hd
    exact hd
  have hprod_dvd : (∏ i ∈ H, (Polynomial.X - Polynomial.C (centers i)) ^ m) ∣
      differentialSpecialization Q.1 S := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr fun h => hij (hcenters h)).isUnit).pow_left.pow_right
    · exact hdvd_i
  -- Degree bound: `(differentialSpecialization Q.1 S).natDegree < D_cut` (when `Q ≠ 0`).
  by_contra hspec_ne
  have hQne : Q.1 ≠ 0 := by
    intro h0
    rw [h0, ← differentialSpecializationHom_apply, map_zero] at hspec_ne
    exact hspec_ne rfl
  have hdeg_lt : (differentialSpecialization Q.1 S).natDegree < D_cut :=
    natDegree_differentialSpecialization_lt hw Q.2 hQne hS
  have hprod_deg : (∏ i ∈ H, (Polynomial.X - Polynomial.C (centers i)) ^ m).natDegree =
      m * H.card := by
    rw [Polynomial.natDegree_prod _ _
      (fun i _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (centers i)))]
    simp [Polynomial.natDegree_pow, mul_comm]
  have hle := Polynomial.natDegree_le_of_dvd hprod_dvd hspec_ne
  omega

/-! ### Part 6: Clean Bridge from `BiPoly F` (`f = A(X, Y₀) * Y₁ + B(X, Y₀)`) for `@drdos-engine` -/

/-- Embed a bivariate polynomial `A ∈ F[X][Y₀]` into `DifferentialPolynomial F 1`. -/
def biPolyToDiff {R : Type*} [CommRing R] :
    Polynomial (Polynomial R) →+* DifferentialPolynomial R 1 :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
    (MvPolynomial.X (some 0))

/-- Embed a first-order linear-in-`Y₁` polynomial `f = A(X, Y₀) * Y₁ + B(X, Y₀)` into
`DifferentialPolynomial R 1`. -/
def contactLinearDiff {R : Type*} [CommRing R] (A B : Polynomial (Polynomial R)) :
    DifferentialPolynomial R 1 :=
  biPolyToDiff A * MvPolynomial.X (some 1) + biPolyToDiff B

theorem degreeOf_contactLinearDiff_le_one {R : Type*} [CommRing R]
    (A B : Polynomial (Polynomial R)) :
    (contactLinearDiff A B).degreeOf (some 1) ≤ 1 := by
  rcases subsingleton_or_nontrivial R with hsub | hnontriv
  · simp [Subsingleton.elim (contactLinearDiff A B) 0]
  · have hbi : ∀ P : Polynomial (Polynomial R), (biPolyToDiff P).degreeOf (some 1) = 0 := by
      intro P
      apply Nat.eq_zero_of_le_zero
      rw [MvPolynomial.degreeOf_le_iff]
      intro u hu
      induction P using Polynomial.induction_on' generalizing u with
      | add P₁ P₂ h₁ h₂ =>
        rw [map_add] at hu
        rcases Finset.mem_union.mp (MvPolynomial.support_add hu) with h | h
        · exact h₁ u h
        · exact h₂ u h
      | monomial j p =>
        rw [biPolyToDiff, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial] at hu
        induction p using Polynomial.induction_on' generalizing u with
        | add p₁ p₂ hp₁ hp₂ =>
          rw [map_add, add_mul] at hu
          rcases Finset.mem_union.mp (MvPolynomial.support_add hu) with h | h
          · exact hp₁ u h
          · exact hp₂ u h
        | monomial i a =>
          rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
            MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
            MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial, mul_one] at hu
          have heq : u = Finsupp.single none i + Finsupp.single (some 0) j :=
            Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hu)
          subst heq; simp
    unfold contactLinearDiff
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ (by rw [hbi B]; omega))
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    rw [hbi A, zero_add, MvPolynomial.degreeOf_X_self]

end

#print axioms exists_outside_multiples
#print axioms exists_in_ker_outside_range
#print axioms finrank_primeFirstOrderSpace
#print axioms mul_mem_primeFirstOrderSpace_iff
#print axioms det_pascal_submatrix
#print axioms finrank_range_localConstraintAt_primeFirstOrderSpace
#print axioms localConstraintAt_mul_eq_zero_iff
#print axioms finrank_range_localConstraintAt_mul_eq
#print axioms finrank_range_localConstraintAt_mul_primeFirstOrderSpace
#print axioms natDegree_differentialSpecialization_lt
#print axioms exists_quotient_contact_interpolant
#print axioms degreeOf_contactLinearDiff_le_one

end ArkLib.ProximityGap.Frontier.PrimeHDQuotientContact
