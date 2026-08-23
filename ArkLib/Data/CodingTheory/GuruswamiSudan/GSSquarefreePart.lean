/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorDegreeOverRatFunc
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorizationOverRatFunc
import ArkLib.ToMathlib.DiscriminantSeparableConverse
import Mathlib.RingTheory.Radical.Basic

/-!
# Hab25 §3 Step S5, global form — squarefree-part extraction of the GS interpolant

The paper statement of S5 (`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`) is a
*global* discriminant non-vanishing: replace the GS interpolant `Q` by its squarefree part
`Q̃` and show `disc_Y(Q̃) ≠ 0`. The in-tree S5 development
(`GSDiscriminantOverRatFunc` / `GSSeparabilityCharZero` / `GSSeparableCoreDescent`) went
through the *per-factor* form instead. This file supplies the squarefree-WLOG itself — the
standard honest route — as reusable bricks:

* **Squarefree-part extraction preserving the decoded-factor and degree data.**
  `radical Q` (mathlib's `UniqueFactorizationMonoid.radical`, the product of the distinct
  normalized prime factors) is a squarefree divisor of `Q` with
  - the *same decoded linear factors*: `(Y - C p) ∣ radical Q ↔ (Y - C p) ∣ Q`
    (`radical_linearFactor_dvd_iff`, via `dvd_radical_iff_of_irreducible`),
  - the *same factor index set*: `primeFactors (radical Q) = primeFactors Q`,
  - *inherited degree data*: `deg_Y (radical Q) ≤ deg_Y Q` and
    `degreeX (radical Q) ≤ degreeX Q` (divisor bounds).
  Note the multiplicity-`m` interpolation conditions are **not** preserved by passing to the
  radical (dividing out repeated factors lowers vanishing orders); they are not needed
  downstream — the `Conditions` are consumed once, by `gs_divisibility`, *before* the
  squarefree reduction, and only the divisibility/factor structure survives it. The capstone
  below keeps `Conditions` for `Q` itself and attaches the radical data alongside.

* **Global separability of the squarefree part over a perfect fraction field.**
  `separable_map_radical`: over a domain `A` with perfect fraction field, the image of
  `radical Q` in `(FractionRing A)[X]` is separable — each distinct prime factor maps to an
  irreducible (Gauss) hence separable (perfect field) polynomial or to a unit constant, and
  distinct normalized primes have non-associate, hence coprime, images
  (`IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` blocks any common factor); the product
  of pairwise-coprime separables is separable.

* **Global discriminant non-vanishing** (`discr_radical_ne_zero`): consequently
  `disc(radical Q) ≠ 0` whenever `radical Q` has positive degree — which the existence of a
  single decoded linear factor already forces
  (`natDegree_radical_pos_of_linearFactor_dvd`).

* **GS capstones** over `K = F(Z)`:
  `gs_interpolant_squarefree_part` (any characteristic — extraction + transfer + degree
  data + S4 index preservation) and `gs_interpolant_squarefree_discr_charZero`
  (characteristic zero — additionally `disc(radical Q) ≠ 0` as soon as the decoded list is
  nonempty). **Honest caveat:** in characteristic `p` the global `disc ≠ 0` is genuinely
  *false* in the presence of inseparable factors (`R(X, Y^{p^f})`, which are squarefree but
  not separable); there the in-tree separable-core descent
  (`gs_interpolant_good_specialization_expChar`) is the correct per-factor substitute, and
  no global claim is made here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate UniqueFactorizationMonoid

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-! ## Generic squarefree-part bricks over a domain with `NormalizedGCDMonoid` structure -/

section Generic

variable {A : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
  [UniqueFactorizationMonoid A]

/-- A unit is coprime to everything. -/
private lemma isCoprime_of_isUnit_left {R : Type*} [CommSemiring R] {u y : R}
    (hu : IsUnit u) : IsCoprime u y :=
  ⟨↑hu.unit⁻¹, 0, by rw [zero_mul, add_zero, hu.val_inv_mul]⟩

/-- **Per-factor separable image.** Over a domain `A` with perfect fraction field, every
distinct normalized prime factor of `Q : A[X]` maps to a separable polynomial of
`(FractionRing A)[X]`: positive-degree factors are primitive, so Gauss transports
irreducibility and perfectness gives separability; degree-zero factors map to unit
constants. -/
lemma separable_map_of_mem_primeFactors [PerfectField (FractionRing A)]
    {Q R : A[X]} (hQ0 : Q ≠ 0) (hR : R ∈ primeFactors Q) :
    (R.map (algebraMap A (FractionRing A))).Separable := by
  obtain ⟨hirr, hnorm, hdvd⟩ :=
    (mem_normalizedFactors_iff' hQ0).mp (mem_primeFactors.mp hR)
  by_cases hdeg : R.natDegree = 0
  · -- degree-zero prime factor: the image is a unit constant
    have hR0 : R ≠ 0 := hirr.ne_zero
    have hC : R = Polynomial.C (R.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc0 : R.coeff 0 ≠ 0 := fun h => hR0 (by rw [hC, h, map_zero])
    rw [hC, Polynomial.map_C, Polynomial.separable_C]
    exact isUnit_iff_ne_zero.mpr fun h =>
      hc0 ((IsFractionRing.injective A (FractionRing A)) (by rw [h, map_zero]))
  · -- positive degree: Gauss + perfect field
    have hprim : R.IsPrimitive := hirr.isPrimitive hdeg
    exact PerfectField.separable_of_irreducible
      (hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr)

/-- **Distinct prime factors have coprime fraction-field images.** Distinct normalized
primes are non-associate; Gauss's lemma blocks any divisibility between their (irreducible
or unit) images, so the images are coprime in the PID `(FractionRing A)[X]`. -/
lemma isCoprime_map_of_mem_primeFactors {Q R S : A[X]} (hQ0 : Q ≠ 0)
    (hR : R ∈ primeFactors Q) (hS : S ∈ primeFactors Q) (hne : R ≠ S) :
    IsCoprime (R.map (algebraMap A (FractionRing A)))
      (S.map (algebraMap A (FractionRing A))) := by
  obtain ⟨hirrR, hnormR, _⟩ :=
    (mem_normalizedFactors_iff' hQ0).mp (mem_primeFactors.mp hR)
  obtain ⟨hirrS, hnormS, _⟩ :=
    (mem_normalizedFactors_iff' hQ0).mp (mem_primeFactors.mp hS)
  by_cases hdegR : R.natDegree = 0
  · -- R maps to a unit constant
    have hR0 : R ≠ 0 := hirrR.ne_zero
    have hC : R = Polynomial.C (R.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegR
    have hc0 : R.coeff 0 ≠ 0 := fun h => hR0 (by rw [hC, h, map_zero])
    refine isCoprime_of_isUnit_left ?_
    rw [hC, Polynomial.map_C]
    exact (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr fun h =>
      hc0 ((IsFractionRing.injective A (FractionRing A)) (by rw [h, map_zero])))
  by_cases hdegS : S.natDegree = 0
  · -- S maps to a unit constant
    have hS0 : S ≠ 0 := hirrS.ne_zero
    have hC : S = Polynomial.C (S.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegS
    have hc0 : S.coeff 0 ≠ 0 := fun h => hS0 (by rw [hC, h, map_zero])
    refine (isCoprime_of_isUnit_left ?_).symm
    rw [hC, Polynomial.map_C]
    exact (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr fun h =>
      hc0 ((IsFractionRing.injective A (FractionRing A)) (by rw [h, map_zero])))
  -- both positive degree: irreducible images, non-associate by Gauss descent
  have hprimR : R.IsPrimitive := hirrR.isPrimitive hdegR
  have hprimS : S.IsPrimitive := hirrS.isPrimitive hdegS
  have hirrR' : Irreducible (R.map (algebraMap A (FractionRing A))) :=
    hprimR.irreducible_iff_irreducible_map_fraction_map.mp hirrR
  refine hirrR'.coprime_iff_not_dvd.mpr fun hdvd => ?_
  have hRS : R ∣ S := hprimR.dvd_of_fraction_map_dvd_fraction_map hprimS hdvd
  exact hne ((hirrR.associated_of_dvd hirrS hRS).eq_of_normalized hnormR hnormS)

/-- **Global separability of the squarefree part.** Over a domain `A` with perfect fraction
field, the image of `radical Q` in `(FractionRing A)[X]` is separable: it is the product of
the pairwise-coprime separable images of the distinct prime factors. -/
theorem separable_map_radical [PerfectField (FractionRing A)] (Q : A[X]) :
    ((radical Q).map (algebraMap A (FractionRing A))).Separable := by
  classical
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hmap : (radical Q).map (algebraMap A (FractionRing A)) =
      ∏ R ∈ primeFactors Q, R.map (algebraMap A (FractionRing A)) := by
    rw [radical, ← Polynomial.coe_mapRingHom, map_prod]
    rfl
  rw [hmap]
  exact Polynomial.separable_prod'
    (fun R hR S hS hne => isCoprime_map_of_mem_primeFactors hQ0 hR hS hne)
    (fun R hR => separable_map_of_mem_primeFactors hQ0 hR)

/-- **Global discriminant non-vanishing of the squarefree part** (the paper form of S5's
`disc_Y(Q̃) ≠ 0`): over a domain with perfect fraction field, `radical Q` of positive degree
has nonzero discriminant — squarefree ⟺ separable over the perfect fraction field, and the
converse-discriminant bridge pulls `disc ≠ 0` back to `A`. -/
theorem discr_radical_ne_zero [PerfectField (FractionRing A)] {Q : A[X]}
    (hdeg : 0 < (radical Q).natDegree) :
    (radical Q).discr ≠ 0 :=
  Polynomial.discr_ne_zero_of_separable_map
    (IsFractionRing.injective A (FractionRing A)) hdeg (separable_map_radical Q)

end Generic

/-! ## Squarefree-part bricks for bivariate interpolants `K[X][Y]` -/

section Bivariate

variable {K : Type} [Field K]

set_option maxHeartbeats 1600000 in
/-- **Decoded linear factors survive the squarefree reduction, in both directions:**
`(Y - C p) ∣ radical Q ↔ (Y - C p) ∣ Q`. -/
theorem radical_linearFactor_dvd_iff {Q : K[X][Y]} (hQ : Q ≠ 0) (p : K[X]) :
    (X - C p : K[X][Y]) ∣ radical Q ↔ (X - C p : K[X][Y]) ∣ Q := by
  have H := dvd_radical_iff_of_irreducible (irreducible_linearFactor (K := K) p) hQ
  exact H

set_option maxHeartbeats 1600000 in
/-- One decoded linear factor already forces the squarefree part to have positive
`Y`-degree — the hypothesis the global discriminant brick consumes. -/
theorem natDegree_radical_pos_of_linearFactor_dvd {Q : K[X][Y]} (hQ : Q ≠ 0)
    {p : K[X]} (hdvd : (X - C p : K[X][Y]) ∣ Q) :
    0 < (radical Q).natDegree := by
  have h1 : (X - C p : K[X][Y]) ∣ radical Q :=
    (radical_linearFactor_dvd_iff hQ p).mpr hdvd
  have hne : (radical Q : K[X][Y]) ≠ 0 := radical_ne_zero
  have h2 := Polynomial.natDegree_le_of_dvd h1 hne
  rw [natDegree_X_sub_C] at h2
  omega

end Bivariate

/-! ## GS capstones over `K = F(Z)` -/

variable {F : Type} [Field F]

/-- **Hab25 §3 squarefree-WLOG, any characteristic.**

There is a generic-fold GS interpolant `Q` (S2 `Conditions`) whose squarefree part
`radical Q` satisfies, with `D := gs_degree_bound k n m`:

1. `radical Q ∣ Q` and `Squarefree (radical Q)`;
2. the S3 degree data is inherited: `deg_Y (radical Q) ≤ D/(k−1)` and
   `degreeX (radical Q) ≤ D`;
3. decoded linear factors transfer in both directions:
   `(Y - C p) ∣ radical Q ↔ (Y - C p) ∣ Q` for every message `p ∈ K[X]` — in particular
   every GS-decoded codeword of the generic fold divides the squarefree part;
4. the S4 factor index set is unchanged: `primeFactors (radical Q) = primeFactors Q`.

The multiplicity-`m` interpolation conditions hold for `Q` (and are deliberately *not*
claimed for `radical Q`: they do not survive dividing out repeated factors, and nothing
downstream needs them to). -/
theorem gs_interpolant_squarefree_part {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      radical Q ∣ Q ∧
      Squarefree (radical Q) ∧
      (radical Q).natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      degreeX (radical Q) ≤ gs_degree_bound k n m ∧
      (∀ p : (RatFunc F)[X],
        (X - C p : (RatFunc F)[X][Y]) ∣ radical Q ↔ (X - C p : (RatFunc F)[X][Y]) ∣ Q) ∧
      primeFactors (radical Q) = primeFactors Q := by
  obtain ⟨Q, hQ, hydeg⟩ := genericInterpolant_yDegree_le k m ωs f₀ f₁ hk1 hn0 hm hk
  have hQ0 : Q ≠ 0 := hQ.Q_ne_0
  exact ⟨Q, hQ, radical_dvd_self, squarefree_radical,
    le_trans (Polynomial.natDegree_le_of_dvd radical_dvd_self hQ0) hydeg,
    le_trans (degreeX_le_of_dvd radical_dvd_self hQ0) (conditions_degreeX_le hQ),
    fun p => radical_linearFactor_dvd_iff hQ0 p,
    primeFactors_radical⟩

/-- **Hab25 §3 S5, global discriminant form, characteristic zero.**

The squarefree-WLOG of `gs_interpolant_squarefree_part`, plus: in characteristic zero the
paper's global S5 holds — `disc_Y(radical Q) ≠ 0` as soon as the decoded list is nonempty
(a single decoded linear factor forces positive `Y`-degree of the squarefree part, and
squarefree ⟺ separable over the perfect fraction field `K(X)`).

In characteristic `p` this global form is genuinely false in the presence of inseparable
factors; the in-tree per-factor separable-core descent
(`gs_interpolant_good_specialization_expChar`) is the honest substitute there. -/
theorem gs_interpolant_squarefree_discr_charZero [CharZero F]
    {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      Squarefree (radical Q) ∧
      (radical Q).natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      degreeX (radical Q) ≤ gs_degree_bound k n m ∧
      (∀ p : (RatFunc F)[X],
        (X - C p : (RatFunc F)[X][Y]) ∣ radical Q ↔ (X - C p : (RatFunc F)[X][Y]) ∣ Q) ∧
      (∀ p₀ : (RatFunc F)[X],
        (X - C p₀ : (RatFunc F)[X][Y]) ∣ Q → (radical Q).discr ≠ 0) := by
  haveI : CharZero (RatFunc F) :=
    charZero_of_injective_algebraMap (algebraMap F (RatFunc F)).injective
  haveI : CharZero ((RatFunc F)[X]) :=
    charZero_of_injective_algebraMap (C_injective : Function.Injective (C (R := RatFunc F)))
  haveI : CharZero (FractionRing ((RatFunc F)[X])) :=
    charZero_of_injective_algebraMap
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))
  obtain ⟨Q, hQ, _, hsf, hydeg, hxdeg, htransfer, _⟩ :=
    gs_interpolant_squarefree_part k m ωs f₀ f₁ hk1 hn0 hm hk
  have hQ0 : Q ≠ 0 := hQ.Q_ne_0
  exact ⟨Q, hQ, hsf, hydeg, hxdeg, htransfer,
    fun p₀ hdvd =>
      discr_radical_ne_zero (natDegree_radical_pos_of_linearFactor_dvd hQ0 hdvd)⟩

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.separable_map_radical
#print axioms GuruswamiSudan.OverRatFunc.discr_radical_ne_zero
#print axioms GuruswamiSudan.OverRatFunc.radical_linearFactor_dvd_iff
#print axioms GuruswamiSudan.OverRatFunc.natDegree_radical_pos_of_linearFactor_dvd
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_squarefree_part
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_squarefree_discr_charZero
