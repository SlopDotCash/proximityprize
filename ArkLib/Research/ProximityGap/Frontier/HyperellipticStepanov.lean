/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Polynomial.IrreducibleRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General-degree elementary Stepanov–Weil bound for hyperelliptic character sums

This file proves, completely unconditionally and with only standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), a square-root-scale quadratic character sum bound
for **every** monic squarefree polynomial `f : F[X]` of **any** positive degree `d` over
**every** finite field `F` of odd characteristic:

* `linear_charSum_eq_zero`: `∑ s : F, χ(s - a) = 0`.
* `quadratic_charSum_eq_neg_one`: `∑ s : F, χ((s - a) * (s - b)) = -1` for `a ≠ b`.
* `hyperelliptic_stepanov_sq_le`: `(∑ s : F, χ(f.eval s)) ^ 2 ≤ (4 * d) ^ 2 * |F|` for every
  monic squarefree `f : F[X]` of degree `d ≥ 2`, with **zero small-field gap**.
* `hyperelliptic_stepanov_abs_le`: `|∑ s : F, χ(f.eval s)| ≤ 4 * d * √|F|`.
* **Tight triangular constants** (from the graded condition space
  `(k : Fin m) × Fin (D + (d - 1) * k + J)`, improving the uniform-box cubic constant from
  `2√10 ≈ 6.32` down to `2√6 ≈ 4.90`):
  - `hyperelliptic_stepanov_deg3_tight`: `S ^ 2 ≤ 25 * q` for `d = 3`, `q ≥ 43357`.
  - `hyperelliptic_stepanov_deg4_tight`: `S ^ 2 ≤ 64 * q` for `d = 4`, `q ≥ 683`.
  - `hyperelliptic_stepanov_deg6_tight`: `S ^ 2 ≤ 144 * q` for `d = 6`, `q ≥ 1772`.
  - `hyperelliptic_stepanov_deg6_ultra`: `100 * S ^ 2 ≤ 12321 * q` (`|S| ≤ 11.1 √q`)
    for `d = 6`, `q ≥ 10 ^ 7 + 1`.

Both `N⁺ = {s : χ(f s) = 1}` and `N⁻ = {s : χ(f s) = -1}` are bounded directly using a single
unified sign-parametrized auxiliary polynomial `P = ∑_j (f^m a_j + f^{m+e} b_j) X^{qj}`, so the
proof applies uniformly to both even and odd degrees without requiring a rational root or twist.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.longFile 1700
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.HyperellipticStepanov

open Finset Polynomial

/-! ## 1. Base-`q` substitution and squarefree non-vanishing -/

section NonVanishing

variable {F : Type*}

/-- Substitution `Y ↦ X^q` on `A ∈ F[X][Y]`. -/
noncomputable def subq [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) : F[X] :=
  A.eval₂ (RingHom.id F[X]) (X ^ q)

noncomputable def subqHom [CommRing F] (q : ℕ) : Polynomial (Polynomial F) →+* F[X] :=
  Polynomial.eval₂RingHom (RingHom.id F[X]) (X ^ q)

private theorem subq_eq_sum [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) :
    subq q A = ∑ j ∈ Finset.range (A.natDegree + 1), (A.coeff j) * X ^ (q * j) := by
  unfold subq
  rw [eval₂_eq_sum_range]
  simp only [RingHom.id_apply, ← pow_mul]

private theorem coeff_subq_digit [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) (j0 i : ℕ) (hi : i < q) :
    (subq q A).coeff (q * j0 + i) = (A.coeff j0).coeff i := by
  rw [subq_eq_sum, finsetSum_coeff]
  have hvanish : ∀ j ∈ Finset.range (A.natDegree + 1), j ≠ j0 →
      ((A.coeff j) * X ^ (q * j)).coeff (q * j0 + i) = 0 := by
    intro j _hj hjne
    rw [coeff_mul_X_pow']
    split_ifs with hcond
    · rcases lt_or_gt_of_ne hjne with hlt | hgt
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have heq : q * j + q * (j0 - j) = q * j0 := by rw [← Nat.mul_add]; congr 1; omega
        have h2 : q ≤ q * (j0 - j) := by
          calc q = q * 1 := (Nat.mul_one q).symm
            _ ≤ q * (j0 - j) := Nat.mul_le_mul_left q (by omega)
        exact lt_of_lt_of_le (hdig j) (by omega)
      · exfalso
        have : q * (j0 + 1) ≤ q * j := Nat.mul_le_mul_left q (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega
    · rfl
  by_cases hj0 : j0 ≤ A.natDegree
  · rw [Finset.sum_eq_single j0]
    · rw [coeff_mul_X_pow']
      simp only [Nat.le_add_right, ↓reduceIte]
      congr 1; omega
    · exact hvanish
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · push Not at hj0
    rw [coeff_eq_zero_of_natDegree_lt hj0, Polynomial.coeff_zero]
    exact Finset.sum_eq_zero fun j hj => hvanish j hj (by simp only [Finset.mem_range] at hj; omega)

private theorem subq_eq_zero_iff [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) :
    subq q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext j i'
    by_cases hi' : i' < q
    · have := coeff_subq_digit q A hdig j i' hi'
      rw [h, Polynomial.coeff_zero] at this
      rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
      exact this.symm
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdig j) (by omega)),
        Polynomial.coeff_zero, Polynomial.coeff_zero]
  · intro h; rw [h]; unfold subq; simp

private theorem subq_mul [CommRing F] (q : ℕ) (A B : Polynomial (Polynomial F)) :
    subq q (A * B) = subq q A * subq q B :=
  map_mul (subqHom q) A B

private theorem subq_pow [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) (k : ℕ) :
    subq q (A ^ k) = (subq q A) ^ k :=
  map_pow (subqHom q) A k

private theorem subq_C [CommRing F] (q : ℕ) (G : F[X]) : subq q (Polynomial.C G) = G := by
  show subqHom q (Polynomial.C G) = G; simp [subqHom, Polynomial.eval₂RingHom]

private theorem subq_map_C [CommRing F] (q : ℕ) (g : F[X]) :
    subq q (g.map (Polynomial.C)) = Polynomial.expand F q g := by
  unfold subq
  rw [Polynomial.eval₂_map]
  rw [show (RingHom.id F[X]).comp Polynomial.C = Polynomial.C from rfl]
  rw [Polynomial.expand_eq_comp_X_pow]; rfl

private theorem pow_card_eq_subq_map_C [Field F] [Fintype F] (g : F[X]) :
    g ^ (Fintype.card F) = subq (Fintype.card F) (g.map (Polynomial.C)) := by
  rw [subq_map_C, FiniteField.Polynomial.expand_card]

private theorem squarefree_pos_not_isSquare_frac {L : Type*} [Field L] (p : L[X])
    (hsf : Squarefree p) (hdeg : 0 < p.natDegree) :
    ¬ IsSquare (algebraMap L[X] (FractionRing L[X]) p) := by
  classical
  rintro ⟨r, hr⟩
  have hr2 : r ^ 2 = algebraMap L[X] (FractionRing L[X]) p := by rw [sq]; exact hr.symm
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hrb⟩ := IsLocalization.surj (nonZeroDivisors L[X]) r
  set ν := algebraMap L[X] (FractionRing L[X])
  have hνinj : Function.Injective ν := IsFractionRing.injective L[X] (FractionRing L[X])
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have heq : a ^ 2 = p * b ^ 2 := by
    apply hνinj
    calc ν (a ^ 2) = (ν a) ^ 2 := map_pow ν a 2
      _ = (r * ν b) ^ 2 := by rw [← hrb]
      _ = r ^ 2 * (ν b) ^ 2 := mul_pow r (ν b) 2
      _ = ν p * (ν b) ^ 2 := by rw [hr2]
      _ = ν (p * b ^ 2) := by rw [map_mul, map_pow]
  set g := EuclideanDomain.gcd a b
  have hga : g ∣ a := EuclideanDomain.gcd_dvd_left a b
  have hgb : g ∣ b := EuclideanDomain.gcd_dvd_right a b
  have hg0 : g ≠ 0 := fun h => hb0 (zero_dvd_iff.mp (h ▸ hgb))
  obtain ⟨a', ha'⟩ := hga
  obtain ⟨b', hb'⟩ := hgb
  have hb'0 : b' ≠ 0 := fun h => hb0 (by rw [hb', h, mul_zero])
  have heq' : a' ^ 2 = p * b' ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc g ^ 2 * a' ^ 2 = (g * a') ^ 2 := by ring
      _ = a ^ 2 := by rw [← ha']
      _ = p * b ^ 2 := heq
      _ = p * (g * b') ^ 2 := by rw [← hb']
      _ = g ^ 2 * (p * b' ^ 2) := by ring
  have hb'_unit : IsUnit b' := by
    by_contra hnu
    obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hb'0
    have hqa2 : q ∣ a' ^ 2 := by
      rw [heq']
      exact dvd_mul_of_dvd_right (dvd_pow hq_dvd two_ne_zero) p
    have hqa : q ∣ a' := by
      set d' := EuclideanDomain.gcd q a'
      have hdq : d' ∣ q := EuclideanDomain.gcd_dvd_left q a'
      have hda : d' ∣ a' := EuclideanDomain.gcd_dvd_right q a'
      obtain ⟨w, hw⟩ := hdq
      rcases hq_irr.isUnit_or_isUnit hw with hd_unit | hw_unit
      · obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hd_unit
        have hbez : q * (EuclideanDomain.gcdA q a' * v * a') +
            a' ^ 2 * (EuclideanDomain.gcdB q a' * v) = a' := by
          have hg := EuclideanDomain.gcd_eq_gcd_ab q a'
          calc q * (EuclideanDomain.gcdA q a' * v * a') +
                a' ^ 2 * (EuclideanDomain.gcdB q a' * v)
              = (q * EuclideanDomain.gcdA q a' + a' * EuclideanDomain.gcdB q a') * v * a' := by ring
            _ = d' * v * a' := by rw [← hg]
            _ = 1 * a' := by rw [hv]
            _ = a' := one_mul a'
        rw [← hbez]
        exact dvd_add (dvd_mul_right q _) (dvd_mul_of_dvd_left hqa2 _)
      · obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hw_unit
        have hqd : q ∣ d' := ⟨v, by
          calc d' = d' * (w * v) := by rw [hv, mul_one]
            _ = q * v := by rw [← mul_assoc, ← hw]⟩
        exact hqd.trans hda
    have hqg_a : g * q ∣ a := by rw [ha']; exact mul_dvd_mul_left g hqa
    have hqg_b : g * q ∣ b := by rw [hb']; exact mul_dvd_mul_left g hq_dvd
    have hqg_g : g * q ∣ g := EuclideanDomain.dvd_gcd hqg_a hqg_b
    obtain ⟨c, hc⟩ := hqg_g
    have h1 : 1 = q * c := by
      apply mul_left_cancel₀ hg0
      calc g * 1 = g := mul_one g
        _ = g * q * c := hc
        _ = g * (q * c) := mul_assoc _ _ _
    exact hq_irr.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, h1.symm⟩)
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hb'_unit
  have hp : p = (a' * u) ^ 2 := by
    calc p = p * (b' * u) ^ 2 := by rw [hu, one_pow, mul_one]
      _ = (p * b' ^ 2) * u ^ 2 := by ring
      _ = a' ^ 2 * u ^ 2 := by rw [← heq']
      _ = (a' * u) ^ 2 := by ring
  have hu2 : IsUnit ((a' * u) * (a' * u)) :=
    (hsf (a' * u) (by rw [hp, sq])).mul (hsf (a' * u) (by rw [hp, sq]))
  rw [← sq, ← hp] at hu2
  have := natDegree_eq_zero_of_isUnit hu2
  omega

private theorem const_times_sq_eq_squarefree_times_sq {K : Type*} [Field K]
    (γ : K) (hγ : γ ≠ 0) (gL : K[X]) (hsf : Squarefree gL) (hdeg : 0 < gL.natDegree)
    (s t : K[X]) (hrel : C γ * s ^ 2 = gL * t ^ 2) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    rw [zero_pow two_ne_zero, mul_zero] at hrel
    have hCγ0 : (C γ : K[X]) ≠ 0 := by rwa [ne_eq, C_eq_zero]
    rcases mul_eq_zero.mp hrel with h | h
    · exact absurd h hCγ0
    · exact ⟨(pow_eq_zero_iff two_ne_zero).mp h, rfl⟩
  · exfalso
    set A := FractionRing K[X]
    set ν := algebraMap K[X] A
    have hνinj : Function.Injective ν := IsFractionRing.injective K[X] A
    have ht0 : ν t ≠ 0 := by
      simp only [ne_eq, map_eq_zero_iff ν hνinj]; exact ht
    have hassoc : Associated (C γ⁻¹ * gL) gL :=
      ⟨(isUnit_C.mpr (Ne.isUnit hγ)).unit, by
        rw [IsUnit.unit_spec]
        rw [mul_comm (C γ⁻¹) gL, mul_assoc, ← C_mul, inv_mul_cancel₀ hγ, C_1, mul_one]⟩
    have hsf2 : Squarefree (C γ⁻¹ * gL) := hassoc.squarefree_iff.mpr hsf
    have hdeg2 : 0 < (C γ⁻¹ * gL).natDegree := by
      rw [natDegree_C_mul (inv_ne_zero hγ)]; exact hdeg
    apply squarefree_pos_not_isSquare_frac (C γ⁻¹ * gL) hsf2 hdeg2
    refine ⟨ν s / ν t, ?_⟩
    have hmap : ν (C γ) * ν s ^ 2 = ν gL * ν t ^ 2 := by
      have := congrArg ν hrel
      rwa [map_mul, map_mul, map_pow, map_pow] at this
    have hCC : ν (C γ⁻¹) * ν (C γ) = 1 := by
      rw [← map_mul, ← C_mul, inv_mul_cancel₀ hγ, C_1, map_one]
    rw [map_mul, div_mul_div_comm, ← sq, ← sq, eq_div_iff (pow_ne_zero 2 ht0)]
    linear_combination (-ν (C γ⁻¹)) * hmap + ν s ^ 2 * hCC

private theorem genus_squarefree_forces_trivial [Field F] [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (A0 A1 : Polynomial (Polynomial F))
    (hrel : Polynomial.C g * A0 ^ 2 = (g.map Polynomial.C) * A1 ^ 2) :
    A0 = 0 ∧ A1 = 0 := by
  set ι : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  have hιinj : Function.Injective ι := IsFractionRing.injective F[X] (RatFunc F)
  set φ : Polynomial (Polynomial F) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom ι
  have hφinj : Function.Injective φ := Polynomial.map_injective ι hιinj
  have himg : φ (C g * A0 ^ 2) = φ ((g.map C) * A1 ^ 2) := by rw [hrel]
  rw [map_mul, map_mul, map_pow, map_pow] at himg
  have h1 : φ (C g) = C (ι g) := by rw [coe_mapRingHom, Polynomial.map_C]
  have h2 : φ (g.map (C : F →+* F[X])) = g.map (algebraMap F (RatFunc F)) := by
    rw [coe_mapRingHom, Polynomial.map_map]; congr 1
  rw [h1, h2] at himg
  have hγ : ι g ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff ι hιinj]; rintro rfl; simp at hdeg
  have hgLsf : Squarefree (g.map (algebraMap F (RatFunc F))) :=
    (PerfectField.separable_iff_squarefree.mpr hg).map.squarefree
  have hgLdeg : 0 < (g.map (algebraMap F (RatFunc F))).natDegree := by
    rw [natDegree_map_eq_of_injective (algebraMap F (RatFunc F)).injective]; exact hdeg
  obtain ⟨ha0, ha1⟩ := const_times_sq_eq_squarefree_times_sq (ι g) hγ
    (g.map (algebraMap F (RatFunc F))) hgLsf hgLdeg (φ A0) (φ A1) himg
  exact ⟨hφinj (by rw [ha0, map_zero]), hφinj (by rw [ha1, map_zero])⟩

/-- General Stepanov non-vanishing for any squarefree polynomial `g` of positive degree `d`:
if every `X`-block of `A0, A1` has degree `≤ D` with `2 * D + d < q`, then
`A0(X, X^q) + g^((q-1)/2) * A1(X, X^q) = 0` forces `A0 = A1 = 0`. -/
theorem stepanov_independence [Field F] [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    {D : ℕ} (hD : 2 * D + g.natDegree < Fintype.card F)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree ≤ D) (h1 : ∀ j, (A1.coeff j).natDegree ≤ D)
    (hR : subq (Fintype.card F) A0
      + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1 = 0) :
    A0 = 0 ∧ A1 = 0 := by
  set q := Fintype.card F
  have hmul : ∀ A B : Polynomial (Polynomial F), ∀ DA DB : ℕ,
      (∀ j, (A.coeff j).natDegree ≤ DA) → (∀ j, (B.coeff j).natDegree ≤ DB) →
      ∀ j, ((A * B).coeff j).natDegree ≤ DA + DB := fun A B DA DB hA hB j => by
    rw [coeff_mul]
    exact natDegree_sum_le_of_forall_le _ _ fun _ _ =>
      natDegree_mul_le.trans (add_le_add (hA _) (hB _))
  have hblk : ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < q := by
    intro j
    have hA0sq : ∀ i, ((A0 ^ 2).coeff i).natDegree ≤ D + D := by rw [sq]; exact hmul _ _ D D h0 h0
    have hA1sq : ∀ i, ((A1 ^ 2).coeff i).natDegree ≤ D + D := by rw [sq]; exact hmul _ _ D D h1 h1
    have ht1 : ((C g * A0 ^ 2).coeff j).natDegree ≤ g.natDegree + (D + D) := by
      rw [coeff_C_mul]
      exact natDegree_mul_le.trans (add_le_add le_rfl (hA0sq j))
    have hmap : ∀ i, ((g.map (C : F →+* F[X])).coeff i).natDegree ≤ 0 := fun i => by
      rw [coeff_map]; exact le_of_eq (natDegree_C _)
    have ht2 : (((g.map C) * A1 ^ 2).coeff j).natDegree ≤ 0 + (D + D) :=
      hmul _ _ 0 (D + D) hmap hA1sq j
    calc ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree
        = ((C g * A0 ^ 2).coeff j - ((g.map C) * A1 ^ 2).coeff j).natDegree := by rw [coeff_sub]
      _ ≤ max ((C g * A0 ^ 2).coeff j).natDegree (((g.map C) * A1 ^ 2).coeff j).natDegree :=
          natDegree_sub_le _ _
      _ < q := max_lt (by omega) (by omega)
  have hq1 : 1 ≤ q := Fintype.card_pos
  have heven : Even (q - 1) := Nat.Odd.sub_odd hq_odd odd_one
  have htwo : 2 * ((q - 1) / 2) = q - 1 := Nat.two_mul_div_two_of_even heven
  have hg2 : (g ^ ((q - 1) / 2)) ^ 2 = g ^ (q - 1) := by
    rw [← pow_mul, mul_comm ((q - 1) / 2) 2, htwo]
  have hsq : (subq q A0) ^ 2 = g ^ (q - 1) * (subq q A1) ^ 2 := by
    have h0' : subq q A0 = - (g ^ ((q - 1) / 2)) * subq q A1 := by linear_combination hR
    rw [h0', neg_mul, neg_sq, mul_pow, hg2]
  have hgmul : g * (subq q A0) ^ 2 = g ^ q * (subq q A1) ^ 2 := by
    rw [hsq, ← mul_assoc, ← pow_succ', show q - 1 + 1 = q from by omega]
  have hfold : subq q (C g * A0 ^ 2) = subq q ((g.map C) * A1 ^ 2) := by
    rw [subq_mul, subq_mul, subq_C, subq_pow, subq_pow, hgmul, pow_card_eq_subq_map_C]
  have hdiff : subq q (C g * A0 ^ 2 - (g.map C) * A1 ^ 2) = 0 := by
    have : subqHom q (C g * A0 ^ 2 - (g.map C) * A1 ^ 2) = 0 := by
      rw [map_sub]; show subq q _ - subq q _ = 0; rw [hfold]; ring
    exact this
  have hrel0 : C g * A0 ^ 2 - (g.map C) * A1 ^ 2 = 0 :=
    (subq_eq_zero_iff q _ hblk).mp hdiff
  exact genus_squarefree_forces_trivial g hg hdeg A0 A1 (by linear_combination hrel0)

end NonVanishing

/-! ## 2. Hasse-derivative toolkit and Stepanov degree counting -/

section HasseToolkit

private theorem le_rootMultiplicity_of_hasseDeriv_eq_zero {K : Type*} [Field K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {a : K} {m : ℕ}
    (h : ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) :
    m ≤ P.rootMultiplicity a := by
  rw [le_rootMultiplicity_iff hP, X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro d hd
  have hcoeff : (Polynomial.taylor a P).coeff d = 0 := by
    rw [Polynomial.taylor_coeff]; exact h d hd
  rwa [Polynomial.taylor_apply] at hcoeff

private theorem hasseDeriv_stepanov_degree_count {K : Type*} [Field K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {S : Finset K} {m : ℕ}
    (h : ∀ a ∈ S, ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) :
    m * S.card ≤ P.natDegree := by
  classical
  calc m * S.card = ∑ _a ∈ S, m := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ S, P.roots.count a := by
        refine sum_le_sum fun a ha => ?_
        rw [count_roots]; exact le_rootMultiplicity_of_hasseDeriv_eq_zero hP (h a ha)
    _ = ∑ a ∈ S ∩ P.roots.toFinset, P.roots.count a := by
        refine (sum_subset inter_subset_left fun a haS hna => ?_).symm
        exact Multiset.count_eq_zero.mpr fun hmem =>
          hna (mem_inter.mpr ⟨haS, Multiset.mem_toFinset.mpr hmem⟩)
    _ ≤ ∑ a ∈ P.roots.toFinset, P.roots.count a :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => Nat.zero_le _
    _ = Multiset.card P.roots := P.roots.toFinset_sum_count_eq
    _ ≤ P.natDegree := P.card_roots'

private theorem cast_choose_prime_pow_mul_eq_zero {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    [CharP F p] (μ j k : ℕ) (hk0 : 0 < k) (hkq : k < p ^ μ) :
    (((p ^ μ * j).choose k : ℕ) : F) = 0 := by
  have := Fact.mk hp
  have : CharP F[X] p := inferInstance
  have : ExpChar F[X] p := ExpChar.prime hp
  have key : ((1 : F[X]) + X) ^ (p ^ μ * j) = (1 + X ^ p ^ μ) ^ j := by
    rw [pow_mul, add_pow_char_pow, one_pow]
  have hL : (((1 : F[X]) + X) ^ (p ^ μ * j)).coeff k = (((p ^ μ * j).choose k : ℕ) : F) :=
    coeff_one_add_X_pow F (p ^ μ * j) k
  have hR : (((1 : F[X]) + X ^ p ^ μ) ^ j).coeff k = 0 := by
    rw [add_pow, finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [one_pow, one_mul, ← C_eq_natCast, mul_comm, ← pow_mul, coeff_C_mul, coeff_X_pow]
    have hne : k ≠ p ^ μ * (j - i) := by
      rcases Nat.eq_zero_or_pos (j - i) with hi | hi
      · rw [hi, Nat.mul_zero]; omega
      · have : p ^ μ ≤ p ^ μ * (j - i) := Nat.le_mul_of_pos_right _ hi
        omega
    simp only [hne, ↓reduceIte, mul_zero]
  rw [← hL, key, hR]

private theorem hasseDeriv_X_card_mul_eq_zero {F : Type*} [Field F] [Fintype F] (j k : ℕ)
    (hk0 : 0 < k) (hkq : k < Fintype.card F) :
    hasseDeriv k ((X : F[X]) ^ (Fintype.card F * j)) = 0 := by
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' F
  have := hcp
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  have hz : ((Fintype.card F * j).choose k : F) = 0 := by
    rw [hcard]
    exact cast_choose_prime_pow_mul_eq_zero hp (n : ℕ) j k hk0 (hcard ▸ hkq)
  rw [hz, zero_mul, monomial_zero_right]

private theorem hasseDeriv_mul_X_card_pow {F : Type*} [Field F] [Fintype F] (u : F[X]) (j k : ℕ)
    (hkq : k < Fintype.card F) :
    hasseDeriv k (u * X ^ (Fintype.card F * j))
      = hasseDeriv k u * X ^ (Fintype.card F * j) := by
  rw [hasseDeriv_mul, Finset.sum_eq_single (k, 0)]
  · rw [hasseDeriv_zero']
  · rintro ⟨i, l⟩ hmem hne
    rw [HasAntidiagonal.mem_antidiagonal] at hmem
    have hl0 : 0 < l := by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact absurd (by simp [h, ← hmem]) hne
      · exact h
    rw [hasseDeriv_X_card_mul_eq_zero j l hl0 (by omega), mul_zero]
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by omega)) h

private theorem pow_sub_dvd_hasseDeriv_pow {F : Type*} [Field F] (f : F[X]) :
    ∀ N k : ℕ, k ≤ N → f ^ (N - k) ∣ hasseDeriv k (f ^ N) := by
  intro N
  induction N with
  | zero => intro k hk; interval_cases k; simp
  | succ N ih =>
    intro k hk
    rw [pow_succ, mul_comm (f ^ N) f, hasseDeriv_mul]
    refine Finset.dvd_sum ?_
    rintro ⟨i, l⟩ hmem
    rw [HasAntidiagonal.mem_antidiagonal] at hmem
    rcases Nat.eq_zero_or_pos i with hi | hi
    · have hl : l = k := by omega
      subst hi
      rw [hasseDeriv_zero', hl]
      rcases Nat.lt_or_ge k (N + 1) with hkN | hkN
      · have hdvd := ih k (by omega)
        rw [show N + 1 - k = (N - k) + 1 by omega, pow_succ, mul_comm (f ^ (N - k)) f]
        exact mul_dvd_mul_left f hdvd
      · rw [show N + 1 - k = 0 by omega, pow_zero]
        exact one_dvd _
    · have hdvd := ih l (by omega)
      exact dvd_trans (pow_dvd_pow f (by omega)) (Dvd.dvd.mul_left hdvd _)

private theorem pow_sub_dvd_hasseDeriv_pow_mul {F : Type*} [Field F] (f a : F[X]) (N k : ℕ)
    (hk : k ≤ N) : f ^ (N - k) ∣ hasseDeriv k (f ^ N * a) := by
  rw [hasseDeriv_mul]
  refine Finset.dvd_sum ?_
  rintro ⟨i, l⟩ hmem
  rw [HasAntidiagonal.mem_antidiagonal] at hmem
  exact dvd_trans (pow_dvd_pow f (by omega))
    (Dvd.dvd.mul_right (pow_sub_dvd_hasseDeriv_pow f N i (by omega)) _)

private theorem divByMonic_exact {F : Type*} [Field F] {g p : F[X]} (hg : g.Monic) (hdvd : g ∣ p) :
    g * (p /ₘ g) = p := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [mul_divByMonic_cancel_left c hg]

private theorem add_divByMonic_of_dvd {F : Type*} [Field F] {g p q : F[X]}
    (hg : g.Monic) (hp : g ∣ p) (hq : g ∣ q) :
    (p + q) /ₘ g = p /ₘ g + q /ₘ g := by
  have heq : p + q = g * (p /ₘ g + q /ₘ g) := by
    rw [mul_add, divByMonic_exact hg hp, divByMonic_exact hg hq]
  rw [heq, mul_divByMonic_cancel_left _ hg]

private theorem smul_divByMonic_of_dvd {F : Type*} [Field F] {g p : F[X]}
    (hg : g.Monic) (c : F) (hp : g ∣ p) :
    (c • p) /ₘ g = c • (p /ₘ g) := by
  have heq : c • p = g * (c • (p /ₘ g)) := by
    rw [mul_smul_comm, divByMonic_exact hg hp]
  rw [heq, mul_divByMonic_cancel_left _ hg]

end HasseToolkit

/-! ## 3. General-degree triangular S2 auxiliary polynomial (both fibers `σ = ±1`) -/

section GeneralS2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def polyOf (D : ℕ) (c : Fin (D + 1) → F) : F[X] :=
  ∑ i : Fin (D + 1), C (c i) * X ^ (i : ℕ)

private theorem polyOf_natDegree_le (D : ℕ) (c : Fin (D + 1) → F) :
    (polyOf D c).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_C, natDegree_X_pow]
  omega

private theorem polyOf_coeff (D : ℕ) (c : Fin (D + 1) → F) (i : Fin (D + 1)) :
    (polyOf D c).coeff (i : ℕ) = c i := by
  rw [polyOf, finsetSum_coeff, Finset.sum_eq_single i]
  · simp [coeff_C_mul, coeff_X_pow]
  · intro b _ hb
    have hne : (i : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
    simp [coeff_C_mul, coeff_X_pow, hne]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem polyOf_add (D : ℕ) (c d : Fin (D + 1) → F) :
    polyOf D (c + d) = polyOf D c + polyOf D d := by
  rw [polyOf, polyOf, polyOf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, C_add, add_mul]

private theorem polyOf_smul (D : ℕ) (r : F) (c : Fin (D + 1) → F) :
    polyOf D (r • c) = r • polyOf D c := by
  rw [polyOf, polyOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul, C_mul, smul_eq_C_mul, mul_assoc]

@[reducible] private def Unknowns (F : Type*) (J D : ℕ) : Type _ :=
  ((Fin J × Fin (D + 1)) → F) × ((Fin J × Fin (D + 1)) → F)

private noncomputable def redWitness (f : F[X]) (σ : F) (m e J D k : ℕ)
    (x : Unknowns F J D) : F[X] :=
  ∑ j : Fin J,
    (hasseDeriv k (f ^ m * polyOf D (fun i => x.1 (j, i))) /ₘ f ^ (m - k)
      + C σ * (hasseDeriv k (f ^ (m + e) * polyOf D (fun i => x.2 (j, i)))
          /ₘ f ^ (m + e - k))) * X ^ (j : ℕ)

private noncomputable def auxP (f : F[X]) (q m e J D : ℕ) (x : Unknowns F J D) : F[X] :=
  ∑ j : Fin J,
    (f ^ m * polyOf D (fun i => x.1 (j, i))
      + f ^ (m + e) * polyOf D (fun i => x.2 (j, i))) * X ^ (q * (j : ℕ))

private theorem redWitness_add {f : F[X]} (hf : f.Monic) (σ : F) (m e J D k : ℕ)
    (hkm : k ≤ m) (x y : Unknowns F J D) :
    redWitness f σ m e J D k (x + y) =
      redWitness f σ m e J D k x + redWitness f σ m e J D k y := by
  rw [redWitness, redWitness, redWitness, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hP1 : polyOf D (fun i => (x + y).1 (j, i))
      = polyOf D (fun i => x.1 (j, i)) + polyOf D (fun i => y.1 (j, i)) := by
    rw [← polyOf_add]; rfl
  have hP2 : polyOf D (fun i => (x + y).2 (j, i))
      = polyOf D (fun i => x.2 (j, i)) + polyOf D (fun i => y.2 (j, i)) := by
    rw [← polyOf_add]; rfl
  rw [hP1, hP2, mul_add, mul_add, map_add, map_add,
    add_divByMonic_of_dvd (hf.pow _)
      (pow_sub_dvd_hasseDeriv_pow_mul f _ m k hkm)
      (pow_sub_dvd_hasseDeriv_pow_mul f _ m k hkm),
    add_divByMonic_of_dvd (hf.pow _)
      (pow_sub_dvd_hasseDeriv_pow_mul f _ (m + e) k (by omega))
      (pow_sub_dvd_hasseDeriv_pow_mul f _ (m + e) k (by omega))]
  ring

private theorem redWitness_smul {f : F[X]} (hf : f.Monic) (σ : F) (m e J D k : ℕ)
    (hkm : k ≤ m) (r : F) (x : Unknowns F J D) :
    redWitness f σ m e J D k (r • x) = r • redWitness f σ m e J D k x := by
  rw [redWitness, redWitness, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hP1 : polyOf D (fun i => (r • x).1 (j, i)) = r • polyOf D (fun i => x.1 (j, i)) := by
    rw [← polyOf_smul]; rfl
  have hP2 : polyOf D (fun i => (r • x).2 (j, i)) = r • polyOf D (fun i => x.2 (j, i)) := by
    rw [← polyOf_smul]; rfl
  rw [hP1, hP2, mul_smul_comm, mul_smul_comm, map_smul, map_smul,
    smul_divByMonic_of_dvd (hf.pow _) r (pow_sub_dvd_hasseDeriv_pow_mul f _ m k hkm),
    smul_divByMonic_of_dvd (hf.pow _) r (pow_sub_dvd_hasseDeriv_pow_mul f _ (m + e) k (by omega)),
    mul_smul_comm, ← smul_add, smul_mul_assoc]

/-- Triangular (graded) condition map: extracts only the first `D + (d - 1) * k + J` coefficients
of the `k`-th reduced witness `W_k`, matching its exact degree bound. -/
private noncomputable def condMapTri {f : F[X]} (hf : f.Monic) (σ : F) (d m e J D : ℕ) :
    Unknowns F J D →ₗ[F] ((k : Fin m) × Fin (D + (d - 1) * (k : ℕ) + J) → F) where
  toFun x := fun ki => (redWitness f σ m e J D (ki.1 : ℕ) x).coeff (ki.2 : ℕ)
  map_add' x y := by
    funext ki
    rw [redWitness_add hf σ m e J D (ki.1 : ℕ) (le_of_lt ki.1.isLt)]
    simp [coeff_add]
  map_smul' r x := by
    funext ki
    rw [redWitness_smul hf σ m e J D (ki.1 : ℕ) (le_of_lt ki.1.isLt)]
    simp

private theorem card_tri_target (d m J D : ℕ) :
    2 * Fintype.card ((k : Fin m) × Fin (D + (d - 1) * (k : ℕ) + J)) =
      2 * m * (D + J) + (d - 1) * (m * (m - 1)) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hsum : ∑ k : Fin m, (D + (d - 1) * (k : ℕ) + J) =
      m * (D + J) + (d - 1) * ∑ k ∈ Finset.range m, k := by
    rw [Fin.sum_univ_eq_sum_range (fun k => D + (d - 1) * k + J)]
    calc ∑ k ∈ Finset.range m, (D + (d - 1) * k + J)
        = ∑ k ∈ Finset.range m, ((D + J) + (d - 1) * k) :=
            Finset.sum_congr rfl fun k _ => by omega
      _ = ∑ _k ∈ Finset.range m, (D + J) + ∑ k ∈ Finset.range m, (d - 1) * k :=
            Finset.sum_add_distrib
      _ = m * (D + J) + (d - 1) * ∑ k ∈ Finset.range m, k := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
  have h2sum : 2 * ∑ k ∈ Finset.range m, k = m * (m - 1) := by
    rw [mul_comm, Finset.sum_range_id_mul_two]
  rw [hsum]
  calc 2 * (m * (D + J) + (d - 1) * ∑ k ∈ Finset.range m, k)
      = 2 * m * (D + J) + (d - 1) * (2 * ∑ k ∈ Finset.range m, k) := by ring
    _ = 2 * m * (D + J) + (d - 1) * (m * (m - 1)) := by rw [h2sum]

private theorem exists_kernel_vector_tri {f : F[X]} (hf : f.Monic) (σ : F) (d m e J D : ℕ)
    (hcount : 2 * m * (D + J) + (d - 1) * (m * (m - 1)) < 4 * (J * (D + 1))) :
    ∃ x : Unknowns F J D, x ≠ 0 ∧ condMapTri hf σ d m e J D x = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (condMapTri hf σ d m e J D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    exact hcon x hne hx
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin] at hle
  have hcard := card_tri_target d m J D
  omega

private theorem quotient_natDegree_le {f : F[X]} (hf : f.Monic) {d : ℕ}
    (hdeg : f.natDegree = d) (hd : 1 ≤ d) (a : F[X]) {Da : ℕ} (ha : a.natDegree ≤ Da)
    (N k : ℕ) (hk : k ≤ N) :
    (hasseDeriv k (f ^ N * a) /ₘ f ^ (N - k)).natDegree ≤ Da + (d - 1) * k := by
  rw [natDegree_divByMonic _ (hf.pow _)]
  have h1 : (hasseDeriv k (f ^ N * a)).natDegree ≤ (f ^ N * a).natDegree - k :=
    natDegree_hasseDeriv_le _ _
  have h2 : (f ^ N * a).natDegree ≤ d * N + Da := by
    refine natDegree_mul_le.trans ?_
    rw [hf.natDegree_pow, hdeg, Nat.mul_comm]
    omega
  have h3 : (f ^ (N - k)).natDegree = d * (N - k) := by
    rw [hf.natDegree_pow, hdeg, Nat.mul_comm]
  have hmul : d * (N - k) + d * k = d * N := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  have hdk : (d - 1) * k + k = d * k := by
    cases d with
    | zero => omega
    | succ d' => simp [Nat.add_mul]
  omega

private theorem redWitness_natDegree_le {f : F[X]} (hf : f.Monic) {d : ℕ}
    (hdeg : f.natDegree = d) (hd : 1 ≤ d) (σ : F) (m e J D k : ℕ) (x : Unknowns F J D)
    (hk : k ≤ m) (hJ : 0 < J) :
    (redWitness f σ m e J D k x).natDegree ≤ D + (d - 1) * k + (J - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have hq1 := quotient_natDegree_le hf hdeg hd (polyOf D (fun i => x.1 (j, i)))
    (polyOf_natDegree_le _ _) m k hk
  have hq2 := quotient_natDegree_le hf hdeg hd (polyOf D (fun i => x.2 (j, i)))
    (polyOf_natDegree_le _ _) (m + e) k (by omega)
  have hq2' : (C σ * (hasseDeriv k (f ^ (m + e) * polyOf D (fun i => x.2 (j, i)))
      /ₘ f ^ (m + e - k))).natDegree ≤ D + (d - 1) * k :=
    natDegree_mul_le.trans (by rw [natDegree_C]; omega)
  have hadd := natDegree_add_le
    (hasseDeriv k (f ^ m * polyOf D (fun i => x.1 (j, i))) /ₘ f ^ (m - k))
    (C σ * (hasseDeriv k (f ^ (m + e) * polyOf D (fun i => x.2 (j, i))) /ₘ f ^ (m + e - k)))
  have hjlt : (j : ℕ) ≤ J - 1 := by omega
  omega

private theorem redWitness_eq_zero_of_kernel {f : F[X]} (hf : f.Monic) {d : ℕ}
    (hdeg : f.natDegree = d) (hd : 1 ≤ d) (σ : F) (m e J D k : ℕ) (x : Unknowns F J D)
    (hk : k < m) (hJ : 0 < J) (hx : condMapTri hf σ d m e J D x = 0) :
    redWitness f σ m e J D k x = 0 := by
  ext n
  rw [coeff_zero]
  rcases Nat.lt_or_ge n (D + (d - 1) * k + J) with hn | hn
  · exact congrFun hx ⟨⟨k, hk⟩, ⟨n, hn⟩⟩
  · refine coeff_eq_zero_of_natDegree_lt ?_
    have := redWitness_natDegree_le hf hdeg hd σ m e J D k x (le_of_lt hk) hJ
    omega

private theorem eval_hasseDeriv_auxP {f : F[X]} (hf : f.Monic) (σ : F)
    (m e J D k : ℕ) (x : Unknowns F J D) (hkm : k ≤ m) (hkq : k < Fintype.card F)
    (s : F) (hse : (f.eval s) ^ e = σ) :
    (hasseDeriv k (auxP f (Fintype.card F) m e J D x)).eval s
      = (f.eval s) ^ (m - k) * (redWitness f σ m e J D k x).eval s := by
  rw [auxP, map_sum, eval_finsetSum, redWitness, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set Pa := polyOf D (fun i => x.1 (j, i))
  set Pb := polyOf D (fun i => x.2 (j, i))
  have hd1 : f ^ (m - k) * (hasseDeriv k (f ^ m * Pa) /ₘ f ^ (m - k))
      = hasseDeriv k (f ^ m * Pa) :=
    divByMonic_exact (hf.pow _) (pow_sub_dvd_hasseDeriv_pow_mul f Pa m k hkm)
  have hd2 : f ^ (m + e - k) * (hasseDeriv k (f ^ (m + e) * Pb) /ₘ f ^ (m + e - k))
      = hasseDeriv k (f ^ (m + e) * Pb) :=
    divByMonic_exact (hf.pow _) (pow_sub_dvd_hasseDeriv_pow_mul f Pb (m + e) k (by omega))
  rw [hasseDeriv_mul_X_card_pow _ (j : ℕ) k hkq, map_add]
  conv_lhs => rw [← hd1, ← hd2]
  have hsq : s ^ (Fintype.card F * (j : ℕ)) = s ^ (j : ℕ) := by
    rw [mul_comm, pow_mul, FiniteField.pow_card]
  have hpow : (f.eval s) ^ (m + e - k) = (f.eval s) ^ (m - k) * (f.eval s) ^ e := by
    rw [← pow_add]; congr 1; omega
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
  rw [hsq, hpow, hse]
  ring

private noncomputable def liftY {J : ℕ} (g : Fin J → F[X]) : Polynomial (Polynomial F) :=
  ∑ j : Fin J, Polynomial.C (g j) * Polynomial.X ^ (j : ℕ)

private theorem liftY_coeff {J : ℕ} (g : Fin J → F[X]) (n : ℕ) :
    (liftY g).coeff n = if h : n < J then g ⟨n, h⟩ else 0 := by
  rw [liftY, finsetSum_coeff]
  by_cases h : n < J
  · simp only [h, ↓reduceDIte]
    rw [Finset.sum_eq_single (⟨n, h⟩ : Fin J)]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro b _ hb
      have hne : n ≠ (b : ℕ) := fun hh => hb (Fin.ext hh.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · simp only [h, ↓reduceDIte]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : n ≠ (b : ℕ) := fun hh => h (by rw [hh]; exact b.isLt)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]

private theorem subq_liftY {J : ℕ} (q : ℕ) (g : Fin J → F[X]) :
    subq q (liftY g) = ∑ j : Fin J, g j * X ^ (q * (j : ℕ)) := by
  rw [subq, liftY, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, RingHom.id_apply, ← pow_mul]

private theorem auxP_eq_mul (f : F[X]) (q m e J D : ℕ) (x : Unknowns F J D) :
    auxP f q m e J D x = f ^ m *
      (subq q (liftY (fun j => polyOf D (fun i => x.1 (j, i))))
        + f ^ e * subq q (liftY (fun j => polyOf D (fun i => x.2 (j, i))))) := by
  rw [subq_liftY, subq_liftY, auxP, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring

private theorem auxP_ne_zero (hq_odd : Odd (Fintype.card F))
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) (hdeg : 0 < f.natDegree)
    {m e J D : ℕ} (hD : 2 * D + f.natDegree < Fintype.card F)
    (he : e = (Fintype.card F - 1) / 2)
    (x : Unknowns F J D) (hx : x ≠ 0) :
    auxP f (Fintype.card F) m e J D x ≠ 0 := by
  set A0 := liftY (fun j => polyOf D (fun i => x.1 (j, i)))
  set A1 := liftY (fun j => polyOf D (fun i => x.2 (j, i)))
  have hblk0 : ∀ jn, (A0.coeff jn).natDegree ≤ D := fun jn => by
    rw [liftY_coeff]; split_ifs
    · exact polyOf_natDegree_le _ _
    · simp
  have hblk1 : ∀ jn, (A1.coeff jn).natDegree ≤ D := fun jn => by
    rw [liftY_coeff]; split_ifs
    · exact polyOf_natDegree_le _ _
    · simp
  have hne : ¬(A0 = 0 ∧ A1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hx
    have hz : ∀ (w : (Fin J × Fin (D + 1)) → F),
        liftY (fun j => polyOf D (fun i => w (j, i))) = 0 → w = 0 := by
      intro w hw
      funext ⟨j, i⟩
      have hc := congrArg (fun p => (p.coeff (j : ℕ)).coeff (i : ℕ)) hw
      simp only [liftY_coeff, Polynomial.coeff_zero, j.isLt, ↓reduceDIte, Fin.eta,
        polyOf_coeff] at hc
      exact hc
    exact Prod.ext (hz x.1 h0) (hz x.2 h1)
  have hinner : subq (Fintype.card F) A0
      + f ^ ((Fintype.card F - 1) / 2) * subq (Fintype.card F) A1 ≠ 0 :=
    fun h => hne (stepanov_independence f hsf hdeg hq_odd hD A0 A1 hblk0 hblk1 h)
  rw [auxP_eq_mul, he]
  exact mul_ne_zero (pow_ne_zero _ hf.ne_zero) hinner

private theorem auxP_natDegree_le {f : F[X]} (hf : f.Monic) {d : ℕ} (hdeg : f.natDegree = d)
    (q m e J D : ℕ) (x : Unknowns F J D) (hJ : 0 < J) :
    (auxP f q m e J D x).natDegree ≤ d * (m + e) + D + q * (J - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have h1 : (f ^ m * polyOf D (fun i => x.1 (j, i))).natDegree ≤ d * m + D := by
    refine natDegree_mul_le.trans ?_
    have := polyOf_natDegree_le D (fun i => x.1 (j, i))
    rw [hf.natDegree_pow, hdeg, Nat.mul_comm]
    omega
  have h2 : (f ^ (m + e) * polyOf D (fun i => x.2 (j, i))).natDegree ≤ d * (m + e) + D := by
    refine natDegree_mul_le.trans ?_
    have := polyOf_natDegree_le D (fun i => x.2 (j, i))
    rw [hf.natDegree_pow, hdeg, Nat.mul_comm]
    omega
  have hadd := natDegree_add_le (f ^ m * polyOf D (fun i => x.1 (j, i)))
    (f ^ (m + e) * polyOf D (fun i => x.2 (j, i)))
  have hjq : q * (j : ℕ) ≤ q * (J - 1) := Nat.mul_le_mul_left q (by omega)
  have hdm : d * m ≤ d * (m + e) := Nat.mul_le_mul_left d (by omega)
  omega

/-- **General-degree triangular Stepanov fiber bound** (covers both `σ = 1` and `σ = -1`!):
for any monic squarefree `f : F[X]` of degree `d ≥ 1` and any admissible `(m, J, D)`,
`m * #{s : (f.eval s)^((q-1)/2) = σ} ≤ d * (m + (q-1)/2) + D + q * (J - 1)`. -/
theorem fiber_bound_of_params
    (hq_odd : Odd (Fintype.card F))
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) {d : ℕ} (hdeg : f.natDegree = d) (hd : 1 ≤ d)
    (σ : F) {m J D : ℕ} (hJ : 0 < J) (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + d < Fintype.card F)
    (hcount : 2 * m * (D + J) + (d - 1) * (m * (m - 1)) < 4 * (J * (D + 1))) :
    m * (Finset.univ.filter fun s : F =>
        (f.eval s) ^ ((Fintype.card F - 1) / 2) = σ).card
      ≤ d * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) := by
  set e := (Fintype.card F - 1) / 2 with he
  obtain ⟨x, hx0, hxker⟩ := exists_kernel_vector_tri hf σ d m e J D hcount
  have hP0 := auxP_ne_zero (m := m) hq_odd hf hsf (by omega) (by omega) he x hx0
  have hPdeg := auxP_natDegree_le hf hdeg (Fintype.card F) m e J D x hJ
  refine le_trans (hasseDeriv_stepanov_degree_count hP0 ?_) hPdeg
  intro s hs k hk
  rw [Finset.mem_filter] at hs
  have hcard3 : 3 ≤ Fintype.card F := by
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rcases hq_odd with ⟨t, ht⟩
    omega
  have hkq : k < Fintype.card F := by omega
  rw [eval_hasseDeriv_auxP hf σ m e J D k x (le_of_lt hk) hkq s hs.2,
    redWitness_eq_zero_of_kernel hf hdeg hd σ m e J D k x hk hJ hxker, eval_zero, mul_zero]

/-! ## 4. Euler bridge for both signs and character-sum bound -/

private theorem card_zero_le_natDegree (f : F[X]) (hf : f ≠ 0) :
    (Finset.univ.filter fun s : F => quadraticChar F (f.eval s) = 0).card ≤ f.natDegree := by
  classical
  have hsub : (Finset.univ.filter fun s : F => quadraticChar F (f.eval s) = 0) ⊆
      f.roots.toFinset := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [Multiset.mem_toFinset, mem_roots hf, IsRoot]
    exact quadraticChar_eq_zero_iff.mp hs.2
  calc _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := f.card_roots'

private theorem pow_eq_one_of_quadChar_eq_one (hF : ringChar F ≠ 2) {x : F}
    (hx : quadraticChar F x = 1) :
    x ^ ((Fintype.card F - 1) / 2) = 1 := by
  have hodd : Odd (Fintype.card F) := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
  have hexp : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rcases hodd with ⟨t, ht⟩; omega
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have heul := quadraticChar_eq_pow_of_char_ne_two hF hx0
  rw [hx] at heul
  by_cases hpow : x ^ (Fintype.card F / 2) = 1
  · rwa [hexp] at hpow
  · simp only [hpow, ↓reduceIte] at heul; norm_num at heul

private theorem pow_eq_neg_one_of_quadChar_eq_neg_one (hF : ringChar F ≠ 2) {x : F}
    (hx : quadraticChar F x = -1) :
    x ^ ((Fintype.card F - 1) / 2) = -1 := by
  have hodd : Odd (Fintype.card F) := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
  have hexp : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rcases hodd with ⟨t, ht⟩; omega
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have heul := quadraticChar_eq_pow_of_char_ne_two hF hx0
  rw [hx] at heul
  have hne1 : x ^ (Fintype.card F / 2) ≠ 1 := by
    intro h1; simp only [h1, ↓reduceIte] at heul; norm_num at heul
  have hsq : (x ^ ((Fintype.card F - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show ((Fintype.card F - 1) / 2) * 2 = Fintype.card F - 1 by
      rcases hodd with ⟨t, ht⟩; omega]
    exact FiniteField.pow_card_sub_one_eq_one x hx0
  have hfac : (x ^ ((Fintype.card F - 1) / 2) - 1) * (x ^ ((Fintype.card F - 1) / 2) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso; apply hne1; rw [hexp]; exact sub_eq_zero.mp h
  · exact eq_neg_of_add_eq_zero_left h

private theorem charSum_eq_two_pos_add_zero_sub_card (g : F → F) :
    ∑ s : F, quadraticChar F (g s)
      = 2 * (((univ.filter fun s : F => quadraticChar F (g s) = 1).card : ℕ) : ℤ)
        + (((univ.filter fun s : F => quadraticChar F (g s) = 0).card : ℕ) : ℤ)
        - Fintype.card F := by
  classical
  have hpt : ∀ s : F,
      quadraticChar F (g s)
        = 2 * (if quadraticChar F (g s) = 1 then (1 : ℤ) else 0)
          + (if quadraticChar F (g s) = 0 then (1 : ℤ) else 0) - 1 := by
    intro s
    rcases (quadraticChar_isQuadratic F) (g s) with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun s _ => hpt s, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.sum_filter]
  simp

private theorem neg_charSum_eq_two_neg_add_zero_sub_card (g : F → F) :
    -(∑ s : F, quadraticChar F (g s))
      = 2 * (((univ.filter fun s : F => quadraticChar F (g s) = -1).card : ℕ) : ℤ)
        + (((univ.filter fun s : F => quadraticChar F (g s) = 0).card : ℕ) : ℤ)
        - Fintype.card F := by
  classical
  have hpt : ∀ s : F,
      -(quadraticChar F (g s))
        = 2 * (if quadraticChar F (g s) = -1 then (1 : ℤ) else 0)
          + (if quadraticChar F (g s) = 0 then (1 : ℤ) else 0) - 1 := by
    intro s
    rcases (quadraticChar_isQuadratic F) (g s) with h | h | h <;> simp [h]
  rw [← Finset.sum_neg_distrib, Finset.sum_congr rfl fun s _ => hpt s,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_filter, ← Finset.sum_filter]
  simp

/-- **Two-sided character-sum bound from admissible Stepanov parameters**:
for any monic squarefree `f : F[X]` of degree `d ≥ 1`, any admissible `(m, J, D)` gives
`m * |∑ s : F, χ(f s)| ≤ 2 * Dtot + d * m - m * q`, where `Dtot = d*(m+e) + D + q*(J-1)`. -/
theorem charSum_abs_bound_of_params
    (hF : ringChar F ≠ 2)
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) {d : ℕ} (hdeg : f.natDegree = d) (hd : 1 ≤ d)
    {m J D : ℕ} (hJ : 0 < J) (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + d < Fintype.card F)
    (hcount : 2 * m * (D + J) + (d - 1) * (m * (m - 1)) < 4 * (J * (D + 1))) :
    (m : ℤ) * |∑ s : F, quadraticChar F (f.eval s)|
      ≤ 2 * ((d * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) : ℕ) : ℤ)
        + (d : ℤ) * m - (m : ℤ) * Fintype.card F := by
  have hodd : Odd (Fintype.card F) := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
  set Dtot := d * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1)
  have hZ : (univ.filter fun s : F => quadraticChar F (f.eval s) = 0).card ≤ d := by
    rw [← hdeg]; exact card_zero_le_natDegree f hf.ne_zero
  have hZ' : ((univ.filter fun s : F => quadraticChar F (f.eval s) = 0).card : ℤ) ≤ d := by
    exact_mod_cast hZ
  have hpos_card : (univ.filter fun s : F => quadraticChar F (f.eval s) = 1).card ≤
      (univ.filter fun s : F => (f.eval s) ^ ((Fintype.card F - 1) / 2) = 1).card :=
    Finset.card_le_card fun s hs => by
      rw [Finset.mem_filter] at hs ⊢
      exact ⟨Finset.mem_univ _, pow_eq_one_of_quadChar_eq_one hF hs.2⟩
  have hneg_card : (univ.filter fun s : F => quadraticChar F (f.eval s) = -1).card ≤
      (univ.filter fun s : F => (f.eval s) ^ ((Fintype.card F - 1) / 2) = -1).card :=
    Finset.card_le_card fun s hs => by
      rw [Finset.mem_filter] at hs ⊢
      exact ⟨Finset.mem_univ _, pow_eq_neg_one_of_quadChar_eq_neg_one hF hs.2⟩
  have hmP : (m : ℤ) * ((univ.filter fun s : F => quadraticChar F (f.eval s) = 1).card : ℤ) ≤
      (Dtot : ℤ) := by
    have h1 := fiber_bound_of_params hodd hf hsf hdeg hd (1 : F) hJ hme hD hcount
    have h2 : m * (univ.filter fun s : F => quadraticChar F (f.eval s) = 1).card ≤ Dtot :=
      (Nat.mul_le_mul_left m hpos_card).trans h1
    exact_mod_cast h2
  have hmN : (m : ℤ) * ((univ.filter fun s : F => quadraticChar F (f.eval s) = -1).card : ℤ) ≤
      (Dtot : ℤ) := by
    have h1 := fiber_bound_of_params hodd hf hsf hdeg hd (-1 : F) hJ hme hD hcount
    have h2 : m * (univ.filter fun s : F => quadraticChar F (f.eval s) = -1).card ≤ Dtot :=
      (Nat.mul_le_mul_left m hneg_card).trans h1
    exact_mod_cast h2
  have hSpos := charSum_eq_two_pos_add_zero_sub_card (fun s => f.eval s)
  have hSneg := neg_charSum_eq_two_neg_add_zero_sub_card (fun s => f.eval s)
  have hup : (m : ℤ) * (∑ s : F, quadraticChar F (f.eval s)) ≤
      2 * (Dtot : ℤ) + (d : ℤ) * m - (m : ℤ) * Fintype.card F := by
    rw [hSpos]; nlinarith [Nat.cast_nonneg (α := ℤ) m]
  have hlo : (m : ℤ) * (-(∑ s : F, quadraticChar F (f.eval s))) ≤
      2 * (Dtot : ℤ) + (d : ℤ) * m - (m : ℤ) * Fintype.card F := by
    rw [hSneg]; nlinarith [Nat.cast_nonneg (α := ℤ) m]
  rcases abs_cases (∑ s : F, quadraticChar F (f.eval s)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · exact hup
  · exact hlo

end GeneralS2

/-! ## 5. Exact degree-1 and degree-2 formulas -/

section SmallDegree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Degree 1: `∑ s : F, χ(s - a) = 0`. -/
theorem linear_charSum_eq_zero (hF : ringChar F ≠ 2) (a : F) :
    ∑ s : F, quadraticChar F (s - a) = 0 := by
  have hbi : Function.Bijective (fun s : F => s - a) := (Equiv.subRight a).bijective
  rw [Fintype.sum_bijective (fun s : F => s - a) hbi _ _ (fun _ => rfl)]
  exact quadraticChar_sum_zero hF

/-- Degree 2: `∑ s : F, χ((s - a) * (s - b)) = -1` for `a ≠ b`. -/
theorem quadratic_charSum_eq_neg_one (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ s : F, quadraticChar F ((s - a) * (s - b)) = -1 := by
  classical
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hbi1 : Function.Bijective (fun u : F => a + (b - a) * u) :=
    (Equiv.addLeft a).bijective.comp (mulLeft_bijective₀ (b - a) hba)
  have hstep1 : ∑ s : F, quadraticChar F ((s - a) * (s - b)) =
      ∑ u : F, quadraticChar F (u * (u - 1)) := by
    rw [← Fintype.sum_bijective (fun u : F => a + (b - a) * u) hbi1 _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have harg : (a + (b - a) * u - a) * (a + (b - a) * u - b) = (b - a) ^ 2 * (u * (u - 1)) := by
      ring
    rw [harg, map_mul, quadraticChar_sq_one' hba, one_mul]
  rw [hstep1]
  have hstep2 : ∑ u : F, quadraticChar F (u * (u - 1)) =
      ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 - u⁻¹) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), zero_mul, MulChar.map_zero, zero_add]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have harg : u * (u - 1) = u ^ 2 * (1 - u⁻¹) := by field_simp [hu0]
    rw [harg, map_mul, quadraticChar_sq_one' hu0, one_mul]
  rw [hstep2]
  have hbij : ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 - u⁻¹) =
      ∑ v ∈ Finset.univ.erase (1 : F), quadraticChar F v := by
    refine Finset.sum_nbij' (fun u => 1 - u⁻¹) (fun v => (1 - v)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      rw [Finset.mem_erase]
      exact ⟨fun h => inv_ne_zero hu0 (sub_eq_self.mp h), Finset.mem_univ _⟩
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      rw [Finset.mem_erase]
      exact ⟨inv_ne_zero (sub_ne_zero.mpr hv1.symm), Finset.mem_univ _⟩
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      field_simp [hu0]; ring
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      have h1v : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
      field_simp [h1v]; ring
    · intro _ _; rfl
  rw [hbij]
  have htot := quadraticChar_sum_zero hF
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : F)), map_one] at htot
  omega

end SmallDegree

/-! ## 6. Explicit integer parameter family and unconditional bounds -/

section ExplicitParams

/-- Base parameter `t = d / 2`, coefficient degree `D = (q - d - 2) / 2`,
and `s = ⌊√(t * D / d)⌋`. -/
private def tP (d : ℕ) : ℕ := d / 2
private def dDegP (d q : ℕ) : ℕ := (q - d - 2) / 2
private def sP (d q : ℕ) : ℕ := Nat.sqrt (tP d * dDegP d q / d)

private theorem param_core_le {d q : ℕ} (hd : 2 ≤ d) (hq_odd : Odd q) (hq : d + 4 ≤ q)
    (hs_pos : 1 ≤ sP d q) (hm_le : 2 * sP d q ≤ (q - 1) / 2) :
    let t := tP d
    let D := dDegP d q
    let s := sP d q
    let m := 2 * s
    let J := s + t
    0 < J ∧ m ≤ (q - 1) / 2 ∧ 2 * D + d < q ∧
      2 * m * (D + J) + (d - 1) * (m * (m - 1)) < 4 * (J * (D + 1)) ∧
      2 * ((d * (m + (q - 1) / 2) + D + q * (J - 1) : ℕ) : ℤ) + (d : ℤ) * m - (m : ℤ) * q
        ≤ ((d + 2 * t - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s := by
  intro t D s m J
  have ht_pos : 1 ≤ t := by dsimp [t, tP]; omega
  have ht2 : 2 * t ≤ d := by dsimp [t, tP]; omega
  have hD_upper : 2 * D + d ≤ q - 2 := by dsimp [D, dDegP]; omega
  have hss : d * (s * s) ≤ t * D := by
    have h1 : s * s ≤ t * D / d := Nat.sqrt_le _
    calc d * (s * s) ≤ d * (t * D / d) := Nat.mul_le_mul_left d h1
      _ ≤ t * D := Nat.mul_div_le _ _
  have hcnt : 2 * m * (D + J) + (d - 1) * (m * (m - 1)) < 4 * (J * (D + 1)) := by
    have hd1 : 1 ≤ d := by omega
    have h1 : 2 * m * (D + J) + (d - 1) * (m * (m - 1)) + 2 * (d - 1) * s
        = 4 * s * D + 4 * d * (s * s) + 4 * t * s := by
      dsimp [m, J]
      zify [hd1, show 1 ≤ 2 * s by omega]
      ring
    have h2 : 4 * (J * (D + 1)) = 4 * s * D + 4 * t * D + 4 * s + 4 * t := by
      dsimp [J]; ring
    have htd : 4 * t * s ≤ 2 * d * s := by nlinarith
    have hds : 4 * d * (s * s) ≤ 4 * t * D := by linarith
    have hlin : 4 * t * s ≤ 2 * (d - 1) * s + 4 * s := by
      have hdeq : 2 * d * s = 2 * (d - 1) * s + 2 * s := by zify [hd1]; ring
      omega
    linarith
  have hdtot :
      2 * ((d * (m + (q - 1) / 2) + D + q * (J - 1) : ℕ) : ℤ) + (d : ℤ) * m - (m : ℤ) * q
        ≤ ((d + 2 * t - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s := by
    have h2e : 2 * (((q - 1 : ℕ) : ℤ) / 2) = (q : ℤ) - 1 := by
      rcases hq_odd with ⟨u, hu⟩; omega
    have hJ1 : ((J - 1 : ℕ) : ℤ) = (s : ℤ) + (t : ℤ) - 1 := by
      dsimp [J]; omega
    have hdt : ((d + 2 * t - 1 : ℕ) : ℤ) = (d : ℤ) + 2 * (t : ℤ) - 1 := by omega
    have h2D : 2 * (D : ℤ) ≤ (q : ℤ) - (d : ℤ) - 2 := by omega
    push_cast
    rw [hJ1, hdt]
    dsimp only [m]
    push_cast
    nlinarith [h2e, h2D]
  exact ⟨by omega, hm_le, by omega, hcnt, hdtot⟩

private theorem sP_succ_sq_ge {d q : ℕ} (hd : 2 ≤ d) (hq : d + 4 ≤ q) :
    2 * tP d * (q - d - 3) < 4 * d * ((sP d q + 1) * (sP d q + 1)) + 4 * tP d := by
  have h1 : tP d * dDegP d q / d < (sP d q + 1) * (sP d q + 1) := Nat.lt_succ_sqrt _
  have hdiv : tP d * dDegP d q = d * (tP d * dDegP d q / d) + tP d * dDegP d q % d :=
    (Nat.div_add_mod _ _).symm
  have hmod : tP d * dDegP d q % d < d := Nat.mod_lt _ (by omega)
  have hmul : tP d * dDegP d q < d * ((sP d q + 1) * (sP d q + 1)) := by
    have : d * (tP d * dDegP d q / d) + d ≤ d * ((sP d q + 1) * (sP d q + 1)) := by
      have : tP d * dDegP d q / d + 1 ≤ (sP d q + 1) * (sP d q + 1) := h1
      calc d * (tP d * dDegP d q / d) + d = d * (tP d * dDegP d q / d + 1) := by ring
        _ ≤ d * ((sP d q + 1) * (sP d q + 1)) := Nat.mul_le_mul_left d this
    omega
  have h2D : q - d - 3 ≤ 2 * dDegP d q + 1 := by unfold dDegP; omega
  have h4 : 2 * tP d * (q - d - 3) ≤ 4 * (tP d * dDegP d q) + 2 * tP d := by
    calc 2 * tP d * (q - d - 3) ≤ 2 * tP d * (2 * dDegP d q + 1) := Nat.mul_le_mul_left _ h2D
      _ = 4 * (tP d * dDegP d q) + 2 * tP d := by ring
  nlinarith

/-- **Universal zero-gap hyperelliptic Stepanov–Weil bound**:
for every finite field `F` of odd characteristic and every monic squarefree `f : F[X]`
of degree `d ≥ 2`, `(∑ s : F, χ(f s)) ^ 2 ≤ (4 * d) ^ 2 * |F|`. Zero small-field gap! -/
theorem hyperelliptic_stepanov_sq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {f : F[X]} (hf : f.Monic) (hsf : Squarefree f)
    {d : ℕ} (hdeg : f.natDegree = d) (hd : 2 ≤ d) :
    (∑ s : F, quadraticChar F (f.eval s)) ^ 2 ≤ ((4 * d : ℕ) : ℤ) ^ 2 * Fintype.card F := by
  set q := Fintype.card F with hqdef
  set S : ℤ := ∑ s : F, quadraticChar F (f.eval s)
  rcases le_or_gt q ((4 * d) ^ 2) with hsmall | hbig
  · -- Small-field trivial bound: `|S| ≤ q ≤ (4*d)^2 ⇒ S^2 ≤ q^2 ≤ (4*d)^2 * q`.
    have htriv : |S| ≤ (q : ℤ) := by
      calc |S| ≤ ∑ _s : F, (1 : ℤ) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
            rcases (quadraticChar_isQuadratic F) (f.eval s) with h | h | h <;> rw [h] <;> decide
        _ = (q : ℤ) := by simp [q]
    have hsm : (q : ℤ) ≤ ((4 * d : ℕ) : ℤ) ^ 2 := by exact_mod_cast hsmall
    have hsq : S ^ 2 ≤ (q : ℤ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) htriv 2
    nlinarith [Nat.cast_nonneg (α := ℤ) q]
  · -- Large-field Stepanov bound (`q > 16 * d^2`).
    have hodd : Odd q := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
    have hq16 : 16 * d * d < q := by nlinarith
    have hq_ge : d + 4 ≤ q := by nlinarith
    set t := tP d
    set D := dDegP d q
    set s := sP d q
    have ht_lo : 2 * d ≤ 3 * (2 * t) := by dsimp [t, tP]; omega
    have ht_hi : 2 * t ≤ d := by dsimp [t, tP]; omega
    have hss : d * (s * s) ≤ t * D := by
      have h1 : s * s ≤ t * D / d := Nat.sqrt_le _
      exact (Nat.mul_le_mul_left d h1).trans (Nat.mul_div_le _ _)
    have h2D_hi : 2 * D ≤ q := by dsimp [D, dDegP]; omega
    have h4s2 : 4 * (s * s) ≤ q := by
      have : 4 * d * (s * s) ≤ 4 * t * D := by linarith
      have : 4 * t * D ≤ 2 * d * D := by nlinarith
      have : 4 * d * (s * s) ≤ d * q := by nlinarith
      nlinarith
    -- Universal lower bound `q - d - 3 ≤ 6 * (s + 1)^2 + 3`
    have hlow_raw := sP_succ_sq_ge hd hq_ge
    have hlow_d : 2 * d * (q - d - 3) ≤ 12 * d * ((s + 1) * (s + 1)) + 6 * d := by
      have h1 : 2 * d * (q - d - 3) ≤ 3 * (2 * t * (q - d - 3)) := by
        calc 2 * d * (q - d - 3) ≤ 3 * (2 * t) * (q - d - 3) :=
              Nat.mul_le_mul_right _ ht_lo
          _ = 3 * (2 * t * (q - d - 3)) := by ring
      have h2 : 3 * (4 * t) ≤ 6 * d := by omega
      nlinarith
    have hlow : q ≤ 6 * ((s + 1) * (s + 1)) + d + 6 := by
      have : 2 * d * (q - d - 3) ≤ 2 * d * (6 * ((s + 1) * (s + 1)) + 3) := by linarith
      have : q - d - 3 ≤ 6 * ((s + 1) * (s + 1)) + 3 :=
        Nat.le_of_mul_le_mul_left this (by omega)
      omega
    have hs_ge2 : 2 ≤ s := by
      by_contra hlt
      have : s ≤ 1 := by omega
      have : (s + 1) * (s + 1) ≤ 4 := by nlinarith
      nlinarith
    have hm_le : 2 * s ≤ (q - 1) / 2 := by
      have : 4 * s < q := by nlinarith
      omega
    obtain ⟨hJ, hm, hD, hcnt, hdtot⟩ := param_core_le hd hodd hq_ge (by omega) hm_le
    have hstep := charSum_abs_bound_of_params hF hf hsf hdeg (by omega) hJ hm hD hcnt
    have habs : (2 * s : ℤ) * |S| ≤ ((2 * d - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s := by
      have h1 : ((d + 2 * t - 1 : ℕ) : ℤ) ≤ ((2 * d - 1 : ℕ) : ℤ) := by omega
      have h2 : (2 * (s : ℤ)) * |S| ≤ ((d + 2 * t - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s := by
        have hstep' : ((2 * s : ℕ) : ℤ) * |S| ≤
            2 * ((d * (2 * s + (q - 1) / 2) + D + q * (s + t - 1) : ℕ) : ℤ)
              + (d : ℤ) * ((2 * s : ℕ) : ℤ) - ((2 * s : ℕ) : ℤ) * q := hstep
        have hcomb := le_trans hstep' hdtot
        push_cast at hcomb
        exact hcomb
      nlinarith [Nat.cast_nonneg (α := ℤ) q]
    -- Show `6 * d * s ≤ q` (from `4*s^2 ≤ q` and `q > 16*d^2`, `36*d^2*s^2 ≤ 9*d^2*q < q^2`)
    have h6ds : 6 * (d : ℤ) * s ≤ q := by
      have hsq : (6 * (d : ℤ) * s) ^ 2 ≤ (q : ℤ) ^ 2 := by
        have h4s2' : 4 * ((s : ℤ) * s) ≤ q := by exact_mod_cast h4s2
        have hq16' : 16 * (d : ℤ) * d < q := by exact_mod_cast hq16
        nlinarith [Nat.cast_nonneg (α := ℤ) d, Nat.cast_nonneg (α := ℤ) s]
      nlinarith [Nat.cast_nonneg (α := ℤ) d, Nat.cast_nonneg (α := ℤ) s,
        Nat.cast_nonneg (α := ℤ) q]
    have habs2 : (2 * s : ℤ) * |S| ≤ 2 * (d : ℤ) * q := by
      have h2d1 : ((2 * d - 1 : ℕ) : ℤ) = 2 * (d : ℤ) - 1 := by omega
      rw [h2d1] at habs
      linarith
    -- Show `q ≤ 16 * s^2` from `s ≥ 2 ⇒ 4*(s+1)^2 ≤ 9*s^2 ⇒ 6*(s+1)^2 ≤ 13.5*s^2` and `d+6 ≤ q/8`
    have hq16s : (q : ℤ) ≤ 16 * ((s : ℤ) * s) := by
      have hlow' : (q : ℤ) ≤ 6 * (((s : ℤ) + 1) * ((s : ℤ) + 1)) + d + 6 := by exact_mod_cast hlow
      have hs2' : (2 : ℤ) ≤ s := by exact_mod_cast hs_ge2
      have hd2' : (2 : ℤ) ≤ d := by exact_mod_cast hd
      have hq16' : 16 * (d : ℤ) * d < q := by exact_mod_cast hq16
      -- `4*(s+1)^2 ≤ 9*s^2`, `8*(d+6) ≤ q`, so `7*q/8 ≤ 27/2 * s^2 ⇒ q ≤ 16*s^2`
      have h9 : 4 * (((s : ℤ) + 1) * ((s : ℤ) + 1)) ≤ 9 * ((s : ℤ) * s) := by nlinarith
      have hd6 : 8 * ((d : ℤ) + 6) ≤ q := by nlinarith
      nlinarith
    -- Finish: `(2*s)^2 * S^2 ≤ (2*d*q)^2 = 4*d^2*q^2 ≤ 4*d^2*(16*s^2)*q = (2*s)^2 * (4*d)^2 * q`
    have hmul_sq : (2 * (s : ℤ)) ^ 2 * S ^ 2 ≤ (2 * (s : ℤ)) ^ 2 * (((4 * d : ℕ) : ℤ) ^ 2 * q) := by
      have hsq1 : ((2 * (s : ℤ)) * |S|) ^ 2 ≤ (2 * (d : ℤ) * q) ^ 2 :=
        pow_le_pow_left₀ (by positivity) habs2 2
      rw [mul_pow, sq_abs] at hsq1
      have h4d : ((4 * d : ℕ) : ℤ) = 4 * (d : ℤ) := by push_cast; ring
      rw [h4d]
      nlinarith [sq_nonneg (d : ℤ), Nat.cast_nonneg (α := ℤ) q]
    have hspos : 0 < (2 * (s : ℤ)) ^ 2 := by positivity
    exact le_of_mul_le_mul_left hmul_sq hspos

/-- Real absolute-value form of `hyperelliptic_stepanov_sq_le`:
`|∑ s : F, χ(f s)| ≤ 4 * d * √|F|` for every monic squarefree `f` of degree `d ≥ 2`. -/
theorem hyperelliptic_stepanov_abs_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {f : F[X]} (hf : f.Monic) (hsf : Squarefree f)
    {d : ℕ} (hdeg : f.natDegree = d) (hd : 2 ≤ d) :
    |((∑ s : F, quadraticChar F (f.eval s) : ℤ) : ℝ)| ≤
      (4 * d : ℝ) * Real.sqrt (Fintype.card F) := by
  have hsq : ((∑ s : F, quadraticChar F (f.eval s) : ℤ) : ℝ) ^ 2 ≤
      ((4 * d : ℝ) * Real.sqrt (Fintype.card F)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have h := hyperelliptic_stepanov_sq_le hF hf hsf hdeg hd
    have h' : ((∑ s : F, quadraticChar F (f.eval s) : ℤ) : ℝ) ^ 2 ≤
        (((4 * d : ℕ) : ℝ) ^ 2) * (Fintype.card F : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_mul, Nat.cast_ofNat] using h'
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

/-! ## 7. Sharp large-field constants for `d = 3, 4, 6` -/

/-- Helper reducing a sharp rational bound `den * |S| ≤ num * √q` to a single symbolic check on
the parameter `s = sP d q`. -/
private theorem tight_bound_of_symbolic {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {f : F[X]} (hf : f.Monic) (hsf : Squarefree f)
    {d : ℕ} (hdeg : f.natDegree = d) (hd : 2 ≤ d)
    (num den : ℕ)
    (hq_ge : d + 4 ≤ Fintype.card F)
    (hs_pos : 1 ≤ sP d (Fintype.card F))
    (hm_le : 2 * sP d (Fintype.card F) ≤ (Fintype.card F - 1) / 2)
    (hmain : (den : ℤ) ^ 2 *
        (((d + 2 * tP d - 1 : ℕ) : ℤ) * Fintype.card F + 6 * (d : ℤ) * sP d (Fintype.card F)) ^ 2
        ≤ (num : ℤ) ^ 2 * (4 * (sP d (Fintype.card F) : ℤ) ^ 2 * Fintype.card F)) :
    (den : ℤ) ^ 2 * (∑ s : F, quadraticChar F (f.eval s)) ^ 2 ≤
      (num : ℤ) ^ 2 * Fintype.card F := by
  set q := Fintype.card F
  set S : ℤ := ∑ s : F, quadraticChar F (f.eval s)
  set s := sP d q
  have hodd : Odd q := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
  obtain ⟨hJ, hm, hD, hcnt, hdtot⟩ := param_core_le hd hodd hq_ge hs_pos hm_le
  have hstep := charSum_abs_bound_of_params hF hf hsf hdeg (by omega) hJ hm hD hcnt
  have habs : (2 * (s : ℤ)) * |S| ≤ ((d + 2 * tP d - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s := by
    have hstep' : ((2 * s : ℕ) : ℤ) * |S| ≤
        2 * ((d * (2 * s + (q - 1) / 2) + dDegP d q + q * (s + tP d - 1) : ℕ) : ℤ)
          + (d : ℤ) * ((2 * s : ℕ) : ℤ) - ((2 * s : ℕ) : ℤ) * q := hstep
    have hcomb := le_trans hstep' hdtot
    push_cast at hcomb
    exact hcomb
  have hsq : ((2 * s : ℤ) * |S|) ^ 2 ≤ (((d + 2 * tP d - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) habs 2
  rw [mul_pow, sq_abs] at hsq
  have hcomb : (4 * (s : ℤ) ^ 2) * ((den : ℤ) ^ 2 * S ^ 2) ≤
      (4 * (s : ℤ) ^ 2) * ((num : ℤ) ^ 2 * q) := by
    calc (4 * (s : ℤ) ^ 2) * ((den : ℤ) ^ 2 * S ^ 2)
        = (den : ℤ) ^ 2 * ((2 * (s : ℤ)) ^ 2 * S ^ 2) := by ring
      _ ≤ (den : ℤ) ^ 2 * (((d + 2 * tP d - 1 : ℕ) : ℤ) * q + 6 * (d : ℤ) * s) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ ≤ (num : ℤ) ^ 2 * (4 * (s : ℤ) ^ 2 * q) := hmain
      _ = (4 * (s : ℤ) ^ 2) * ((num : ℤ) ^ 2 * q) := by ring
  have hspos : 0 < 4 * (s : ℤ) ^ 2 := by positivity
  exact le_of_mul_le_mul_left hcomb hspos

/-- **Sharp cubic bound (`d = 3`, `|S| ≤ 5 √q`)** for all odd-characteristic finite fields
with `q ≥ 43357`. Improves the uniform-box constant `7` (`K = 49`) down to `5` (`K = 25`). -/
theorem hyperelliptic_stepanov_deg3_tight {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hq : 43357 ≤ Fintype.card F)
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) (hdeg : f.natDegree = 3) :
    (∑ s : F, quadraticChar F (f.eval s)) ^ 2 ≤ 25 * Fintype.card F := by
  set q := Fintype.card F
  set s := sP 3 q
  have hlow : 2 * (q - 3 - 3) < 12 * ((s + 1) * (s + 1)) + 4 := by
    simpa [tP, s] using sP_succ_sq_ge (d := 3) (q := q) (by decide) (by omega)
  have hq_le : (q : ℤ) ≤ 6 * (((s : ℤ) + 1) * ((s : ℤ) + 1)) + 7 := by
    have : q ≤ 6 * ((s + 1) * (s + 1)) + 7 := by omega
    exact_mod_cast this
  have hss : 6 * ((s : ℤ) * s) ≤ q := by
    have h1 : 3 * (s * s) ≤ 1 * dDegP 3 q := by
      have := Nat.sqrt_le (tP 3 * dDegP 3 q / 3)
      calc 3 * (s * s) ≤ 3 * (tP 3 * dDegP 3 q / 3) := Nat.mul_le_mul_left 3 this
        _ ≤ tP 3 * dDegP 3 q := Nat.mul_div_le _ _
    have h2 : 2 * dDegP 3 q ≤ q := by unfold dDegP; omega
    have h3 : 6 * (s * s) ≤ q := by omega
    exact_mod_cast h3
  have hs85_nat : 85 ≤ s := by
    have hD : 21676 ≤ dDegP 3 q := by unfold dDegP; omega
    have hdiv : 85 * 85 ≤ tP 3 * dDegP 3 q / 3 := by simp only [tP]; omega
    exact Nat.le_sqrt.mpr hdiv
  have hs85 : (85 : ℤ) ≤ s := by exact_mod_cast hs85_nat
  have hm_le : 2 * s ≤ (q - 1) / 2 := by
    have : 4 * (s : ℤ) ≤ q - 1 := by nlinarith
    omega
  have hmain : (1 : ℤ) ^ 2 *
      (((3 + 2 * tP 3 - 1 : ℕ) : ℤ) * q + 6 * (3 : ℤ) * s) ^ 2
      ≤ (5 : ℤ) ^ 2 * (4 * (s : ℤ) ^ 2 * q) := by
    simp only [tP]
    norm_num
    have hq_pos : (0 : ℤ) < q := by omega
    have h1 : 16 * (q : ℤ) + 144 * s + 54 ≤ 100 * (s : ℤ) ^ 2 := by nlinarith
    nlinarith
  simpa using tight_bound_of_symbolic hF hf hsf hdeg (by decide) 5 1 (by omega)
    (show 1 ≤ s by omega) hm_le hmain

/-- **Sharp quartic bound (`d = 4`, `|S| ≤ 8 √q`)** for all odd-characteristic finite fields
with `q ≥ 683`. -/
theorem hyperelliptic_stepanov_deg4_tight {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hq : 683 ≤ Fintype.card F)
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) (hdeg : f.natDegree = 4) :
    (∑ s : F, quadraticChar F (f.eval s)) ^ 2 ≤ 64 * Fintype.card F := by
  set q := Fintype.card F
  set s := sP 4 q
  have hlow : 4 * (q - 4 - 3) < 16 * ((s + 1) * (s + 1)) + 8 := by
    simpa [tP, s] using sP_succ_sq_ge (d := 4) (q := q) (by decide) (by omega)
  have hq_le : (q : ℤ) ≤ 4 * (((s : ℤ) + 1) * ((s : ℤ) + 1)) + 8 := by
    have : q ≤ 4 * ((s + 1) * (s + 1)) + 8 := by omega
    exact_mod_cast this
  have hss : 4 * ((s : ℤ) * s) ≤ q := by
    have h1 : 4 * (s * s) ≤ 2 * dDegP 4 q := by
      have := Nat.sqrt_le (tP 4 * dDegP 4 q / 4)
      calc 4 * (s * s) ≤ 4 * (tP 4 * dDegP 4 q / 4) := Nat.mul_le_mul_left 4 this
        _ ≤ tP 4 * dDegP 4 q := Nat.mul_div_le _ _
    have h2 : 2 * dDegP 4 q ≤ q := by unfold dDegP; omega
    exact_mod_cast h1.trans h2
  have hs13_nat : 13 ≤ s := by
    have hD : 338 ≤ dDegP 4 q := by unfold dDegP; omega
    have hdiv : 13 * 13 ≤ tP 4 * dDegP 4 q / 4 := by simp only [tP]; omega
    exact Nat.le_sqrt.mpr hdiv
  have hs13 : (13 : ℤ) ≤ s := by exact_mod_cast hs13_nat
  have hm_le : 2 * s ≤ (q - 1) / 2 := by
    have : 4 * (s : ℤ) ≤ q - 1 := by nlinarith
    omega
  have hmain : (1 : ℤ) ^ 2 *
      (((4 + 2 * tP 4 - 1 : ℕ) : ℤ) * q + 6 * (4 : ℤ) * s) ^ 2
      ≤ (8 : ℤ) ^ 2 * (4 * (s : ℤ) ^ 2 * q) := by
    simp only [tP]
    norm_num
    rcases le_or_gt (14 : ℤ) s with hs14 | hs13'
    · have h1 : 49 * (q : ℤ) + 336 * s + 144 ≤ 256 * (s : ℤ) ^ 2 := by nlinarith
      nlinarith
    · have hs_eq_nat : s = 13 := by omega
      have hq789_nat : q ≤ 789 := by
        have hlt : tP 4 * dDegP 4 q / 4 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
        rw [hs_eq_nat] at hlt
        unfold tP dDegP at hlt
        omega
      have hs_eq : (s : ℤ) = 13 := by exact_mod_cast hs_eq_nat
      have hq683 : (683 : ℤ) ≤ q := by exact_mod_cast hq
      have hq789 : (q : ℤ) ≤ 789 := by exact_mod_cast hq789_nat
      rw [hs_eq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hq683) (sub_nonneg.mpr hq789)]
  simpa using tight_bound_of_symbolic hF hf hsf hdeg (by decide) 8 1 (by omega)
    (show 1 ≤ s by omega) hm_le hmain

/-- **Sharp sextic bound (`d = 6`, `|S| ≤ 12 √q`)** for all odd-characteristic finite fields
with `q ≥ 1772`. -/
theorem hyperelliptic_stepanov_deg6_tight {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hq : 1772 ≤ Fintype.card F)
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) (hdeg : f.natDegree = 6) :
    (∑ s : F, quadraticChar F (f.eval s)) ^ 2 ≤ 144 * Fintype.card F := by
  set q := Fintype.card F
  set s := sP 6 q
  have hlow : 6 * (q - 6 - 3) < 24 * ((s + 1) * (s + 1)) + 12 := by
    simpa [tP, s] using sP_succ_sq_ge (d := 6) (q := q) (by decide) (by omega)
  have hq_le : (q : ℤ) ≤ 4 * (((s : ℤ) + 1) * ((s : ℤ) + 1)) + 10 := by
    have : q ≤ 4 * ((s + 1) * (s + 1)) + 10 := by omega
    exact_mod_cast this
  have hss : 4 * ((s : ℤ) * s) ≤ q := by
    have h1 : 6 * (s * s) ≤ 3 * dDegP 6 q := by
      have := Nat.sqrt_le (tP 6 * dDegP 6 q / 6)
      calc 6 * (s * s) ≤ 6 * (tP 6 * dDegP 6 q / 6) := Nat.mul_le_mul_left 6 this
        _ ≤ tP 6 * dDegP 6 q := Nat.mul_div_le _ _
    have h2 : 2 * dDegP 6 q ≤ q := by unfold dDegP; omega
    exact_mod_cast (show 4 * (s * s) ≤ q by omega)
  have hs21_nat : 21 ≤ s := by
    have hD : 882 ≤ dDegP 6 q := by unfold dDegP; omega
    have hdiv : 21 * 21 ≤ tP 6 * dDegP 6 q / 6 := by simp only [tP]; omega
    exact Nat.le_sqrt.mpr hdiv
  have hs21 : (21 : ℤ) ≤ s := by exact_mod_cast hs21_nat
  have hm_le : 2 * s ≤ (q - 1) / 2 := by
    have : 4 * (s : ℤ) ≤ q - 1 := by nlinarith
    omega
  have hmain : (1 : ℤ) ^ 2 *
      (((6 + 2 * tP 6 - 1 : ℕ) : ℤ) * q + 6 * (6 : ℤ) * s) ^ 2
      ≤ (12 : ℤ) ^ 2 * (4 * (s : ℤ) ^ 2 * q) := by
    simp only [tP]
    norm_num
    have h1 : 121 * (q : ℤ) + 792 * s + 324 ≤ 576 * (s : ℤ) ^ 2 := by nlinarith
    nlinarith
  simpa using tight_bound_of_symbolic hF hf hsf hdeg (by decide) 12 1 (by omega)
    (show 1 ≤ s by omega) hm_le hmain

/-- **Ultra-sharp sextic bound (`d = 6`, `|S| ≤ 11.1 √q`, i.e., `100 * S^2 ≤ 12321 * q`)**
for all odd-characteristic finite fields with `q ≥ 10 ^ 7 + 1`. This feeds the production-prime
6th-moment transversal theorem (`|A| ≥ 2^59` on both designated production primes). -/
theorem hyperelliptic_stepanov_deg6_ultra {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hq : 10 ^ 7 + 1 ≤ Fintype.card F)
    {f : F[X]} (hf : f.Monic) (hsf : Squarefree f) (hdeg : f.natDegree = 6) :
    100 * (∑ s : F, quadraticChar F (f.eval s)) ^ 2 ≤ 12321 * Fintype.card F := by
  set q := Fintype.card F
  set s := sP 6 q
  have hlow : 6 * (q - 6 - 3) < 24 * ((s + 1) * (s + 1)) + 12 := by
    simpa [tP, s] using sP_succ_sq_ge (d := 6) (q := q) (by decide) (by omega)
  have hq_le : (q : ℤ) ≤ 4 * (((s : ℤ) + 1) * ((s : ℤ) + 1)) + 10 := by
    have : q ≤ 4 * ((s + 1) * (s + 1)) + 10 := by omega
    exact_mod_cast this
  have hss : 4 * ((s : ℤ) * s) ≤ q := by
    have h1 : 6 * (s * s) ≤ 3 * dDegP 6 q := by
      have := Nat.sqrt_le (tP 6 * dDegP 6 q / 6)
      calc 6 * (s * s) ≤ 6 * (tP 6 * dDegP 6 q / 6) := Nat.mul_le_mul_left 6 this
        _ ≤ tP 6 * dDegP 6 q := Nat.mul_div_le _ _
    have h2 : 2 * dDegP 6 q ≤ q := by unfold dDegP; omega
    exact_mod_cast (show 4 * (s * s) ≤ q by omega)
  have hs1580_nat : 1580 ≤ s := by
    have hD : 4999996 ≤ dDegP 6 q := by unfold dDegP; omega
    have hdiv : 1580 * 1580 ≤ tP 6 * dDegP 6 q / 6 := by simp only [tP]; omega
    exact Nat.le_sqrt.mpr hdiv
  have hs1580 : (1580 : ℤ) ≤ s := by exact_mod_cast hs1580_nat
  have hm_le : 2 * s ≤ (q - 1) / 2 := by
    have : 4 * (s : ℤ) ≤ q - 1 := by nlinarith
    omega
  have hmain : (10 : ℤ) ^ 2 *
      (((6 + 2 * tP 6 - 1 : ℕ) : ℤ) * q + 6 * (6 : ℤ) * s) ^ 2
      ≤ (111 : ℤ) ^ 2 * (4 * (s : ℤ) ^ 2 * q) := by
    simp only [tP]
    norm_num
    have h1 : 12100 * (q : ℤ) + 79200 * s + 32400 ≤ 49284 * (s : ℤ) ^ 2 := by nlinarith
    nlinarith
  have h := tight_bound_of_symbolic hF hf hsf hdeg (by decide) 111 10 (by omega)
    (show 1 ≤ s by omega) hm_le hmain
  norm_num at h
  exact h

end ExplicitParams

/-! ## 8. Reduction of arbitrary products of linear factors to squarefree polynomials -/

section ProductOfLinears

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Monic squarefree product of distinct linear factors `∏ a ∈ S, (X - C a)`. -/
noncomputable def prodLinear (S : Finset F) : F[X] :=
  ∏ a ∈ S, (X - C a)

theorem prodLinear_monic (S : Finset F) : (prodLinear S).Monic :=
  monic_prod_of_monic S _ fun a _ => monic_X_sub_C a

theorem prodLinear_natDegree (S : Finset F) : (prodLinear S).natDegree = S.card := by
  unfold prodLinear
  rw [natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C a]
  simp

theorem prodLinear_squarefree (S : Finset F) : Squarefree (prodLinear S) := by
  unfold prodLinear
  exact (separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree

theorem prodLinear_eval (S : Finset F) (x : F) :
    (prodLinear S).eval x = ∏ a ∈ S, (x - a) := by
  unfold prodLinear
  rw [eval_prod]
  exact Finset.prod_congr rfl fun a _ => by simp

/-- Removing even-multiplicity linear factors from a character product changes each term only at
their roots, shifting the complete sum by at most the number of distinct omitted roots. -/
theorem charSum_prod_sub_squarefree_le {ι : Type*} [DecidableEq ι] (I : Finset ι) (a : ι → F) :
    let supp := I.image a
    let oddSet := supp.filter fun u => Odd (I.filter fun i => a i = u).card
    let evenSet := supp.filter fun u => Even (I.filter fun i => a i = u).card
    |(∑ x : F, ∏ i ∈ I, quadraticChar F (x - a i)) -
        (∑ x : F, quadraticChar F ((prodLinear oddSet).eval x))|
      ≤ (evenSet.card : ℤ) := by
  classical
  intro supp oddSet evenSet
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ x : F,
      |(∏ i ∈ I, quadraticChar F (x - a i)) -
          quadraticChar F ((prodLinear oddSet).eval x)|
        ≤ if x ∈ evenSet then (1 : ℤ) else 0 := by
    intro x
    -- Group the product over `I` by fiber values `u ∈ supp`.
    have hfiber : ∏ i ∈ I, quadraticChar F (x - a i) =
        ∏ u ∈ supp, quadraticChar F (x - u) ^ (I.filter fun i => a i = u).card := by
      rw [← Finset.prod_fiberwise_of_maps_to (g := a) (t := supp)
        (fun i hi => Finset.mem_image_of_mem a hi)]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]]
      rw [Finset.prod_const]
    have hsplit : supp = oddSet ∪ evenSet := by
      ext u
      simp only [oddSet, evenSet, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hu
        rcases Nat.even_or_odd (I.filter fun i => a i = u).card with he | ho
        · exact Or.inr ⟨hu, he⟩
        · exact Or.inl ⟨hu, ho⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    have hdisj : Disjoint oddSet evenSet := by
      rw [Finset.disjoint_left]
      intro u huo hue
      have ho := (Finset.mem_filter.mp huo).2
      have he := (Finset.mem_filter.mp hue).2
      exact (Nat.not_odd_iff_even.mpr he) ho
    rw [hfiber, hsplit, Finset.prod_union hdisj, prodLinear_eval, map_prod]
    have hodd_prod : ∏ u ∈ oddSet, quadraticChar F (x - u) ^ (I.filter fun i => a i = u).card =
        ∏ u ∈ oddSet, quadraticChar F (x - u) := by
      refine Finset.prod_congr rfl fun u hu => ?_
      have ho := (Finset.mem_filter.mp hu).2
      rcases (quadraticChar_isQuadratic F) (x - u) with h | h | h
      · have hne : (I.filter fun i => a i = u).card ≠ 0 := by rcases ho with ⟨k, hk⟩; omega
        rw [h, zero_pow hne]
      · rw [h, one_pow]
      · rw [h, ho.neg_one_pow]
    rw [hodd_prod]
    by_cases hx : x ∈ evenSet
    · simp only [hx, ↓reduceIte]
      have hne_pos : 0 < (I.filter fun i => a i = x).card := by
        have hxs : x ∈ supp := (Finset.mem_filter.mp hx).1
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxs
        exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
      have heven_zero : ∏ u ∈ evenSet, quadraticChar F (x - u) ^ (I.filter fun i => a i = u).card = 0 :=
        Finset.prod_eq_zero hx (by rw [sub_self, MulChar.map_zero, zero_pow hne_pos.ne'])
      rw [heven_zero, mul_zero, zero_sub, abs_neg]
      have hprod_le : |∏ u ∈ oddSet, quadraticChar F (x - u)| ≤ 1 := by
        rw [Finset.abs_prod]
        induction oddSet using Finset.induction_on with
        | empty => simp
        | @insert u s hu ih =>
          rw [Finset.prod_insert hu]
          have hu1 : |quadraticChar F (x - u)| ≤ 1 := by
            rcases (quadraticChar_isQuadratic F) (x - u) with h | h | h <;> rw [h] <;> decide
          have hs0 : 0 ≤ ∏ v ∈ s, |quadraticChar F (x - v)| :=
            Finset.prod_nonneg fun _ _ => abs_nonneg _
          nlinarith
      exact hprod_le
    · simp only [hx, ↓reduceIte]
      have heven_one : ∏ u ∈ evenSet, quadraticChar F (x - u) ^ (I.filter fun i => a i = u).card = 1 := by
        refine Finset.prod_eq_one fun u hu => ?_
        have hxu : x - u ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ hu)
        have he := (Finset.mem_filter.mp hu).2
        rcases quadraticChar_dichotomy hxu with h | h
        · rw [h, one_pow]
        · rw [h, he.neg_one_pow]
      rw [heven_one, mul_one, sub_self, abs_zero]
  calc |∑ x : F, ((∏ i ∈ I, quadraticChar F (x - a i)) -
          quadraticChar F ((prodLinear oddSet).eval x))|
      ≤ ∑ x : F, |(∏ i ∈ I, quadraticChar F (x - a i)) -
          quadraticChar F ((prodLinear oddSet).eval x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : F, if x ∈ evenSet then (1 : ℤ) else 0 := Finset.sum_le_sum fun x _ => hterm x
    _ = (evenSet.card : ℤ) := by rw [← Finset.sum_filter]; simp

/-- **General tuple character-sum bound**: for ANY tuple `a : Fin n → F` whose odd-multiplicity
set has `o ≥ 1` distinct points and even-multiplicity set has `e` distinct points:
`|∑ x : F, ∏ i, χ(x - a i)| ≤ 4 * o * √|F| + e` (and exact `≤ e` when `o = 1`, `≤ 1 + e` when `o = 2`). -/
theorem tuple_charSum_abs_le (hF : ringChar F ≠ 2) {n : ℕ} (a : Fin n → F)
    (hodd_nonempty : ((Finset.univ.image a).filter fun u =>
      Odd (Finset.univ.filter fun i : Fin n => a i = u).card).Nonempty) :
    let supp := Finset.univ.image a
    let oddSet := supp.filter fun u => Odd (Finset.univ.filter fun i : Fin n => a i = u).card
    let evenSet := supp.filter fun u => Even (Finset.univ.filter fun i : Fin n => a i = u).card
    |((∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i) : ℤ) : ℝ)| ≤
      (4 * oddSet.card : ℝ) * Real.sqrt (Fintype.card F) + evenSet.card := by
  classical
  intro supp oddSet evenSet
  have hdiff_int := charSum_prod_sub_squarefree_le Finset.univ a
  have hdiff : |((∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i) : ℤ) : ℝ) -
      ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| ≤
      (evenSet.card : ℝ) := by exact_mod_cast hdiff_int
  have htri : |((∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i) : ℤ) : ℝ)| ≤
      |((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| + (evenSet.card : ℝ) := by
    have hadd : |((∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i) : ℤ) : ℝ)| ≤
        |((∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i) : ℤ) : ℝ) -
          ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| +
        |((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| := by
      simpa only [sub_add_cancel] using abs_add_le
        (((∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i) : ℤ) : ℝ) -
          ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ))
        ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)
    linarith
  have ho_pos : 1 ≤ oddSet.card := Finset.card_pos.mpr hodd_nonempty
  rcases eq_or_lt_of_le ho_pos with ho1 | ho2
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp ho1.symm
    have hzero : ∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) = 0 := by
      have : ∀ x : F, (prodLinear oddSet).eval x = x - u := fun x => by
        rw [prodLinear_eval, hu, Finset.prod_singleton]
      simp_rw [this]
      exact linear_charSum_eq_zero hF u
    rw [hzero, Int.cast_zero, abs_zero, zero_add] at htri
    linarith [mul_nonneg (show (0 : ℝ) ≤ 4 * oddSet.card by positivity) (Real.sqrt_nonneg (Fintype.card F))]
  · have hstep := hyperelliptic_stepanov_abs_le hF (prodLinear_monic oddSet)
      (prodLinear_squarefree oddSet) (prodLinear_natDegree oddSet) ho2
    linarith

/-- Sharp bound when the odd-multiplicity set has size `2`: `|∑ x, ∏ i, χ(x - a i)| ≤ 1 + e`. -/
theorem tuple_charSum_oddCard_two (hF : ringChar F ≠ 2) {n : ℕ} (a : Fin n → F)
    (h2 : ((Finset.univ.image a).filter fun u =>
      Odd (Finset.univ.filter fun i : Fin n => a i = u).card).card = 2) :
    let supp := Finset.univ.image a
    let evenSet := supp.filter fun u => Even (Finset.univ.filter fun i : Fin n => a i = u).card
    |∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i)| ≤ 1 + (evenSet.card : ℤ) := by
  classical
  intro supp evenSet
  set oddSet := supp.filter fun u => Odd (Finset.univ.filter fun i : Fin n => a i = u).card
  obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp h2
  have hquad : ∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) = -1 := by
    have : ∀ x : F, (prodLinear oddSet).eval x = (x - u) * (x - v) := fun x => by
      rw [prodLinear_eval, hpair, Finset.prod_pair huv]
    simp_rw [this]
    exact quadratic_charSum_eq_neg_one hF huv
  have hdiff := charSum_prod_sub_squarefree_le Finset.univ a
  change |(∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i)) -
      (∑ x : F, quadraticChar F ((prodLinear oddSet).eval x))| ≤ (evenSet.card : ℤ) at hdiff
  rw [hquad] at hdiff
  have := abs_le.mp hdiff
  rw [abs_le]
  omega

end ProductOfLinears

end ProximityGap.HyperellipticStepanov

#print axioms ProximityGap.HyperellipticStepanov.stepanov_independence
#print axioms ProximityGap.HyperellipticStepanov.fiber_bound_of_params
#print axioms ProximityGap.HyperellipticStepanov.charSum_abs_bound_of_params
#print axioms ProximityGap.HyperellipticStepanov.linear_charSum_eq_zero
#print axioms ProximityGap.HyperellipticStepanov.quadratic_charSum_eq_neg_one
#print axioms ProximityGap.HyperellipticStepanov.hyperelliptic_stepanov_sq_le
#print axioms ProximityGap.HyperellipticStepanov.hyperelliptic_stepanov_abs_le
#print axioms ProximityGap.HyperellipticStepanov.hyperelliptic_stepanov_deg3_tight
#print axioms ProximityGap.HyperellipticStepanov.hyperelliptic_stepanov_deg4_tight
#print axioms ProximityGap.HyperellipticStepanov.hyperelliptic_stepanov_deg6_tight
#print axioms ProximityGap.HyperellipticStepanov.hyperelliptic_stepanov_deg6_ultra
#print axioms ProximityGap.HyperellipticStepanov.tuple_charSum_abs_le
#print axioms ProximityGap.HyperellipticStepanov.tuple_charSum_oddCard_two
