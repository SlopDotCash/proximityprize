/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarCubicObstruction

/-! # Reciprocal interpolation at the first nonnegative relative coordinate degree -/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.ApolarBorderCoordinates
open ApolarDividedLocator ApolarDividedPolynomial ApolarParameterTransition
open ApolarSyndromeInterpolation ApolarChartDescent ApolarCoordinateEquations
open ApolarInverseCoordinates ApolarUnitChartSpecialization ApolarCubicObstruction
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts
variable {K : Type*} [Field K]

/-- At relative coordinate twist zero the degree bound is weak. -/
theorem small_degree_weak (f B B' : K[X][X]) {n a : ℕ} (hpos : 0 < f.natDegree)
    (htwist : n ≤ a + f.natDegree)
    (hb : (Bivariate.swap B).natDegree < (Bivariate.swap f).natDegree)
    (hb' : (Bivariate.swap B').natDegree < (Bivariate.swap f).natDegree)
    (h : ∀ b c, b + a = n + c →
      Bivariate.swap f ∣ C (X^b) * reverseCoeffs B'.natDegree (Bivariate.swap B') -
        C (X^(B'.natDegree+c)) * Bivariate.swap B) :
    B.natDegree ≤ f.natDegree := by
  have hm (j : ℕ) : ((Bivariate.swap B').coeff j).natDegree ≤ B'.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [swap_coeff,coeff_eq_zero_of_natDegree_lt hk,coeff_zero]
  by_cases he : a ≤ n
  · have hc := h (n-a) 0 (by omega)
    simp only [Nat.add_zero] at hc
    have hdeg := swapped_degree hb hb' hm hc
    rw [Bivariate.swap_swap_apply] at hdeg
    omega
  · have hc := h 0 (a-n) (by omega)
    rw [pow_zero] at hc
    obtain ⟨hzero,_⟩ := negative_twist (by omega : 0<a-n) hb hb' hm hc
    have hz : B=0 := Bivariate.swap.injective (by simpa using hzero)
    simpa only [hz,natDegree_zero] using hpos.le

/-- Clear the actual power interpolation identities at relative twist zero. -/
theorem coordinate_small_weak (power : ℕ) [IsAlgClosed K] {J : Type*}
    (D : Finset J) (y : J → K[X]ˣ) (w : J → K[X])
    (f V B B' Q Q' : K[X][X]) (S : K[X]) {r k n : ℕ}
    (hr : 0 < f.natDegree) (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hfree : ∀ t : K, f.map (evalRingHom t) ≠ 0) (hz : f.coeff 0 ≠ 0) (hS : S ≠ 0)
    (hsize : n ≤ (k + 1) * power + f.natDegree)
    (hb : (Bivariate.swap B).natDegree < (Bivariate.swap f).natDegree)
    (hb' : (Bivariate.swap B').natDegree < (Bivariate.swap f).natDegree)
    (ha : ApolarThrough (ApolarRootTransition.measure D (fun i => (y i : K[X])) w) f (k - 1))
    (h0 : V * (representative D (fun i => (y i : K[X])) w f)^power = f * Q + C S * B)
    (h1 : reflect n V * (-representative D (fun i => (↑(y i)⁻¹ : K[X]))
      (fun i => w i * (y i : K[X])^(r + k)) (reflect (r + 1) f))^power =
      reflect (r + 1) f * Q' + C S * B') : B.natDegree ≤ f.natDegree := by
  apply small_degree_weak f B B' hr hsize hb hb'
  intro b c he
  exact power_congruence power D y w f V B B' Q Q' S hk hf hV hfree hz hS le_rfl he ha h0 h1

/-- Actual interpolation produces remainders of coordinate degree at most r. -/
theorem small_interpolation_weak (power : ℕ) (hpower : 0 < power) [IsAlgClosed K] [DecidableEq K]
    (D G : Finset K) (w : K → K[X]) (f : K[X][X]) (V : K[X]) {l r s n : ℕ}
    (hD : 0 ∉ D) (hG : G.Nonempty) (hl : 0 < l) (hr : 0 < r) (hdeg : f.natDegree = r)
    (hpdeg : (Bivariate.swap f).natDegree = l) (hV : Lagrange.nodal D id ∣ V)
    (hn : V.natDegree ≤ n) (htwist : n ≤ power * (s + 2) + r)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l)
    (hz : f.coeff 0 ≠ 0) (hprim : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hm : power * (l + 1) < G.card + l)
    (ha : ApolarThrough (ApolarRootTransition.measure D C w) f s)
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ s + 1 ∧ ∃ v : K → K, ∀ p : K[X],
      p.natDegree ≤ r + s → weighted D (RingHom.id K) (fun i => (w i).eval t) p =
        weighted E (RingHom.id K) v p) :
    ∃ Q B : K[X][X], Q.natDegree < G.card ∧ B.natDegree < l ∧
      (Bivariate.swap B).natDegree ≤ r ∧
      C V * (Bivariate.swap (representative D C w f))^power =
        Bivariate.swap f * Q + Lagrange.nodal G C * B := by
  obtain ⟨Q, B, Qi, Bi, hQ, _, hB, hBi, h0, h1⟩ :=
    paired_power_coordinates power hpower D G w f V l r s n hD hG hl hV hn hw hf hdeg.le hm hsp
      (fun t _ => specialize_apolar D w f s ha t)
  have hr' : r - 1 + 1 = r := by omega
  have hs' : r - 1 + (s + 1) = r + s := by omega
  have hmeas : ApolarThrough (ApolarRootTransition.measure D
      (fun i => (coordinateUnit i : K[X])) w) f ((s + 1) - 1) := by
    simpa only [measure_forward D hD w, Nat.add_sub_cancel] using ha
  have hbc : (Bivariate.swap B).natDegree ≤ f.natDegree := by
    apply coordinate_small_weak power D coordinateUnit w f (V.map C) (Bivariate.swap B) (Bivariate.swap Bi)
      (Bivariate.swap Q) (Bivariate.swap Qi) (Lagrange.nodal G id)
      (r := r - 1) (k := s + 1) (n := n) (by omega) (by omega) (by omega)
      (natDegree_map_le.trans hn) hprim hz Lagrange.nodal_ne_zero (by simpa only [show s+1+1=s+2 by omega,Nat.mul_comm,hdeg] using htwist)
      (by rwa [Bivariate.swap_swap_apply, hpdeg]) (by rwa [Bivariate.swap_swap_apply, hpdeg])
      hmeas h0
    simpa only [hr', hs'] using h1
  refine ⟨Q, B, hQ, hB, hdeg ▸ hbc, ?_⟩
  rw [reindex_forward D hD] at h0
  have eq := congrArg Bivariate.swap h0
  have hnod : Bivariate.swap (C (Lagrange.nodal G id)) =
      Lagrange.nodal G (C : K →+* K[X]) := by
    rw [← swap_nodal G, Bivariate.swap_swap_apply]
  simpa only [map_mul, map_add, map_pow, Bivariate.swap_map_C, hnod, Bivariate.swap_swap_apply]
    using eq

#print axioms small_interpolation_weak
end ProximityGap.ApolarBorderCoordinates
