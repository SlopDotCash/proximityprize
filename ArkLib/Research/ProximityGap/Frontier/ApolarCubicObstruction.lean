/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarParameterTransition
import ArkLib.Research.ProximityGap.Frontier.ApolarCoordinateEquations
import ArkLib.Research.ProximityGap.Frontier.ApolarFixedTarget
import ArkLib.Research.ProximityGap.Frontier.ApolarInverseCoordinates
import ArkLib.Research.ProximityGap.Frontier.ApolarUnitChartSpecialization

/-! # The cubic obstruction for a moving apolar pencil

At a negative parameter twist, interpolation in the two parameter charts
forces the primitive locator to divide the fixed vanisher times the cube
of its divided polynomial. Minimality rules out that divisibility.
-/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.ApolarCubicObstruction

open ApolarDividedLocator ApolarDividedPolynomial ApolarParameterTransition
open ApolarSyndromeInterpolation ApolarChartDescent ApolarCoordinateEquations
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts
open ArkLib.ProximityGap.Frontier.ApolarFixedTarget

variable {K : Type*} [Field K]

/-- The parameter degree of the locator is attained by any nonzero coordinate
coefficient having maximal parameter degree. -/
theorem parameter_degree (f : K[X][X]) {l j : ℕ}
    (h : ∀ i, (f.coeff i).natDegree ≤ l) (hj : (f.coeff j).natDegree = l)
    (hn : f.coeff j ≠ 0) : (Bivariate.swap f).natDegree = l := by
  apply le_antisymm (degree_swap f l h)
  apply le_natDegree_of_ne_zero
  intro hz
  have he := congrArg (fun q : K[X] => q.coeff j) hz
  rw [swap_coeff, ← hj, coeff_natDegree, coeff_zero] at he
  exact hn (leadingCoeff_eq_zero.mp he)

/-- Reversing the parameter preserves the coordinate degree, irrespective
of the constant and leading coefficient in the parameter. -/
theorem reverse_coordinate_degree (f : K[X][X]) (l : ℕ) :
    (reverseCoeffs l f).natDegree = f.natDegree := by
  have bound (p : K[X][X]) : (reverseCoeffs l p).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [coeff_eq_zero_of_natDegree_lt hj]
  have inv : reverseCoeffs l (reverseCoeffs l f) = f := by
    ext j
    simp only [coeff_reverseCoeffs, reflect_reflect]
  have back := bound (reverseCoeffs l f)
  rw [inv] at back
  exact le_antisymm (bound f) back

/-- The coordinate twist forces the interpolation remainder to have degree below the
locator degree at an arbitrary power. -/
theorem coordinate_small_power (power : ℕ) [IsAlgClosed K] {J : Type*}
    (D : Finset J) (y : J → K[X]ˣ) (w : J → K[X])
    (f V B B' Q Q' : K[X][X]) (S : K[X]) {r k n : ℕ}
    (hr : 0 < f.natDegree) (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hfree : ∀ t : K, f.map (evalRingHom t) ≠ 0) (hz : f.coeff 0 ≠ 0) (hS : S ≠ 0)
    (hsize : n < (k + 1) * power + f.natDegree)
    (hb : (Bivariate.swap B).natDegree < (Bivariate.swap f).natDegree)
    (hb' : (Bivariate.swap B').natDegree < (Bivariate.swap f).natDegree)
    (ha : ApolarThrough (ApolarRootTransition.measure D (fun i => (y i : K[X])) w) f (k - 1))
    (h0 : V * (representative D (fun i => (y i : K[X])) w f)^power = f * Q + C S * B)
    (h1 : reflect n V * (-representative D (fun i => (↑(y i)⁻¹ : K[X]))
      (fun i => w i * (y i : K[X])^(r + k)) (reflect (r + 1) f))^power =
      reflect (r + 1) f * Q' + C S * B') : B.natDegree < f.natDegree := by
  apply small_degree_from_cleared f B B' hr hsize hb hb'
  intro b c he
  exact power_congruence power D y w f V B B' Q Q' S hk hf hV hfree hz hS le_rfl he ha h0 h1

/-- A pair of coordinate identities makes its remainder strictly shorter in
the coordinate variable, even when the coordinate twist is negative. -/
theorem coordinate_small [IsAlgClosed K] {J : Type*}
    (D : Finset J) (y : J → K[X]ˣ) (w : J → K[X])
    (f V B B' Q Q' : K[X][X]) (S : K[X]) {r k n : ℕ}
    (hr : 0 < f.natDegree) (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hfree : ∀ t : K, f.map (evalRingHom t) ≠ 0) (hz : f.coeff 0 ≠ 0) (hS : S ≠ 0)
    (hsize : n < (k + 1) * 3 + f.natDegree)
    (hb : (Bivariate.swap B).natDegree < (Bivariate.swap f).natDegree)
    (hb' : (Bivariate.swap B').natDegree < (Bivariate.swap f).natDegree)
    (ha : ApolarThrough (ApolarRootTransition.measure D (fun i => (y i : K[X])) w) f (k - 1))
    (h0 : V * (representative D (fun i => (y i : K[X])) w f)^3 = f * Q + C S * B)
    (h1 : reflect n V * (-representative D (fun i => (↑(y i)⁻¹ : K[X]))
      (fun i => w i * (y i : K[X])^(r + k)) (reflect (r + 1) f))^3 =
      reflect (r + 1) f * Q' + C S * B') : B.natDegree < f.natDegree :=
  coordinate_small_power 3 D y w f V B B' Q Q' S hr hk hf hV hfree hz hS hsize hb hb' ha h0 h1

private theorem nodal_congr {J : Type*} (G : Finset J) (a b : J → K[X])
    (h : ∀ t ∈ G, a t = b t) : Lagrange.nodal G a = Lagrange.nodal G b := by
  apply Finset.prod_congr rfl
  intro t ht
  rw [h t ht]

/-- At a negative parameter twist the two chart relations force the moving locator to
divide the fixed vanisher, contradicting generic coprimality. -/
theorem card_le_of_small_power (power : ℕ) [IsAlgClosed K] [DecidableEq K]
    (D G : Finset K) (w : K → K[X]) (f : K[X][X]) (V : K[X]) {l j : ℕ}
    (h0G : 0 ∉ G) (hV : V ≠ 0) (hw : ∀ i ∈ D, (w i).natDegree ≤ 1)
    (hf : ∀ i, (f.coeff i).natDegree ≤ l) (hmov : 0 < (f.coeff j).natDegree)
    (hfree : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X]))))
    (Q Qt B Bt : K[X][X]) (hQt : Qt.natDegree < G.card) (hBt : Bt.natDegree < l)
    (hb : (Bivariate.swap B).natDegree < f.natDegree)
    (hbt : (Bivariate.swap Bt).natDegree < f.natDegree)
    (hforward : C V * (Bivariate.swap (representative D C w f))^power =
      Bivariate.swap f * Q + Lagrange.nodal G C * B)
    (hback : C V * (Bivariate.swap (representative D C (fun i => reflect 1 (w i))
      (reverseCoeffs l f)))^power =
      Bivariate.swap (reverseCoeffs l f) * Qt +
        Lagrange.nodal (G.image Inv.inv) C * Bt) : G.card ≤ power * (l + 1) := by
  classical
  by_contra! hmany
  let site (t : K) : K[X]ˣ := Units.map (C : K →+* K[X]).toMonoidHom
    (if h : t = 0 then 1 else Units.mk0 t h)
  have hs (t : K) (ht : t ∈ G) : (site t : K[X]) = C t := by
    have hn : t ≠ 0 := fun he => h0G (he ▸ ht)
    simp [site, hn]
  have hsi (t : K) (ht : t ∈ G) : (↑(site t)⁻¹ : K[X]) = C t⁻¹ := by
    have hn : t ≠ 0 := fun he => h0G (he ▸ ht)
    simp [site, hn]
  have hfwd := hforward
  rw [← nodal_congr G _ _ hs] at hfwd
  rw [nodal_inverse_image, ← nodal_congr G _ _ hsi] at hback
  have hg (i : K) (hi : i ∈ G) : (Bivariate.swap f).eval (site i : K[X]) ≠ 0 := by
    rw [hs i hi, eval_swap]
    exact hfree i
  let a := G.card - power * (l + 1)
  have ha : G.card = power * (l + 1) + a := by dsimp [a]; omega
  have hd := cleared_power_remainders power G site D w f V l (l - 1) a Q Qt B Bt ha hw hf
    (by omega) (by omega) hg hfwd hback
  obtain ⟨hb0, _⟩ := vanish_of_cleared f B Bt (∏ i ∈ G, -(site i))⁻¹
    (by dsimp [a]; omega : 0 < a) hb hbt (by omega : Bt.natDegree ≤ l - 1) hd
  rw [hb0, mul_zero, add_zero] at hforward
  have he := congrArg Bivariate.swap hforward
  simp only [map_mul, map_pow, Bivariate.swap_C, Bivariate.swap_swap_apply] at he
  exact not_dvd_fixed_mul_pow f (representative D C w f) V hV hfree j hmov hc power ⟨_, he⟩

/-- Contradiction at strictly more than three times the parameter weight.
The two interpolation remainders have already been bounded in the coordinate
variable, and the second one has also been bounded in the parameter. -/
theorem card_le_of_small [IsAlgClosed K] [DecidableEq K]
    (D G : Finset K) (w : K → K[X]) (f : K[X][X]) (V : K[X]) {l j : ℕ}
    (h0G : 0 ∉ G) (hV : V ≠ 0) (hw : ∀ i ∈ D, (w i).natDegree ≤ 1)
    (hf : ∀ i, (f.coeff i).natDegree ≤ l) (hmov : 0 < (f.coeff j).natDegree)
    (hfree : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X]))))
    (Q Qt B Bt : K[X][X]) (hQt : Qt.natDegree < G.card) (hBt : Bt.natDegree < l)
    (hb : (Bivariate.swap B).natDegree < f.natDegree)
    (hbt : (Bivariate.swap Bt).natDegree < f.natDegree)
    (hforward : C V * (Bivariate.swap (representative D C w f))^3 =
      Bivariate.swap f * Q + Lagrange.nodal G C * B)
    (hback : C V * (Bivariate.swap (representative D C (fun i => reflect 1 (w i))
      (reverseCoeffs l f)))^3 =
      Bivariate.swap (reverseCoeffs l f) * Qt +
        Lagrange.nodal (G.image Inv.inv) C * Bt) : G.card ≤ 3 * (l + 1) :=
  card_le_of_small_power 3 D G w f V h0G hV hw hf hmov hfree hc Q Qt B Bt hQt hBt hb hbt hforward hback

open ApolarInverseCoordinates ApolarUnitChartSpecialization

/-- If the original parameter-zero fiber is nonzero, the reciprocal locator
attains its full parameter degree. -/
theorem reverse_parameter_degree (f : K[X][X]) (l : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ l) (h0 : f.map (evalRingHom 0) ≠ 0) :
    (Bivariate.swap (reverseCoeffs l f)).natDegree = l := by
  rw [swap_reverse]
  apply le_antisymm (natDegree_reflect_le.trans (max_le le_rfl (degree_swap f l hf)))
  apply le_natDegree_of_ne_zero
  intro h
  rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self] at h
  apply h0
  have eq := eval_swap f 0
  simpa only [map_zero, ← coeff_zero_eq_eval_zero, h] using eq.symm

/-- Bound the interpolation remainders in both variables for an arbitrary positive power. -/
theorem small_power_interpolation (power : ℕ) (hpower : 0 < power) [IsAlgClosed K] [DecidableEq K]
    (D G : Finset K) (w : K → K[X]) (f : K[X][X]) (V : K[X]) {l r s n : ℕ}
    (hD : 0 ∉ D) (hG : G.Nonempty) (hl : 0 < l) (hr : 0 < r) (hdeg : f.natDegree = r)
    (hpdeg : (Bivariate.swap f).natDegree = l) (hV : Lagrange.nodal D id ∣ V)
    (hn : V.natDegree ≤ n) (htwist : n < power * (s + 2) + r)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l)
    (hz : f.coeff 0 ≠ 0) (hprim : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hm : power * (l + 1) < G.card + l)
    (ha : ApolarThrough (ApolarRootTransition.measure D C w) f s)
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ s + 1 ∧ ∃ v : K → K, ∀ p : K[X],
      p.natDegree ≤ r + s → weighted D (RingHom.id K) (fun i => (w i).eval t) p =
        weighted E (RingHom.id K) v p) :
    ∃ Q B : K[X][X], Q.natDegree < G.card ∧ B.natDegree < l ∧
      (Bivariate.swap B).natDegree < r ∧
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
  have hbc : (Bivariate.swap B).natDegree < f.natDegree := by
    apply coordinate_small_power power D coordinateUnit w f (V.map C) (Bivariate.swap B) (Bivariate.swap Bi)
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

/-- Interpolation quotient and remainder on one parameter chart, after applying
both coordinate charts. -/
theorem small_interpolation [IsAlgClosed K] [DecidableEq K]
    (D G : Finset K) (w : K → K[X]) (f : K[X][X]) (V : K[X]) {l r s n : ℕ}
    (hD : 0 ∉ D) (hG : G.Nonempty) (hl : 0 < l) (hr : 0 < r) (hdeg : f.natDegree = r)
    (hpdeg : (Bivariate.swap f).natDegree = l) (hV : Lagrange.nodal D id ∣ V)
    (hn : V.natDegree ≤ n) (htwist : n < 3 * (s + 2) + r)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l)
    (hz : f.coeff 0 ≠ 0) (hprim : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hm : 3 * (l + 1) < G.card + l)
    (ha : ApolarThrough (ApolarRootTransition.measure D C w) f s)
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ s + 1 ∧ ∃ v : K → K, ∀ p : K[X],
      p.natDegree ≤ r + s → weighted D (RingHom.id K) (fun i => (w i).eval t) p =
        weighted E (RingHom.id K) v p) :
    ∃ Q B : K[X][X], Q.natDegree < G.card ∧ B.natDegree < l ∧
      (Bivariate.swap B).natDegree < r ∧
      C V * (Bivariate.swap (representative D C w f))^3 =
        Bivariate.swap f * Q + Lagrange.nodal G C * B :=
  small_power_interpolation 3 (by decide) D G w f V hD hG hl hr hdeg hpdeg hV hn htwist hw hf hz hprim hm ha hsp

/-- A moving primitive locator has at most power times its parameter weight in sparse
fibers when the coordinate twist lies below its degree. -/
theorem card_le_power (power : ℕ) (hpower : 0 < power) [IsAlgClosed K] [DecidableEq K] (D G : Finset K)
    (w : K → K[X]) (f : K[X][X]) {r d l : ℕ} (hr : 0 < r) (hrd : r ≤ d) (hl : 0 < l)
    (hdeg : f.natDegree = r) (htop : (f.coeff r).natDegree = l) (hz : f.coeff 0 ≠ 0)
    (hf : ∀ j, (f.coeff j).natDegree ≤ l) (hprim : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hD : 0 ∉ D) (hG : 0 ∉ G) (hne : G.Nonempty)
    (htwist : D.card < power * (d + 2 - r) + r)
    (ha : ApolarThrough (ApolarRootTransition.measure D C w) f (d - r))
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X]))))
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ d - r + 1 ∧ ∃ v : K → K, ∀ p : K[X],
      p.natDegree ≤ d → weighted D (RingHom.id K) (fun i => (w i).eval t) p =
        weighted E (RingHom.id K) v p) :
    G.card ≤ power * (l + 1) := by
  classical
  by_contra! hmany
  have htop0 : f.coeff r ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at htop
    omega
  let V := Lagrange.nodal D id
  have hV : V.natDegree ≤ D.card := Lagrange.natDegree_nodal.le
  have htw : D.card < power * (d - r + 2) + r := by rwa [show d-r+2=d+2-r by omega]
  have hrs : r + (d - r) = d := by omega
  have hpdeg := parameter_degree f hf htop htop0
  obtain ⟨Q, B, _, _, hb, hforward⟩ := small_power_interpolation power hpower D G w f V
    hD hne hl hr hdeg hpdeg (dvd_refl V) hV htw hw hf hz hprim (by omega) ha
    (by simpa only [hrs] using hsp)
  let Gt := G.image Inv.inv
  let ft := reverseCoeffs l f
  let wt := fun i => reflect 1 (w i)
  have hgcard : Gt.card = G.card := card_image_of_injective _ inv_injective
  have hft (j : ℕ) : (ft.coeff j).natDegree ≤ l :=
    natDegree_reflect_le.trans (max_le le_rfl (hf j))
  have hwt (i : K) (hi : i ∈ D) : (wt i).natDegree ≤ 1 :=
    natDegree_reflect_le.trans (max_le le_rfl (hw i hi))
  have hf0 : ft.coeff 0 ≠ 0 := by
    intro h
    have hu := congrArg (reflect l) h
    apply hz
    simpa only [ft, coeff_reverseCoeffs, reflect_reflect, reflect_zero] using hu
  have htprim := reverse_fibers_nonzero f l hf ⟨r, htop, htop0⟩ hprim
  have hrev := reciprocal_sparse_family D G w d (d - r + 1) hG hw hsp
  obtain ⟨Qt, Bt, hQt, hBt, hbt, hback⟩ := small_power_interpolation power hpower D Gt wt ft V
    hD (hne.image _) hl hr ((reverse_coordinate_degree f l).trans hdeg)
    (reverse_parameter_degree f l hf (hprim 0)) (dvd_refl V) hV htw hwt hft hf0 htprim
    (by omega) (apolar_parameter_reverse D w f l (d - r) hw hf ha)
    (by simpa only [hrs] using hrev)
  rw [hgcard] at hQt
  exact hmany.not_ge (card_le_of_small_power power D G w f V hG Lagrange.nodal_ne_zero hw hf
    (htop ▸ hl) hprim hc Q Qt B Bt hQt hBt (hdeg.symm ▸ hb) (hdeg.symm ▸ hbt) hforward hback)

/-- A primitive moving locator with generic coprime divided polynomial has at
most three times its parameter weight in sparse fibers. -/
theorem card_le [IsAlgClosed K] [DecidableEq K] (D G : Finset K)
    (w : K → K[X]) (f : K[X][X]) {r d l : ℕ} (hr : 0 < r) (hrd : r ≤ d) (hl : 0 < l)
    (hdeg : f.natDegree = r) (htop : (f.coeff r).natDegree = l) (hz : f.coeff 0 ≠ 0)
    (hf : ∀ j, (f.coeff j).natDegree ≤ l) (hprim : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hD : 0 ∉ D) (hG : 0 ∉ G) (hne : G.Nonempty)
    (htwist : D.card < 3 * (d + 2 - r) + r)
    (ha : ApolarThrough (ApolarRootTransition.measure D C w) f (d - r))
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X]))))
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ d - r + 1 ∧ ∃ v : K → K, ∀ p : K[X],
      p.natDegree ≤ d → weighted D (RingHom.id K) (fun i => (w i).eval t) p =
        weighted E (RingHom.id K) v p) :
    G.card ≤ 3 * (l + 1) :=
  card_le_power 3 (by decide) D G w f hr hrd hl hdeg htop hz hf hprim hw hD hG hne htwist ha hc hsp

#print axioms card_le_power
#print axioms card_le
#print axioms parameter_degree
#print axioms coordinate_small
#print axioms card_le_of_small
end ProximityGap.ApolarCubicObstruction
