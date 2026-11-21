/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.IntegralOrdinaryPolars
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusSections

/-! # Ordinary polar gcd on actual selected sections of a terminal cubic -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeActualPolarGcd

open Polynomial Finset SecondPrimeMobiusSections
open SecondPrimeCoordinateWeight IntegralOrdinaryPolars

variable {K : Type} [Field K]

/-- The chart in the coefficient order scalar Z, coordinate X, and ordinate Y. -/
noncomputable def rawChart (r : K) (W d : ℕ) (f : K[X][X][X]) : K[X][X][X] :=
  (surfaceChart r W d f).map Bivariate.swap.toRingHom

/-- The actual curve over the scalar function field. -/
noncomputable def fieldChart (r : K) (W d : ℕ) (f : K[X][X][X]) : (RatFunc K)[X][X] :=
  (rawChart r W d f).map (mapRingHom (algebraMap K[X] (RatFunc K)))

private theorem coordinate_support (r : K) (d : ℕ) (f : K[X][X][X]) (j : ℕ)
    (hn : (rawChart r (weight d f) d f).coeff j ≠ 0) :
    ((rawChart r (weight d f) d f).coeff j).natDegree + d * j ≤ weight d f := by
  let W := weight d f
  let F := surfaceChart r W d f
  have hF : F.coeff j ≠ 0 := fun he => hn (by
    rw [rawChart, coeff_map, show (surfaceChart r W d f).coeff j = 0 from he, map_zero])
  obtain ⟨i, hi, htop, _⟩ := Bivariate.exists_max_index_degreeX (F.coeff j) hF
  have hp := (scalar_value_support r W d f j i).mp (mem_support_iff.mp hi)
  have hw := coeff_weight_le d f (leadingCoeff_ne_zero.mpr hp)
  change ((f.coeff j).coeff i).natDegree + j * d ≤ W at hw
  have hc := chart_degree_le r (W - j * d) ((f.coeff j).coeff i) (by omega)
  rw [rawChart, coeff_map]
  change (Bivariate.swap (F.coeff j)).natDegree + d * j ≤ W
  rw [show (Bivariate.swap (F.coeff j)).natDegree = Bivariate.degreeX (F.coeff j) from
    Bivariate.natDegreeY_swap _, ← htop]
  change (((surfaceChart r W d f).coeff j).coeff i).natDegree + d * j ≤ W
  rw [surface_coeff, Nat.mul_comm d j]
  omega

private theorem scalar_support (r : K) (W d : ℕ) (f : K[X][X][X])
    (hs : WeightedSylvesterDegree.TotalDegreeLe f 34) (j : ℕ)
    (hn : (rawChart r W d f).coeff j ≠ 0) :
    Bivariate.degreeX ((rawChart r W d f).coeff j) + j ≤ 34 := by
  let F := surfaceChart r W d f
  have hF : F.coeff j ≠ 0 := fun he => hn (by
    rw [rawChart, coeff_map, show (surfaceChart r W d f).coeff j = 0 from he, map_zero])
  have hc := (scalar_value_support r W d f j _).mp (leadingCoeff_ne_zero.mpr hF)
  have hj : f.coeff j ≠ 0 := fun he => hc (by simp [he])
  rw [rawChart, coeff_map]
  change Bivariate.degreeX (Bivariate.swap (F.coeff j)) + j ≤ _
  rw [Bivariate.degreeX_swap]
  exact (Nat.add_le_add_right (le_natDegree_of_ne_zero hc) j).trans (hs j hj)

private theorem value_bound (r : K) (W d : ℕ) (f : K[X][X][X]) (hb : f.natDegree = 3) :
    (rawChart r W d f).natDegree ≤ 3 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj' : f.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [rawChart, coeff_map]
  change Bivariate.swap ((surfaceChart r W d f).coeff j) = 0
  suffices he : (surfaceChart r W d f).coeff j = 0 by rw [he, map_zero]
  ext1 i
  rw [surface_coeff, hj', coeff_zero, map_zero]

private theorem chart_fiber (r z : K) (W d : ℕ) (f : K[X][X][X]) :
    (rawChart r W d f).map (mapRingHom (evalRingHom z)) =
    (surfaceChart r W d f).map (evalRingHom (C z)) := by
  ext1 j
  simp only [rawChart, coeff_map, coe_mapRingHom, coe_evalRingHom]
  change (Bivariate.swap _).map (evalRingHom z) = ((surfaceChart r W d f).coeff j).eval (C z)
  simpa only [Bivariate.evalY, Bivariate.evalX_eq_map] using
    (Bivariate.evalY_eq_evalX_swap z ((surfaceChart r W d f).coeff j)).symm

private theorem gcd_to_functionField (A B : K[X][X]) (hA : A ≠ 0) :
    open scoped Classical in
    OrdinaryPolarGcdBudget.genericDegree A B ≤
      (GCDMonoid.gcd (A.map (algebraMap K[X] (RatFunc K)))
        (B.map (algebraMap K[X] (RatFunc K)))).natDegree := by
  classical
  let F := FractionRing K[X]
  let φ := algebraMap K[X] F
  let ψ := algebraMap K[X] (RatFunc K)
  let θ := (FractionRing.algEquiv K[X] (RatFunc K)).toRingEquiv.toRingHom
  let g := GCDMonoid.gcd (A.map φ) (B.map φ)
  have comp : θ.comp φ = ψ := RingHom.ext (fun x =>
    (FractionRing.algEquiv K[X] (RatFunc K)).commutes x)
  have hd (P : K[X][X]) (hp : g ∣ P.map φ) : g.map θ ∣ P.map ψ := by
    have h := map_dvd (mapRingHom θ) hp
    simpa only [coe_mapRingHom, Polynomial.map_map, comp] using h
  have hne := (Polynomial.map_injective ψ (RatFunc.algebraMap_injective K)).ne hA
  have hdeg := natDegree_le_of_dvd (dvd_gcd (hd A (gcd_dvd_left ..)) (hd B (gcd_dvd_right ..)))
    (gcd_ne_zero_of_left (by simpa using hne))
  simpa only [natDegree_map_eq_of_injective θ.injective, g, F, φ, ψ,
    OrdinaryPolarGcdBudget.genericDegree] using hdeg

variable {F : Type} [Field F]

/-- On the common chart of a genuine terminal cubic, any two nonzero ordinary polar
resultants share the square divisors supplied by the retained simple sections.
The center and selected labels are inputs from `actual_cubic_chart`. -/
theorem gcd_of_cubic_chart (σ : F →+* K) (f : K[X][X][X]) (r : K) (W : ℕ)
    (hW : W = weight 67108863 f) (hlo : 201326589 ≤ W) (hhi : W ≤ 290805098)
    (hb : f.natDegree = 3) (htr : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (S : Finset F) (hs : 1342177085 ≤ S.card) (w : F → K[X])
    (hroot : ∀ z ∈ S, (surfaceChart r W 67108863 f).eval₂ (evalRingHom (C (σ z))) (w z) = 0)
    (hder : ∀ z ∈ S, ((surfaceChart r W 67108863 f).derivative.eval₂ (evalRingHom (C (σ z)))
      (w z)).natDegree = W - 67108863) (c₁ c₂ : K)
    (hA : polarResultant (fieldChart r W 67108863 f) (RatFunc.C c₁) ≠ 0)
    (hB : polarResultant (fieldChart r W 67108863 f) (RatFunc.C c₂) ≠ 0) :
    open scoped Classical in
    2 * (W - 67108863) ≤ (GCDMonoid.gcd
      (polarResultant (fieldChart r W 67108863 f) (RatFunc.C c₁))
      (polarResultant (fieldChart r W 67108863 f) (RatFunc.C c₂))).natDegree + 201 := by
  classical
  let d := 67108863
  let P := rawChart r W d f
  let φ := algebraMap K[X] (RatFunc K)
  let L := S.map (⟨σ, σ.injective⟩ : F ↪ K)
  let q := Function.extend σ w (fun _ => 0)
  have hLS : 1342177085 ≤ L.card := by simpa only [L, card_map] using hs
  have hq (z : F) : q (σ z) = w z := σ.injective.extend_apply _ _ _
  have hsec (z) (hz : z ∈ L) :
      (P.map (mapRingHom (evalRingHom z))).eval (q z) = 0 ∧
      ((P.map (mapRingHom (evalRingHom z))).derivative.eval (q z)).natDegree = W - d := by
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hz
    change ((rawChart r W d f).map (mapRingHom (evalRingHom (σ x)))).eval (q (σ x)) = 0 ∧
      (((rawChart r W d f).map (mapRingHom (evalRingHom (σ x)))).derivative.eval
        (q (σ x))).natDegree = W - d
    rw [hq, chart_fiber, derivative_map, eval_map, eval_map]
    exact ⟨hroot x hx, hder x hx⟩
  let A := polarResultant P (C c₁)
  let B := polarResultant P (C c₂)
  have ham (c : K) : (polarResultant P (C c)).map φ =
      polarResultant (fieldChart r W d f) (RatFunc.C c) := by
    rw [map_resultant]
    rfl
  have ha : A ≠ 0 := fun he => hA (by
    rw [← ham, show polarResultant P (C c₁) = 0 from he, Polynomial.map_zero])
  have hB' : B ≠ 0 := fun he => hB (by
    rw [← ham, show polarResultant P (C c₂) = 0 from he, Polynomial.map_zero])
  have H := supported_gcd_lower P c₁ c₂ W hlo hhi (value_bound r W d f hb)
    (by subst W; exact coordinate_support r d f) (scalar_support r W d f htr) ha hB' L hLS q
    (fun z hz => (hsec z hz).1) (fun z hz => (hsec z hz).2)
  have H' := gcd_to_functionField A B ha
  have hfinal := H.trans (Nat.add_le_add_right H' 201)
  change 2 * (W - d) ≤ (GCDMonoid.gcd ((polarResultant P (C c₁)).map φ)
    ((polarResultant P (C c₂)).map φ)).natDegree + 201 at hfinal
  rw [ham, ham] at hfinal
  dsimp only [d] at hfinal
  exact hfinal

end ArkLib.ProximityGap.Frontier.SecondPrimeActualPolarGcd
