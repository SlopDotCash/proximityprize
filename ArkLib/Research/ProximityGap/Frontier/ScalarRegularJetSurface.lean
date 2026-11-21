/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicQuotientWindow

/-! # Removing scalar factors without losing rich interpolation sections -/

set_option autoImplicit false
noncomputable section
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.ScalarRegularJetSurface
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation SecondPrimeDegreeSevenDimension
open JetMultiplierGraph IntrinsicReceivedSections IntrinsicCubicQuotientWindow
open QuarticIntrinsicAuxiliary TerminalQuarticHessianTransport SecondPrimeCoordinateWeight

variable {F I : Type} [Field F] {s v d T r : ℕ}

private theorem permute_surface (c : Monomials s v d T → F) : permute (surface c) = sectionMap c := by
  rw [← permute_section]
  apply Polynomial.ext
  intro j
  rw [permute_coeff,permute_coeff,Bivariate.swap_swap_apply]

private theorem jet_surface (c : Monomials s v d T → F) (i j : ℕ) (x a b : F) :
    ((shift (permute (surface c)) (C x) (received a b)).coeff j).coeff i =
      ∑ m, C (c m)*jetTerm m i j x a b := by
  rw [permute_surface]
  change ((shift (∑ m : Monomials s v d T, monomial m.1.val
    (monomial m.2.2.val (monomial m.2.1.val (c m)))) (C x) (received a b)).coeff j).coeff i = _
  simp only [shift,map_sum,Polynomial.map_sum,finsetSum_coeff]
  apply sum_congr rfl
  intro m _
  change ((shift (monomial m.1.val (monomial m.2.2.val (monomial m.2.1.val (c m))))
    (C x) (received a b)).coeff j).coeff i = _
  rw [coeff_shift_monomial]
  simp only [jetTerm,received,← C_mul_X_pow_eq_monomial,map_mul,map_pow,map_natCast]
  ring

private def scalarFactor (z : F) : F[X][X][X] := C (Polynomial.X-C (C z))

private theorem factor_ne (z : F) : scalarFactor z ≠ 0 := by
  unfold scalarFactor
  exact C_ne_zero.mpr (X_sub_C_ne_zero _)

private theorem shift_factor (z : F) (R : F[X][X][X]) (i j : ℕ) (x a b : F) :
    ((shift (permute (scalarFactor z*R)) (C x) (received a b)).coeff j).coeff i =
      (Polynomial.X-C z)*((shift (permute R) (C x) (received a b)).coeff j).coeff i := by
  have he : permute (scalarFactor z) = C (C (Polynomial.X-C z)) := by
    simp [scalarFactor,permute,Polynomial.mapEquiv_apply,Bivariate.swap_Y,Bivariate.swap_C_C]
  simp only [map_mul,he,shift,taylor_mul,taylor_C,Polynomial.map_mul,map_C,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe,taylorAlgHom_apply,coeff_C_mul]

/-- Scalar factors can be stripped in the polynomial jet identities. The resulting
surface retains the support and all jets at all labels, and no scalar fiber is identically zero. -/
theorem normalize (dom : I ↪ F) (u v₁ : I → F) (hT : 0 < T)
    (c : Monomials s v d T → F) (hc : c ≠ 0)
    (hjets : ∀ x i j, i+j<r → ∑ m, C (c m)*jetTerm m i j (dom x) (u x) (v₁ x) = 0) :
    ∃ (s' : ℕ) (b : Monomials s' v d T → F), s' ≤ s ∧ b ≠ 0 ∧
      (∀ x i j, i+j<r → ∑ m, C (b m)*jetTerm m i j (dom x) (u x) (v₁ x) = 0) ∧
      ∀ z : F, (surface b).map (evalRingHom (C z)) ≠ 0 := by
  classical
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hgood : ∀ z : F, (surface c).map (evalRingHom (C z)) ≠ 0
    · exact ⟨s,c,le_rfl,hc,hjets,hgood⟩
    push Not at hgood
    obtain ⟨z,hz⟩ := hgood
    have hd : scalarFactor z ∣ surface c := by
      apply (C_dvd_iff_dvd_coeff ..).mpr
      intro j
      apply dvd_iff_isRoot.mpr
      simpa only [IsRoot,coeff_map,coe_evalRingHom,coeff_zero] using
        congrArg (fun p : F[X][X] => p.coeff j) hz
    obtain ⟨R,hR⟩ := hd
    have hQ := surface_ne_zero hc
    have hRn : R ≠ 0 := fun e => hQ (by simp [hR,e])
    have hcoeff (j : ℕ) (hjr : R.coeff j ≠ 0) :
        (R.coeff j).natDegree+1+j ≤ s ∧ j ≤ v := by
      have he : (surface c).coeff j = (Polynomial.X-C (C z))*(R.coeff j) := by rw [hR,scalarFactor,coeff_C_mul]
      have hn : (surface c).coeff j ≠ 0 := he ▸ mul_ne_zero (X_sub_C_ne_zero _) hjr
      have h₁ := leadingCoeff_ne_zero.mpr hn
      have h₂ := leadingCoeff_ne_zero.mpr h₁
      have hs := surface_support c h₂
      rw [he,natDegree_mul (X_sub_C_ne_zero _) hjr,natDegree_X_sub_C] at hs
      omega
    have hw := weight_le_of_coeff d (surface c) (W:=T-1)
      (fun j i a hh => by have := (surface_support c hh).2.2; omega)
    rw [hR,weight_mul _ _ _ (factor_ne z) hRn] at hw
    have hs0 := (hcoeff R.natDegree (leadingCoeff_ne_zero.mpr hRn)).1
    obtain ⟨b,hb⟩ := exists_coefficients_of_support (s:=s-1) (v:=v) (d:=d) (t:=T) R (by
      intro j i a hna
      have hi : (R.coeff j).coeff i ≠ 0 := fun e => hna (by simp [e])
      have hj : R.coeff j ≠ 0 := fun e => hi (by simp [e])
      have hup := hcoeff j hj
      have hvar := le_natDegree_of_ne_zero hi
      have hwt := coeff_weight_le d R hna
      omega)
    have hbn : b ≠ 0 := by
      intro e
      apply hRn
      rw [← hb,e]
      exact SecondPrimeDegreeSevenDimension.surfaceLinear.map_zero
    have hjet (x i j) (h : i+j<r) : ∑ m, C (b m)*jetTerm m i j (dom x) (u x) (v₁ x) = 0 := by
      have he := hjets x i j h
      rw [← jet_surface,hR,shift_factor,← hb,jet_surface] at he
      exact (mul_eq_zero.mp he).resolve_left (X_sub_C_ne_zero z)
    obtain ⟨s',c',hs',hrest⟩ := ih (s-1) (by omega) b hbn hjet
    exact ⟨s',c',by omega,hrest⟩

#print axioms normalize
end ArkLib.ProximityGap.Frontier.ScalarRegularJetSurface
