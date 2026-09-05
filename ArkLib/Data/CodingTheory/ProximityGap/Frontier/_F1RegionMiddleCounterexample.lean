/-
Copyright (c) 2026 Leo Guinan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Guinan
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._F1RegionSyzygyInterface --#git-secret-ignore
import Mathlib.Tactic.LinearCombination

/-!
# F1 — a `ZMod 23` counterexample to the region middle exclusion

This file gives an explicit region/syzygy configuration at profile
`(a,b,c,t,k,δ₁) = (6,6,6,4,11,7)`. Its minimal product-degree is seven, placing it in the
middle band and refuting `RegionMiddleExclusion (ZMod 23)`.

The result is confined to the region/syzygy interface. It does not construct a genuine
over-budget MCA stack, discharge the SYZ42/SYZ28 lift gate, or determine production `δ*`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.F1RegionSyzygy

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

instance prime23Fact : Fact (Nat.Prime 23) := ⟨by norm_num⟩

private abbrev F23 := ZMod 23

private def omega23 : Finset F23 := Finset.univ.erase 0
private def SAB23 : Finset F23 := {1, 6, 7, 10, 15, 21}
private def SAC23 : Finset F23 := {3, 8, 11, 12, 16, 18}
private def SBC23 : Finset F23 := {2, 5, 9, 13, 14, 17}
private def T23 : Finset F23 := {4, 19, 20, 22}

private noncomputable def WAB23 : F23[X] :=
  C 4 + C 18 * X + C 12 * X ^ 2 + C 8 * X ^ 3 + C 17 * X ^ 4 + C 9 * X ^ 5 + X ^ 6

private noncomputable def WAC23 : F23[X] :=
  C 20 + C 7 * X + C 13 * X ^ 2 + C 12 * X ^ 3 + C 13 * X ^ 4 + X ^ 5 + X ^ 6

private noncomputable def WBC23 : F23[X] :=
  C 22 + C 15 * X + C 15 * X ^ 4 + C 9 * X ^ 5 + X ^ 6

private noncomputable def sAB23 : F23[X] := C 18 + C 17 * X
private noncomputable def sAC23 : F23[X] := C 2 + C 5 * X
private noncomputable def sBC23 : F23[X] := C 20 + X

private theorem F23_natCast_mod (n : ℕ) : (n : F23) = (n % 23 : ℕ) := by
  apply ZMod.val_injective
  simp [ZMod.val_natCast]

private theorem polynomial_natCast_mod (n : ℕ) :
    (n : F23[X]) = (n % 23 : ℕ) := by
  change C (n : F23) = C ((n % 23 : ℕ) : F23)
  exact congrArg (C : F23 → F23[X]) (F23_natCast_mod n)

private theorem polynomial_natCast_eq_of_mod_eq {n r : ℕ} (h : n % 23 = r) :
    (n : F23[X]) = (r : F23[X]) := by
  rw [polynomial_natCast_mod n, h]

private theorem polynomial_char23 : (23 : F23[X]) = 0 := by
  change C (23 : F23) = 0
  have h23 : (23 : F23) = 0 := by decide
  rw [h23, C_0]

private theorem vanishing_SAB23 : vanishing SAB23 = WAB23 := by
  classical
  simp only [vanishing, SAB23]
  repeat' rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, WAB23]
  ring_nf
  C_simp
  ring_nf
  have h0 : (132300 : F23[X]) = 4 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h1 : (201600 : F23[X]) = 5 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h2 : (83157 : F23[X]) = 12 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h3 : (15172 : F23[X]) = 15 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h4 : (1374 : F23[X]) = 17 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h5 : (60 : F23[X]) = 14 := polynomial_natCast_eq_of_mod_eq (by decide)
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination -(X + X ^ 3 + X ^ 5) * polynomial_char23

private theorem vanishing_SAC23 : vanishing SAC23 = WAC23 := by
  classical
  simp only [vanishing, SAC23]
  repeat' rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, WAC23]
  ring_nf
  C_simp
  ring_nf
  have h0 : (912384 : F23[X]) = 20 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h1 : (684864 : F23[X]) = 16 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h2 : (189096 : F23[X]) = 13 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h3 : (25702 : F23[X]) = 11 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h4 : (1853 : F23[X]) = 13 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h5 : (68 : F23[X]) = 22 := polynomial_natCast_eq_of_mod_eq (by decide)
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination -(X + X ^ 3 + X ^ 5) * polynomial_char23

private theorem vanishing_SBC23 : vanishing SBC23 = WBC23 := by
  classical
  simp only [vanishing, SBC23]
  repeat' rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, WBC23]
  ring_nf
  C_simp
  ring_nf
  have h0 : (278460 : F23[X]) = 22 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h1 : (283552 : F23[X]) = 8 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h2 : (100257 : F23[X]) = ((0 : ℕ) : F23[X]) :=
    polynomial_natCast_eq_of_mod_eq (n := 100257) (r := 0) (by decide)
  have h3 : (16652 : F23[X]) = ((0 : ℕ) : F23[X]) :=
    polynomial_natCast_eq_of_mod_eq (n := 16652) (r := 0) (by decide)
  have h4 : (1418 : F23[X]) = 15 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h5 : (60 : F23[X]) = 14 := polynomial_natCast_eq_of_mod_eq (by decide)
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination -(X + X ^ 5) * polynomial_char23

private theorem venn23 : VennRegions omega23 SAB23 SAC23 SBC23 T23 6 6 6 4 11 := by
  unfold VennRegions
  decide

private theorem band23 : BandStack 6 6 6 4 11 := by
  norm_num [BandStack]

private theorem SAB23_card : SAB23.card = 6 := by decide
private theorem SAC23_card : SAC23.card = 6 := by decide
private theorem SBC23_card : SBC23.card = 6 := by decide

private theorem sAB23_ne_zero : sAB23 ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : F23[X] => p.coeff 1) h
  norm_num [sAB23] at h1
  exact (by decide : (17 : F23) ≠ 0) h1

private theorem sAC23_ne_zero : sAC23 ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : F23[X] => p.coeff 1) h
  norm_num [sAC23] at h1
  exact (by decide : (5 : F23) ≠ 0) h1

private theorem sBC23_ne_zero : sBC23 ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : F23[X] => p.coeff 1) h
  norm_num [sBC23] at h1

private theorem sAB23_natDegree : sAB23.natDegree = 1 := by
  rw [show sAB23 = C (17 : F23) * X + C 18 by simp [sAB23, add_comm]]
  exact natDegree_linear (by decide)

private theorem sAC23_natDegree : sAC23.natDegree = 1 := by
  rw [show sAC23 = C (5 : F23) * X + C 2 by simp [sAC23, add_comm]]
  exact natDegree_linear (by decide)

private theorem sBC23_natDegree : sBC23.natDegree = 1 := by
  rw [show sBC23 = C (1 : F23) * X + C 20 by simp [sBC23, add_comm]]
  exact natDegree_linear (by norm_num)

private theorem cofactor_constant_of_product_degree_le_six
    (W s : F23[X]) (hW : W ≠ 0) (hWdeg : W.natDegree = 6)
    {δ : ℕ} (hδ : δ ≤ 6) (hprod : (W * s).natDegree ≤ δ) :
    s = C (s.coeff 0) := by
  by_cases hs : s = 0
  · simp [hs]
  have hmul := natDegree_mul hW hs
  have hsdeg : s.natDegree ≤ 0 := by omega
  exact eq_C_of_natDegree_le_zero hsdeg

private theorem minimalSyzygy23 :
    MinimalSyzygyDegree (vanishing SAB23) (vanishing SAC23) (vanishing SBC23) 7 := by
  constructor
  · refine ⟨sAB23, sAC23, sBC23, ?_, ?_, ?_, ?_, ?_⟩
    · rw [vanishing_SAB23, vanishing_SAC23, vanishing_SBC23]
      simp only [WAB23, WAC23, WBC23, sAB23, sAC23, sBC23]
      ring_nf
      C_simp
      ring_nf
      have h0 : (552 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 552) (r := 0) (by decide)
      have h1 : (828 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 828) (r := 0) (by decide)
      have h2 : (598 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 598) (r := 0) (by decide)
      have h3 : (437 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 437) (r := 0) (by decide)
      have h4 : (713 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 713) (r := 0) (by decide)
      have h5 : (207 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 207) (r := 0) (by decide)
      have h6 : (23 : F23[X]) = ((0 : ℕ) : F23[X]) :=
        polynomial_natCast_eq_of_mod_eq (n := 23) (r := 0) (by decide)
      rw [h0, h1, h2, h3, h4, h5, h6]
      simp
    · intro h
      exact sAB23_ne_zero h.1
    · rw [natDegree_mul (vanishing_ne_zero SAB23) sAB23_ne_zero,
        vanishing_natDegree, SAB23_card, sAB23_natDegree]
    · rw [natDegree_mul (vanishing_ne_zero SAC23) sAC23_ne_zero,
        vanishing_natDegree, SAC23_card, sAC23_natDegree]
    · rw [natDegree_mul (vanishing_ne_zero SBC23) sBC23_ne_zero,
        vanishing_natDegree, SBC23_card, sBC23_natDegree]
  · intro δ hsyz
    obtain ⟨sAB, sAC, sBC, hrel, hnz, hAB, hAC, hBC⟩ := hsyz
    by_contra hnot
    have hδ : δ ≤ 6 := by omega
    have hsAB : sAB = C (sAB.coeff 0) :=
      cofactor_constant_of_product_degree_le_six (vanishing SAB23) sAB
        (vanishing_ne_zero SAB23) (by rw [vanishing_natDegree, SAB23_card]) hδ hAB
    have hsAC : sAC = C (sAC.coeff 0) :=
      cofactor_constant_of_product_degree_le_six (vanishing SAC23) sAC
        (vanishing_ne_zero SAC23) (by rw [vanishing_natDegree, SAC23_card]) hδ hAC
    have hsBC : sBC = C (sBC.coeff 0) :=
      cofactor_constant_of_product_degree_le_six (vanishing SBC23) sBC
        (vanishing_ne_zero SBC23) (by rw [vanishing_natDegree, SBC23_card]) hδ hBC
    rw [hsAB, hsAC, hsBC, vanishing_SAB23, vanishing_SAC23, vanishing_SBC23] at hrel
    have h0 := congrArg (fun p : F23[X] => p.coeff 0) hrel
    have h1 := congrArg (fun p : F23[X] => p.coeff 1) hrel
    have h2 := congrArg (fun p : F23[X] => p.coeff 2) hrel
    norm_num [WAB23, WAC23, WBC23] at h0 h1 h2
    have hzAB' : (162 : F23) * sAB.coeff 0 + 207 * sAC.coeff 0 + 207 * sBC.coeff 0 = 0 := by
      linear_combination 6 * h0 + 5 * h1 + 4 * h2
    have hzAC' : (276 : F23) * sAB.coeff 0 + 553 * sAC.coeff 0 + 552 * sBC.coeff 0 = 0 := by
      linear_combination 21 * h0 + 6 * h1 + 7 * h2
    have hzBC' : (276 : F23) * sAB.coeff 0 + 368 * sAC.coeff 0 + 162 * sBC.coeff 0 = 0 := by
      linear_combination 6 * h0 + 2 * h1 + 18 * h2
    have hzAB : sAB.coeff 0 = 0 := by
      have h162 : (162 : F23) = 1 := by decide
      have h207 : (207 : F23) = 0 := by decide
      rw [h162, h207] at hzAB'
      simpa using hzAB'
    have hzAC : sAC.coeff 0 = 0 := by
      have h276 : (276 : F23) = 0 := by decide
      have h553 : (553 : F23) = 1 := by decide
      have h552 : (552 : F23) = 0 := by decide
      rw [h276, h553, h552] at hzAC'
      simpa using hzAC'
    have hzBC : sBC.coeff 0 = 0 := by
      have h276 : (276 : F23) = 0 := by decide
      have h368 : (368 : F23) = 0 := by decide
      have h162 : (162 : F23) = 1 := by decide
      rw [h276, h368, h162] at hzBC'
      simpa using hzBC'
    apply hnz
    constructor
    · rw [hsAB, hzAB]
      simp
    constructor
    · rw [hsAC, hzAC]
      simp
    · rw [hsBC, hzBC]
      simp

/-- The explicit finite-field region/syzygy configuration at profile
`(a,b,c,t,k,δ₁) = (6,6,6,4,11,7)`. This is region-layer data only; it does not
construct a genuine MCA stack. -/
theorem zmod23_regionSyzygyRealizable :
    RegionSyzygyRealizable (ZMod 23) 6 6 6 4 11 7 := by
  exact ⟨omega23, SAB23, SAC23, SBC23, T23, venn23, band23, minimalSyzygy23⟩

/-- The explicit `ZMod 23` region/syzygy profile falsifies the region-layer
middle-exclusion conjecture. This does not construct a genuine MCA stack. -/
theorem zmod23_not_regionMiddleExclusion :
    ¬ RegionMiddleExclusion (ZMod 23) := by
  apply family_witness_refutes_regionMiddleExclusion (K := ZMod 23) (d := 6) (by norm_num)
  simpa using zmod23_regionSyzygyRealizable

#print axioms zmod23_regionSyzygyRealizable
#print axioms zmod23_not_regionMiddleExclusion

end ArkLib.ProximityGap.F1RegionSyzygy
