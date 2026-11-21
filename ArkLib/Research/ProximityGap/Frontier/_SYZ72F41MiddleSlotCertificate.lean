/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._F1RegionSyzygyInterface
import ArkLib.Research.ProximityGap.Frontier._SYZ70FirstOpenMiddleSlot
import Mathlib.Tactic.LinearCombination

/-!
# SYZ72 — a kernel-checked finite-field middle-slot witness

This file turns the recorded `F_41`, `μ_20` witness into an axiom-clean
`RegionSyzygyRealizable` theorem. It refutes emptiness at the on-domain
region/syzygy layer. It does not lift the witness to an over-budget MCA stack
or close the production near-balance residual.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.SYZ72

open Polynomial
open ArkLib.ProximityGap.F1RegionSyzygy

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local instance prime41Fact : Fact (Nat.Prime 41) := ⟨by norm_num⟩

private abbrev F41 := ZMod 41

private def mu20 : Finset F41 := (Finset.range 20).image (fun i => (2 : F41) ^ i)
private def SAB41 : Finset F41 := {4, 9, 21, 31, 33, 40}
private def SAC41 : Finset F41 := {1, 2, 23, 25, 37, 39}
private def SBC41 : Finset F41 := {5, 8, 10, 16, 18, 36}
private def T41 : Finset F41 := {20, 32}

private noncomputable def WAB41 : F41[X] :=
  C 36 + C 37 * X + C 37 * X ^ 2 + C 18 * X ^ 3 + C 7 * X ^ 4 + C 26 * X ^ 5 + X ^ 6
private noncomputable def WAC41 : F41[X] :=
  C 16 + C 40 * X + C 10 * X ^ 2 + C 6 * X ^ 3 + C 13 * X ^ 4 + C 37 * X ^ 5 + X ^ 6
private noncomputable def WBC41 : F41[X] :=
  C 9 + C 21 * X + C 16 * X ^ 2 + C 38 * X ^ 3 + C 12 * X ^ 4 + C 30 * X ^ 5 + X ^ 6

private noncomputable def rAB41 : F41[X] := -(C 9 + C 11 * X)
private noncomputable def rAC41 : F41[X] := C 29 + C 10 * X
private noncomputable def rBC41 : F41[X] := C 30 + X

private theorem F41_natCast_mod (n : ℕ) : (n : F41) = (n % 41 : ℕ) := by
  apply ZMod.val_injective
  simp [ZMod.val_natCast]

private theorem polynomial_natCast_mod (n : ℕ) :
    (n : F41[X]) = (n % 41 : ℕ) := by
  change C (n : F41) = C ((n % 41 : ℕ) : F41)
  exact congrArg (C : F41 → F41[X]) (F41_natCast_mod n)

private theorem polynomial_natCast_eq_of_mod_eq {n r : ℕ} (h : n % 41 = r) :
    (n : F41[X]) = (r : F41[X]) := by
  rw [polynomial_natCast_mod n, h]

private theorem polynomial_char41 : (41 : F41[X]) = 0 := by
  change C (41 : F41) = 0
  have h41 : (41 : F41) = 0 := by decide
  rw [h41, C_0]

private theorem vanishing_SAB41 : vanishing SAB41 = WAB41 := by
  classical
  simp only [vanishing, SAB41]
  repeat' rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, WAB41]
  ring_nf
  C_simp
  ring_nf
  have h0 : (30935520 : F41[X]) = 36 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h1 : (15353028 : F41[X]) = 4 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h2 : (2577051 : F41[X]) = 37 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h3 : (195634 : F41[X]) = 23 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h4 : (7428 : F41[X]) = 7 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h5 : (138 : F41[X]) = 15 := polynomial_natCast_eq_of_mod_eq (by decide)
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination -(X + X ^ 3 + X ^ 5) * polynomial_char41

private theorem vanishing_SAC41 : vanishing SAC41 = WAC41 := by
  classical
  simp only [vanishing, SAC41]
  repeat' rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, WAC41]
  ring_nf
  C_simp
  ring_nf
  have h0 : (1659450 : F41[X]) = 16 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h1 : (2715103 : F41[X]) = 1 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h2 : (1179949 : F41[X]) = 10 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h3 : (130210 : F41[X]) = 35 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h4 : (6040 : F41[X]) = 13 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h5 : (127 : F41[X]) = 4 := polynomial_natCast_eq_of_mod_eq (by decide)
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination -(X + X ^ 3 + X ^ 5) * polynomial_char41

private theorem vanishing_SBC41 : vanishing SBC41 = WBC41 := by
  classical
  simp only [vanishing, SBC41]
  repeat' rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, WBC41]
  ring_nf
  C_simp
  ring_nf
  have h0 : (4147200 : F41[X]) = 9 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h1 : (2367360 : F41[X]) = 20 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h2 : (523504 : F41[X]) = 16 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h3 : (57444 : F41[X]) = 3 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h4 : (3292 : F41[X]) = 12 := polynomial_natCast_eq_of_mod_eq (by decide)
  have h5 : (93 : F41[X]) = 11 := polynomial_natCast_eq_of_mod_eq (by decide)
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination -(X + X ^ 3 + X ^ 5) * polynomial_char41

private theorem cofactor_identity :
    WAB41 * rAB41 + WAC41 * rAC41 + WBC41 * rBC41 = 0 := by
  simp only [WAB41, WAC41, WBC41, rAB41, rAC41, rBC41]
  ring_nf
  C_simp
  ring_nf
  linear_combination
    (10 + 30 * X + 11 * X ^ 2 + 21 * X ^ 3 + 14 * X ^ 4 + 44 * X ^ 5 +
      4 * X ^ 6) * polynomial_char41

private theorem venn41 : VennRegions mu20 SAB41 SAC41 SBC41 T41 6 6 6 2 10 := by
  unfold VennRegions mu20 SAB41 SAC41 SBC41 T41
  decide

private theorem band41 : BandStack 6 6 6 2 10 := by
  norm_num [BandStack]

private theorem rAB41_ne_zero : rAB41 ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : F41[X] => p.coeff 1) h
  norm_num [rAB41] at h1
  exact (by decide : (11 : F41) ≠ 0) h1

private theorem rAC41_ne_zero : rAC41 ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : F41[X] => p.coeff 1) h
  norm_num [rAC41] at h1
  exact (by decide : (10 : F41) ≠ 0) h1

private theorem rBC41_ne_zero : rBC41 ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : F41[X] => p.coeff 1) h
  norm_num [rBC41] at h1

private theorem rAB41_natDegree : rAB41.natDegree = 1 := by
  rw [show rAB41 = C (-11 : F41) * X + C (-9 : F41) by simp [rAB41, add_comm]]
  exact natDegree_linear (by decide)

private theorem rAC41_natDegree : rAC41.natDegree = 1 := by
  rw [show rAC41 = C (10 : F41) * X + C 29 by simp [rAC41, add_comm]]
  exact natDegree_linear (by decide)

private theorem rBC41_natDegree : rBC41.natDegree = 1 := by
  rw [show rBC41 = C (1 : F41) * X + C 30 by simp [rBC41, add_comm]]
  exact natDegree_linear (by norm_num)

private theorem cofactor_constant_of_product_degree_le_six
    (W s : F41[X]) (hW : W ≠ 0) (hWdeg : W.natDegree = 6)
    {δ : ℕ} (hδ : δ ≤ 6) (hprod : (W * s).natDegree ≤ δ) :
    s = C (s.coeff 0) := by
  by_cases hs : s = 0
  · simp [hs]
  have hmul := natDegree_mul hW hs
  have hsdeg : s.natDegree ≤ 0 := by omega
  exact eq_C_of_natDegree_le_zero hsdeg

private theorem minimalSyzygy41 :
    MinimalSyzygyDegree (vanishing SAB41) (vanishing SAC41) (vanishing SBC41) 7 := by
  constructor
  · refine ⟨rAB41, rAC41, rBC41, ?_, ?_, ?_, ?_, ?_⟩
    · rw [vanishing_SAB41, vanishing_SAC41, vanishing_SBC41]
      exact cofactor_identity
    · rintro ⟨hAB, hAC, hBC⟩
      exact rAB41_ne_zero hAB
    · rw [natDegree_mul (vanishing_ne_zero SAB41) rAB41_ne_zero,
        vanishing_natDegree, show SAB41.card = 6 by decide, rAB41_natDegree]
    · rw [natDegree_mul (vanishing_ne_zero SAC41) rAC41_ne_zero,
        vanishing_natDegree, show SAC41.card = 6 by decide, rAC41_natDegree]
    · rw [natDegree_mul (vanishing_ne_zero SBC41) rBC41_ne_zero,
        vanishing_natDegree, show SBC41.card = 6 by decide, rBC41_natDegree]
  · intro δ hsyz
    obtain ⟨sAB, sAC, sBC, hrel, hnz, hAB, hAC, hBC⟩ := hsyz
    by_contra hnot
    have hδ : δ ≤ 6 := by omega
    have hsAB : sAB = C (sAB.coeff 0) :=
      cofactor_constant_of_product_degree_le_six (vanishing SAB41) sAB
        (vanishing_ne_zero SAB41) (by rw [vanishing_natDegree]; decide) hδ hAB
    have hsAC : sAC = C (sAC.coeff 0) :=
      cofactor_constant_of_product_degree_le_six (vanishing SAC41) sAC
        (vanishing_ne_zero SAC41) (by rw [vanishing_natDegree]; decide) hδ hAC
    have hsBC : sBC = C (sBC.coeff 0) :=
      cofactor_constant_of_product_degree_le_six (vanishing SBC41) sBC
        (vanishing_ne_zero SBC41) (by rw [vanishing_natDegree]; decide) hδ hBC
    rw [hsAB, hsAC, hsBC, vanishing_SAB41, vanishing_SAC41, vanishing_SBC41] at hrel
    have h6 := congrArg (fun p : F41[X] => p.coeff 6) hrel
    have h5 := congrArg (fun p : F41[X] => p.coeff 5) hrel
    have h4 := congrArg (fun p : F41[X] => p.coeff 4) hrel
    norm_num [WAB41, WAC41, WBC41] at h6 h5 h4
    let a := sAB.coeff 0
    let b := sAC.coeff 0
    let c := sBC.coeff 0
    have e6 : a + b + c = 0 := by simpa [a, b, c] using h6
    have e5 : 26 * a + 37 * b + 30 * c = 0 := by simpa [a, b, c] using h5
    have e4 : 7 * a + 13 * b + 12 * c = 0 := by simpa [a, b, c] using h4
    have e1 : -4 * a + 7 * b = 0 := by linear_combination e5 - 30 * e6
    have e2 : -5 * a + b = 0 := by linear_combination e4 - 12 * e6
    have ha : a = 0 := by
      have h31 : (31 : F41) ≠ 0 := by decide
      have : (31 : F41) * a = 0 := by linear_combination e1 - 7 * e2
      exact (mul_eq_zero.mp this).resolve_left h31
    have hb : b = 0 := by linear_combination e2 + 5 * ha
    have hc : c = 0 := by linear_combination e6 - ha - hb
    apply hnz
    constructor
    · rw [hsAB]
      simpa using congrArg (C : F41 → F41[X]) ha
    constructor
    · rw [hsAC]
      simpa using congrArg (C : F41 → F41[X]) hb
    · rw [hsBC]
      simpa using congrArg (C : F41 → F41[X]) hc

/-- The explicit `F_41`, `μ_20` configuration from SYZ71/SYZ72, now checked
by Lean: the actual domain is partitioned into disjoint regions of sizes
`(6,6,6,2)`, and the vanishing-polynomial syzygy has minimal product-degree 7. -/
theorem zmod41_regionSyzygyRealizable :
    RegionSyzygyRealizable F41 6 6 6 2 10 7 := by
  exact ⟨mu20, SAB41, SAC41, SBC41, T41, venn41, band41, minimalSyzygy41⟩

/-- The universal region-layer middle-exclusion statement is false at `F_41`.
This is not a counterexample to the production theorem: the region interface
does not assert that the regions come from a genuine MCA stack. -/
theorem zmod41_not_regionMiddleExclusion : ¬ RegionMiddleExclusion F41 := by
  intro hEx
  exact hEx 6 6 6 2 10 7 zmod41_regionSyzygyRealizable
    ArkLib.ProximityGap.SYZ70.first_balanced_middle_occupied

#print axioms zmod41_regionSyzygyRealizable
#print axioms zmod41_not_regionMiddleExclusion

end ArkLib.ProximityGap.SYZ72
