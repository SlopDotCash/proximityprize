/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R389WickBudgetSupBound
import ArkLib.Research.ProximityGap.Frontier._FunctionFieldModelSubfieldDegeneracy
import ArkLib.Research.ProximityGap.Frontier._R240GeneralRFoldVariance
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# R389: the uniform subgroup Wick budget is false for every constant

`R389WickBudgetSupBound.UniformSubgroupWickBudget C` asks for one inflation constant `C` such that
the DC-subtracted Wick budget holds for *every* finite field and *every* torsion subgroup at the
calibrated depth `k* = ⌈(log q)/2⌉₊`.  Its docstring records a subfield obstruction as a written
argument, "not kernel-checked".  This file kernel-checks it: `¬ UniformSubgroupWickBudget C` for
every real `C`.

## The argument

* `C ≥ 0`.  Take a prime `p` and `F = GF(p²)`.  The torsion set `μ_{p-1} ⊂ F` contains the
  `p - 1` nonzero elements of the prime subfield (`pred_le_card_torsionSet`).  It lies in the
  proper additive subgroup `{x : x^p = x}`, so some nontrivial — hence primitive — additive
  character of `F` is identically `1` on it
  (`FFModelW4.ffThin_prizeLaw_countermodel`): the period `η_1` equals `|μ_{p-1}|`.  The R389
  consumer `sup_le_three_sqrt_of_dcEnergyBudget` turns the budget into
  `|μ_{p-1}| ≤ 3·√(C·|μ_{p-1}|·log q)`, i.e. `|μ_{p-1}| ≤ 9·C·log q`
  (`card_torsionSet_le_of_budget`).  With `q = p²` and `log p ≤ 2(√p - 1)` this gives
  `√p + 1 ≤ 36·C`, false once `p > (36·⌈C⌉₊)²`.
* `C < 0`.  At `F = ZMod 2`, `d = 1` the depth is `k* = 1`, the right-hand side `2·C` is
  negative, and the left-hand side is nonnegative by the DC floor.

## Scope

The witness is a subfield subgroup: `μ_{p-1} = GF(p)^×` inside `GF(p²)`, where there is no
cancellation at all.  This refutes the *uniform* statement over all finite fields.  It says
nothing about prime fields or about the prize-shaped subgroups `μ_{2^k} ⊂ 𝔽_p`, for which the
budget remains open in both directions, exactly as the R389 docstring states.
-/

set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.R389UniformWickBudgetRefuted

open ArkLib.ProximityGap.R389WickBudgetSupBound

/-- In a field of characteristic `p`, the `p - 1` nonzero elements of the prime subfield are
`(p-1)`-th roots of unity, so `μ_{p-1}` has at least `p - 1` elements. -/
theorem pred_le_card_torsionSet (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [CharP F p] :
    p - 1 ≤ (torsionSet F (p - 1)).card := by
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) F) :=
    (ZMod.castHom (dvd_refl p) F).injective
  have hsub : ((univ : Finset (ZMod p)).erase 0).image (ZMod.castHom (dvd_refl p) F)
      ⊆ torsionSet F (p - 1) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    simp only [torsionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one ha0, map_one]
  calc p - 1 = ((univ : Finset (ZMod p)).erase 0).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
    _ = (((univ : Finset (ZMod p)).erase 0).image (ZMod.castHom (dvd_refl p) F)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (torsionSet F (p - 1)).card := Finset.card_le_card hsub

/-- **The budget on a subfield subgroup forces `|μ_{p-1}| ≤ 9·C·log q`.**  In a finite field of
characteristic `p` with more than `p` elements, some primitive additive character is trivial on
`μ_{p-1}`, so its period there is `|μ_{p-1}|`; the R389 sup bound then caps the cardinality. -/
theorem card_torsionSet_le_of_budget {C : ℝ} (hC : 0 ≤ C) (p : ℕ) [Fact p.Prime] (F : Type)
    [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    (hcard : p < Fintype.card F) (hq5 : 5 ≤ Fintype.card F)
    (hbudget : DCEnergyBudget (torsionSet F (p - 1)) (wickDepth (Fintype.card F)) C) :
    ((torsionSet F (p - 1)).card : ℝ) ≤ 9 * C * Real.log (Fintype.card F) := by
  obtain ⟨ψ, hψ1, hsum⟩ := FFModelW4.ffThin_prizeLaw_countermodel (F := F) (p := p)
    (n := p - 1) (s := 1) le_rfl (by simp) (by simpa using hcard)
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ1
  have hsup := sup_le_three_sqrt_of_dcEnergyBudget hψ hC hq5 hbudget (b := 1) one_ne_zero
  have heta : eta ψ (torsionSet F (p - 1)) 1 = ((torsionSet F (p - 1)).card : ℂ) := by
    unfold eta
    simpa [torsionSet] using hsum
  rw [heta, Complex.norm_natCast] at hsup
  have hL : 0 ≤ Real.log (Fintype.card F) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card F))
  rcases (Nat.cast_nonneg (torsionSet F (p - 1)).card : (0 : ℝ) ≤ _).eq_or_lt with hg0 | hgpos
  · rw [← hg0]
    positivity
  · have h1 : ((torsionSet F (p - 1)).card : ℝ) / 3
        ≤ Real.sqrt (C * ((torsionSet F (p - 1)).card : ℝ) * Real.log (Fintype.card F)) := by
      linarith
    have h2 := (Real.le_sqrt' (by positivity)).mp h1
    have h3 : ((torsionSet F (p - 1)).card : ℝ) * ((torsionSet F (p - 1)).card : ℝ)
        ≤ ((torsionSet F (p - 1)).card : ℝ) * (9 * C * Real.log (Fintype.card F)) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 hgpos

/-- **No nonnegative constant works.**  For `C ≥ 0` the uniform budget fails at `F = GF(p²)`,
`d = p - 1`, for any prime `p > (36·⌈C⌉₊)²`. -/
theorem not_uniformSubgroupWickBudget_of_nonneg {C : ℝ} (hC : 0 ≤ C) :
    ¬ UniformSubgroupWickBudget C := by
  intro hbudget
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes ((36 * ⌈C⌉₊) ^ 2 + 5)
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype (GaloisField p 2) := Fintype.ofFinite _
  classical
  have hcardF : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by norm_num)
  have hp5 : 5 ≤ p := by omega
  have hlt : p < Fintype.card (GaloisField p 2) := by
    rw [hcardF]
    nlinarith
  have hq5 : 5 ≤ Fintype.card (GaloisField p 2) := by omega
  have hb := card_torsionSet_le_of_budget hC p (GaloisField p 2) hlt hq5
    (hbudget (GaloisField p 2) (p - 1))
  have hG : ((p : ℝ) - 1) ≤ ((torsionSet (GaloisField p 2) (p - 1)).card : ℝ) := by
    have h := pred_le_card_torsionSet p (GaloisField p 2)
    have h' : ((p - 1 : ℕ) : ℝ) ≤ ((torsionSet (GaloisField p 2) (p - 1)).card : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h'
  -- real arithmetic with `s = √p`
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hlogq : Real.log (Fintype.card (GaloisField p 2)) = 2 * Real.log p := by
    rw [hcardF]
    push_cast
    rw [Real.log_pow]
    norm_num
  have hlogp : Real.log p ≤ 2 * (Real.sqrt p - 1) := by
    have h := Real.log_le_sub_one_of_pos hspos
    have h2 : Real.log p = 2 * Real.log (Real.sqrt p) := by
      rw [← hs2, Real.log_pow, hs2]
      norm_num
    linarith
  have hsbig : (36 : ℝ) * C < Real.sqrt p := by
    have hceil : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
    have h1 : ((36 * ⌈C⌉₊ : ℕ) : ℝ) < Real.sqrt p := by
      apply Real.lt_sqrt_of_sq_lt
      have : (36 * ⌈C⌉₊) ^ 2 < p := by omega
      exact_mod_cast this
    push_cast at h1
    linarith
  have hs1 : 1 < Real.sqrt p := by
    have : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    exact Real.lt_sqrt_of_sq_lt (by simpa using this)
  rw [hlogq] at hb
  -- p - 1 ≤ 9 C · 2 log p ≤ 36 C (√p - 1), and p - 1 = (√p - 1)(√p + 1)
  have hchain : (p : ℝ) - 1 ≤ 36 * C * (Real.sqrt p - 1) := by
    have : 9 * C * (2 * Real.log p) ≤ 9 * C * (2 * (2 * (Real.sqrt p - 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hsbig)]

/-- **No negative constant works either.**  At `F = ZMod 2`, `d = 1` the depth is `1`, the budget
`2·C·|μ_1|` is negative, and the DC-subtracted energy is nonnegative. -/
theorem not_uniformSubgroupWickBudget_of_neg {C : ℝ} (hC : C < 0) :
    ¬ UniformSubgroupWickBudget C := by
  intro hbudget
  have h := hbudget (ZMod 2) 1
  have hdepth : wickDepth (Fintype.card (ZMod 2)) = 1 := by
    unfold wickDepth
    rw [ZMod.card, Nat.ceil_eq_iff (by norm_num)]
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_two_lt_d9
    constructor <;> norm_num <;> linarith
  rw [hdepth] at h
  unfold DCEnergyBudget at h
  have hfloor := ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dc_floor
    (torsionSet (ZMod 2) 1) 1
  have hGpos : (0 : ℝ) < ((torsionSet (ZMod 2) 1).card : ℝ) := by
    have hmem : (1 : ZMod 2) ∈ torsionSet (ZMod 2) 1 := by simp [torsionSet]
    exact_mod_cast Finset.card_pos.mpr ⟨1, hmem⟩
  have hq : (0 : ℝ) < (Fintype.card (ZMod 2) : ℝ) := by
    rw [ZMod.card]
    norm_num
  have hdf : ((Nat.doubleFactorial (2 * 1 - 1) : ℕ) : ℝ) = 1 := by norm_num [Nat.doubleFactorial]
  rw [hdf] at h
  nlinarith [mul_pos hq hGpos]

/-- **`UniformSubgroupWickBudget C` is false for every real `C`.** -/
theorem not_uniformSubgroupWickBudget (C : ℝ) : ¬ UniformSubgroupWickBudget C := by
  rcases lt_or_ge C 0 with hC | hC
  · exact not_uniformSubgroupWickBudget_of_neg hC
  · exact not_uniformSubgroupWickBudget_of_nonneg hC

end ArkLib.ProximityGap.R389UniformWickBudgetRefuted

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.R389UniformWickBudgetRefuted
#print axioms pred_le_card_torsionSet
#print axioms card_torsionSet_le_of_budget
#print axioms not_uniformSubgroupWickBudget_of_nonneg
#print axioms not_uniformSubgroupWickBudget_of_neg
#print axioms not_uniformSubgroupWickBudget
end AxiomAudit
