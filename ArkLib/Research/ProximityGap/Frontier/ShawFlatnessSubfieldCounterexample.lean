/-
Copyright (c) 2026 ArkLib Contributors and Proximity Prize contributors. All rights reserved.
The workbench definitions retain their original Apache 2.0 license.
The new proof is released under the MIT and Apache 2.0 licenses in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._FunctionFieldModelSubfieldDegeneracy
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The all-finite-field Shaw flatness conjecture has subfield counterexamples

The two definitions below are the spectral tests originally stated in §8 of
`PROXIMITY_PRIZE_WORKBENCH`. In the quadratic field of order `p²`, additive
duality provides a primitive character that equals one on the prime subfield.
For its multiplicative group of size `p-1`, the frequency-one sum equals
`p-1`. An elementary logarithm estimate and Euclid's theorem rule out every
absolute constant in the conjecture. The prime-field variant remains open.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ProximityPrize

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The worst-case nonzero frequency bound at constant `C`. -/
noncomputable def ShawGapLaw (ψ : AddChar F ℂ) (D : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖eta ψ D b‖ ≤ C * Real.sqrt ((D.card : ℝ) * Real.logb 2 ((Fintype.card F : ℝ) / D.card))

/-- The workbench assertion over multiplicative subgroups of all finite fields. -/
def ShawFlatnessConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (ψ : AddChar F ℂ) (D : Finset F),
      ψ.IsPrimitive → (0 : F) ∉ D → (1 : F) ∈ D → (∀ x ∈ D, ∀ y ∈ D, x * y ∈ D) →
      (D.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) →
      ShawGapLaw ψ D C

private theorem logb_quadratic_le {x : ℝ} (hx : 2 ≤ x) :
    Real.logb 2 (x ^ 2 / (x - 1)) ≤ 8 * Real.sqrt x := by
  have hx' : 0 < x := by linarith
  have hle : x ^ 2 / (x - 1) ≤ x ^ 2 := div_le_self (sq_nonneg x) (by linarith)
  have hlog : Real.log x / 2 ≤ Real.sqrt x - 1 := by
    rw [← Real.log_sqrt hx'.le]
    exact Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx')
  have hbase := Real.one_sub_inv_le_log_of_pos (show 0 < (2 : ℝ) by norm_num)
  norm_num at hbase
  apply (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (div_pos (sq_pos_of_pos hx') (by linarith)) hle).trans
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num)), Real.log_pow]
  calc
    _ ≤ 4 * Real.sqrt x := by norm_num; linarith
    _ = (8 * Real.sqrt x) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)

private theorem subfield_bound (p : ℕ) (hp : Nat.Prime p) (C : ℝ)
    (hflat : ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (ψ : AddChar F ℂ) (D : Finset F),
      ψ.IsPrimitive → (0 : F) ∉ D → (1 : F) ∈ D → (∀ x ∈ D, ∀ y ∈ D, x * y ∈ D) →
      (D.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) → ShawGapLaw ψ D C) :
    (p : ℝ) - 1 ≤ C * Real.sqrt (((p : ℝ) - 1) * Real.logb 2 ((p : ℝ)^2 / (p - 1))) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p 2
  let : Fintype F := Fintype.ofFinite F
  let f : ZMod p →+* F := algebraMap _ F
  have hcardF : Fintype.card F = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by decide)
  let D : Finset F := (Finset.univ.erase (0 : ZMod p)).map ⟨f, f.injective⟩
  have hmem (x : F) : x ∈ D ↔ ∃ y : ZMod p, y ≠ 0 ∧ f y = x := by
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
      exact ⟨y, (Finset.mem_erase.mp hy).1, hyx⟩
    · rintro ⟨y, hy, hyx⟩
      exact Finset.mem_map.mpr ⟨y, Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩, hyx⟩
  have hcardD : D.card = p - 1 := by simp [D, ZMod.card]
  let K := f.toAddMonoidHom.range
  have hK : K ≠ ⊤ := by
    intro htop
    have hs : Function.Surjective f := by
      intro x
      have hx : x ∈ K := htop ▸ AddSubgroup.mem_top x
      exact hx
    have hi := Fintype.card_le_of_surjective f hs
    rw [hcardF, ZMod.card] at hi
    nlinarith [hp.two_le, Nat.mul_le_mul_left p hp.two_le]
  obtain ⟨ψ, hψ, hsum⟩ := FFModelW4.thin_regime_zero_cancellation K hK D (by
    intro x hx
    obtain ⟨y, _, hy⟩ := (hmem x).mp hx
    exact ⟨y, hy⟩)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hD : (D.card : ℝ) = (p : ℝ) - 1 := by rw [hcardD, Nat.cast_sub hp.one_lt.le]; simp
  have hF : (Fintype.card F : ℝ) = (p : ℝ) ^ 2 := by rw [hcardF]; norm_cast
  have h := hflat ψ D (AddChar.IsPrimitive.of_ne_one hψ)
    (by
      intro hx
      obtain ⟨y, hy, heq⟩ := (hmem 0).mp hx
      exact hy ((map_eq_zero f).mp heq))
    ((hmem 1).mpr ⟨1, one_ne_zero, map_one f⟩)
    (by
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := (hmem _).mp hx
      obtain ⟨b, hb, rfl⟩ := (hmem _).mp hy
      exact (hmem _).mpr ⟨a*b, mul_ne_zero ha hb, map_mul f a b⟩)
    (by rw [hD, hF]; nlinarith)
    1 one_ne_zero
  simpa [eta, hsum, hD, hF] using h

/-- No absolute constant satisfies the all-finite-field Shaw gap bound. -/
theorem not_shawFlatnessConjecture : ¬ ShawFlatnessConjecture := by
  rintro ⟨C, hC, hflat⟩
  obtain ⟨a, ha⟩ := exists_nat_gt ((16 * C ^ 2 + 2) ^ 2)
  obtain ⟨p, hap, hp⟩ := Nat.exists_infinite_primes a
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hbig : (16 * C ^ 2 + 2) ^ 2 < (p : ℝ) := lt_of_lt_of_le ha (by exact_mod_cast hap)
  have hroot : 16 * C ^ 2 + 2 < Real.sqrt (p : ℝ) := by
    apply (Real.lt_sqrt (by positivity)).2
    exact hbig
  have h := subfield_bound p hp C hflat
  let x : ℝ := p
  change x - 1 ≤ C * √((x - 1) * Real.logb 2 (x ^ 2 / (x - 1))) at h
  change 2 ≤ x at hp2
  change 16 * C ^ 2 + 2 < √x at hroot
  have hx : 0 < x - 1 := by linarith
  have hr : x ^ 2 / (x - 1) ≥ 1 := (le_div_iff₀ hx).2 (by nlinarith [sq_nonneg x])
  have hsup := pow_le_pow_left₀ hx.le h 2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hx.le (Real.logb_nonneg (by norm_num) hr))] at hsup
  have hcancel : x-1 ≤ C^2 * Real.logb 2 (x^2/(x-1)) := by
    apply (le_of_mul_le_mul_left (a := x-1) _ hx)
    linarith only [hsup]
  have hn := hcancel.trans (mul_le_mul_of_nonneg_left (logb_quadratic_le hp2) (sq_nonneg C))
  nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith),
    mul_nonneg (Real.sqrt_nonneg x) (show 0 ≤ √x - (16 * C ^ 2 + 2) by linarith)]

#print axioms not_shawFlatnessConjecture
end ProximityPrize
