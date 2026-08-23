/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.RingTheory.IntegralDomain
import VCVio

/-!
# Exact level-set counting for linear forms over finite rings (issue #329)

The quantitative core of the random-linear-combination batching bound: if `d : ι → R` has a unit
coordinate, then every affine level set `{r | ∑ i, r i * d i = t}` of the linear form
`r ↦ ∑ i, r i * d i` has exactly `|R|^(|ι| - 1)` elements — equivalently, a uniformly random `r`
hits the level set with probability exactly `1/|R|`.

This is the *exact* (not Schwartz–Zippel `n/|R|`) bound: the proof is the textbook coset argument,
implemented as an explicit shift bijection between level sets followed by a fiber-partition count.
For Spartan (#329) it gives the tight per-round error of the `linearCombination` round once the
evaluation claims are pinned: a wrong claim vector survives the RLC challenge with probability
exactly `1/|R|`, replacing the proven-forced error `1` of the claim-blind relation chain.

The finite-integral-domain specialization (`probEvent_linearForm_eq_inv_card_of_ne_zero`) matches
ArkLib's standing Spartan hypotheses `[CommRing R] [IsDomain R] [Fintype R]`.
-/

open OracleComp

namespace LinearFormKernel

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

section CommRing

variable [CommRing R] [Fintype R] [DecidableEq R]

/-- The shift `r ↦ r + ((t₂ - t₁)/d i₀) · δ_{i₀}` is a bijection between the `t₁`- and
`t₂`-level sets of the linear form `r ↦ ∑ i, r i * d i`, provided `d i₀` is a unit. -/
def levelSetShiftEquiv (d : ι → R) (i₀ : ι) (u : Rˣ) (hu : (u : R) = d i₀) (t₁ t₂ : R) :
    {r : ι → R // ∑ i, r i * d i = t₁} ≃ {r : ι → R // ∑ i, r i * d i = t₂} where
  toFun := fun ⟨r, hr⟩ =>
    ⟨fun i => r i + if i = i₀ then (t₂ - t₁) * (↑u⁻¹ : R) else 0, by
      simp only [add_mul, Finset.sum_add_distrib, hr, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i => (t₂ - t₁) * (↑u⁻¹ : R) * d i)]
      simp only [Finset.mem_univ, if_true]
      rw [← hu, mul_assoc, Units.inv_mul, mul_one]
      ring⟩
  invFun := fun ⟨r, hr⟩ =>
    ⟨fun i => r i + if i = i₀ then (t₁ - t₂) * (↑u⁻¹ : R) else 0, by
      simp only [add_mul, Finset.sum_add_distrib, hr, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i => (t₁ - t₂) * (↑u⁻¹ : R) * d i)]
      simp only [Finset.mem_univ, if_true]
      rw [← hu, mul_assoc, Units.inv_mul, mul_one]
      ring⟩
  left_inv := by
    rintro ⟨r, hr⟩
    ext i
    by_cases h : i = i₀
    · simp only [h, if_true]; ring
    · simp [h]
  right_inv := by
    rintro ⟨r, hr⟩
    ext i
    by_cases h : i = i₀
    · simp only [h, if_true]; ring
    · simp [h]

/-- All affine level sets of a linear form with a unit coordinate are equinumerous. -/
theorem card_levelSet_eq (d : ι → R) {i₀ : ι} (hd : IsUnit (d i₀)) (t₁ t₂ : R) :
    (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t₁).card
      = (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t₂).card := by
  obtain ⟨u, hu⟩ := hd
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (levelSetShiftEquiv d i₀ u hu t₁ t₂)

/-- **Exact level-set count.** A linear form with a unit coordinate partitions `ι → R` into `|R|`
equinumerous level sets: `|{r | ∑ i, r i * d i = t}| * |R| = |ι → R|`. -/
theorem card_levelSet_mul_card (d : ι → R) {i₀ : ι} (hd : IsUnit (d i₀)) (t : R) :
    (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t).card * Fintype.card R
      = Fintype.card (ι → R) := by
  classical
  have hpart : ∑ t' : R, (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t').card
      = Fintype.card (ι → R) := by
    rw [← Finset.card_univ (α := ι → R)]
    exact (Finset.card_eq_sum_card_fiberwise
      (f := fun r : ι → R => ∑ i, r i * d i) (t := Finset.univ)
      (fun r _ => Finset.mem_univ _)).symm
  calc (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t).card * Fintype.card R
      = ∑ _t' : R, (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t).card := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    _ = ∑ t' : R, (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t').card :=
        Finset.sum_congr rfl fun t' _ => card_levelSet_eq d hd t t'
    _ = Fintype.card (ι → R) := hpart

end CommRing

section ProbCommRing

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [Fintype R] [DecidableEq R]

/-- **Exact RLC hitting probability.** A uniformly random `r : ι → R` satisfies
`∑ i, r i * d i = t` with probability exactly `1/|R|`, whenever `d` has a unit coordinate. -/
theorem probEvent_linearForm_eq_inv_card (d : ι → R) {i₀ : ι} (hd : IsUnit (d i₀)) (t : R)
    [SampleableType (ι → R)] :
    Pr[fun r : ι → R => ∑ i, r i * d i = t | $ᵗ (ι → R)]
      = ((Fintype.card R : ENNReal))⁻¹ := by
  classical
  rw [probEvent_uniformSample]
  have hmul := card_levelSet_mul_card d hd t
  set a : ℕ := (Finset.univ.filter fun r : ι → R => ∑ i, r i * d i = t).card with ha
  have hbpos : 0 < Fintype.card (ι → R) := Fintype.card_pos
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h
    · rw [h0, zero_mul] at hmul; omega
    · exact h
  rw [← hmul, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast hapos.ne')) (Or.inl (ENNReal.natCast_ne_top a)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hapos.ne') (ENNReal.natCast_ne_top a),
    one_mul]

end ProbCommRing

section FiniteDomain

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R] [Fintype R]
  [DecidableEq R]

omit [DecidableEq R] in
/-- In a finite integral domain every nonzero element is a unit. -/
theorem isUnit_of_ne_zero_of_finite {a : R} (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := (Finite.isField_of_domain R).mul_inv_cancel ha
  exact isUnit_iff_exists_inv.mpr ⟨b, hb⟩

/-- **Exact RLC hitting probability over a finite integral domain.** For a nonzero deviation
vector `d`, a uniformly random challenge `r` satisfies `∑ i, r i * d i = t` with probability
exactly `1/|R|`. This is the tight per-round error of a random-linear-combination batching round:
a claim vector that deviates from the truth by `d ≠ 0` survives the challenge iff the challenge
lands in one affine level set. -/
theorem probEvent_linearForm_eq_inv_card_of_ne_zero {d : ι → R} (hd : d ≠ 0) (t : R)
    [SampleableType (ι → R)] :
    Pr[fun r : ι → R => ∑ i, r i * d i = t | $ᵗ (ι → R)]
      = ((Fintype.card R : ENNReal))⁻¹ := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hd
  exact probEvent_linearForm_eq_inv_card d (isUnit_of_ne_zero_of_finite hi₀) t

end FiniteDomain

end LinearFormKernel

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms LinearFormKernel.card_levelSet_mul_card
#print axioms LinearFormKernel.probEvent_linearForm_eq_inv_card
#print axioms LinearFormKernel.probEvent_linearForm_eq_inv_card_of_ne_zero
