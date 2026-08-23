/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RootsOfUnityAdditiveEnergy
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# Discharging `SidonModNeg` for unit-circle sets — the char-0 anchor made UNCONDITIONAL (#389)

The campaign's exact additive-energy theorem
`AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg : additiveEnergy G = 3|G|² − 3|G|`
holds for any negation-closed set satisfying the structural hypothesis `SidonModNeg G` (the only
additive coincidences are trivial or zero-sum).  But `SidonModNeg` was an **undischarged
hypothesis** everywhere — no concrete set was shown to satisfy it.

This file discharges it for the case that matters — the complex unit circle (hence the roots of
unity) — from the in-tree `unitCircle_reps_le_two` (a nonzero sum has `≤ 2` representations):

> **`unitCircle_sidonModNeg`** — every finite set `S` on the complex unit circle satisfies
> `SidonModNeg S`.

Composed with the campaign's energy theorem this gives the **unconditional** exact additive
energy of any negation-closed unit-circle set — in particular `E(μ_n) = 3n² − 3n` for even `n`
(the rigid char-0 anchor: `μ_n`'s only nontrivial additive relations are antipodal).  The engine
is `unitCircle_filter_eq_pair`: a nonzero sum `a + b` has representation set **exactly** `{a, b}`,
because a third representative would force `≥ 3 > 2` reps.  This is the bridge that turns the
campaign's conditional energy/Sidon results into theorems about the actual smooth domain.
Issue #389.
-/

open Polynomial Finset
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

variable {S : Finset ℂ}

/-- **A nonzero sum's representation set is exactly the pair.**  For `a, b` on the unit circle
with `a + b ≠ 0`, `{y ∈ S : (a+b) − y ∈ S} = {a, b}` — a third representative `y ∉ {a,b}`
produces three distinct representatives, contradicting `unitCircle_reps_le_two`. -/
theorem unitCircle_filter_eq_pair (hunit : ∀ y ∈ S, y * conj y = 1) {a b : ℂ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a + b ≠ 0) :
    S.filter (fun y => (a + b) - y ∈ S) = {a, b} := by
  classical
  have hle2 : (S.filter (fun y => (a + b) - y ∈ S)).card ≤ 2 :=
    unitCircle_reps_le_two (a + b) hab S hunit
  have hain : a ∈ S.filter (fun y => (a + b) - y ∈ S) := by
    rw [Finset.mem_filter]; exact ⟨ha, by rw [show a + b - a = b from by ring]; exact hb⟩
  have hbin : b ∈ S.filter (fun y => (a + b) - y ∈ S) := by
    rw [Finset.mem_filter]; exact ⟨hb, by rw [show a + b - b = a from by ring]; exact ha⟩
  refine Finset.Subset.antisymm ?_ ?_
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyS, hyrep⟩ := hy
    by_contra hcon
    rw [Finset.mem_insert, Finset.mem_singleton] at hcon
    push_neg at hcon
    obtain ⟨hya, hyb⟩ := hcon
    have hyin : y ∈ S.filter (fun z => (a + b) - z ∈ S) := by
      rw [Finset.mem_filter]; exact ⟨hyS, hyrep⟩
    have hcin : a + b - y ∈ S.filter (fun z => (a + b) - z ∈ S) := by
      rw [Finset.mem_filter]
      exact ⟨hyrep, by rw [show a + b - (a + b - y) = y from by ring]; exact hyS⟩
    by_cases hab2 : a = b
    · -- a = b: the three distinct reps are a, y, (a+a)-y
      subst hab2
      have h3 : ({a, y, a + a - y} : Finset ℂ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; intro h; exact hya (by linear_combination h / 2)
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨fun h => hya h.symm, fun h => hya (by linear_combination h)⟩
      have hsub : ({a, y, a + a - y} : Finset ℂ) ⊆ S.filter (fun z => (a + a) - z ∈ S) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hain
        · exact hyin
        · exact hcin
      have := Finset.card_le_card hsub
      rw [h3] at this; omega
    · -- a ≠ b: the three distinct reps are a, b, y
      have h3 : ({a, b, y} : Finset ℂ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; exact fun h => hyb h.symm
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hab2, fun h => hya h.symm⟩
      have hsub : ({a, b, y} : Finset ℂ) ⊆ S.filter (fun z => (a + b) - z ∈ S) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hain
        · exact hbin
        · exact hyin
      have := Finset.card_le_card hsub
      rw [h3] at this; omega
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hain
    · exact hbin

/-- **Unit-circle sets are Sidon-modulo-negation.**  Every finite `S` on the complex unit circle
satisfies `AdditiveEnergySidonModNeg.SidonModNeg S`: the only additive coincidences `a+b=c+d` are
the trivial ones or the zero-sum ones.  This DISCHARGES the standing hypothesis of the campaign's
exact-energy theorem for the roots of unity. -/
theorem unitCircle_sidonModNeg (hunit : ∀ y ∈ S, y * conj y = 1) :
    AdditiveEnergySidonModNeg.SidonModNeg S := by
  classical
  intro a ha b hb c hc d hd hsum
  by_cases hab : a + b = 0
  · exact Or.inr (Or.inr hab)
  · have hpair := unitCircle_filter_eq_pair hunit ha hb hab
    have hcin : c ∈ S.filter (fun y => (a + b) - y ∈ S) := by
      rw [Finset.mem_filter]
      exact ⟨hc, by rw [hsum, show c + d - c = d from by ring]; exact hd⟩
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hcin
    rcases hcin with rfl | rfl
    · exact Or.inl ⟨rfl, by linear_combination hsum⟩
    · exact Or.inr (Or.inl ⟨by linear_combination hsum, rfl⟩)

/-- **The exact char-0 additive energy of a negation-closed unit-circle set, UNCONDITIONAL.**
Composing the discharger with the campaign's energy theorem: any finite negation-closed `S` on
the unit circle (e.g. the even-order roots of unity `μ_n`) has additive energy EXACTLY
`3|S|² − 3|S| = 3|S|(|S|−1)` — the Sidon floor plus the forced antipodal correction.  This is
the rigid char-0 anchor the finite-field proximity prize inflates from. -/
theorem unitCircle_negClosed_additiveEnergy_eq (hunit : ∀ y ∈ S, y * conj y = 1)
    (hneg : ∀ y ∈ S, -y ∈ S) :
    AdditiveEnergyRepBound.additiveEnergy S = 3 * S.card ^ 2 - 3 * S.card := by
  have h0 : (0 : ℂ) ∉ S := fun h => by simpa using hunit 0 h
  exact AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg
    two_ne_zero h0 hneg (unitCircle_sidonModNeg hunit)

open AdditiveEnergyRepBound in
/-- The pointwise representation count on the unit circle: `repCount S (a+b)` is `repCount S 0`
when `a+b=0` and `|{a,b}|` otherwise. -/
theorem unitCircle_repCount (hunit : ∀ y ∈ S, y * conj y = 1) {a b : ℂ}
    (ha : a ∈ S) (hb : b ∈ S) :
    repCount S (a + b) = if a + b = 0 then repCount S 0 else ({a, b} : Finset ℂ).card := by
  by_cases hab : a + b = 0
  · rw [if_pos hab, hab]
  · rw [if_neg hab, repCount, unitCircle_filter_eq_pair hunit ha hb hab]

/-- Pure counting: `∑_{a,b∈S} |{a,b}| + |S| = 2|S|²` (`|{a,b}| + [a=b] = 2` pointwise). -/
theorem pair_card_sum {α : Type*} [DecidableEq α] (T : Finset α) :
    (∑ a ∈ T, ∑ b ∈ T, ({a, b} : Finset α).card) + T.card = 2 * T.card ^ 2 := by
  classical
  have hkey : ∀ a ∈ T, (∑ b ∈ T, ({a, b} : Finset α).card)
      + (T.filter (fun b => a = b)).card = 2 * T.card := by
    intro a _
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    calc (∑ b ∈ T, (({a, b} : Finset α).card + if a = b then 1 else 0))
        = ∑ _b ∈ T, 2 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases hab : a = b
          · subst hab; simp
          · rw [Finset.card_pair hab]; simp [hab]
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hdiag : (∑ a ∈ T, (T.filter (fun b => a = b)).card) = T.card := by
    refine (Finset.sum_congr rfl fun a ha => ?_).trans (by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one])
    rw [Finset.filter_eq T a, if_pos ha, Finset.card_singleton]
  calc (∑ a ∈ T, ∑ b ∈ T, ({a, b} : Finset α).card) + T.card
      = (∑ a ∈ T, ∑ b ∈ T, ({a, b} : Finset α).card)
        + (∑ a ∈ T, (T.filter (fun b => a = b)).card) := by rw [hdiag]
    _ = ∑ a ∈ T, ((∑ b ∈ T, ({a, b} : Finset α).card)
          + (T.filter (fun b => a = b)).card) := by rw [Finset.sum_add_distrib]
    _ = ∑ _a ∈ T, (2 * T.card) := Finset.sum_congr rfl hkey
    _ = 2 * T.card ^ 2 := by rw [Finset.sum_const, smul_eq_mul]; ring

open AdditiveEnergyRepBound in
/-- **THE EXACT char-0 additive energy of ANY unit-circle set** (both parities, no
negation-closure needed): `E(S) + 2·r₀ + |S| = r₀² + 2|S|²`, with `r₀ = repCount S 0` the
ordered antipodal-pair count.  Specializes to `E(μ_n) = 2n²−n` (`n` odd, `r₀=0`, SIDON) and
`3n²−3n` (`n` even, `r₀=n`).  Sharpens the in-tree `≤ 3|S|²` to an exact equality for every
finite unit-circle set — the complete form-2/3 char-0 anchor. -/
theorem unitCircle_additiveEnergy_eq (hunit : ∀ y ∈ S, y * conj y = 1) :
    additiveEnergy S + 2 * repCount S 0 + S.card = repCount S 0 ^ 2 + 2 * S.card ^ 2 := by
  classical
  set r0 := repCount S 0 with hr0
  have hne0 : ∀ a ∈ S, a ≠ 0 := fun a ha h => by simpa [h] using hunit a ha
  -- antipodal-pair count `Z = ∑_{a,b} [a+b=0] = r0`
  have hZ : (∑ a ∈ S, ∑ b ∈ S, if a + b = 0 then (1 : ℕ) else 0) = r0 := by
    have hinner : ∀ a, (∑ b ∈ S, if a + b = 0 then (1 : ℕ) else 0)
        = if -a ∈ S then 1 else 0 := by
      intro a
      have hcond : ∀ b, (a + b = 0) ↔ (b = -a) :=
        fun b => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
      simp only [hcond]
      exact Finset.sum_ite_eq' S (-a) (fun _ => 1)
    rw [Finset.sum_congr rfl (fun a _ => hinner a), hr0, repCount, Finset.card_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [zero_sub]
  -- `repCount S (a+b) = if a+b=0 then r0 else |{a,b}|`
  have hE : additiveEnergy S
      = ∑ a ∈ S, ∑ b ∈ S, (if a + b = 0 then r0 else ({a, b} : Finset ℂ).card) := by
    rw [additiveEnergy]
    exact Finset.sum_congr rfl fun a ha =>
      Finset.sum_congr rfl fun b hb => by rw [unitCircle_repCount hunit ha hb, hr0]
  -- the pointwise identity: g + 2·[a+b=0] = |{a,b}| + r0·[a+b=0]
  have hpt : ∀ a ∈ S, ∀ b ∈ S,
      (if a + b = 0 then r0 else ({a, b} : Finset ℂ).card)
        + 2 * (if a + b = 0 then (1 : ℕ) else 0)
      = ({a, b} : Finset ℂ).card + r0 * (if a + b = 0 then (1 : ℕ) else 0) := by
    intro a ha b hb
    by_cases hab : a + b = 0
    · have hane : a ≠ b := by
        intro h; exact hne0 a ha (by linear_combination hab / 2 + h / 2)
      rw [if_pos hab, if_pos hab, Finset.card_pair hane]; ring
    · rw [if_neg hab, if_neg hab]; ring
  -- `∑∑ 2·[a+b=0] = 2·r0` and `∑∑ r0·[a+b=0] = r0·r0`
  have h2z : (∑ a ∈ S, ∑ b ∈ S, 2 * (if a + b = 0 then (1 : ℕ) else 0)) = 2 * r0 := by
    simp only [← Finset.mul_sum]; rw [hZ]
  have hr0z : (∑ a ∈ S, ∑ b ∈ S, r0 * (if a + b = 0 then (1 : ℕ) else 0)) = r0 * r0 := by
    simp only [← Finset.mul_sum]; rw [hZ]
  -- sum the pointwise identity
  have hsum : (∑ a ∈ S, ∑ b ∈ S, (if a + b = 0 then r0 else ({a, b} : Finset ℂ).card))
        + 2 * r0
      = (∑ a ∈ S, ∑ b ∈ S, ({a, b} : Finset ℂ).card) + r0 ^ 2 := by
    have key : (∑ a ∈ S, ∑ b ∈ S, ((if a + b = 0 then r0 else ({a, b} : Finset ℂ).card)
          + 2 * (if a + b = 0 then (1 : ℕ) else 0)))
        = (∑ a ∈ S, ∑ b ∈ S, (({a, b} : Finset ℂ).card
          + r0 * (if a + b = 0 then (1 : ℕ) else 0))) :=
      Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hpt a ha b hb
    simp only [Finset.sum_add_distrib] at key
    rw [h2z, hr0z] at key
    rw [pow_two]
    exact key
  -- assemble with `pair_card_sum`
  have hpc := pair_card_sum S
  rw [hE]
  omega

end ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_filter_eq_pair
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_sidonModNeg
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_negClosed_additiveEnergy_eq
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.pair_card_sum
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_additiveEnergy_eq
