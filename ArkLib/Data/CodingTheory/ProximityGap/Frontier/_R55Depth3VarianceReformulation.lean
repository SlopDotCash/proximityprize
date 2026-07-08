/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMarkovWick
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# LANE B2 (#466 round 55): THE VARIANCE REFORMULATION — the DC-subtracted depth-3 energy IS the
  ℓ²-flatness deficit of the representation function

Every prior route to the deep-`r` wall (`Σ_{c≠0}‖η_c‖^{2r}` small) circled back to a character
sum.  This brick recasts the depth-3 target as an **equidistribution** statement, division-free,
with NO cyclotomic machinery — a different attack surface.

Let `rep3 G c` be the 3-fold representation function `#{(y₁,y₂,y₃) ∈ G³ : y₁+y₂+y₃ = c}`.  Then:

* `sum_rep3` :        `∑_c rep3 G c = |G|³`   (total triples);
* `addEnergy3_eq` :   `addEnergy3 G = ∑_c (rep3 G c)²`   (energy = ℓ² norm of the rep function);
* **`variance_identity`** :  `∑_c (q·rep3 G c − |G|³)² = q·(q·addEnergy3 G − |G|⁶)`.

The RHS is EXACTLY the DC-subtracted energy `q·E₃ − |G|⁶` (the object in `DCEnergyBound G 3`),
times `q`.  So:

* **`dcEnergyBound_three_iff_variance`** :  the prize's `DCEnergyBound G 3` holds **iff** the
  representation function is flat to within the Wick fluctuation:
  `∑_c (q·rep3 G c − |G|³)² ≤ 15·q²·|G|³`.

Two immediate unconditional facts:

* **`dc_floor`** :  `|G|⁶ ≤ q·addEnergy3 G` ALWAYS — the DC term is a genuine floor (the LHS
  variance is a sum of squares, `≥ 0`).  This is why the raw `E₃ ≤ Wick` fails and the
  DC-subtracted form is mandatory (cf. round 54).
* the target is now an **ℓ² equidistribution deficit**, inviting large-sieve / equidistribution
  tools on the multiplicative-subgroup representation function — not only character-sum bounds.

This does NOT close the prize: bounding the flatness deficit at `r ≈ log q` is still the
Paley / BGK wall.  It is a correct, machine-checked reformulation that sharpens the target and
opens a new toolset.  Issue #466, round 55, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation

open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.DCEnergyCorrection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **3-fold representation function**: the number of triples in `G³` summing to `c`. -/
def rep3 (G : Finset F) (c : F) : ℕ :=
  ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, if y₁ + y₂ + y₃ = c then 1 else 0

/-- **The weighted-triple regrouping.**  For any weight `g : F → ℕ`,
`∑_{y₁,y₂,y₃∈G} g(y₁+y₂+y₃) = ∑_c rep3 G c · g c`.  The engine behind `sum_rep3` (`g = 1`) and
`addEnergy3_eq` (`g = rep3 G`). -/
theorem sum_triples_weight (G : Finset F) (g : F → ℕ) :
    ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, g (y₁ + y₂ + y₃)
      = ∑ c : F, rep3 G c * g c := by
  classical
  unfold rep3
  -- RHS: distribute the `* g c` inside and pull the `c`-sum out
  have hR : ∑ c : F, (∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, if y₁ + y₂ + y₃ = c then 1 else 0) * g c
      = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ c : F, (if y₁ + y₂ + y₃ = c then 1 else 0) * g c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y₁ _ => ?_)
    rw [Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y₂ _ => ?_)
    rw [Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y₃ _ => ?_)
    rw [Finset.sum_mul]
  rw [hR]
  refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
    Finset.sum_congr rfl (fun y₃ _ => ?_)))
  -- ∑_c (if s = c then 1 else 0) * g c = g s
  have hpt : ∀ c : F, (if y₁ + y₂ + y₃ = c then (1:ℕ) else 0) * g c
      = if y₁ + y₂ + y₃ = c then g c else 0 := by
    intro c; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun c _ => hpt c),
    Finset.sum_ite_eq Finset.univ (y₁ + y₂ + y₃) g]
  simp

/-- **Total mass**: the representation function sums to `|G|³`. -/
theorem sum_rep3 (G : Finset F) : ∑ c : F, rep3 G c = (G.card) ^ 3 := by
  have h := sum_triples_weight G (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  ring

/-- **Energy = ℓ² of the representation function**: `addEnergy3 G = ∑_c (rep3 G c)²`. -/
theorem addEnergy3_eq (G : Finset F) : addEnergy3 G = ∑ c : F, (rep3 G c) ^ 2 := by
  classical
  -- fold the inner (y₄,y₅,y₆)-sum of `addEnergy3` into `rep3 (y₁+y₂+y₃)`
  have hfold : addEnergy3 G = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, rep3 G (y₁ + y₂ + y₃) := by
    unfold addEnergy3 rep3
    refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
      Finset.sum_congr rfl (fun y₃ _ => ?_)))
    refine Finset.sum_congr rfl (fun y₄ _ => Finset.sum_congr rfl (fun y₅ _ =>
      Finset.sum_congr rfl (fun y₆ _ => ?_)))
    by_cases h : y₁ + y₂ + y₃ = y₄ + y₅ + y₆ <;> simp [h, eq_comm]
  rw [hfold, sum_triples_weight G (rep3 G)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [sq]

/-- **THE VARIANCE IDENTITY (round-55 main theorem).**  The DC-subtracted depth-3 energy is the
ℓ²-flatness deficit of the representation function:
`∑_c (q·rep3 G c − |G|³)² = q·(q·addEnergy3 G − |G|⁶)`. -/
theorem variance_identity (G : Finset F) :
    ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      = (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (addEnergy3 G : ℝ) - (G.card : ℝ) ^ 6) := by
  have hsum : ∑ c : F, (rep3 G c : ℝ) = (G.card : ℝ) ^ 3 := by
    have := sum_rep3 G
    calc ∑ c : F, (rep3 G c : ℝ) = ((∑ c : F, rep3 G c : ℕ) : ℝ) := by push_cast; rfl
      _ = ((G.card ^ 3 : ℕ) : ℝ) := by rw [this]
      _ = (G.card : ℝ) ^ 3 := by push_cast; ring
  have hsq : ∑ c : F, (rep3 G c : ℝ) ^ 2 = (addEnergy3 G : ℝ) := by
    have := addEnergy3_eq G
    calc ∑ c : F, (rep3 G c : ℝ) ^ 2 = ((∑ c : F, (rep3 G c) ^ 2 : ℕ) : ℝ) := by push_cast; rfl
      _ = ((addEnergy3 G : ℕ) : ℝ) := by rw [← this]
  have hcard : ∑ _c : F, (1 : ℝ) = (Fintype.card F : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  -- expand the square and collect
  have hexp : ∀ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      = (Fintype.card F : ℝ) ^ 2 * (rep3 G c : ℝ) ^ 2
        - 2 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 3 * (rep3 G c : ℝ)
        + (G.card : ℝ) ^ 6 * 1 := by
    intro c; ring
  rw [Finset.sum_congr rfl (fun c _ => hexp c)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsq, hsum, hcard]
  ring

/-- **THE DC FLOOR (unconditional).**  `|G|⁶ ≤ q·addEnergy3 G` for every field and every `G`:
the DC term is a genuine lower bound on the energy, not a removable artifact. -/
theorem dc_floor (G : Finset F) :
    (G.card : ℝ) ^ 6 ≤ (Fintype.card F : ℝ) * (addEnergy3 G : ℝ) := by
  have hvar : (0 : ℝ) ≤ (Fintype.card F : ℝ)
      * ((Fintype.card F : ℝ) * (addEnergy3 G : ℝ) - (G.card : ℝ) ^ 6) := by
    rw [← variance_identity G]
    exact Finset.sum_nonneg (fun c _ => sq_nonneg _)
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith [hvar, hq]

/-- **THE VARIANCE FORM OF THE PRIZE TARGET (round-55 headline).**  The prize's DC-subtracted
depth-3 energy bound is EQUIVALENT to the representation function being flat to within the Wick
fluctuation: `DCEnergyBound G 3 ↔ ∑_c (q·rep3 G c − |G|³)² ≤ 15·q²·|G|³`. -/
theorem dcEnergyBound_three_iff_variance {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    DCEnergyBound G 3
      ↔ ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 := by
  have hbridge : (rEnergy G 3 : ℝ) = (addEnergy3 G : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (rEnergy_three_eq_addEnergy3 hψ G)
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold DCEnergyBound
  rw [hbridge]
  have hpow : (G.card : ℝ) ^ (2 * 3) = (G.card : ℝ) ^ 6 := by norm_num
  rw [hpow]
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rw [hdf, variance_identity G]
  -- goal: (q·E − n⁶ ≤ q·(15·n³))  ↔  (q·(q·E − n⁶) ≤ 15·q²·n³)
  constructor
  · intro h
    calc (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (addEnergy3 G : ℝ) - (G.card : ℝ) ^ 6)
        ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_left h (le_of_lt hq)
      _ = 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 := by ring
  · intro h
    have h' : (Fintype.card F : ℝ)
        * ((Fintype.card F : ℝ) * (addEnergy3 G : ℝ) - (G.card : ℝ) ^ 6)
        ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3)) := by
      rw [show (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3))
        = 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 from by ring]
      exact h
    exact le_of_mul_le_mul_left h' hq

end ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation
