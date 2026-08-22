/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMarkovWick
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyRungThree
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R53Depth3ExcessHeadroom

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

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.EnergyBoundImplication
open ArkLib.ProximityGap.DCEnergyRungThree
open ArkLib.ProximityGap.GaussianEnergyThreeRepThree
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom

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
  -- per-`c`, distribute `g c` through the triple sum
  have hc : ∀ c : F, rep3 G c * g c
      = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, if y₁ + y₂ + y₃ = c then g c else 0 := by
    intro c
    unfold rep3
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y₁ _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y₂ _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y₃ _ => ?_)
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun c _ => hc c)]
  -- pull the `c`-sum inside past the three `G`-sums (targeting only the RHS), then collapse
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y₁ _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y₂ _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y₃ _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (y₁ + y₂ + y₃) g]
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

/-- **Variance-flatness input gives the depth-3 DC energy bound.**  This is the forward
consumer form of `dcEnergyBound_three_iff_variance`, useful for plugging large-sieve or
equidistribution estimates on `rep3` directly into the prize-correct moment hypothesis. -/
theorem dcEnergyBound_three_of_variance {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hvar : ∑ c : F,
        ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3) :
    DCEnergyBound G 3 :=
  (dcEnergyBound_three_iff_variance hψ G).mpr hvar

/-- **DC energy input gives variance flatness.**  This is the reverse consumer form of
`dcEnergyBound_three_iff_variance`: any existing r=3 `DCEnergyBound` producer can now feed
the representation-function flatness surface directly. -/
theorem variance_bound_of_dcEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hdc : DCEnergyBound G 3) :
    ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 :=
  (dcEnergyBound_three_iff_variance hψ G).mp hdc

/-- **Raw Gaussian r=3 input gives variance flatness.**  This records that the round-55
flatness surface also subsumes every older producer of the stronger raw Wick statement
`GaussianEnergyBound G 3`. -/
theorem variance_bound_of_gaussianEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hgauss : GaussianEnergyBound G 3) :
    ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 :=
  variance_bound_of_dcEnergyBound hψ G (dcEnergyBound_of_gaussianEnergyBound hgauss)

/-- **Depth-3 excess headroom gives variance flatness.**  The round-53 one-sided excess
target now feeds the round-55 representation-function target directly. -/
theorem variance_bound_of_excess_headroom {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {E : ℝ} (hexc : Depth3ExcessBounded G E)
    (hhead : E ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ)) :
    ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 :=
  variance_bound_of_gaussianEnergyBound hψ G
    (gaussianEnergyBound_three_of_excess_headroom hψ G hexc hhead)

/-- **Quadratic depth-3 excess gives variance flatness.**  This is the concrete round-52/53
regime (`E = C n²`, `C ≤ 44`, `n ≥ 40`) stated on the variance side. -/
theorem variance_bound_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ)) :
    ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 :=
  variance_bound_of_gaussianEnergyBound hψ G
    (gaussianEnergyBound_three_of_quadraticExcess hψ G hexc hC hn)

/-- **Variance-flatness input gives the nonzero-frequency sixth-moment bound.**  This closes the
round-55 equidistribution interface to the same per-frequency endpoint as the round-54 headroom
route: for every nonzero `b`, `‖η_b‖⁶ ≤ 15 q |G|³`. -/
theorem eta_sixth_le_of_variance {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hvar : ∑ c : F,
        ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
  have hdc : DCEnergyBound G 3 := dcEnergyBound_three_of_variance hψ G hvar
  have h := eta_pow_le_of_dcEnergyBound hψ hdc hb
  have hpow : (2 * 3 : ℕ) = 6 := by norm_num
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rw [hpow, hdf] at h
  exact h

/-- **Variance-flatness gives a nonzero-frequency sixth-moment level-set bound.**  This is the
DC-correct level-set consumer: the zero frequency is excluded, so the variance/DCEnergy input
controls the whole remaining sixth-moment mass. -/
theorem nonzero_levelset_sixth_of_variance {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hvar : ∑ c : F,
        ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (((Finset.univ.erase (0 : F)).filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ)
        * lam ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
  classical
  set S := (Finset.univ.erase (0 : F)).filter (fun b => lam ≤ ‖eta ψ G b‖) with hSdef
  have hconst : (S.card : ℝ) * lam ^ 6 = ∑ _b ∈ S, lam ^ 6 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hpoint : ∑ _b ∈ S, lam ^ 6 ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 6 :=
    Finset.sum_le_sum (fun b hb => pow_le_pow_left₀ hlam (Finset.mem_filter.mp hb).2 6)
  have hsubset : S ⊆ Finset.univ.erase (0 : F) := Finset.filter_subset _ _
  have hmass : ∑ b ∈ S, ‖eta ψ G b‖ ^ 6
      ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun b _ _ => by positivity)
  have hdc : DCEnergyBound G 3 := dcEnergyBound_three_of_variance hψ G hvar
  have hdc' : (Fintype.card F : ℝ) * (rEnergy G 3 : ℝ) - (G.card : ℝ) ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
    unfold DCEnergyBound at hdc
    have hpow : (2 * 3 : ℕ) = 6 := by norm_num
    have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by
      norm_num [Nat.doubleFactorial]
    rwa [hpow, hdf] at hdc
  have hsum : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6
      = (Fintype.card F : ℝ) * (rEnergy G 3 : ℝ) - (G.card : ℝ) ^ 6 := by
    have h := sum_nonzero_moment hψ G 3
    have hpow : (2 * 3 : ℕ) = 6 := by norm_num
    rwa [hpow] at h
  calc
    (S.card : ℝ) * lam ^ 6 = ∑ _b ∈ S, lam ^ 6 := hconst
    _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 6 := hpoint
    _ ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6 := hmass
    _ = (Fintype.card F : ℝ) * (rEnergy G 3 : ℝ) - (G.card : ℝ) ^ 6 := hsum
    _ ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := hdc'

/-- **Variance-flatness forbids nonzero Johnson-scale frequencies under the sixth-moment guard.**
If `15 |G|³ < q²`, then the nonzero frequencies with
`sqrt(q) ≤ ‖eta ψ G b‖` form an empty set. This is the DC-correct analogue of the
sixth-moment no-Johnson corollary: the principal frequency is excluded by construction. -/
theorem no_nonzero_sqrt_card_levelset_of_variance_lt {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F)
    (hvar : ∑ c : F,
        ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    (hlt : 15 * (G.card : ℝ) ^ 3 < (Fintype.card F : ℝ) ^ 2) :
    ((Finset.univ.erase (0 : F)).filter
      (fun b => Real.sqrt (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖)) = ∅ := by
  classical
  by_contra hne
  set S := (Finset.univ.erase (0 : F)).filter
    (fun b => Real.sqrt (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖) with hSdef
  have hnemp : S.Nonempty := by
    rw [hSdef]
    exact Finset.nonempty_iff_ne_empty.mpr hne
  have hcard1 : (1 : ℝ) ≤ (S.card : ℝ) := by
    have : 1 ≤ S.card := Finset.Nonempty.card_pos hnemp
    exact_mod_cast this
  have hq0 : 0 ≤ (Fintype.card F : ℝ) := by positivity
  have hsqrt_pow : (Real.sqrt (Fintype.card F : ℝ)) ^ 6
      = (Fintype.card F : ℝ) ^ 3 := by
    calc
      (Real.sqrt (Fintype.card F : ℝ)) ^ 6
          = ((Real.sqrt (Fintype.card F : ℝ)) ^ 2) ^ 3 := by ring
      _ = (Fintype.card F : ℝ) ^ 3 := by rw [Real.sq_sqrt hq0]
  have hlevel := nonzero_levelset_sixth_of_variance hψ G hvar
    (Real.sqrt_nonneg (Fintype.card F : ℝ))
  rw [← hSdef, hsqrt_pow] at hlevel
  have hqpos : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq3pos : 0 < (Fintype.card F : ℝ) ^ 3 := by positivity
  have hq3le : (Fintype.card F : ℝ) ^ 3 ≤
      (S.card : ℝ) * (Fintype.card F : ℝ) ^ 3 := by
    nlinarith [hcard1, hq3pos]
  have hguard_mul :
      (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3)
        < (Fintype.card F : ℝ) ^ 3 := by
    nlinarith [hlt, hqpos]
  linarith [hq3le, hlevel, hguard_mul]

/-- **Quadratic depth-3 excess forbids nonzero Johnson-scale frequencies.**  This is the
concrete round-52/53 atom composed through the round-55 variance surface: if
`Depth3ExcessBounded G (C n²)` with `C ≤ 44`, `n ≥ 40`, and `15n³ < q²`, then no nonzero
frequency reaches `sqrt(q)`. -/
theorem no_nonzero_sqrt_card_levelset_of_quadraticExcess_lt {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hlt : 15 * (G.card : ℝ) ^ 3 < (Fintype.card F : ℝ) ^ 2) :
    ((Finset.univ.erase (0 : F)).filter
      (fun b => Real.sqrt (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖)) = ∅ :=
  no_nonzero_sqrt_card_levelset_of_variance_lt hψ G
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hlt

/-- **The older `RepThree` atom implies the variance-flatness target.**  This connects the
round-407 antipodal-pairing residual to the round-55 representation-function formulation:
for negation-closed `G`, `RepThree G` is strong enough to prove the Wick-scale flatness
inequality for `rep3`. -/
theorem variance_bound_of_repThree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : ∀ x ∈ G, -x ∈ G) (hrep : RepThree G) :
    ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 :=
  variance_bound_of_dcEnergyBound hψ G (dcEnergyBound_three_of_repThree hψ hG hrep)

end ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.sum_rep3
#print axioms ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.addEnergy3_eq
#print axioms ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.variance_identity
#print axioms ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.dc_floor
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.dcEnergyBound_three_iff_variance
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.dcEnergyBound_three_of_variance
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.variance_bound_of_dcEnergyBound
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.variance_bound_of_gaussianEnergyBound
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.variance_bound_of_excess_headroom
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.variance_bound_of_quadraticExcess
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.eta_sixth_le_of_variance
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.nonzero_levelset_sixth_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.no_nonzero_sqrt_card_levelset_of_variance_lt
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.no_nonzero_sqrt_card_levelset_of_quadraticExcess_lt
#print axioms
  ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation.variance_bound_of_repThree
