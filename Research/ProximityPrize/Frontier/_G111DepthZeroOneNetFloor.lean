/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# G111: depth zero and depth one have a nonnegative net anomaly

The exact signed-depth weld writes the depth-`s` anomaly as `q*D_s-P_s`, where `D_s` is the
equal-sum depth fiber and `P_s` is the corresponding all-pairs population.  Landed structure gives
`D₀=P₀` and `D₁=0`, hence

`A₀+A₁ = (q-1)P₀-P₁`.

A depth-one pair differs, after maximal cancellation, by one symbol on each side.  Repairing one
chosen residual coordinate turns it into a depth-zero pair; recording the coordinate and its old
symbol suggests the concrete finite encoding `P₁ ≤ r*n*P₀`.  This file proves the exact arithmetic
consumer: under that repair-map bound and `r*n+1 ≤ q`, the combined anomaly is nonnegative.

Thus depth one's deterministic negative sign cannot pay any of the positive depth-zero floor at
the production field size.  Genuine signed compensation must involve depth at least two.  The
actual word-pair repair injection remains an explicit combinatorial input; no analytic closure is
claimed.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor

/-- Code suggested by the one-coordinate repair operation: repaired depth-zero object, repaired
coordinate, and the overwritten alphabet symbol. -/
abbrev RepairCode (X₀ A : Type*) (r : ℕ) := X₀ × Fin r × A

/-- Exact cardinality of the repair code. -/
theorem card_repairCode (X₀ A : Type*) [Fintype X₀] [Fintype A] (r : ℕ) :
    Fintype.card (RepairCode X₀ A r) = r * Fintype.card A * Fintype.card X₀ := by
  simp only [RepairCode, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Any injective one-coordinate repair encoding proves the population bound needed below. -/
theorem card_le_of_injective_repair
    (X₁ X₀ A : Type*) [Fintype X₁] [Fintype X₀] [Fintype A]
    (r : ℕ) (encode : X₁ → RepairCode X₀ A r)
    (hencode : Function.Injective encode) :
    Fintype.card X₁ ≤ r * Fintype.card A * Fintype.card X₀ := by
  rw [← card_repairCode X₀ A r]
  exact Fintype.card_le_of_injective encode hencode

/-- Natural-number form of the net-floor inequality. -/
theorem depth_zero_one_population_le
    {q r n P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ r * n * P₀)
    (hfield : r * n + 1 ≤ q) :
    P₀ + P₁ ≤ q * P₀ := by
  calc
    P₀ + P₁ ≤ P₀ + r * n * P₀ := Nat.add_le_add_left hrepair _
    _ = (r * n + 1) * P₀ := by ring
    _ ≤ q * P₀ := Nat.mul_le_mul_right _ hfield

/-- Signed anomaly form.  With `D₀=P₀` and `D₁=0`, the combined depth-zero/depth-one anomaly is
`q*P₀-P₀-P₁`, which is nonnegative under the repair-map population bound. -/
theorem depth_zero_one_anomaly_nonneg
    {q r n P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ r * n * P₀)
    (hfield : r * n + 1 ≤ q) :
    (0 : ℤ) ≤ (q : ℤ) * P₀ - P₀ - P₁ := by
  have h := depth_zero_one_population_le hrepair hfield
  have hz : (P₀ : ℤ) + P₁ ≤ (q : ℤ) * P₀ := by exact_mod_cast h
  omega

/-- Quantitative form: after paying the entire depth-one population, at least
`(q-1-r*n)*P₀` of signed depth-zero mass remains.  This statement is over integers and therefore
does not require a separate nonnegativity guard on the coefficient. -/
theorem depth_zero_one_anomaly_lower_bound
    {q r n P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ r * n * P₀) :
    ((q : ℤ) - 1 - (r : ℤ) * n) * P₀ ≤
      (q : ℤ) * P₀ - P₀ - P₁ := by
  have hz : (P₁ : ℤ) ≤ (r : ℤ) * n * P₀ := by exact_mod_cast hrepair
  nlinarith

/-- Absolute form using the diagonal injection into the depth-zero population: if `n^r ≤ P₀`,
then the first two depths leave at least `(q-1-r*n)*n^r` signed mass. -/
theorem depth_zero_one_absolute_lower_bound
    {q r n P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ r * n * P₀)
    (hdiag : n ^ r ≤ P₀)
    (hfield : r * n + 1 ≤ q) :
    ((q : ℤ) - 1 - (r : ℤ) * n) * (n : ℤ) ^ r ≤
      (q : ℤ) * P₀ - P₀ - P₁ := by
  have hfieldZ : ((r * n + 1 : ℕ) : ℤ) ≤ q := by exact_mod_cast hfield
  have hcoef : (0 : ℤ) ≤ (q : ℤ) - 1 - (r : ℤ) * n := by
    push_cast at hfieldZ
    nlinarith
  have hdiagZ : (n : ℤ) ^ r ≤ P₀ := by exact_mod_cast hdiag
  calc
    ((q : ℤ) - 1 - (r : ℤ) * n) * (n : ℤ) ^ r ≤
        ((q : ℤ) - 1 - (r : ℤ) * n) * P₀ :=
      mul_le_mul_of_nonneg_left hdiagZ hcoef
    _ ≤ (q : ℤ) * P₀ - P₀ - P₁ := depth_zero_one_anomaly_lower_bound hrepair

/-- End-to-end abstract repair consumer: an injective repair code and the field-size guard imply
that the depth-zero/depth-one signed anomaly is nonnegative. -/
theorem anomaly_nonneg_of_injective_repair
    (X₁ X₀ A : Type*) [Fintype X₁] [Fintype X₀] [Fintype A]
    (q r : ℕ) (encode : X₁ → RepairCode X₀ A r)
    (hencode : Function.Injective encode)
    (hfield : r * Fintype.card A + 1 ≤ q) :
    (0 : ℤ) ≤ (q : ℤ) * Fintype.card X₀ - Fintype.card X₀ - Fintype.card X₁ := by
  apply depth_zero_one_anomaly_nonneg (n := Fintype.card A)
  · exact card_le_of_injective_repair X₁ X₀ A r encode hencode
  · exact hfield

/-- Production field size overwhelmingly satisfies the only arithmetic guard. -/
theorem production_depth_zero_one_field_guard :
    110 * (2 ^ 30) + 1 ≤ (2 ^ 30) * (2 ^ 128 + 192) + 1 := by
  norm_num

/-- Production specialization: any concrete repair encoding with at most `110*n` labels per
depth-zero pair forces the first two signed depth anomalies to have nonnegative total. -/
theorem production_depth_zero_one_anomaly_nonneg
    {P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ 110 * (2 ^ 30) * P₀) :
    (0 : ℤ) ≤ (((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) * P₀ - P₀ - P₁ := by
  exact depth_zero_one_anomaly_nonneg hrepair production_depth_zero_one_field_guard

/-- Production quantitative residue.  Any negative cross-depth compensation for this explicit
positive multiple of the depth-zero population can only come from depths at least two. -/
theorem production_depth_zero_one_anomaly_lower_bound
    {P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ 110 * (2 ^ 30) * P₀) :
    (((2 ^ 30) * (2 ^ 128 + 192) - 110 * (2 ^ 30) : ℕ) : ℤ) * P₀ ≤
      (((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) * P₀ - P₀ - P₁ := by
  have h := depth_zero_one_anomaly_lower_bound
    (q := (2 ^ 30) * (2 ^ 128 + 192) + 1) (r := 110) (n := 2 ^ 30) hrepair
  norm_num at h ⊢
  exact h

/-- Production absolute residue after inserting the diagonal population floor
`n^110 ≤ P₀`. -/
theorem production_depth_zero_one_absolute_lower_bound
    {P₀ P₁ : ℕ}
    (hrepair : P₁ ≤ 110 * (2 ^ 30) * P₀)
    (hdiag : (2 ^ 30) ^ 110 ≤ P₀) :
    (((2 ^ 30) * (2 ^ 128 + 82) : ℕ) : ℤ) * ((2 ^ 30 : ℕ) : ℤ) ^ 110 ≤
      (((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) * P₀ - P₀ - P₁ := by
  have h := depth_zero_one_absolute_lower_bound
    (q := (2 ^ 30) * (2 ^ 128 + 192) + 1) (r := 110) (n := 2 ^ 30)
    hrepair hdiag production_depth_zero_one_field_guard
  norm_num at h ⊢
  exact h

/-- **Interpretation guard.**  Although the absolute floor is large, it still fits inside the
full signed-depth Wick allowance.  Therefore G111 alone does not force the depth-`≥2` tail to be
negative; it only proves that depths zero and one cannot provide negative compensation. -/
theorem production_absolute_floor_fits_signed_wick_budget :
    ((2 ^ 30) * (2 ^ 128 + 82)) * (2 ^ 30) ^ 110 ≤
      ((2 ^ 30) * (2 ^ 128 + 192) + 1) *
        (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) := by
  norm_num [Nat.doubleFactorial]

/-- Lossless arithmetic extraction of the remaining tail budget.  A lower bound `L ≤ head` and
the global signed bound `head + tail ≤ B` imply `tail ≤ B-L`; no sign is asserted for the tail. -/
theorem tail_le_budget_sub_floor
    {head tail floor budget : ℤ}
    (hfloor : floor ≤ head)
    (htotal : head + tail ≤ budget) :
    tail ≤ budget - floor := by
  linarith

/-- Production residual target for the aggregate anomaly over depths at least two.  This theorem
is intentionally parameterized by that aggregate `tail`; welding it to G101 is purely a finite-sum
rewrite once the concrete repair and diagonal injections are supplied. -/
theorem production_depth_ge_two_tail_allowance
    {P₀ P₁ : ℕ} {tail : ℤ}
    (hrepair : P₁ ≤ 110 * (2 ^ 30) * P₀)
    (hdiag : (2 ^ 30) ^ 110 ≤ P₀)
    (htotal :
      ((((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) * P₀ - P₀ - P₁) + tail ≤
        (((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) *
          (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110)) :
    tail ≤
      (((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) *
          (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) -
        (((2 ^ 30) * (2 ^ 128 + 82) : ℕ) : ℤ) * ((2 ^ 30 : ℕ) : ℤ) ^ 110 := by
  apply tail_le_budget_sub_floor
    (head := (((2 ^ 30) * (2 ^ 128 + 192) + 1 : ℕ) : ℤ) * P₀ - P₀ - P₁)
  · exact production_depth_zero_one_absolute_lower_bound hrepair hdiag
  · exact htotal

end ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.anomaly_nonneg_of_injective_repair
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.depth_zero_one_population_le
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.depth_zero_one_anomaly_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.depth_zero_one_anomaly_lower_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.depth_zero_one_absolute_lower_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.production_depth_zero_one_anomaly_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.production_depth_zero_one_anomaly_lower_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.production_depth_zero_one_absolute_lower_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.production_absolute_floor_fits_signed_wick_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.tail_le_budget_sub_floor
#print axioms
  ArkLib.ProximityGap.Frontier.G111DepthZeroOneNetFloor.production_depth_ge_two_tail_allowance
