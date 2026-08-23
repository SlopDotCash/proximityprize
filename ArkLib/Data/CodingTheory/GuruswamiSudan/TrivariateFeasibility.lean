/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.TrivariateInterpolation

/-!
# Trivariate GS feasibility past the unique-decoding radius ([BCIKS20] §5 radius window)

Pure arithmetic linking the trivariate GS cubic dimension count to a decoding radius strictly past
the unique-decoding radius. `gs3_feasible_radius_past_udr` bundles the nonzero-interpolant existence
(`exists_ne_zero_vanishesToOrder3_of_cubic`) with the Z-root decoding criterion `D < (n-e)·m` and
the strict past-UDR bound `(n-k)/2 < e` under an integer window condition;
`gs3_feasible_radius_past_udr_witness` certifies non-vacuity (`k=2, ρ=2, D=14, m=2, n=20 ⟹ e=12 >
UDR=9`). (The full `(2·min(1-√ρ-δ,√ρ/20))⁷` Johnson-radius optimization with irrational `√ρ`
remains the multi-paper kernel.)
-/
open Finset
namespace GS3

variable {F : Type*} [Field F]

/-- The derived Sudan/curve agreement radius `e := n − (D/m + 1)` satisfies the Z-root decoding
criterion `D < (n − e)·m` when `0 < m` and `D/m + 1 ≤ n`. -/
theorem decoding_criterion_of_derived_radius (D m n : ℕ) (hm : 0 < m)
    (hDn : D / m + 1 ≤ n) : D < (n - (n - (D / m + 1))) * m := by
  rw [Nat.sub_sub_self hDn]
  have hdm : m * (D / m) + D % m = D := Nat.div_add_mod D m
  have hmod : D % m < m := Nat.mod_lt D hm
  nlinarith [hdm, hmod]

/-- The derived radius `e := n − (D/m + 1)` strictly exceeds the UDR `(n−k)/2` under the strict
small-degree window `D/m + (n−k)/2 + 2 ≤ n`. -/
theorem radius_gt_udr_of_window (D m n k : ℕ)
    (hwin : D / m + (n - k) / 2 + 2 ≤ n) : (n - k) / 2 < n - (D / m + 1) := by
  set q := D / m; set u := (n - k) / 2; clear_value q u; omega

/-- The UDR excess of the derived radius is `≥ 1` under the strict window. -/
theorem udr_excess_ge_one_of_window (D m n k : ℕ)
    (hwin : D / m + (n - k) / 2 + 2 ≤ n) :
    1 ≤ (n - (D / m + 1)) - (n - k) / 2 := by
  set q := D / m; set u := (n - k) / 2; clear_value q u; omega

/-- **ROUTE F4 capstone.** Trivariate GS dimension count satisfiable past UDR. -/
theorem gs3_feasible_radius_past_udr
    (k ρ D t t₃ m n : ℕ) (xs ys zs : Fin n → F)
    (hk : 0 < k) (ht3 : t₃ ≤ D)
    (hval1 : k * (t - 1) ≤ D - ρ * (t₃ - 1)) (hval2 : t ≤ D - ρ * (t₃ - 1))
    (hbeat : n * (multIdx3 m).card < t₃ * (t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2)))
    (hm : 0 < m) (hDn : D / m + 1 ≤ n)
    (hwin : D / m + (n - k) / 2 + 2 ≤ n) :
    (∃ cf : CoeffSpace3 (F := F) k ρ D, cf ≠ 0 ∧
        ∀ i : Fin n, vanishesToOrder3 k ρ D m cf (xs i) (ys i) (zs i))
      ∧ D < (n - (n - (D / m + 1))) * m
      ∧ (n - k) / 2 < n - (D / m + 1) :=
  ⟨exists_ne_zero_vanishesToOrder3_of_cubic k ρ D t t₃ m n xs ys zs hk ht3 hval1 hval2 hbeat,
   decoding_criterion_of_derived_radius D m n hm hDn,
   radius_gt_udr_of_window D m n k hwin⟩

/-- **Non-vacuity witness:** k=2, ρ=2, D=14, t=6, t₃=2, m=2, n=20 over ℚ. Radius e=12 > UDR=9. -/
theorem gs3_feasible_radius_past_udr_witness :
    (∃ cf : CoeffSpace3 (F := ℚ) 2 2 14, cf ≠ 0 ∧
        ∀ i : Fin 20, vanishesToOrder3 2 2 14 2 cf
          ((fun _ => 0 : Fin 20 → ℚ) i) ((fun _ => 0) i) ((fun _ => 0) i))
      ∧ (14 : ℕ) < (20 - (20 - (14 / 2 + 1))) * 2
      ∧ (20 - 2) / 2 < 20 - (14 / 2 + 1) :=
  gs3_feasible_radius_past_udr (F := ℚ) 2 2 14 6 2 2 20
    (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (multIdx3 2).card = 4 from by decide]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GS3

#print axioms GS3.decoding_criterion_of_derived_radius
#print axioms GS3.radius_gt_udr_of_window
#print axioms GS3.udr_excess_ge_one_of_window
#print axioms GS3.gs3_feasible_radius_past_udr
#print axioms GS3.gs3_feasible_radius_past_udr_witness
