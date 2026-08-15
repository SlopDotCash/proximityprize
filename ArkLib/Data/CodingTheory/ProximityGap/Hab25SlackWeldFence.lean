/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25SlackWeld

/-!
# The slack-weld fence: the witness data is load-bearing (#302, R-A5)

The slack weld (`global_branch_of_witnessed_subcell`) counts unwitnessed scalars away — an
obvious "simplification" a future pass might attempt is dropping the witness/factor data
altogether (keep only the decode divisibility `hdvdP`, the degree leg, and the count leg).
This file proves that strawman **FALSE**, fencing the weld against laundering:

* `square_root_branch_dvd` — over `F = ZMod 7`, the trivariate `R := Y² − Z` admits the full
  slack-data package: the cell `E = {0, 1, 2, 4}` of squares, per-scalar decodes
  `P γ := √γ` (constants), `(Y − C (P γ)) ∣ R(γ)` at every cell scalar, flat coefficient
  budget `BR = 1`, and the count leg `BR + deg_Y R·(L−1) + k·M = 2 < 4 = |E|` with genuine
  slack (`k = M = 1`);
* `no_global_branch_for_square` — yet NO global branch exists: `(Y − C pHat) ∣ Y² − Z`
  forces `pHat² = Z`, impossible by `X`-degree parity;
* **`slack_only_strawman_false`** — the packaged refutation: the slack weld with the
  `hroot`/`hrich`/`hwit` legs deleted is not a theorem.  The witnessed fold-agreement data
  is exactly what excludes `Y² − Z` (its fiber roots `±√γ` are not the values of any single
  polynomial section), so it cannot be weakened away.

This is the formal counterpart of the prose honesty note in `Hab25CandidateProduction`
("algebra-only production is FALSE").

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset

attribute [local instance] Classical.propDecidable

local notation "F7" => ZMod 7

instance primeFact_Hab25SlackWeldFence_1 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The square-root table on the squares of `ZMod 7`. -/
def sq7 : F7 → F7 := fun γ =>
  if γ = 0 then 0 else if γ = 1 then 1 else if γ = 2 then 3 else 2

/-- The Y²−Z counterexample object, as a trivariate in the weld's orientation
(`Z` innermost, the domain variable in the middle, `Y` outermost). -/
noncomputable def squareBranchR : (F7[X])[X][Y] :=
  Polynomial.X ^ 2 - Polynomial.C (Polynomial.C (Polynomial.X : F7[X]))

/-- The cell of squares. -/
def squareCell : Finset F7 := {0, 1, 2, 4}

lemma squareCell_card : squareCell.card = 4 := by decide

lemma sq7_sq : ∀ γ ∈ squareCell, sq7 γ * sq7 γ = γ := by decide

/-- **Per-scalar divisibility holds at every cell scalar**: `(Y − √γ) ∣ (Y² − γ)`. -/
lemma square_root_branch_dvd : ∀ γ ∈ squareCell,
    (Polynomial.X - Polynomial.C (Polynomial.C (sq7 γ) : F7[X])) ∣
      squareBranchR.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  intro γ hγ
  refine ⟨Polynomial.X + Polynomial.C (Polynomial.C (sq7 γ) : F7[X]), ?_⟩
  have hfiber : squareBranchR.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))
      = Polynomial.X ^ 2 - Polynomial.C (Polynomial.C γ : F7[X]) := by
    unfold squareBranchR
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    congr 1
    simp [Polynomial.coe_mapRingHom, Polynomial.map_C]
  rw [hfiber]
  have key : (Polynomial.C (Polynomial.C (sq7 γ)) : F7[X][Y]) ^ 2
      = Polynomial.C (Polynomial.C γ) := by
    rw [← Polynomial.C_pow, ← Polynomial.C_pow, pow_two, sq7_sq γ hγ]
  rw [← key]
  ring

/-- The flat coefficient budget of `Y² − Z` is `1`. -/
lemma squareBranchR_budget : ∀ b a : ℕ,
    ((squareBranchR.coeff b).coeff a).natDegree ≤ 1 := by
  intro b a
  unfold squareBranchR
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  rcases eq_or_ne b 2 with hb2 | hb2
  · rw [if_pos hb2, if_neg (by omega : b ≠ 0), sub_zero]
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      simp
    · rw [Polynomial.coeff_one, if_neg (by omega : a ≠ 0)]
      simp
  · rw [if_neg hb2]
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [if_pos hb0, zero_sub, Polynomial.coeff_neg]
      rcases eq_or_ne a 0 with ha | ha
      · subst ha
        rw [Polynomial.coeff_C, if_pos rfl, Polynomial.natDegree_neg]
        exact le_of_eq Polynomial.natDegree_X
      · rw [Polynomial.coeff_C, if_neg ha, neg_zero]
        simp
    · rw [if_neg hb0, sub_zero]
      simp

/-- The `Y`-degree of `Y² − Z` is `2`. -/
lemma squareBranchR_natDegree : squareBranchR.natDegree = 2 := by
  unfold squareBranchR
  exact Polynomial.natDegree_X_pow_sub_C

/-- **No global branch exists for `Y² − Z`**: `(Y − C pHat) ∣ R` would force `pHat² = Z`,
impossible by `Z`-degree parity. -/
lemma no_global_branch_for_square (pHat : (F7[X])[X]) :
    ¬ (Polynomial.X - Polynomial.C pHat) ∣ squareBranchR := by
  intro hdvd
  have hroot : Polynomial.eval pHat squareBranchR = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul]
  unfold squareBranchR at hroot
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero] at hroot
  -- `pHat² = C Z`: the middle (`X`) degree forces `pHat` constant
  have hndX : pHat.natDegree = 0 := by
    have h2 : (pHat ^ 2).natDegree = 2 * pHat.natDegree := Polynomial.natDegree_pow pHat 2
    rw [hroot] at h2
    have hC : (Polynomial.C (Polynomial.X : F7[X])).natDegree = 0 :=
      Polynomial.natDegree_C _
    omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hndX
  -- then `c² = Z` in `F7[X]`: degree parity contradiction
  rw [← hc] at hroot
  rw [show (Polynomial.C c : (F7[X])[X]) ^ 2 = Polynomial.C (c ^ 2) by
    rw [← Polynomial.C_pow]] at hroot
  have hcsq : c ^ 2 = (Polynomial.X : F7[X]) := Polynomial.C_injective hroot
  have hpar : (c ^ 2).natDegree = 2 * c.natDegree := Polynomial.natDegree_pow c 2
  rw [hcsq, Polynomial.natDegree_X] at hpar
  omega

/-- **THE FENCE (R-A5)**: the slack weld with the witness/factor legs deleted is FALSE.
The statement below is the literal shape of `global_branch_of_witnessed_subcell` with the
`(Hf, assign, S, hirr, hB, hroot, hrich, hwit)` data removed and the conclusion weakened to
a bare existential — and it is refutable. -/
theorem slack_only_strawman_false :
    ¬ (∀ (R : (F7[X])[X][Y]) (BR : ℕ),
        (∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR) →
        ∀ (E : Finset F7) (P : F7 → F7[X]) (k L M : ℕ), 0 < k → 0 < L →
        (∀ γ ∈ E, (P γ).degree < (k : ℕ)) →
        (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        BR + R.natDegree * (L - 1) + k * M < E.card →
        ∃ pHat : (F7[X])[X], (Polynomial.X - Polynomial.C pHat) ∣ R) := by
  intro hstraw
  obtain ⟨pHat, hdvd⟩ := hstraw squareBranchR 1 squareBranchR_budget
    squareCell (fun γ => Polynomial.C (sq7 γ)) 1 1 1 (by omega) (by omega)
    (fun γ _ => lt_of_le_of_lt (Polynomial.degree_C_le) (by norm_num))
    square_root_branch_dvd
    (by rw [squareCell_card, squareBranchR_natDegree]; omega)
  exact no_global_branch_for_square pHat hdvd

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms slack_only_strawman_false
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms no_global_branch_for_square
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms square_root_branch_dvd
