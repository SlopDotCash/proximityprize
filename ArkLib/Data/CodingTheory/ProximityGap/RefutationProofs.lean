/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BruteForceRefutations

/-!
# Discharged refutations of the Grand Challenge 1 brute-force list-size hypotheses

`GrandChallenge1BruteForceRefutations.lean` *states* the refutation targets
`refute_HypN : Prop` for the ten naive list-size bounds, but leaves them unproven.

This file **proves** the seven that admit elementary finite counterexamples, turning
them from bare propositions into verified `theorem`s with no `sorry`.  This is exactly
the "attack the candidate hypothesis down" half of the research loop: each naive bound
is refuted by an explicit witness, so it cannot be the route to the open beyond-UDR
list-size bound.

The three that remain open here (`Hyp1`, `Hyp2`, `Hyp4`) hinge on the semantics of the
bivariate resultant / Hasse `Y`-derivative and need that algebraic infrastructure before
their (also concrete) counterexamples can be formalised; they are intentionally not
claimed here.
-/

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal
open GrandChallenge1BruteForce

namespace GrandChallenge1BruteForceRefutations

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Hyp5 refuted.** With `H = 0` the total degree is `0`, so the claimed bound
`L.card ≤ totalDegree H * |ι|` forces `1 ≤ 0` on `L = {0}`. -/
theorem refute_Hyp5_proof : refute_Hyp5 (ι := ι) (F := F) := by
  intro h
  have h1 := h 0 {0}
  simp only [Hyp5_SchwartzZippelDensity, Bivariate.totalDegree, Polynomial.support_zero,
    Finset.sup_empty, Nat.bot_eq_zero, Nat.zero_mul, Finset.card_singleton] at h1
  omega

/-- **Hyp7 refuted.** Taking `k = 0` collapses the bound `L.card ≤ k²` to `L.card ≤ 0`,
impossible for the nonempty list `{0}`. -/
theorem refute_Hyp7_proof : refute_Hyp7 (ι := ι) (F := F) := by
  intro h
  have h1 := h {0} 0
  simp only [Hyp7_MatrixRankBound, Finset.card_singleton, pow_two, Nat.mul_zero] at h1
  omega

/-- **Hyp9 refuted.** `Bivariate.natDegreeX 0 = 0`, so `L.card ≤ natDegreeX H` fails on `{0}`. -/
theorem refute_Hyp9_proof : refute_Hyp9 (ι := ι) (F := F) := by
  intro h
  have h1 := h 0 {0}
  simp only [Hyp9_MultiplicityIntersection, Finset.card_singleton] at h1
  have hz : Bivariate.natDegreeX (0 : F[X][Y]) = 0 := by
    simp [Bivariate.natDegreeX, Bivariate.degreeX]
  omega

/-- **Hyp10 refuted.** `Bivariate.natDegreeY 0 = 0`, so `L.card ≤ natDegreeY H` fails on `{0}`. -/
theorem refute_Hyp10_proof : refute_Hyp10 (ι := ι) (F := F) := by
  intro h
  have h1 := h 0 {0}
  simp only [Hyp10_AffineVarietyDimension, Finset.card_singleton, Bivariate.natDegreeY,
    Polynomial.natDegree_zero] at h1
  omega

/-- **Hyp8 refuted.** The whole message space has `|ι → F| = |F|^|ι|` elements, which exceeds
`|F|` once `|ι| ≥ 2` (as `|F| ≥ 2` for a field). -/
theorem refute_Hyp8_proof (hι : Fintype.card ι ≥ 2) :
    refute_Hyp8 (ι := ι) (F := F) := by
  intro h
  have h1 := h Finset.univ
  rw [Hyp8_AlgebraicIndependence, Finset.card_univ, Fintype.card_fun] at h1
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ Fintype.card ι :=
    Nat.pow_le_pow_right (by omega) hι
  have e2 : Fintype.card F ^ 2 = Fintype.card F * Fintype.card F := by ring
  nlinarith [h1, hpow, e2, hq]

/-- **Hyp6 refuted.** The two distinct indicator vectors `Pi.single a 1` and `Pi.single b 1`
(`a ≠ b`, available once `|ι| ≥ 2`) cannot both be scalar multiples of a single `v`. -/
theorem refute_Hyp6_proof (hι : Fintype.card ι ≥ 2) :
    refute_Hyp6 (ι := ι) (F := F) := by
  have hnt : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  intro h
  obtain ⟨v, _, hcov⟩ := h {Pi.single a 1, Pi.single b 1}
  obtain ⟨c1, hc1⟩ := hcov (Pi.single a 1) (by simp)
  obtain ⟨c2, hc2⟩ := hcov (Pi.single b 1) (by simp)
  have e1b := congrFun hc1 b
  have e2b := congrFun hc2 b
  rw [Pi.single_eq_of_ne hab.symm, Pi.smul_apply, smul_eq_mul] at e1b
  rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at e2b
  have hvb : v b ≠ 0 := by
    intro hvb0; rw [hvb0, mul_zero] at e2b; exact one_ne_zero e2b
  have e1a := congrFun hc1 a
  rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at e1a
  have hc1ne : c1 ≠ 0 := by
    intro hc10; rw [hc10, zero_mul] at e1a; exact one_ne_zero e1a
  exact hvb (by rw [eq_comm, mul_eq_zero] at e1b; exact e1b.resolve_left hc1ne)

/-- **Hyp3 refuted.** Under the sparsity premise `|ι| ≤ |F|^(1/2)` an evaluation embedding
exists, and `L = univ` again has `|F|^|ι| > |ι|` elements, breaking `L.card ≤ |ι|`. -/
theorem refute_Hyp3_proof (hF : (Fintype.card ι : ℝ) ≤ (Fintype.card F : ℝ) ^ (1/2 : ℝ)) :
    refute_Hyp3 (ι := ι) (F := F) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hcardF : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq.le
  have hsqrt : (Fintype.card F : ℝ) ^ (1/2 : ℝ) ≤ (Fintype.card F : ℝ) := by
    calc (Fintype.card F : ℝ) ^ (1/2 : ℝ)
        ≤ (Fintype.card F : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hcardF (by norm_num)
      _ = (Fintype.card F : ℝ) := Real.rpow_one _
  have hle : Fintype.card ι ≤ Fintype.card F := by
    have : (Fintype.card ι : ℝ) ≤ (Fintype.card F : ℝ) := le_trans hF hsqrt
    exact_mod_cast this
  obtain ⟨domain⟩ := Function.Embedding.nonempty_of_card_le hle
  intro h
  have h2 := (h domain Finset.univ) hF
  rw [Finset.card_univ, Fintype.card_fun] at h2
  have hlt := Nat.lt_pow_self hq (n := Fintype.card ι)
  omega

#print axioms refute_Hyp3_proof
#print axioms refute_Hyp5_proof
#print axioms refute_Hyp6_proof
#print axioms refute_Hyp7_proof
#print axioms refute_Hyp8_proof
#print axioms refute_Hyp9_proof
#print axioms refute_Hyp10_proof

end GrandChallenge1BruteForceRefutations
