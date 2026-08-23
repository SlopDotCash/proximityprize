/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice
import ArkLib.Data.CodingTheory.InterleavedListSize
import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# Squared-form Johnson floor for the genuine list-decoding threshold

The Johnson floor of `GrandChallengeLDThreshold.lean` carries the radical-free Johnson
side condition with its free shift parameter `β`.  This file gives the definitive form:
the **optimal-β squared Johnson condition** (ABF26 Theorem 3.2, radical-free, via
`closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist`), where the only
remaining hypothesis is a concrete polynomial inequality in `n, q, ℓ, j, minDist` —
directly checkable by `norm_num` on numeric instances:

  `(ℓ+1) · ((n−j) − n/q)² > n(1−1/q) · (n(1−1/q) + ℓ·((n−d) − n/q))`.

At grid radius `j/n` the floor `⌊(j/n)·n⌋ = j` is exact (`floor_grid_mul`), so all
hypotheses are stated directly in terms of the lattice index `j`.
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι] in
/-- At a grid radius the floor recovers the lattice index exactly:
`⌊(j/n)·n⌋ = j`. -/
lemma floor_grid_mul (j : ℕ) :
    ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)⌋₊ = j := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [show ((((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0)) : ℝ)
      = (j : ℝ) / (Fintype.card ι : ℝ) by push_cast; ring]
  rw [div_mul_cancel₀ _ (ne_of_gt hn)]
  exact Nat.floor_natCast j

omit [Field F] in
/-- **Squared-form Johnson cap at `Λ`-level**: the optimal-β radical-free Johnson bound,
with hypotheses phrased directly in the lattice index `j`. -/
theorem Lambda_le_of_johnson_sq
    (C : Code ι F) {j ℓ : ℕ} (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - j : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist C : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞) := by
  classical
  refine Lambda_le_of_forall_ncard_le fun f => ?_
  have hδ : (0 : ℝ) ≤ (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) :=
    NNReal.coe_nonneg _
  have hfl := floor_grid_mul (ι := ι) j
  have hpt := JohnsonBound.closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist
    (C := C) (f := f) (δ := (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ))
    (ℓ := ℓ) hδ hq1 (by rw [hfl]; exact hP) (by rw [hfl]; exact hsq)
  rw [card_closeCodewordsRelFinset_eq_ncard] at hpt
  exact_mod_cast hpt

omit [Field F] in
/-- **Squared-form Johnson membership in the lattice set**: if the optimal-β Johnson
inequality holds at lattice index `j` with cap `ℓ`, and `ℓ^m` clears the budget, then
`j` belongs to the list-decoding lattice set. -/
theorem mem_listLatticeSet_of_johnson_sq
    (C : Set (ι → F)) {m j ℓ : ℕ} (hjn : j ≤ Fintype.card ι) (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - j : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist C : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    j ∈ GrandChallenges.listLatticeSet C m ε_star := by
  classical
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.lt_succ_of_le hjn, ?_⟩
  have hbase : Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞) :=
    Lambda_le_of_johnson_sq C hq1 hP hsq
  have hint : Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) ^ m := by
    show Lambda (Code.interleavedCodeSet (κ := Fin m) C)
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ _
    exact InterleavedCode.ListSize.Lambda_interleaved_le_pow (m := m) C _
  have hpowENat : Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      ((ℓ : ℕ∞)) ^ m :=
    le_trans hint (pow_le_pow_left' hbase m)
  calc (Lambda (C^⋈ (Fin m)) (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)
      ≤ (((ℓ : ℕ∞) ^ m : ℕ∞) : ENNReal) := by exact_mod_cast hpowENat
    _ = ((ℓ : ENNReal)) ^ m := by
        push_cast
        rfl
    _ ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) := hpow

omit [Field F] in
/-- **Definitive Johnson floor on the genuine threshold** (optimal-β squared form):
the only hypotheses are the concrete squared Johnson inequality at index `j` and the
budget `ℓ^m ≤ ε*·|F|`. -/
theorem le_listLatticeThreshold_of_johnson_sq
    (C : Set (ι → F)) {m j ℓ : ℕ} (hjn : j ≤ Fintype.card ι) (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - j : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist C : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hne : (GrandChallenges.listLatticeSet C m ε_star).Nonempty) :
    j ≤ GrandChallenges.listLatticeThreshold C m ε_star hne :=
  Finset.le_max' _ _ (mem_listLatticeSet_of_johnson_sq C hjn hq1 hP hsq hpow)

end ProximityGap
