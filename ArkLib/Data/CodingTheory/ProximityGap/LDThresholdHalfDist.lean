/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LDThreshold
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Unconditional half-distance floor for the genuine list-decoding threshold

`GrandChallengeLDThreshold.lean` gives the genuine lattice threshold a Johnson-side floor
*parameterized* by the radical-free Johnson condition.  This file complements it with a
fully *unconditional* floor from the unique-decoding regime: below half the minimum
distance every list has at most one element, so every grid radius `j/n` with
`2j < minDist` belongs to the lattice set as soon as the budget admits one codeword
(`1 ≤ ε*·|F|`, i.e. `|F| ≥ 2^128` at the prize's `ε* = 2⁻¹²⁸`).

Together with the unconditional capacity ceiling this pins the genuine threshold of every
Reed–Solomon instance in the *fully discharged* sandwich

  `⌊(n - deg)/2⌋  ≤  listLatticeThreshold  ≤  n - deg`,

with no parameterized hypotheses beyond the budget.  As a by-product the lattice set is
unconditionally nonempty (`listLatticeSet_nonempty_rs`), discharging the `hne` argument
that all threshold statements carry.  The open prize content lives strictly inside this
factor-of-two gap (the Johnson floor and Elias ceiling narrow it further, each with one
parameterized hypothesis).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal
open ListDecodable

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι] in
/-- Membership in a grid-radius relative-Hamming ball bounds the (ambient-instance)
Hamming distance by the grid index.  The `convert` transports the ball's baked
`Decidable` instances to the ambient ones (they are subsingletons). -/
lemma hammingDist_le_of_mem_relHammingBall {A : Type*} [DecidableEq A]
    {f x : ι → A} {j : ℕ}
    (hx : x ∈ relHammingBall f (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) :
    hammingDist f x ≤ j := by
  have hx' : ((Code.relHammingDist f x : ℚ≥0) : ℝ) ≤
      (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    rw [relHammingBall, Set.mem_setOf_eq] at hx
    convert hx using 3
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrel : (Code.relHammingDist f x : ℚ≥0) =
      (hammingDist f x : ℚ≥0) / (Fintype.card ι : ℚ≥0) := rfl
  rw [hrel] at hx'
  rw [show (((hammingDist f x : ℚ≥0) / (Fintype.card ι : ℚ≥0) : ℚ≥0) : ℝ)
      = (hammingDist f x : ℝ) / (Fintype.card ι : ℝ) by push_cast; ring] at hx'
  rw [show ((((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0)) : ℝ)
      = (j : ℝ) / (Fintype.card ι : ℝ) by push_cast; ring] at hx'
  have hmul := mul_le_mul_of_nonneg_right hx' (le_of_lt hn)
  rw [div_mul_cancel₀ _ (ne_of_gt hn), div_mul_cancel₀ _ (ne_of_gt hn)] at hmul
  exact_mod_cast hmul

omit [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι] in
/-- **Unique-decoding list bound.**  If distinct codewords of `C'` are pairwise farther
than `2j` apart, every radius-`j/n` list has at most one element. -/
lemma ncard_closeCodewordsRel_le_one_of_sep {A : Type*} [DecidableEq A] [Finite A]
    (C' : Code ι A) {j : ℕ}
    (hsep : ∀ u ∈ C', ∀ v ∈ C', u ≠ v → 2 * j < hammingDist u v) (f : ι → A) :
    (closeCodewordsRel C' f
      (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)).ncard ≤ 1 := by
  rw [Set.ncard_le_one (Set.toFinite _)]
  rintro u ⟨huC, hub⟩ v ⟨hvC, hvb⟩
  by_contra hne
  have h1 := hammingDist_le_of_mem_relHammingBall hub
  have h2 := hammingDist_le_of_mem_relHammingBall hvb
  have htri : hammingDist u v ≤ hammingDist u f + hammingDist f v :=
    hammingDist_triangle u f v
  have hcomm : hammingDist u f = hammingDist f u := hammingDist_comm u f
  have hbig := hsep u huC v hvC hne
  omega

omit [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι] [Nonempty ι] in
/-- Pairwise separation lifts from the base code to the interleaved code: stacks that
differ, differ in some row, and the stack distance dominates each row distance. -/
lemma interleaved_sep_of_base {A : Type*} [DecidableEq A] {C : Set (ι → A)} {j m : ℕ}
    (hsep : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * j < hammingDist u v) :
    ∀ U ∈ (C^⋈ (Fin m)), ∀ V ∈ (C^⋈ (Fin m)), U ≠ V → 2 * j < hammingDist U V := by
  intro U hU V hV hne
  have hU' : ∀ k : Fin m, Matrix.transpose U k ∈ C := hU
  have hV' : ∀ k : Fin m, Matrix.transpose V k ∈ C := hV
  have hex : ∃ k : Fin m, Matrix.transpose U k ≠ Matrix.transpose V k := by
    by_contra hall
    push Not at hall
    apply hne
    funext i k
    exact congrFun (hall k) i
  obtain ⟨k, hk⟩ := hex
  have hrow := hsep _ (hU' k) _ (hV' k) hk
  have hle : hammingDist (Matrix.transpose U k) (Matrix.transpose V k) ≤
      hammingDist U V := by
    unfold hammingDist
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ i, fun hUV => hi.2 ?_⟩
    exact congrFun hUV k
  omega

omit [DecidableEq ι] in
/-- **Half-distance lattice membership (unconditional).**  For any Reed–Solomon instance,
every grid radius below half the minimum distance lies in the list-decoding lattice set,
as soon as the budget admits a single codeword (`1 ≤ ε*·|F|`). -/
theorem mem_listLatticeSet_of_lt_half_minDist
    (domain : ι ↪ F) {deg m j : ℕ} (hdeg : deg ≠ 0) (hdegn : deg ≤ Fintype.card ι)
    (hj : 2 * j < Fintype.card ι - deg + 1)
    {ε_star : ℝ≥0} (hbudget : 1 ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    j ∈ GrandChallenges.listLatticeSet
      (ReedSolomon.code domain deg : Set (ι → F)) m ε_star := by
  classical
  have : NeZero deg := ⟨hdeg⟩
  have hmd : Code.minDist ((ReedSolomon.code domain deg) : Set (ι → F)) =
      Fintype.card ι - deg + 1 := ReedSolomon.minDist_eq' hdegn
  have hsep : ∀ u ∈ (ReedSolomon.code domain deg : Set (ι → F)),
      ∀ v ∈ (ReedSolomon.code domain deg : Set (ι → F)),
        u ≠ v → 2 * j < hammingDist u v := by
    intro u hu v hv hne
    have hle : Code.minDist ((ReedSolomon.code domain deg) : Set (ι → F)) ≤
        hammingDist u v := Nat.sInf_le ⟨u, hu, v, hv, hne, rfl⟩
    omega
  have hsep' := interleaved_sep_of_base (m := m) hsep
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · -- j ≤ n
    have hdpos : 0 < deg := Nat.pos_of_ne_zero hdeg
    omega
  · -- Λ ≤ 1 ≤ ε*·|F|
    refine le_trans ?_ hbudget
    have hΛ : Lambda ((ReedSolomon.code domain deg : Set (ι → F))^⋈ (Fin m))
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (1 : ℕ∞) := by
      refine Lambda_le_of_forall_ncard_le fun f => ?_
      exact_mod_cast ncard_closeCodewordsRel_le_one_of_sep _ hsep' f
    calc (Lambda ((ReedSolomon.code domain deg : Set (ι → F))^⋈ (Fin m))
          (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)
        ≤ ((1 : ℕ∞) : ENNReal) := by exact_mod_cast hΛ
      _ = 1 := by simp

omit [DecidableEq ι] in
/-- **The lattice set is unconditionally nonempty** for every Reed–Solomon instance with
`1 ≤ ε*·|F|`: radius `0` always qualifies.  This discharges the `hne` hypothesis carried
by all genuine-threshold statements. -/
theorem listLatticeSet_nonempty_rs
    (domain : ι ↪ F) {deg m : ℕ} (hdeg : deg ≠ 0) (hdegn : deg ≤ Fintype.card ι)
    {ε_star : ℝ≥0} (hbudget : 1 ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    (GrandChallenges.listLatticeSet
      (ReedSolomon.code domain deg : Set (ι → F)) m ε_star).Nonempty :=
  ⟨0, mem_listLatticeSet_of_lt_half_minDist domain hdeg hdegn (by omega) hbudget⟩

omit [DecidableEq ι] in
/-- **Unconditional half-distance floor on the genuine threshold**: combined with the
capacity ceiling of `GrandChallengeLDThreshold.lean`, every Reed–Solomon instance has

  `⌊(n - deg)/2⌋ ≤ listLatticeThreshold ≤ n - deg`

with no hypotheses beyond `1 ≤ ε*·|F|`. -/
theorem half_minDist_le_listLatticeThreshold
    (domain : ι ↪ F) {deg m : ℕ} (hdeg : deg ≠ 0) (hdegn : deg ≤ Fintype.card ι)
    {ε_star : ℝ≥0} (hbudget : 1 ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hne : (GrandChallenges.listLatticeSet
      (ReedSolomon.code domain deg : Set (ι → F)) m ε_star).Nonempty) :
    (Fintype.card ι - deg) / 2 ≤
      GrandChallenges.listLatticeThreshold
        (ReedSolomon.code domain deg : Set (ι → F)) m ε_star hne := by
  apply Finset.le_max'
  apply mem_listLatticeSet_of_lt_half_minDist domain hdeg hdegn ?_ hbudget
  omega

/-- **Fully discharged RS list-threshold sandwich.**

The nonemptiness proof for `listLatticeThreshold` is constructed internally from the radius-`0`
half-distance point, so callers only supply the genuine mathematical side conditions:
positive degree, `deg ≤ n`, positive interleaving, budget `1 ≤ ε*·|F|`, and `ε* < 1`.

This is the direct faithful-list-decoding analogue of the collapsed Prop refutation: it states
the actual lattice-threshold information that survives after replacing the broken real-threshold
encoding by the finite grid threshold. -/
theorem listLatticeThreshold_rs_between_halfDist_and_capacity
    [Fintype F] [Nonempty ι]
    (domain : ι ↪ F) {deg m : ℕ} (hdeg : deg ≠ 0) (hdegn : deg ≤ Fintype.card ι)
    (hm : m ≠ 0) {ε_star : ℝ≥0}
    (hbudget : 1 ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hε : ε_star < 1) :
    let hne := listLatticeSet_nonempty_rs domain hdeg hdegn hbudget
    (Fintype.card ι - deg) / 2 ≤
        GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain deg : Set (ι → F)) m ε_star hne ∧
      GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain deg : Set (ι → F)) m ε_star hne ≤
        Fintype.card ι - deg := by
  intro hne
  exact ⟨half_minDist_le_listLatticeThreshold domain hdeg hdegn hbudget hne,
    listLatticeThreshold_le_capacity domain hdegn hm hε hne⟩

end ProximityGap
