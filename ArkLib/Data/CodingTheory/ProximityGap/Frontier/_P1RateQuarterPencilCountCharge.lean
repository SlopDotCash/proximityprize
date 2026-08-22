/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSharedFreshCoordinate

/-!
# The pencil-count charge at the P1 predecessor

Successor of `_P1RateQuarterSharedFreshTripleP1Refuted.lean`.  With the fixed-witness
escape-charge branch dead (shared-fresh triples exist at literal P1), the surviving counting
route charges bad scalars to the divided-difference pencils their witnesses ride.

For a fixed pencil `(w₀, w₁)` of codewords, a scalar `γ` *rides* it when its witness codeword
is `w₀ + γ•w₁`.  On the witness set then `w₀ + γ•w₁ = u₀ + γ•u₁`, so every coordinate
outside the *aligned* region `{i : w₀ i = u₀ i ∧ w₁ i = u₁ i}` votes for at most one rider.
This file makes the resulting counting exact:

* **Vote partition** (`riders_card_mul_le`, `riders_card_le_compl`): with `A` aligned
  coordinates, `riders·(T − A) ≤ N − A` (for `A ≤ T`), and `riders ≤ N − A` always — the
  non-joint clause forbids witnesses inside the aligned region, so every rider casts a vote.
* **Uniform rider cap** (`riders_card_le_uniform`): every pencil carries at most
  `N − T + 1 = 480946859` bad scalars.
* **Alignment ladder** (`riders_mul_threshold_le`): `riders·T ≤ N + (riders − 1)·A`; heavily
  ridden pencils are heavily aligned.
* **Johnson crossover** (`alignment_floor_of_ten_riders`, `ten_rider_floor_beats_johnson`,
  `nine_rider_floor_below_johnson`): ten riders force `A ≥ 539356427`, whose square exceeds
  `N·(k−1)` — pencils with ≥ 10 riders are Johnson-packable joint pairs (their aligned
  regions pairwise intersect in `< k` coordinates: `alignedSet_inter_card_lt_k`) — while the
  nine-rider floor `532676609` still falls below the Johnson threshold.  Ten is exact.
* **Fiber partition through a base scalar** (`badFamily_card_le_one_add_pencilImage`):
  `#bad ≤ 1 + P·(N − T)` where `P` is the number of distinct divided-difference pencils
  through the base witness.  Hence `P ≤ 2` closes the budget
  (`badFamily_card_le_N_of_image_card_le_two`; `1 + 2·(N−T) = 961893717 ≤ N`), and
  over-budget forces at least three pencils through *every* base scalar
  (`three_pencils_of_overBudget`).
* **Four-witness pigeonhole** (`four_witnesses_triple_overlap`): `4T > 2N`, so any four
  threshold witnesses share a triple-covered coordinate — every over-budget family is
  saturated with the shared-triple configurations of the previous files.

**Honest residual** (`BasePencilImageCap`, OPEN): at most two distinct pencils through a base
witness.  The probe realizes exactly two at the P1 shape (`μ_256/F_257`, base scalar riding
pencils `(x^16, 1)` and `(x^16−x^8+1, x^8)`), so the cap sits on the realizability boundary;
three pencils with *pairwise-only* witness overlaps are impossible (`4T > 2N` forces triple
overlaps), but a triple-overlap design is not excluded — the weighted refinement
`Σ_π (N−T)/(T−A_π) ≤ N − 1` is the true remaining quantity.

Executable certificate: `scripts/probes/probe_rate_quarter_p1_pencil_count_charge.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ProximityGap.SharedFreshPencil

local instance localInstance_P1RateQuarterPencilCountCharge_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterPencilCountCharge_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Aligned coordinates and votes of a pencil -/

section Votes

variable (u₀ u₁ w₀ w₁ : Fin N → F)

/-- Coordinates where the pencil agrees with the stack in both rows. -/
noncomputable def alignedSet : Finset (Fin N) :=
  Finset.univ.filter (fun i => w₀ i = u₀ i ∧ w₁ i = u₁ i)

/-- Coordinates voting for the rider `γ`: the `γ`-line of the pencil meets the `γ`-line of
the stack, but the coordinate is not aligned. -/
noncomputable def voteSet (γ : F) : Finset (Fin N) :=
  Finset.univ.filter
    (fun i => i ∉ alignedSet u₀ u₁ w₀ w₁ ∧ w₀ i + γ * w₁ i = u₀ i + γ * u₁ i)

theorem mem_alignedSet_iff (i : Fin N) :
    i ∈ alignedSet u₀ u₁ w₀ w₁ ↔ w₀ i = u₀ i ∧ w₁ i = u₁ i := by
  rw [alignedSet, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem mem_voteSet_iff (γ : F) (i : Fin N) :
    i ∈ voteSet u₀ u₁ w₀ w₁ γ ↔
      i ∉ alignedSet u₀ u₁ w₀ w₁ ∧ w₀ i + γ * w₁ i = u₀ i + γ * u₁ i := by
  rw [voteSet, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

/-- **Each coordinate votes at most once.** -/
theorem voteSet_disjoint {γ γ' : F} (hne : γ ≠ γ') :
    Disjoint (voteSet u₀ u₁ w₀ w₁ γ) (voteSet u₀ u₁ w₀ w₁ γ') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [mem_voteSet_iff] at hi hi'
  apply hi.1
  rw [mem_alignedSet_iff]
  have hsub : (γ - γ') * (w₁ i - u₁ i) = 0 := by
    have h := hi.2
    have h' := hi'.2
    ring_nf
    ring_nf at h h'
    linear_combination h - h'
  have h₁ : w₁ i = u₁ i := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact sub_eq_zero.mp h
  refine ⟨?_, h₁⟩
  have h := hi.2
  rw [h₁] at h
  exact add_right_cancel h

/-- A rider's witness set lives inside `aligned ∪ votes(γ)`. -/
theorem witness_subset_aligned_union_votes {γ : F} {S : Finset (Fin N)}
    (hagree : ∀ i ∈ S, w₀ i + γ * w₁ i = u₀ i + γ * u₁ i) :
    S ⊆ alignedSet u₀ u₁ w₀ w₁ ∪ voteSet u₀ u₁ w₀ w₁ γ := by
  intro i hi
  by_cases hal : i ∈ alignedSet u₀ u₁ w₀ w₁
  · exact Finset.mem_union_left _ hal
  · exact Finset.mem_union_right _
      ((mem_voteSet_iff u₀ u₁ w₀ w₁ γ i).mpr ⟨hal, hagree i hi⟩)

/-- Non-jointness forces every rider to cast at least one vote. -/
theorem voteSet_nonempty_of_rides (dom : Fin N ↪ F)
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    {γ : F} {S : Finset (Fin N)}
    (hagree : ∀ i ∈ S, w₀ i + γ * w₁ i = u₀ i + γ * u₁ i)
    (hno : ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁)
    (_hScard : 1 ≤ S.card) :
    (voteSet u₀ u₁ w₀ w₁ γ).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hno
  refine ⟨w₀, hw₀, w₁, hw₁, fun i hi ↦ ?_⟩
  have hmem := witness_subset_aligned_union_votes u₀ u₁ w₀ w₁ hagree hi
  rw [hempty, Finset.union_empty, mem_alignedSet_iff] at hmem
  exact hmem

end Votes

/-! ## Rider counting for a fixed pencil -/

section Riders

variable (dom : Fin N ↪ F) (u₀ u₁ w₀ w₁ : Fin N → F)
variable (R : Finset F) (Sf : F → Finset (Fin N))

/-- The riding hypotheses: each `γ ∈ R` has a threshold witness on which the pencil's
`γ`-line matches the stack's `γ`-line, with the non-joint clause. -/
def RidesAll : Prop :=
  ∀ γ ∈ R, predecessorThreshold ≤ (Sf γ).card ∧
    (∀ i ∈ Sf γ, w₀ i + γ * w₁ i = u₀ i + γ * u₁ i) ∧
    ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) (Sf γ) u₀ u₁

theorem votes_biUnion_card_le :
    (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card ≤
      N - (alignedSet u₀ u₁ w₀ w₁).card := by
  have hsub : R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ) ⊆
      Finset.univ \ alignedSet u₀ u₁ w₀ w₁ := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hiv⟩ := hi
    rw [mem_voteSet_iff] at hiv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiv.1⟩
  calc (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card
      ≤ (Finset.univ \ alignedSet u₀ u₁ w₀ w₁).card := Finset.card_le_card hsub
    _ = N - (alignedSet u₀ u₁ w₀ w₁).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin]

theorem card_biUnion_votes :
    (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card =
      ∑ γ ∈ R, (voteSet u₀ u₁ w₀ w₁ γ).card :=
  Finset.card_biUnion (fun _γ _ _γ' _ hne => voteSet_disjoint u₀ u₁ w₀ w₁ hne)

/-- **Vote-partition bound**: `riders · (T − A) ≤ N − A` when `A ≤ T`. -/
theorem riders_card_mul_le (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) :
    R.card * (predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card) ≤
      N - (alignedSet u₀ u₁ w₀ w₁).card := by
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hA
  have hper : ∀ γ ∈ R, predecessorThreshold - A ≤ (voteSet u₀ u₁ w₀ w₁ γ).card := by
    intro γ hγ
    obtain ⟨hcard, hagree, _⟩ := h γ hγ
    have hsub := witness_subset_aligned_union_votes u₀ u₁ w₀ w₁ hagree
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  calc R.card * (predecessorThreshold - A)
      = ∑ _γ ∈ R, (predecessorThreshold - A) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ R, (voteSet u₀ u₁ w₀ w₁ γ).card := Finset.sum_le_sum hper
    _ = (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card :=
        (card_biUnion_votes u₀ u₁ w₀ w₁ R).symm
    _ ≤ N - A := votes_biUnion_card_le u₀ u₁ w₀ w₁ R

/-- **Complement bound**: every rider votes, so `riders ≤ N − A`. -/
theorem riders_card_le_compl
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) :
    R.card ≤ N - (alignedSet u₀ u₁ w₀ w₁).card := by
  have hper : ∀ γ ∈ R, 1 ≤ (voteSet u₀ u₁ w₀ w₁ γ).card := by
    intro γ hγ
    obtain ⟨hcard, hagree, hno⟩ := h γ hγ
    have hT : 1 ≤ (Sf γ).card := by
      have := predecessorThreshold_eq
      omega
    exact Finset.card_pos.mpr
      (voteSet_nonempty_of_rides u₀ u₁ w₀ w₁ dom hw₀ hw₁ hagree hno hT)
  calc R.card = ∑ _γ ∈ R, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ γ ∈ R, (voteSet u₀ u₁ w₀ w₁ γ).card := Finset.sum_le_sum hper
    _ = (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card :=
        (card_biUnion_votes u₀ u₁ w₀ w₁ R).symm
    _ ≤ N - (alignedSet u₀ u₁ w₀ w₁).card := votes_biUnion_card_le u₀ u₁ w₀ w₁ R

/-- Step form of the vote bound: `(riders − 1)·(T − A) ≤ N − T`. -/
theorem riders_pred_mul_le (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf)
    (hA : (alignedSet u₀ u₁ w₀ w₁).card ≤ predecessorThreshold) :
    (R.card - 1) * (predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card) ≤
      N - predecessorThreshold := by
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hAdef
  have hmul := riders_card_mul_le dom u₀ u₁ w₀ w₁ R Sf h
  rw [← hAdef] at hmul
  rcases Nat.eq_zero_or_pos R.card with hR | hR
  · simp [hR]
  · have hsplit : R.card * (predecessorThreshold - A) =
        (R.card - 1) * (predecessorThreshold - A) + (predecessorThreshold - A) := by
      obtain ⟨r, hr⟩ : ∃ r, R.card = r + 1 := ⟨R.card - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      exact Nat.succ_mul r _
    have hTN : predecessorThreshold ≤ N := by
      rw [predecessorThreshold_eq]
      norm_num [N]
    omega

/-- **Uniform rider cap**: no pencil carries more than `N − T + 1 = 480946859` bad
scalars. -/
theorem riders_card_le_uniform
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) :
    R.card ≤ 480946859 := by
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hAdef
  have hcompl := riders_card_le_compl dom u₀ u₁ w₀ w₁ R Sf hw₀ hw₁ h
  rw [← hAdef] at hcompl
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  by_cases hA : A ≤ predecessorThreshold
  · have hstep := riders_pred_mul_le dom u₀ u₁ w₀ w₁ R Sf h hA
    rw [← hAdef] at hstep
    by_cases hAT : A = predecessorThreshold
    · omega
    · have hpos : 1 ≤ predecessorThreshold - A := by omega
      have : R.card - 1 ≤ (R.card - 1) * (predecessorThreshold - A) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
  · omega

/-- **Alignment ladder**: `riders·T ≤ N + (riders − 1)·A`. -/
theorem riders_mul_threshold_le (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) :
    R.card * predecessorThreshold ≤ N + (R.card - 1) * (alignedSet u₀ u₁ w₀ w₁).card := by
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hAdef
  set m := R.card with hm
  have hAN : A ≤ N := by
    have h := Finset.card_le_univ (alignedSet u₀ u₁ w₀ w₁)
    rw [Fintype.card_fin] at h
    exact h
  by_cases hA : A ≤ predecessorThreshold
  · have hmul := riders_card_mul_le dom u₀ u₁ w₀ w₁ R Sf h
    rw [← hAdef, ← hm] at hmul
    have hdist : m * (predecessorThreshold - A) + m * A = m * predecessorThreshold := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hA]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · have hm1 : (m - 1) * A + A = m * A := by
        obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
        rw [hr, Nat.add_sub_cancel, Nat.succ_mul]
      omega
  · rw [not_le] at hA
    have h1 : m * predecessorThreshold ≤ m * A :=
      Nat.mul_le_mul_left m (le_of_lt hA)
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · have hm1 : (m - 1) * A + A = m * A := by
        obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
        rw [hr, Nat.add_sub_cancel, Nat.succ_mul]
      omega

/-- **The Johnson crossover floor**: ten riders force alignment `≥ 539356427`. -/
theorem alignment_floor_of_ten_riders (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf)
    (h10 : 10 ≤ R.card) :
    539356427 ≤ (alignedSet u₀ u₁ w₀ w₁).card := by
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hAdef
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  by_cases hA : A ≤ predecessorThreshold
  · have hstep := riders_pred_mul_le dom u₀ u₁ w₀ w₁ R Sf h hA
    rw [← hAdef] at hstep
    have h9 : 9 * (predecessorThreshold - A) ≤
        (R.card - 1) * (predecessorThreshold - A) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · omega

/-- The ten-rider alignment floor exceeds the Johnson threshold `√(N(k−1))`. -/
theorem ten_rider_floor_beats_johnson : N * (k - 1) < 539356427 ^ 2 := by
  norm_num [N, k]

/-- The nine-rider floor does not: ten is exact. -/
theorem nine_rider_floor_below_johnson : 532676609 ^ 2 ≤ N * (k - 1) := by
  norm_num [N, k]

end Riders

/-! ## Distinct pencils have almost-disjoint aligned regions -/

theorem alignedSet_inter_card_lt_k (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    {w₀ w₁ w₀' w₁' : Fin N → F}
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hw₀' : w₀' ∈ predecessorCode dom) (hw₁' : w₁' ∈ predecessorCode dom)
    (hne : (w₀, w₁) ≠ (w₀', w₁')) :
    (alignedSet u₀ u₁ w₀ w₁ ∩ alignedSet u₀ u₁ w₀' w₁').card ≤ k - 1 := by
  by_contra hbig
  rw [not_le] at hbig
  have hk : k ≤ (alignedSet u₀ u₁ w₀ w₁ ∩ alignedSet u₀ u₁ w₀' w₁').card := by
    have hkval : k = 268435456 := by norm_num [k]
    omega
  have hagree0 : ∀ x ∈ alignedSet u₀ u₁ w₀ w₁ ∩ alignedSet u₀ u₁ w₀' w₁',
      w₀ x = w₀' x := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    rw [mem_alignedSet_iff] at h1 h2
    rw [h1.1, h2.1]
  have hagree1 : ∀ x ∈ alignedSet u₀ u₁ w₀ w₁ ∩ alignedSet u₀ u₁ w₀' w₁',
      w₁ x = w₁' x := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    rw [mem_alignedSet_iff] at h1 h2
    rw [h1.2, h2.2]
  exact hne (Prod.ext
    (predecessor_sep dom w₀ hw₀ w₀' hw₀' _ hk hagree0)
    (predecessor_sep dom w₁ hw₁ w₁' hw₁' _ hk hagree1))

/-! ## The fiber partition through a base scalar -/

section Fibers

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- Witness data for a bad family: thresholds, codeword membership, line agreement,
non-jointness. -/
def BadFamilyData : Prop :=
  ∀ γ ∈ G, predecessorThreshold ≤ (Sf γ).card ∧
    pf γ ∈ predecessorCode dom ∧
    (∀ i ∈ Sf γ, pf γ i = u₀ i + γ * u₁ i) ∧
    ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) (Sf γ) u₀ u₁

/-- The divided-difference pencil of the pair `(γ₀, γ)`. -/
noncomputable def pencilOf (γ₀ γ : F) : (Fin N → F) × (Fin N → F) :=
  (pencilBase γ₀ γ (pf γ₀) (pf γ), pencilDir γ₀ γ (pf γ₀) (pf γ))

/-- Every fiber of the base-scalar pencil map has at most `N − T` members. -/
theorem fiber_card_le (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (π : (Fin N → F) × (Fin N → F)) (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) :
    ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card ≤
      N - predecessorThreshold := by
  classical
  obtain ⟨γ₁, hγ₁, hπeq⟩ := Finset.mem_image.mp hπ
  have hγ₁ne : γ₁ ≠ γ₀ := (Finset.mem_erase.mp hγ₁).1
  have hγ₁G : γ₁ ∈ G := (Finset.mem_erase.mp hγ₁).2
  set fib := (G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π) with hfib
  set R := insert γ₀ fib with hR
  set W₀ := π.1 with hW₀
  set W₁ := π.2 with hW₁
  -- the pencil components are codewords
  have hW₀mem : W₀ ∈ predecessorCode dom := by
    rw [hW₀, ← hπeq]
    exact pencilBase_mem _ (hdata γ₀ hγ₀).2.1 (hdata γ₁ hγ₁G).2.1
  have hW₁mem : W₁ ∈ predecessorCode dom := by
    rw [hW₁, ← hπeq]
    exact pencilDir_mem _ (hdata γ₀ hγ₀).2.1 (hdata γ₁ hγ₁G).2.1
  -- everybody in `R` rides `π`
  have hfunext : ∀ γ ∈ R, pf γ = W₀ + γ • W₁ := by
    intro γ hγ
    rcases Finset.mem_insert.mp hγ with rfl | hγf
    · -- the base rides via `pencil_reproduces_first`
      have := pencil_reproduces_first γ (γ₁) (pf γ) (pf γ₁)
      rw [hW₀, hW₁, ← hπeq]
      exact this.symm
    · -- fiber members ride via `pencil_reproduces_second`
      have hγπ := (Finset.mem_filter.mp hγf).2
      have hγne : γ₀ ≠ γ :=
        fun h ↦ (Finset.mem_erase.mp (Finset.mem_filter.mp hγf).1).1 h.symm
      have := pencil_reproduces_second hγne (pf γ₀) (pf γ)
      rw [hW₀, hW₁, ← hγπ]
      exact this.symm
  have hrides : RidesAll dom u₀ u₁ W₀ W₁ R Sf := by
    intro γ hγ
    have hγG : γ ∈ G := by
      rcases Finset.mem_insert.mp hγ with rfl | hγf
      · exact hγ₀
      · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hγf).1
    obtain ⟨hcard, hmem, hagree, hno⟩ := hdata γ hγG
    refine ⟨hcard, fun i hi ↦ ?_, hno⟩
    have hfun := congrFun (hfunext γ hγ) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hfun
    rw [← hfun]
    exact hagree i hi
  -- extract the numeric bound
  have hγ₀fib : γ₀ ∉ fib := by
    rw [hfib]
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  have hRcard : R.card = fib.card + 1 := by
    rw [hR, Finset.card_insert_of_notMem hγ₀fib]
  set A := (alignedSet u₀ u₁ W₀ W₁).card with hAdef
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  by_cases hA : A ≤ predecessorThreshold
  · have hstep := riders_pred_mul_le dom u₀ u₁ W₀ W₁ R Sf hrides hA
    rw [← hAdef, hRcard] at hstep
    have hstep' : fib.card * (predecessorThreshold - A) ≤ N - predecessorThreshold := by
      simpa using hstep
    by_cases hAT : A = predecessorThreshold
    · have hcompl := riders_card_le_compl dom u₀ u₁ W₀ W₁ R Sf hW₀mem hW₁mem hrides
      rw [← hAdef, hRcard] at hcompl
      omega
    · have hfibmul : fib.card ≤ fib.card * (predecessorThreshold - A) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
  · have hcompl := riders_card_le_compl dom u₀ u₁ W₀ W₁ R Sf hW₀mem hW₁mem hrides
    rw [← hAdef, hRcard] at hcompl
    omega

/-- **Fiber partition**: `#bad ≤ 1 + (#pencils through the base) · (N − T)`. -/
theorem badFamily_card_le_one_add_pencilImage
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf) (γ₀ : F) (hγ₀ : γ₀ ∈ G) :
    G.card ≤ 1 + ((G.erase γ₀).image (pencilOf pf γ₀)).card *
      (N - predecessorThreshold) := by
  classical
  have hsplit : (G.erase γ₀).card + 1 = G.card := Finset.card_erase_add_one hγ₀
  have hfiber : (G.erase γ₀).card =
      ∑ π ∈ (G.erase γ₀).image (pencilOf pf γ₀),
        ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun γ hγ ↦ Finset.mem_image_of_mem _ hγ)
  have hbound : ∑ π ∈ (G.erase γ₀).image (pencilOf pf γ₀),
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card ≤
      ((G.erase γ₀).image (pencilOf pf γ₀)).card * (N - predecessorThreshold) := by
    calc ∑ π ∈ (G.erase γ₀).image (pencilOf pf γ₀),
        ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card
        ≤ ∑ _π ∈ (G.erase γ₀).image (pencilOf pf γ₀), (N - predecessorThreshold) :=
          Finset.sum_le_sum (fun π hπ ↦ fiber_card_le dom u₀ u₁ G Sf pf hdata γ₀ hγ₀ π hπ)
      _ = ((G.erase γ₀).image (pencilOf pf γ₀)).card * (N - predecessorThreshold) := by
          rw [Finset.sum_const, smul_eq_mul]
  omega

/-- **Consumer.**  Two pencils through the base close the prize budget:
`1 + 2·(N − T) = 961893717 ≤ N`. -/
theorem badFamily_card_le_N_of_image_card_le_two
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf) (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (himg : ((G.erase γ₀).image (pencilOf pf γ₀)).card ≤ 2) :
    G.card ≤ N := by
  have h := badFamily_card_le_one_add_pencilImage dom u₀ u₁ G Sf pf hdata γ₀ hγ₀
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hmul : ((G.erase γ₀).image (pencilOf pf γ₀)).card *
      (N - predecessorThreshold) ≤ 2 * (N - predecessorThreshold) :=
    Nat.mul_le_mul_right _ himg
  omega

/-- **Over-budget forces three pencils through every base scalar.** -/
theorem three_pencils_of_overBudget
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf) (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hover : N < G.card) :
    3 ≤ ((G.erase γ₀).image (pencilOf pf γ₀)).card := by
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (badFamily_card_le_N_of_image_card_le_two dom u₀ u₁ G Sf pf
    hdata γ₀ hγ₀ (by omega)) (by omega)

end Fibers

/-- **Named residual (OPEN).**  At most two distinct divided-difference pencils through a
base scalar of a bad family.  The probe attains exactly two at the P1 shape, so the cap sits
on the realizability boundary; the weighted refinement `Σ_π (N−T)/(T−A_π) ≤ N−1` is the true
remaining quantity, and pairwise-only three-pencil designs are excluded by
`four_witnesses_triple_overlap`. -/
def BasePencilImageCap (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F),
    BadFamilyData dom u₀ u₁ G Sf pf →
    ∀ γ₀ ∈ G, ((G.erase γ₀).image (pencilOf pf γ₀)).card ≤ 2

/-- The residual closes the pencil branch: every bad family has at most `N` scalars. -/
theorem badFamily_card_le_N_of_basePencilImageCap (dom : Fin N ↪ F)
    (hcap : BasePencilImageCap dom)
    (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf) :
    G.card ≤ N := by
  by_contra hover
  rw [not_le] at hover
  have hpos : 0 < G.card := by
    have : 0 < N := by norm_num [N]
    omega
  obtain ⟨γ₀, hγ₀⟩ := Finset.card_pos.mp hpos
  exact absurd (badFamily_card_le_N_of_image_card_le_two dom u₀ u₁ G Sf pf
    hdata γ₀ hγ₀ (hcap u₀ u₁ G Sf pf hdata γ₀ hγ₀)) (by omega)

/-! ## Any four threshold witnesses share a triple-covered coordinate -/

/-- `4T > 2N`: four threshold witnesses cannot be pairwise-only; some coordinate lies in at
least three of them.  Every over-budget family is saturated with shared-triple
configurations. -/
theorem four_witnesses_triple_overlap (S₁ S₂ S₃ S₄ : Finset (Fin N))
    (h₁ : predecessorThreshold ≤ S₁.card) (h₂ : predecessorThreshold ≤ S₂.card)
    (h₃ : predecessorThreshold ≤ S₃.card) (h₄ : predecessorThreshold ≤ S₄.card) :
    ∃ x : Fin N,
      (x ∈ S₁ ∧ x ∈ S₂ ∧ x ∈ S₃) ∨ (x ∈ S₁ ∧ x ∈ S₂ ∧ x ∈ S₄) ∨
      (x ∈ S₁ ∧ x ∈ S₃ ∧ x ∈ S₄) ∨ (x ∈ S₂ ∧ x ∈ S₃ ∧ x ∈ S₄) := by
  by_contra hnone
  rw [not_exists] at hnone
  have e12 := Finset.card_union_add_card_inter S₁ S₂
  have e34 := Finset.card_union_add_card_inter S₃ S₄
  have ecross := Finset.card_union_add_card_inter (S₁ ∪ S₂) (S₃ ∪ S₄)
  have hdisj1 : Disjoint (S₁ ∩ S₂) ((S₁ ∪ S₂) ∩ (S₃ ∪ S₄)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    obtain ⟨-, hx34⟩ := Finset.mem_inter.mp hx'
    apply hnone x
    rcases Finset.mem_union.mp hx34 with h3 | h4
    · exact Or.inl ⟨hx1, hx2, h3⟩
    · exact Or.inr (Or.inl ⟨hx1, hx2, h4⟩)
  have hdisj2 : Disjoint (S₃ ∩ S₄) ((S₁ ∪ S₂) ∩ (S₃ ∪ S₄)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hx3, hx4⟩ := Finset.mem_inter.mp hx
    obtain ⟨hx12, -⟩ := Finset.mem_inter.mp hx'
    apply hnone x
    rcases Finset.mem_union.mp hx12 with h1 | h2
    · exact Or.inr (Or.inr (Or.inl ⟨h1, hx3, hx4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h2, hx3, hx4⟩))
  have hdisj3 : Disjoint (S₁ ∩ S₂) (S₃ ∩ S₄) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    obtain ⟨hx3, -⟩ := Finset.mem_inter.mp hx'
    exact hnone x (Or.inl ⟨hx1, hx2, hx3⟩)
  have hdisj23 : Disjoint (S₁ ∩ S₂ ∪ S₃ ∩ S₄) ((S₁ ∪ S₂) ∩ (S₃ ∪ S₄)) :=
    Finset.disjoint_union_left.mpr ⟨hdisj1, hdisj2⟩
  have hthree : (S₁ ∩ S₂).card + (S₃ ∩ S₄).card +
      ((S₁ ∪ S₂) ∩ (S₃ ∪ S₄)).card ≤ N := by
    have hcup : (S₁ ∩ S₂ ∪ S₃ ∩ S₄ ∪ (S₁ ∪ S₂) ∩ (S₃ ∪ S₄)).card =
        (S₁ ∩ S₂).card + (S₃ ∩ S₄).card + ((S₁ ∪ S₂) ∩ (S₃ ∪ S₄)).card := by
      rw [Finset.card_union_of_disjoint hdisj23,
        Finset.card_union_of_disjoint hdisj3]
    have hle := Finset.card_le_univ (S₁ ∩ S₂ ∪ S₃ ∩ S₄ ∪ (S₁ ∪ S₂) ∩ (S₃ ∪ S₄))
    rw [Fintype.card_fin] at hle
    omega
  have hall : (S₁ ∪ S₂ ∪ (S₃ ∪ S₄)).card ≤ N := by
    have hle := Finset.card_le_univ (S₁ ∪ S₂ ∪ (S₃ ∪ S₄))
    rwa [Fintype.card_fin] at hle
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

end ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge

#print axioms voteSet_disjoint
#print axioms riders_card_mul_le
#print axioms riders_card_le_compl
#print axioms riders_card_le_uniform
#print axioms riders_mul_threshold_le
#print axioms alignment_floor_of_ten_riders
#print axioms ten_rider_floor_beats_johnson
#print axioms nine_rider_floor_below_johnson
#print axioms alignedSet_inter_card_lt_k
#print axioms fiber_card_le
#print axioms badFamily_card_le_one_add_pencilImage
#print axioms badFamily_card_le_N_of_image_card_le_two
#print axioms three_pencils_of_overBudget
#print axioms badFamily_card_le_N_of_basePencilImageCap
#print axioms four_witnesses_triple_overlap
