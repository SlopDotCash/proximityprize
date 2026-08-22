/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W15SafeBranchLinearCeiling

/-!
# LANE W15 part 5 (#466, thread ll:low-profile-fiber): THE MULTI-BLOCK LADDER —
# `L_near = 2` is NOT a universal ceiling (three-block refuter), and the constant-block
# ladder is shape-dependent with the campaign shape capped at `M = 2`

## Position in the lane

Part 4 (`_W15WindowTwoReference.lean`) refuted `L_near = 1` at `3a ≤ 2n` via two-block
lines and asked whether `L_near^{true} = 2`.  Probe
`scripts/probes/probe_466_w15_active_scalar_ceiling.py` (deterministic, exit 0) decides
the question is SHAPE-DEPENDENT:

* at `(q, n, k, a) = (11, 10, 2, 6)` the THREE-constant-block line is safe, large-zero,
  and carries `Λ = 3` — `L_near = 2` is FALSE there (formalized below);
* at the campaign rate-quarter shape `(17, 16, 4, 9)` the constant-block ladder is capped
  at `M = 2` by the safety gate `M(k−1) < a` (`3·3 = 9 ≥ 9 = a`), the structured
  non-constant three-piece search found `0` feasible triples in `4000` samples (the
  required `≥ 7` pairwise Z-overlap is essentially unreachable for degree-`< 4`
  codewords), and randomized hill-climbs at `z ∈ {9, 14}` topped out at `Λ = 2`:
  the empirical ceiling there is `2`, but no proof is landed — see honesty below.

## Headlines

1. `not_largeZeroSafeLineListBudgeted_two` — **the three-block refuter**: for any block
   size `b` with `3b ≥ a` (large-zero), `a + 2b ≤ n` (appearance: each constant scores
   `b + (n − 3b) = n − 2b ≥ a`), `b + 1 ≤ a`, `3(k−1) + 1 ≤ a` (safety), `1 ≤ k`, and
   any `μ ∉ {0, 1}`, the budget `L = 2` is FALSE: the constants `0`, `1`, `μ` all appear
   on the three-block line.
2. `elevenShape_L_two_refuted` — the `(n, k, a) = (10, 2, 6)` instantiation (`b = 2`),
   for every field with `≥ 3` elements: `L_near^{true} ≥ 3` at that shape.
3. `campaign_constant_cap` — the campaign shape FAILS the `M = 3` safety gate
   (`¬ 3(k−1) + 1 ≤ a` at `k = 4, a = 9`): the constant-block ladder cannot pass `M = 2`
   there, matching the probe's empirical ceiling.

## The corrected lower ladder (shape-dependent)

The constant-block family with `M` blocks of size `b` refutes `L = M − 1` whenever
`M·b ≥ a`, `n − (M−1)·b ≥ a`, `b ≤ a − 1`, `M(k−1) < a`, `M ≤ q` — so

  `L_near^{true} ≥ M_max(shape)`,  `M_max ≥ 2` throughout `3a ≤ 2n` (part 4),
  `M_max = 3` at `(10, 2, 6)`-like shapes, `M_max = 2` at the campaign shape.

This file formalizes the `M = 3` rung; the general-`M` rung is a mechanical extension
(indexed block families) not needed until a consumer asks for it.

## Honesty

* NO upper bound `Λ ≤ 2` is proved at the campaign shape — the probe evidence
  (structured search + hill-climbs) is measurement, not proof.  The open content of
  `LargeZeroSafeLineListBudgeted` in the deep window is now: prove `Λ ≤ 2` at shapes
  with `3(k−1) ≥ a` (where constant blocks cap at 2 and, per the part-4 secant
  dichotomy, any third codeword must be non-constant with `≥ 7`-point coordinated
  Z-overlaps), or find a non-constant refuter.  Both directions resist the current
  in-tree machinery; the residual stays open with its boundary machine-pinned one rung
  deeper.
* The weld consequence stands as in part 4, sharpened: at `(10,2,6)`-like shapes the
  safe-branch factor is `≥ 3`; at the campaign shape it is `≥ 2` with empirical
  evidence for exactly `2`.

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15MultiBlockRefuter

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld
open ProximityGap.Frontier.W15SafeBranchLinearCeiling

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The three-block direction: `1` exactly off `B₀ ∪ B₁ ∪ B₂`. -/
def threeBlockDirection (B₀ B₁ B₂ : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ B₀ ∪ B₁ ∪ B₂ then 0 else 1

/-- The three-block offset: `1` on `B₁`, `μ` on `B₂`, `0` elsewhere. -/
def threeBlockOffset (B₁ B₂ : Finset (Fin n)) (μ : F) : Fin n → F :=
  fun i => if i ∈ B₁ then 1 else if i ∈ B₂ then μ else 0

open Classical in
theorem directionZeroSet_threeBlock (B₀ B₁ B₂ : Finset (Fin n)) :
    directionZeroSet (threeBlockDirection (F := F) B₀ B₁ B₂) = B₀ ∪ B₁ ∪ B₂ := by
  ext i
  rw [directionZeroSet, Finset.mem_filter]
  constructor
  · rintro ⟨-, hz⟩
    by_contra hi
    simp only [threeBlockDirection, if_neg hi] at hz
    exact one_ne_zero hz
  · intro hi
    exact ⟨Finset.mem_univ _, by simp only [threeBlockDirection, if_pos hi]⟩

/-- Constant codewords. -/
theorem const_mem_rsCode (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (v : F) :
    (fun _ : Fin n => v) ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  refine ⟨Polynomial.C v, lt_of_le_of_lt Polynomial.degree_C_le ?_, by funext i; simp⟩
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk

section Construction

variable {k a b : ℕ} {μ : F}
variable {B₀ B₁ B₂ : Finset (Fin n)}

open Classical in
/-- **Safety of the three-block line.**  Constants score exactly their own block
(`b ≤ a − 1`); every other codeword scores `≤ 3(k−1) < a`. -/
theorem threeBlock_zeroDirectionSafeLine
    (dom : Fin n ↪ F) (hk : 1 ≤ k)
    (hb : b + 1 ≤ a) (hak : 3 * (k - 1) + 1 ≤ a)
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (h01 : Disjoint B₀ B₁) (h02 : Disjoint B₀ B₂) (h12 : Disjoint B₁ B₂)
    (hB₀ : B₀.card = b) (hB₁ : B₁.card = b) (hB₂ : B₂.card = b) :
    ZeroDirectionSafeLine dom k a (threeBlockOffset B₁ B₂ μ)
      (threeBlockDirection B₀ B₁ B₂) := by
  intro c hc
  rw [directionZeroAgreementSet, directionZeroSet_threeBlock]
  have hsplit : ((B₀ ∪ B₁ ∪ B₂).filter
        (fun i => c i = threeBlockOffset B₁ B₂ μ i)).card
      ≤ (B₀.filter (fun i => c i = 0)).card + (B₁.filter (fun i => c i = 1)).card
        + (B₂.filter (fun i => c i = μ)).card := by
    have hsub : (B₀ ∪ B₁ ∪ B₂).filter (fun i => c i = threeBlockOffset B₁ B₂ μ i)
        ⊆ (B₀.filter (fun i => c i = 0)) ∪ (B₁.filter (fun i => c i = 1))
          ∪ (B₂.filter (fun i => c i = μ)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiZ, hieq⟩ := hi
      rcases Finset.mem_union.mp hiZ with h01' | h2
      · rcases Finset.mem_union.mp h01' with h0 | h1
        · have hi1 : i ∉ B₁ := Finset.disjoint_left.mp h01 h0
          have hi2 : i ∉ B₂ := Finset.disjoint_left.mp h02 h0
          refine Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨h0, ?_⟩))
          simpa [threeBlockOffset, if_neg hi1, if_neg hi2] using hieq
        · refine Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨h1, ?_⟩))
          simpa [threeBlockOffset, if_pos h1] using hieq
      · have hi1 : i ∉ B₁ := Finset.disjoint_right.mp h12 h2
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h2, ?_⟩)
        simpa [threeBlockOffset, if_neg hi1, if_pos h2] using hieq
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _)
        (by
          have := Finset.card_union_le (B₀.filter (fun i => c i = 0))
            (B₁.filter (fun i => c i = 1))
          omega))
  -- case split on which constant (if any) c is
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : (B₁.filter (fun i => (0 : Fin n → F) i = 1)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr fun i _ h =>
        (zero_ne_one : (0 : F) ≠ 1) (by simpa using h)
    have h2 : (B₂.filter (fun i => (0 : Fin n → F) i = μ)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr fun i _ h => hμ0 (by simpa using h.symm)
    have h0 : (B₀.filter (fun i => (0 : Fin n → F) i = 0)).card ≤ b :=
      hB₀ ▸ Finset.card_le_card (Finset.filter_subset _ _)
    omega
  by_cases hc1 : c = fun _ => (1 : F)
  · subst hc1
    have h0 : (B₀.filter (fun i => (fun _ : Fin n => (1 : F)) i = 0)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr
        fun i _ h => (one_ne_zero : (1 : F) ≠ 0) (by simpa using h)
    have h2 : (B₂.filter (fun i => (fun _ : Fin n => (1 : F)) i = μ)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr fun i _ h => hμ1 (by simpa using h.symm)
    have h1 : (B₁.filter (fun i => (fun _ : Fin n => (1 : F)) i = 1)).card ≤ b :=
      hB₁ ▸ Finset.card_le_card (Finset.filter_subset _ _)
    omega
  by_cases hcμ : c = fun _ => μ
  · subst hcμ
    have h0 : (B₀.filter (fun i => (fun _ : Fin n => μ) i = 0)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr fun i _ h => hμ0 (by simpa using h)
    have h1 : (B₁.filter (fun i => (fun _ : Fin n => μ) i = 1)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr fun i _ h => hμ1 (by simpa using h)
    have h2 : (B₂.filter (fun i => (fun _ : Fin n => μ) i = μ)).card ≤ b :=
      hB₂ ▸ Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · -- generic codeword: ≤ k−1 agreements with each of the three constants
    have hbound : ∀ (v : F) (B : Finset (Fin n)), c ≠ (fun _ => v) →
        (B.filter (fun i => c i = v)).card ≤ k - 1 := by
      intro v B hne
      refine le_trans (Finset.card_le_card ?_)
        (rsCode_pairwise_agreeSet_card_le dom hk hc (const_mem_rsCode dom hk v) hne)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hi).2⟩
    have h0 := hbound 0 B₀ (by simpa [funext_iff] using hc0)
    have h1 := hbound 1 B₁ hc1
    have h2 := hbound μ B₂ hcμ
    omega

open Classical in
/-- **All three constants appear.**  Constant `v ∈ {0, 1, μ}` appears at `γ = v` with
agreement on its own block plus the whole support: `b + (n − 3b) = n − 2b ≥ a`. -/
theorem threeBlock_constants_appear
    (dom : Fin n ↪ F) (hk : 1 ≤ k)
    (hz : a ≤ 3 * b) (happ : a + 2 * b ≤ n)
    (h01 : Disjoint B₀ B₁) (h02 : Disjoint B₀ B₂) (h12 : Disjoint B₁ B₂)
    (hB₀ : B₀.card = b) (hB₁ : B₁.card = b) (hB₂ : B₂.card = b) :
    ((fun _ : Fin n => (0 : F)) ∈ lineAppearingCodewords dom k a
        (threeBlockOffset B₁ B₂ μ) (threeBlockDirection B₀ B₁ B₂)) ∧
      ((fun _ : Fin n => (1 : F)) ∈ lineAppearingCodewords dom k a
        (threeBlockOffset B₁ B₂ μ) (threeBlockDirection B₀ B₁ B₂)) ∧
      ((fun _ : Fin n => μ) ∈ lineAppearingCodewords dom k a
        (threeBlockOffset B₁ B₂ μ) (threeBlockDirection B₀ B₁ B₂)) := by
  set Z : Finset (Fin n) := B₀ ∪ B₁ ∪ B₂ with hZ
  have hZcard : Z.card = 3 * b := by
    rw [hZ, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint h01, hB₀, hB₁,
      hB₂]
    · omega
    · exact Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  have hScard : ((Finset.univ : Finset (Fin n)) \ Z).card = n - 3 * b := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hZcard]
  -- generic appearance: constant v on block B ⊆ Z where offset = v
  have happear : ∀ (v : F) (B : Finset (Fin n)), B ⊆ Z → B.card = b →
      (∀ i ∈ B, threeBlockOffset (F := F) B₁ B₂ μ i = v) →
      (fun _ : Fin n => v) ∈ lineAppearingCodewords dom k a
        (threeBlockOffset B₁ B₂ μ) (threeBlockDirection B₀ B₁ B₂) := by
    intro v B hBZ hBcard hval
    rw [lineAppearingCodewords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, const_mem_rsCode dom hk v, v, ?_⟩
    have hsub : B ∪ ((Finset.univ : Finset (Fin n)) \ Z)
        ⊆ agreeSet (fun _ : Fin n => v)
          (fun i => threeBlockOffset B₁ B₂ μ i
            + v • threeBlockDirection B₀ B₁ B₂ i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hi with hB | hS
      · have hiZ : i ∈ B₀ ∪ B₁ ∪ B₂ := hBZ hB
        show v = threeBlockOffset B₁ B₂ μ i + v • threeBlockDirection B₀ B₁ B₂ i
        rw [hval i hB]
        simp only [threeBlockDirection, if_pos hiZ, smul_eq_mul, mul_zero, add_zero]
      · have hiZ : i ∉ B₀ ∪ B₁ ∪ B₂ := (Finset.mem_sdiff.mp hS).2
        have hi1 : i ∉ B₁ := fun h => hiZ (Finset.mem_union_left _
          (Finset.mem_union_right _ h))
        have hi2 : i ∉ B₂ := fun h => hiZ (Finset.mem_union_right _ h)
        show v = threeBlockOffset B₁ B₂ μ i + v • threeBlockDirection B₀ B₁ B₂ i
        simp only [threeBlockOffset, threeBlockDirection, if_neg hi1, if_neg hi2,
          if_neg hiZ, smul_eq_mul, mul_one, zero_add]
    have hdisj : Disjoint B ((Finset.univ : Finset (Fin n)) \ Z) :=
      Finset.disjoint_left.mpr fun i hi hS => (Finset.mem_sdiff.mp hS).2 (hBZ hi)
    have hcard : a ≤ (B ∪ ((Finset.univ : Finset (Fin n)) \ Z)).card := by
      rw [Finset.card_union_of_disjoint hdisj, hBcard, hScard]
      omega
    exact le_trans hcard (Finset.card_le_card hsub)
  refine ⟨?_, ?_, ?_⟩
  · refine happear 0 B₀ (fun i hi => Finset.mem_union_left _
      (Finset.mem_union_left _ hi)) hB₀ fun i hi => ?_
    have hi1 : i ∉ B₁ := Finset.disjoint_left.mp h01 hi
    have hi2 : i ∉ B₂ := Finset.disjoint_left.mp h02 hi
    simp only [threeBlockOffset, if_neg hi1, if_neg hi2]
  · refine happear 1 B₁ (fun i hi => Finset.mem_union_left _
      (Finset.mem_union_right _ hi)) hB₁ fun i hi => ?_
    simp only [threeBlockOffset, if_pos hi]
  · refine happear μ B₂ (fun i hi => Finset.mem_union_right _ hi) hB₂ fun i hi => ?_
    have hi1 : i ∉ B₁ := Finset.disjoint_right.mp h12 hi
    simp only [threeBlockOffset, if_neg hi1, if_pos hi]

end Construction

open Classical in
/-- **HEADLINE: the three-block refuter.**  For any block size `b` with `a ≤ 3b`
(large-zero), `a + 2b ≤ n` (appearance), `b + 1 ≤ a`, `3(k−1) + 1 ≤ a` (safety),
`1 ≤ k`, and any `μ ∉ {0, 1}`: the near-code budget `L = 2` is FALSE — the three-block
line is safe and large-zero yet carries three appearing codewords `0`, `1`, `μ`. -/
theorem not_largeZeroSafeLineListBudgeted_two
    (dom : Fin n ↪ F) {k a b : ℕ} (hk : 1 ≤ k)
    (hz : a ≤ 3 * b) (happ : a + 2 * b ≤ n)
    (hb : b + 1 ≤ a) (hak : 3 * (k - 1) + 1 ≤ a)
    {μ : F} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) :
    ¬ LargeZeroSafeLineListBudgeted dom k a 2 := by
  intro hL
  obtain ⟨B₀, -, hB₀⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := b)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨B₁, hB₁sub, hB₁⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n)) \ B₀) (n := b)
    (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hB₀]
      omega)
  obtain ⟨B₂, hB₂sub, hB₂⟩ := Finset.exists_subset_card_eq
    (s := ((Finset.univ : Finset (Fin n)) \ B₀) \ B₁) (n := b)
    (by
      rw [Finset.card_sdiff_of_subset hB₁sub, Finset.card_sdiff_of_subset
        (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hB₀, hB₁]
      omega)
  have h01 : Disjoint B₀ B₁ := Finset.disjoint_left.mpr
    fun i hi h1 => (Finset.mem_sdiff.mp (hB₁sub h1)).2 hi
  have h02 : Disjoint B₀ B₂ := Finset.disjoint_left.mpr
    fun i hi h2 => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hB₂sub h2)).1).2 hi
  have h12 : Disjoint B₁ B₂ := Finset.disjoint_left.mpr
    fun i hi h2 => (Finset.mem_sdiff.mp (hB₂sub h2)).2 hi
  have hne : ¬ SupportEligibleLineDirection a
      (threeBlockDirection (F := F) B₀ B₁ B₂) := by
    rw [SupportEligibleLineDirection, directionZeroSet_threeBlock]
    have : (B₀ ∪ B₁ ∪ B₂).card = 3 * b := by
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint h01, hB₀, hB₁,
        hB₂]
      · omega
      · exact Finset.disjoint_union_left.mpr ⟨h02, h12⟩
    omega
  have hsafe := threeBlock_zeroDirectionSafeLine dom hk hb hak hμ0 hμ1
    h01 h02 h12 hB₀ hB₁ hB₂
  have hbudget := hL (threeBlockOffset B₁ B₂ μ) (threeBlockDirection B₀ B₁ B₂)
    hne hsafe
  rw [LineListBudgeted] at hbudget
  obtain ⟨h0mem, h1mem, hμmem⟩ := threeBlock_constants_appear dom hk hz happ
    h01 h02 h12 hB₀ hB₁ hB₂
  -- three distinct constants ⇒ card ≥ 3
  have hd01 : (fun _ : Fin n => (0 : F)) ≠ (fun _ : Fin n => (1 : F)) := by
    intro h
    have := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact (zero_ne_one : (0 : F) ≠ 1) this
  have hd0μ : (fun _ : Fin n => (0 : F)) ≠ (fun _ : Fin n => μ) := by
    intro h
    have := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact hμ0 this.symm
  have hd1μ : (fun _ : Fin n => (1 : F)) ≠ (fun _ : Fin n => μ) := by
    intro h
    have := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact hμ1 this.symm
  have h3 : 3 ≤ (lineAppearingCodewords dom k a
      (threeBlockOffset (F := F) B₁ B₂ μ) (threeBlockDirection B₀ B₁ B₂)).card := by
    have hsub : ({(fun _ : Fin n => (0 : F)), (fun _ : Fin n => (1 : F)),
        (fun _ : Fin n => μ)} : Finset (Fin n → F))
        ⊆ lineAppearingCodewords dom k a (threeBlockOffset B₁ B₂ μ)
            (threeBlockDirection B₀ B₁ B₂) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact h0mem
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact h1mem
      · rw [Finset.mem_singleton.mp hc]
        exact hμmem
    have hcard3 : ({(fun _ : Fin n => (0 : F)), (fun _ : Fin n => (1 : F)),
        (fun _ : Fin n => μ)} : Finset (Fin n → F)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · exact fun h => hd1μ (Finset.mem_singleton.mp h)
      · intro h
        rcases Finset.mem_insert.mp h with h' | h'
        · exact hd01 h'
        · exact hd0μ (Finset.mem_singleton.mp h')
    calc 3 = ({(fun _ : Fin n => (0 : F)), (fun _ : Fin n => (1 : F)),
          (fun _ : Fin n => μ)} : Finset (Fin n → F)).card := hcard3.symm
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-- **The `(10, 2, 6)` instantiation** (`b = 2`): over every field with `≥ 3` elements
(so a `μ ∉ {0,1}` exists), `L_near = 2` is FALSE — `L_near^{true} ≥ 3` at that shape.
Probe-verified at `q = 11`: `Λ = 3`, safe, large-zero. -/
theorem elevenShape_L_two_refuted (dom : Fin 10 ↪ F) (hcard : 3 ≤ Fintype.card F) :
    ¬ LargeZeroSafeLineListBudgeted dom 2 6 2 := by
  have h01card : ({(0 : F), 1} : Finset F).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
  have hpos : 0 < ((Finset.univ : Finset F) \ {(0 : F), 1}).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨μ, hμmem⟩ := Finset.card_pos.mp hpos
  have hμ01 : μ ∉ ({(0 : F), 1} : Finset F) := (Finset.mem_sdiff.mp hμmem).2
  have hμ0 : μ ≠ 0 := fun h => hμ01 (h ▸ Finset.mem_insert_self _ _)
  have hμ1 : μ ≠ 1 := fun h =>
    hμ01 (Finset.mem_insert_of_mem (h ▸ Finset.mem_singleton_self _))
  exact not_largeZeroSafeLineListBudgeted_two dom (b := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hμ0 hμ1

/-- The campaign rate-quarter shape FAILS the `M = 3` constant-block safety gate:
`3(k−1) + 1 = 10 > 9 = a` at `k = 4` — the constant ladder caps at `M = 2` there,
matching the probe's empirical ceiling `Λ = 2` (hill-climbs at `z ∈ {9, 14}` and a
`4000`-sample structured non-constant search all top out at `2`). -/
theorem campaign_constant_cap : ¬ (3 * (4 - 1) + 1 ≤ 9) := by norm_num

end ProximityGap.Frontier.W15MultiBlockRefuter

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.directionZeroSet_threeBlock
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.const_mem_rsCode
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.threeBlock_zeroDirectionSafeLine
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.threeBlock_constants_appear
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.not_largeZeroSafeLineListBudgeted_two
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.elevenShape_L_two_refuted
#print axioms ProximityGap.Frontier.W15MultiBlockRefuter.campaign_constant_cap
