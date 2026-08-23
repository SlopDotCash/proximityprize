/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W15SafeBranchLinearCeiling

/-!
# LANE W15 part 4 (#466, thread ll:low-profile-fiber): THE WINDOW IS TWO-SIDED —
# `L_near = 1` is REFUTED inside the Johnson-to-doubled-Johnson window (two-block lines),
# and the double-appearance structure is pinned by the secant lemma

## Position in the lane

Part 3 (`_W15NearCodeJohnsonBudget.lean`) discharged the near-code list budget
`LargeZeroSafeLineListBudgeted` at `L = 1` in the regime `2n + k ≤ 3a`, and left the
window `√ρ < α ≤ (1+√ρ)/2` (containing the campaign rate-quarter shape `n=16, k=4, a=9`)
open, with the part-2 probe suggesting `Λ = 1` there.  This file decides the `L = 1`
question in the window: **NO** — the suggestion was an artifact of unoptimized lines.

## Headlines

1. `secant_appearing_agrees_offset` — **the two-reference secant** (positive, fully
   unconditional): a codeword appearing at TWO distinct scalars agrees with the offset
   `u₀` on `≥ 2a − n` coordinates, all inside the direction's zero set — on the common
   agreement positions `(γ − γ')·u₁ = 0`.  Corollary `appearing_dichotomy`: every
   appearing codeword either uses a UNIQUE scalar or is `u₀`-pinned at threshold `2a − n`.
   This is the exact multiplicity structure the coordinator's census probe measured
   (`probe_466_w15_window_two_reference.py`: a natural `Λ = 2` line carries one
   multiplicity-`7` codeword, secant-pinned).
2. `not_largeZeroSafeLineListBudgeted_one` — **the two-block refuter**: whenever
   `1 ≤ k`, `n + 1 ≤ 2a`, `3a ≤ 2n`, `2k − 1 ≤ a`, the budget `L = 1` is FALSE.  The
   line: `Z = B₀ ⊔ B₁` (`|B_j| = n − a`), offset `0` on `B₀`, `1` on `B₁`, direction
   `= 1` exactly on the remaining `2a − n` support points with offset `0` there.  The
   constant codewords `0` and `1` appear (at `γ = 0` and `γ = 1` respectively, each with
   agreement exactly `a = (n − a) + (2a − n)`), the line is zero-direction-safe
   (constants score `n − a < a` on `Z`; every other codeword scores `≤ 2k − 2 < a`), and
   large-zero (`|Z| = 2(n − a) ≥ a`).  Probe-verified at `(17,16,4,9)`:
   `Λ = 2`, safe, large-zero, `mcaEvent` count `2`.
3. `campaign_rateQuarter_L_one_refuted` — the campaign shape `(16, 4, 9)` satisfies all
   four gates: `L_near = 1` is FALSE there, over every field and domain.
4. `three_a_trichotomy` — the boundary is machine-pinned to a width-`k` gap: every shape
   is in the part-3 discharge regime (`2n + k ≤ 3a`), the refuted regime (`3a ≤ 2n`),
   or the residual gap `2n < 3a < 2n + k`.

## What remains open (honesty)

* The window's TRUE `L_near` is now bracketed `2 ≤ L_near^{true}` (this file) and
  `≤ n²/((2a−n)² − n(k−1))` where the doubled-Johnson margin holds (part 3) — but in the
  deep window (margin fails, e.g. the campaign shape) NO finite upper bound is in-tree:
  the open content of `LargeZeroSafeLineListBudgeted` is now "what is the exact
  `L_near ≥ 2` in the window", with the secant dichotomy as the structural handle (the
  multi-appearance part is Johnson-controllable through `u₀`; the single-appearance part
  is per-scalar Johnson; what is missing is a bound on the number of ACTIVE scalars).
* The two-block family cannot push past `Λ = 2` at minimal support (`s = 2a − n` forces
  `M ≤ 2` blocks); the probe's singleton-block scaling does not even fit at the campaign
  shape.  Whether `L_near^{true} = 2` exactly in the window is open.
* Consequence for the weld: the part-2 bracket `n − a ≤ B_near ≤ L_near·(n − a)` stays,
  but at window shapes the safe branch CANNOT be closed exactly at the floor by the
  near-code-list route with `L = 1`; the part-3 `2n + k ≤ 3a` discharge is essentially
  TIGHT (up to the width-`k` gap).

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15WindowTwoReference

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld
open ProximityGap.Frontier.W15SafeBranchLinearCeiling

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The secant lemma: double appearance pins the offset agreement -/

open Classical in
/-- **The two-reference secant.**  If a codeword `c` has agreement `≥ a` with the line at
TWO distinct scalars, then on the (`≥ 2a − n`)-sized common agreement set the direction
vanishes and `c` agrees with the OFFSET: `2a − n ≤ |agree(c, u₀)|`.  No large-zero, no
safety, no code membership needed — pure two-reference arithmetic. -/
theorem secant_appearing_agrees_offset
    (a : ℕ) {u₀ u₁ c : Fin n → F} {γ γ' : F} (hne : γ ≠ γ')
    (h1 : a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)
    (h2 : a ≤ (agreeSet c (fun i => u₀ i + γ' • u₁ i)).card) :
    2 * a - n ≤ (agreeSet c u₀).card := by
  set A := agreeSet c (fun i => u₀ i + γ • u₁ i) with hA
  set A' := agreeSet c (fun i => u₀ i + γ' • u₁ i) with hA'
  have hsub : A ∩ A' ⊆ agreeSet c u₀ := by
    intro i hi
    obtain ⟨hiA, hiA'⟩ := Finset.mem_inter.mp hi
    rw [hA, agreeSet, Finset.mem_filter] at hiA
    rw [hA', agreeSet, Finset.mem_filter] at hiA'
    have hzero : u₁ i = 0 := by
      have heq : γ • u₁ i = γ' • u₁ i := by
        have := hiA.2.symm.trans hiA'.2
        simpa using this
      by_contra hz
      exact hne (smul_left_injective F hz (by simpa using heq))
    rw [agreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hiA.2
    rw [hzero] at this
    simpa using this
  have hie := Finset.card_union_add_card_inter A A'
  have hun : (A ∪ A').card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (A ∪ A'))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have := Finset.card_le_card hsub
  omega

open Classical in
/-- **The appearance dichotomy**: every line-appearing codeword either uses a UNIQUE
scalar, or agrees with the offset on `≥ 2a − n` coordinates.  (The multiplicity census
structure: multi-appearing codewords are `u₀`-pinned.) -/
theorem appearing_dichotomy
    (dom : Fin n ↪ F) (k a : ℕ) {u₀ u₁ : Fin n → F} {c : Fin n → F}
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    (∀ γ γ' : F,
        a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card →
        a ≤ (agreeSet c (fun i => u₀ i + γ' • u₁ i)).card → γ = γ') ∨
      2 * a - n ≤ (agreeSet c u₀).card := by
  by_cases h : ∀ γ γ' : F,
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card →
      a ≤ (agreeSet c (fun i => u₀ i + γ' • u₁ i)).card → γ = γ'
  · exact Or.inl h
  · push_neg at h
    obtain ⟨γ, γ', h1, h2, hne⟩ := h
    exact Or.inr (secant_appearing_agrees_offset a hne h1 h2)

/-! ### 2. The two-block line -/

/-- The two-block direction: `1` exactly off `B₀ ∪ B₁`. -/
def twoBlockDirection (B₀ B₁ : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ B₀ ∪ B₁ then 0 else 1

/-- The two-block offset: `1` on `B₁`, `0` elsewhere (in particular on `B₀` and on the
support). -/
def twoBlockOffset (B₁ : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ B₁ then 1 else 0

open Classical in
theorem directionZeroSet_twoBlock (B₀ B₁ : Finset (Fin n)) :
    directionZeroSet (twoBlockDirection (F := F) B₀ B₁) = B₀ ∪ B₁ := by
  ext i
  rw [directionZeroSet, Finset.mem_filter]
  constructor
  · rintro ⟨-, hz⟩
    by_contra hi
    simp only [twoBlockDirection, if_neg hi] at hz
    exact one_ne_zero hz
  · intro hi
    exact ⟨Finset.mem_univ _, by simp only [twoBlockDirection, if_pos hi]⟩

/-- The constant-one codeword. -/
theorem const_one_mem_rsCode (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    (fun _ : Fin n => (1 : F)) ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  refine ⟨Polynomial.C 1, lt_of_le_of_lt Polynomial.degree_C_le ?_, by funext i; simp⟩
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk

open Classical in
/-- **Safety of the two-block line.**  On `Z = B₀ ∪ B₁`, the constants `0` and `1` score
exactly their own block (`≤ n − a < a`); any other codeword scores `≤ (k−1) + (k−1) < a`. -/
theorem twoBlock_zeroDirectionSafeLine
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (h2a : n + 1 ≤ 2 * a) (hak : 2 * k - 1 ≤ a)
    {B₀ B₁ : Finset (Fin n)} (hd : Disjoint B₀ B₁)
    (hB₀ : B₀.card = n - a) (hB₁ : B₁.card = n - a) :
    ZeroDirectionSafeLine dom k a (twoBlockOffset B₁) (twoBlockDirection B₀ B₁) := by
  intro c hc
  rw [directionZeroAgreementSet, directionZeroSet_twoBlock]
  -- split the filtered set along the two blocks
  have hsplit : ((B₀ ∪ B₁).filter (fun i => c i = twoBlockOffset B₁ i)).card
      ≤ (B₀.filter (fun i => c i = 0)).card + (B₁.filter (fun i => c i = 1)).card := by
    have hsub : (B₀ ∪ B₁).filter (fun i => c i = twoBlockOffset B₁ i)
        ⊆ (B₀.filter (fun i => c i = 0)) ∪ (B₁.filter (fun i => c i = 1)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiZ, hieq⟩ := hi
      rcases Finset.mem_union.mp hiZ with h0 | h1
      · have hiB₁ : i ∉ B₁ := Finset.disjoint_left.mp hd h0
        refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h0, ?_⟩)
        simpa [twoBlockOffset, if_neg hiB₁] using hieq
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h1, ?_⟩)
        simpa [twoBlockOffset, if_pos h1] using hieq
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : (B₁.filter (fun i => (0 : Fin n → F) i = 1)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro i _
      simp only [Pi.zero_apply]
      exact fun h => zero_ne_one h
    have h0 : (B₀.filter (fun i => (0 : Fin n → F) i = 0)).card ≤ n - a :=
      hB₀ ▸ Finset.card_le_card (Finset.filter_subset _ _)
    omega
  by_cases hc1 : c = fun _ => (1 : F)
  · subst hc1
    have h0 : (B₀.filter (fun i => (fun _ : Fin n => (1 : F)) i = 0)).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr
        fun i _ h => (one_ne_zero : (1 : F) ≠ 0) (by simpa using h)
    have h1 : (B₁.filter (fun i => (fun _ : Fin n => (1 : F)) i = 1)).card ≤ n - a :=
      hB₁ ▸ Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · -- generic codeword: ≤ k−1 zeros and ≤ k−1 ones
    have hz : (B₀.filter (fun i => c i = 0)).card ≤ k - 1 := by
      refine le_trans (Finset.card_le_card ?_)
        (rsCode_pairwise_agreeSet_card_le dom hk hc (Submodule.zero_mem _) hc0)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hi).2⟩
    have ho : (B₁.filter (fun i => c i = 1)).card ≤ k - 1 := by
      refine le_trans (Finset.card_le_card ?_)
        (rsCode_pairwise_agreeSet_card_le dom hk hc
          (const_one_mem_rsCode dom hk) hc1)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hi).2⟩
    omega

open Classical in
/-- **Both constants appear.**  `0` appears at `γ = 0` on `B₀ ∪ S` and `1` appears at
`γ = 1` on `B₁ ∪ S`, each with agreement `≥ (n − a) + (2a − n) = a`. -/
theorem twoBlock_constants_appear
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (h2a : n + 1 ≤ 2 * a) (han : a ≤ n)
    {B₀ B₁ : Finset (Fin n)} (hd : Disjoint B₀ B₁)
    (hB₀ : B₀.card = n - a) (hB₁ : B₁.card = n - a) :
    (0 : Fin n → F) ∈ lineAppearingCodewords dom k a
        (twoBlockOffset B₁) (twoBlockDirection B₀ B₁) ∧
      (fun _ : Fin n => (1 : F)) ∈ lineAppearingCodewords dom k a
        (twoBlockOffset B₁) (twoBlockDirection B₀ B₁) := by
  have hZcard : (B₀ ∪ B₁).card = 2 * (n - a) := by
    rw [Finset.card_union_of_disjoint hd, hB₀, hB₁]; omega
  have hScard : ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁)).card = 2 * a - n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hZcard]
    omega
  constructor
  · -- 0 at γ = 0, agreement on B₀ ∪ Sᶜ-part
    rw [lineAppearingCodewords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Submodule.zero_mem _, 0, ?_⟩
    have hsub : B₀ ∪ ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁))
        ⊆ agreeSet (0 : Fin n → F)
          (fun i => twoBlockOffset B₁ i + (0 : F) • twoBlockDirection B₀ B₁ i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hi with h0 | hS
      · have hiB₁ : i ∉ B₁ := Finset.disjoint_left.mp hd h0
        simp [twoBlockOffset, if_neg hiB₁]
      · have hiB₁ : i ∉ B₁ := fun h =>
          (Finset.mem_sdiff.mp hS).2 (Finset.mem_union_right _ h)
        simp [twoBlockOffset, if_neg hiB₁]
    have hcard : a ≤ (B₀ ∪ ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁))).card := by
      have hdisj : Disjoint B₀ ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁)) :=
        Finset.disjoint_left.mpr fun i hi hS =>
          (Finset.mem_sdiff.mp hS).2 (Finset.mem_union_left _ hi)
      rw [Finset.card_union_of_disjoint hdisj, hB₀, hScard]
      omega
    exact le_trans hcard (Finset.card_le_card hsub)
  · -- 1 at γ = 1, agreement on B₁ ∪ Sᶜ-part
    rw [lineAppearingCodewords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, const_one_mem_rsCode dom hk, 1, ?_⟩
    have hsub : B₁ ∪ ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁))
        ⊆ agreeSet (fun _ : Fin n => (1 : F))
          (fun i => twoBlockOffset B₁ i + (1 : F) • twoBlockDirection B₀ B₁ i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hi with h1 | hS
      · have hiZ : i ∈ B₀ ∪ B₁ := Finset.mem_union_right _ h1
        show (fun _ : Fin n => (1 : F)) i
          = twoBlockOffset B₁ i + (1 : F) • twoBlockDirection B₀ B₁ i
        simp only [twoBlockOffset, twoBlockDirection, if_pos h1, if_pos hiZ,
          smul_eq_mul, mul_zero, add_zero]
      · have hiZ : i ∉ B₀ ∪ B₁ := (Finset.mem_sdiff.mp hS).2
        have hiB₁ : i ∉ B₁ := fun h => hiZ (Finset.mem_union_right _ h)
        show (fun _ : Fin n => (1 : F)) i
          = twoBlockOffset B₁ i + (1 : F) • twoBlockDirection B₀ B₁ i
        simp only [twoBlockOffset, twoBlockDirection, if_neg hiB₁, if_neg hiZ,
          smul_eq_mul, mul_one, zero_add]
    have hcard : a ≤ (B₁ ∪ ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁))).card := by
      have hdisj : Disjoint B₁ ((Finset.univ : Finset (Fin n)) \ (B₀ ∪ B₁)) :=
        Finset.disjoint_left.mpr fun i hi hS =>
          (Finset.mem_sdiff.mp hS).2 (Finset.mem_union_right _ hi)
      rw [Finset.card_union_of_disjoint hdisj, hB₁, hScard]
      omega
    exact le_trans hcard (Finset.card_le_card hsub)

/-! ### 3. The refuter -/

open Classical in
/-- **HEADLINE: `L_near = 1` is REFUTED in the window.**  Whenever `1 ≤ k`,
`n + 1 ≤ 2a`, `3a ≤ 2n`, `2k − 1 ≤ a`, the near-code list budget
`LargeZeroSafeLineListBudgeted dom k a 1` is FALSE: the two-block line is safe and
large-zero yet carries the two appearing codewords `0` and `1`. -/
theorem not_largeZeroSafeLineListBudgeted_one
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (h2a : n + 1 ≤ 2 * a) (h3a : 3 * a ≤ 2 * n) (hak : 2 * k - 1 ≤ a) :
    ¬ LargeZeroSafeLineListBudgeted dom k a 1 := by
  intro hL
  -- build the blocks
  obtain ⟨B₀, -, hB₀⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := n - a)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨B₁, hB₁sub, hB₁⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n)) \ B₀) (n := n - a)
    (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hB₀]
      omega)
  have hd : Disjoint B₀ B₁ := Finset.disjoint_left.mpr
    fun i hi h1 => (Finset.mem_sdiff.mp (hB₁sub h1)).2 hi
  -- the line is in the residual's class
  have hne : ¬ SupportEligibleLineDirection a (twoBlockDirection (F := F) B₀ B₁) := by
    rw [SupportEligibleLineDirection, directionZeroSet_twoBlock,
      Finset.card_union_of_disjoint hd, hB₀, hB₁]
    omega
  have hsafe := twoBlock_zeroDirectionSafeLine dom hk h2a hak hd hB₀ hB₁
  have hbudget := hL (twoBlockOffset B₁) (twoBlockDirection B₀ B₁) hne hsafe
  rw [LineListBudgeted] at hbudget
  obtain ⟨h0mem, h1mem⟩ := twoBlock_constants_appear dom hk h2a (by omega) hd hB₀ hB₁
  have hdistinct : (0 : Fin n → F) ≠ (fun _ : Fin n => (1 : F)) := by
    intro h
    have := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact (zero_ne_one : (0 : F) ≠ 1) (by simpa using this)
  have h2 : 1 < (lineAppearingCodewords dom k a
      (twoBlockOffset (F := F) B₁) (twoBlockDirection B₀ B₁)).card :=
    Finset.one_lt_card.mpr
      ⟨(0 : Fin n → F), h0mem, (fun _ : Fin n => (1 : F)), h1mem, hdistinct⟩
  exact absurd hbudget (Nat.not_le.mpr h2)

/-- **The campaign shape is refuted.**  `n = 16, k = 4, a = 9` satisfies all four gates
(`17 ≤ 18`, `27 ≤ 32`, `7 ≤ 9`): no field or domain admits the `L = 1` near-code budget
at the rate-quarter shape.  Together with part 3 (`L = 1` PROVED at `2n + k ≤ 3a`), the
`L = 1` question is now decided on both sides of the width-`k` gap. -/
theorem campaign_rateQuarter_L_one_refuted (dom : Fin 16 ↪ F) :
    ¬ LargeZeroSafeLineListBudgeted dom 4 9 1 :=
  not_largeZeroSafeLineListBudgeted_one dom (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The machine-pinned boundary: every shape lands in the part-3 discharge regime, the
refuted regime, or the width-`k` gap `2n < 3a < 2n + k`. -/
theorem three_a_trichotomy (n k a : ℕ) :
    3 * a ≤ 2 * n ∨ 2 * n + k ≤ 3 * a ∨ (2 * n < 3 * a ∧ 3 * a < 2 * n + k) := by
  omega

end ProximityGap.Frontier.W15WindowTwoReference

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15WindowTwoReference.secant_appearing_agrees_offset
#print axioms ProximityGap.Frontier.W15WindowTwoReference.appearing_dichotomy
#print axioms ProximityGap.Frontier.W15WindowTwoReference.directionZeroSet_twoBlock
#print axioms ProximityGap.Frontier.W15WindowTwoReference.const_one_mem_rsCode
#print axioms ProximityGap.Frontier.W15WindowTwoReference.twoBlock_zeroDirectionSafeLine
#print axioms ProximityGap.Frontier.W15WindowTwoReference.twoBlock_constants_appear
#print axioms ProximityGap.Frontier.W15WindowTwoReference.not_largeZeroSafeLineListBudgeted_one
#print axioms ProximityGap.Frontier.W15WindowTwoReference.campaign_rateQuarter_L_one_refuted
#print axioms ProximityGap.Frontier.W15WindowTwoReference.three_a_trichotomy
