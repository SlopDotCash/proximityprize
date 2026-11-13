/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListMCAWeld

/-!
# The large-zero witness split (#466 round 2, lane HLOW)

The weld `mcaDeltaStar_ge_of_farLineListBudgeted` reduced the prize floor to three
production obligations; this brick shaves its `hlow` branch (large-zero directions,
`#zeroSet(u₁) ≥ a`).

**The witness split.** If a codeword `w` appears on the line `u₀ + γ·u₁` with agreement
`≥ a`, its agreement set meets the zero set `Z` of `u₁` in `≥ a − #support(u₁)` coordinates,
and on `Z` the line word is `u₀` *independently of `γ`*.  Hence every appearing codeword has
zero-agreement count `≥ a − #support(u₁)` and lies in a `coordinateAgreementFiber` of `u₀`
over an `(a − #support)`-subset of `Z` — the SAME γ-free fiber objects that drive the far
branch.  Consequences landed here:

1. `sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords` — the per-codeword
   lower bound (dual to the in-tree upper bound `directionZeroAgreementSet_card_le_agreeSet_line`).
2. `zeroAgreementStratum_eq_empty_of_add_support_lt` — **all strata `t < a − #support` are
   EMPTY** on large-zero lines.  The in-tree stack budgeted them by unknown `N(t)`/`M(t)`
   envelopes; below the threshold no envelope is needed at all.
3. `exists_mem_coordinateAgreementFiber_of_mem_lineAppearingCodewords` — the fiber form.
4. `zeroAgreementStrataCardBudgeted_thresholdChoose` — on **very-large-zero** directions
   (`k + #support(u₁) ≤ a`, i.e. `#Z ≥ n − a + k`), the threshold `a − #support ≥ k` sits at
   or above the MDS endpoint, so EVERY nonempty stratum is binomially bounded: the stratum
   budget `N(t) = if t + #support < a then 0 else choose(#Z, t)` holds **unconditionally**
   (no low-profile hypothesis).
5. `lineBadScalars_card_le_thresholdChoose_sum` /
   `mcaEvent_filter_card_le_thresholdChoose_sum` — the closed per-line bad-count cap
   `Σ_{a−s ≤ t < a} choose(z,t)·⌊s/(a−t)⌋` (`s = #support`, `z = #Z`) on zero-safe
   very-large-zero lines, wired to the weld's exact `hlow` filter object.
6. `MidBandSafeLineBadScalarsBudgeted` + the wiring theorem — the `hlow` residual after this
   brick is EXACTLY the mid band `a ≤ #Z < n − a + k` (safe lines) plus the unsafe branch.

**Honesty (arithmetic at prize parameters).** The cap in 5 is closed-form but binomially
large: at `z ≈ n`, `choose(z, a − s)` far exceeds any `B_near ≈ n` once `a − s` grows, so
this does NOT by itself discharge `hlow` at ε* = 2⁻¹²⁸ — it eliminates the *low* strata
(`t < a − s`) structurally and reduces the very-large-zero branch to explicit binomial
arithmetic, consistent with the recorded choose-arithmetic obstructions
(`LineListCodewordSupportChooseArithmeticObstruction.lean`).  The map note
`docs/kb/deltastar-466b-hlow-map-2026-07-01.md` records the full dependency graph.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LargeZeroWitnessSplit

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The witness split: agreement forces zero-agreement -/

open Classical in
/-- **The witness-split core.** If a codeword agrees with the line word `u₀ + γ·u₁` on `≥ a`
coordinates, then it agrees with the offset `u₀` on at least `a − #support(u₁)` coordinates of
the zero set of `u₁` — independently of `γ`.  Dual to the in-tree upper bound
`directionZeroAgreementSet_card_le_agreeSet_line`. -/
theorem sub_support_le_zeroAgreement_card_of_agree
    (a : ℕ) (c u₀ u₁ : Fin n → F) (γ : F)
    (hagree : a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) :
    a - (directionSupportSet u₁).card ≤ (directionZeroAgreementSet c u₀ u₁).card := by
  have h := agreeSet_line_card_le_zeroAgreement_add_movingFiber c u₀ u₁ γ
  have hfib : ((directionSupportSet u₁).filter
      (fun i => (c i - u₀ i) / u₁ i = γ)).card ≤ (directionSupportSet u₁).card :=
    Finset.card_filter_le _ _
  omega

open Classical in
/-- Every appearing codeword of the line has zero-agreement count at least
`a − #support(u₁)`. -/
theorem sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {c : Fin n → F}
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    a - (directionSupportSet u₁).card ≤ (directionZeroAgreementSet c u₀ u₁).card := by
  rw [lineAppearingCodewords, Finset.mem_filter] at hc
  obtain ⟨-, -, γ, hγ⟩ := hc
  exact sub_support_le_zeroAgreement_card_of_agree a c u₀ u₁ γ hγ

/-! ### 2. Low strata are EMPTY below the witness-split threshold -/

open Classical in
/-- **Stratum emptiness.** On any line, every zero-agreement stratum with
`t + #support(u₁) < a` is empty: no codeword can reach agreement `a` with fewer than
`a − #support` zero-direction agreements.  This eliminates — structurally, with no envelope
hypothesis — all strata below the witness-split threshold. -/
theorem zeroAgreementStratum_eq_empty_of_add_support_lt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {t : ℕ}
    (ht : t + (directionSupportSet u₁).card < a) :
    zeroAgreementStratum dom k a u₀ u₁ t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  rw [zeroAgreementStratum, Finset.mem_filter] at hc
  have hlow := sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
    dom k a u₀ u₁ hc.1
  rw [hc.2] at hlow
  omega

/-! ### 3. The fiber form: appearing codewords live in γ-free coordinate fibers -/

open Classical in
/-- **The fiber form of the witness split.** For `m + #support(u₁) ≤ a`, every appearing
codeword lies in a `coordinateAgreementFiber` of `u₀` over some `m`-subset of the zero set of
`u₁` — the same γ-independent fiber objects that the far branch counts.  The appearing-codeword
list is therefore covered by the `choose(#zeroSet, m)` fibers. -/
theorem exists_mem_coordinateAgreementFiber_of_mem_lineAppearingCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {c : Fin n → F}
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) {m : ℕ}
    (hm : m + (directionSupportSet u₁).card ≤ a) :
    ∃ T ∈ (directionZeroSet u₁).powersetCard m,
      c ∈ coordinateAgreementFiber dom k u₀ T := by
  have hz := sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
    dom k a u₀ u₁ hc
  have hmz : m ≤ (directionZeroAgreementSet c u₀ u₁).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hmz
  refine ⟨T, Finset.mem_powersetCard.mpr
    ⟨hTsub.trans (Finset.filter_subset _ _), hTcard⟩, ?_⟩
  rw [lineAppearingCodewords, Finset.mem_filter] at hc
  rw [coordinateAgreementFiber, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hc.2.1, fun i hi => ?_⟩
  have hmem := hTsub hi
  rw [directionZeroAgreementSet, Finset.mem_filter] at hmem
  exact hmem.2

/-! ### 4. Very-large-zero directions: an UNCONDITIONAL stratum budget -/

open Classical in
/-- **The threshold-choose stratum budget.** On a very-large-zero direction
(`k + #support(u₁) ≤ a`, equivalently `#zeroSet(u₁) ≥ n − a + k`), the witness-split
threshold `a − #support` is at least `k`, so every nonempty stratum sits at or above the MDS
endpoint: strata below the threshold are empty, strata at or above it are bounded by
`choose(#zeroSet(u₁), t)` via `coordinateAgreementFiber_card_le_one_of_k_le`.  No low-profile
(`t < k`) envelope hypothesis remains on this branch. -/
theorem zeroAgreementStrataCardBudgeted_thresholdChoose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (u₀ u₁ : Fin n → F)
    (hks : k + (directionSupportSet u₁).card ≤ a) :
    ZeroAgreementStrataCardBudgeted dom k a u₀ u₁
      (fun t => if t + (directionSupportSet u₁).card < a then 0
        else (directionZeroSet u₁).card.choose t) := by
  intro t ht
  by_cases hcase : t + (directionSupportSet u₁).card < a
  · simp only [if_pos hcase]
    rw [zeroAgreementStratum_eq_empty_of_add_support_lt dom k a u₀ u₁ hcase]
    simp
  · simp only [if_neg hcase]
    exact zeroAgreementStratum_card_le_choose_of_k_le_t dom hk a u₀ u₁ (by omega)

open Classical in
/-- **The closed per-line bad-count cap on very-large-zero safe lines.**  For a zero-safe line
whose direction has `k + #support(u₁) ≤ a`, the bad scalars are bounded — unconditionally —
by the explicit binomial sum `Σ_{t<a, t+s≥a} choose(z,t)·⌊s/(a−t)⌋` where `s = #support(u₁)`
and `z = #zeroSet(u₁)`. -/
theorem lineBadScalars_card_le_thresholdChoose_sum
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hks : k + (directionSupportSet u₁).card ≤ a) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ ∑ t ∈ Finset.range a,
          (if t + (directionSupportSet u₁).card < a then 0
            else (directionZeroSet u₁).card.choose t) *
            ((directionSupportSet u₁).card / (a - t)) :=
  le_trans
    (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight dom k a u₀ u₁ hsafe)
    (puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
      dom k a u₀ u₁ _ hsafe
      (zeroAgreementStrataCardBudgeted_thresholdChoose dom hk a u₀ u₁ hks))

/-! ### 5. The weld-facing `hlow` connector -/

open Classical in
/-- **The `hlow` connector.**  The weld's exact bad-scalar filter on a zero-safe
very-large-zero line is bounded by the closed threshold-choose sum.  This is the shape
consumed by `mcaDeltaStar_ge_of_farLineListBudgeted`'s `hlow` hypothesis (through
`lowWeight_badCount_le_of_largeZeroSafe_budget`), specialized to the very-large-zero
sub-branch. -/
theorem mcaEvent_filter_card_le_thresholdChoose_sum
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hks : k + (directionSupportSet u₁).card ≤ a) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ ∑ t ∈ Finset.range a,
          (if t + (directionSupportSet u₁).card < a then 0
            else (directionZeroSet u₁).card.choose t) *
            ((directionSupportSet u₁).card / (a - t)) :=
  le_trans
    (Finset.card_le_card
      (ProximityGap.LineListMCAWeld.mcaEvent_filter_subset_lineBadScalars
        dom k a δ haF u₀ u₁))
    (lineBadScalars_card_le_thresholdChoose_sum dom hk a u₀ u₁ hsafe hks)

/-! ### 6. The exact residual after this brick: the mid band -/

/-- **The mid-band residual.**  What remains of the large-zero SAFE branch after the
witness split: directions with `a ≤ #zeroSet(u₁)` but `a < k + #support(u₁)`
(equivalently `a ≤ z < n − a + k`), where the witness-split threshold `a − #support` falls
below the MDS endpoint `k` and the `t < k` fibers are genuinely open. -/
def MidBandSafeLineBadScalarsBudgeted (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    a < k + (directionSupportSet u₁).card →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      (lineBadScalars dom k a u₀ u₁).card ≤ B

/-- **The shave.**  The stack's named large-zero safe residual
(`LargeZeroSafeLineBadScalarsBudgeted`) follows from the mid-band residual plus the (purely
arithmetic) fit of the threshold-choose sum on very-large-zero directions.  After this brick
the open geometry in the weld's `hlow` is exactly: the mid band (`a ≤ #zeroSet < n − a + k`,
safe) and the zero-direction-unsafe branch. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_midBand_and_thresholdChooseFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) {B : ℕ}
    (hmid : MidBandSafeLineBadScalarsBudgeted dom k a B)
    (hfit : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      k + (directionSupportSet u₁).card ≤ a →
      ∑ t ∈ Finset.range a,
        (if t + (directionSupportSet u₁).card < a then 0
          else (directionZeroSet u₁).card.choose t) *
          ((directionSupportSet u₁).card / (a - t)) ≤ B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hne hsafe
  by_cases hband : k + (directionSupportSet u₁).card ≤ a
  · exact le_trans
      (lineBadScalars_card_le_thresholdChoose_sum dom hk a u₀ u₁ hsafe hband)
      (hfit u₁ hne hband)
  · exact hmid u₀ u₁ hne (by omega) hsafe

end ProximityGap.LargeZeroWitnessSplit

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LargeZeroWitnessSplit.sub_support_le_zeroAgreement_card_of_agree
#print axioms ProximityGap.LargeZeroWitnessSplit.sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
#print axioms ProximityGap.LargeZeroWitnessSplit.zeroAgreementStratum_eq_empty_of_add_support_lt
#print axioms ProximityGap.LargeZeroWitnessSplit.exists_mem_coordinateAgreementFiber_of_mem_lineAppearingCodewords
#print axioms ProximityGap.LargeZeroWitnessSplit.zeroAgreementStrataCardBudgeted_thresholdChoose
#print axioms ProximityGap.LargeZeroWitnessSplit.lineBadScalars_card_le_thresholdChoose_sum
#print axioms ProximityGap.LargeZeroWitnessSplit.mcaEvent_filter_card_le_thresholdChoose_sum
#print axioms ProximityGap.LargeZeroWitnessSplit.largeZeroSafeLineBadScalarsBudgeted_of_midBand_and_thresholdChooseFit
