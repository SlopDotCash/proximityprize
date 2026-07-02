/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListMCAWeld

/-!
# Lane W5 — the support-aware weld consumer: the vanishing-direction residual, pinned exactly

Issue #466, round-3 lane W5 (round-1 L1 followup).  Companion to
`LineListMCAWeld.lean` (the real floor consumer `mcaDeltaStar_ge_of_farLineListBudgeted`).

## (a) What the residual covers — the class analysis

Two consumer generations exist in-tree:

* the historical round-1 form `Frontier/LineListMCAWeldRound1.lean`
  (`mcaDeltaStar_ge_of_lineList_budget`): its residual `hvanish` covers **every direction with
  ANY zero coordinate** (`¬ (∀ i, u₁ i ≠ 0)`) — the coarse class;
* the root weld `mcaDeltaStar_ge_of_farLineListBudgeted`: its residual `hlow` covers **only
  the coset-large-zero class** (`∃ v₁ ∈ C, #zeroSet(u₁ − v₁) ≥ a`).  Partially-vanishing
  directions (`1 ≤ z < a` on every coset representative) are already served by the far branch
  through the support-aware bound
  `lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero`.

This file makes the second fact *named and machine-checked*, and strengthens the consumer:

1. **`direction_largeZeroCoset_or_far_supportEligible`** — the routing dichotomy as a single
   theorem: every direction is either in the coset-large-zero class (the ONLY residual class)
   or is far with zero-set `< a` (hence support-aware served).  The named residual of the
   assembled consumer is therefore **exactly** the zero-set-`≥ a` stratum, never "any zero".
2. **`lineBadScalars_card_le_of_far_support_exact`** — the sharp per-direction service bound:
   a far direction with zero count `z` (any `z ∈ [0, a)`, in particular every
   partially-vanishing far direction) has bad scalars `≤ L·((n−z)/(a−z))` — the exact
   support-aware budget, not a uniform-in-`z` relaxation.
3. **`mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified`** — the **z-stratified consumer**:
   the far-line list budget may now *depend on the direction's zero count* (`L : ℕ → ℕ`), with
   the per-stratum arithmetic fit `L z · ((n−z)/(a−z)) ≤ B_far` for `z < a`.  The root weld is
   the constant-`L` special case; the stratified form lets a production proof exploit
   puncturing (a direction with `z` zeros lives over an `(n−z)`-coordinate frame, where the
   list can be genuinely smaller — offsetting the growing `1/(a−z)` fiber loss).
4. **`mcaDeltaStar_ge_of_zeroStratified_lowProfileFibers`** — the deepest assembled form:
   stratified far branch + safe large-zero branch localized to low-profile (`t < k`)
   coordinate fibers + unsafe large-zero branch.
5. **Satisfiability guards for the far positions** (skeptic check, round-1 vacuity mode):
   `lineListBudgeted_field_pow_k` (`L = q^k` realizes the list-budget position on EVERY line,
   a fortiori on far ones — the open question is only the size `L ≲ ρn`, never satisfiability)
   and `supportAware_fit_satisfiable` (`B_far = L·n` realizes the fit position).  Together
   with `lowProfileFiber_obligation_satisfiable` (already in the weld), every budget position
   of the assembled consumer now has a machine-checked realizer.

## (c) What remains — the weld's total residual after this file

The named hypotheses of `mcaDeltaStar_ge_of_zeroStratified_lowProfileFibers` are the weld's
total residual (everything else is proven or pure arithmetic):

* `hfarL` — the far-line list budget (class: far directions; per-zero-count budgets allowed);
* `hlowFiber` — the **low-profile fiber theorem** (`t < k` fibers on zero-direction-safe
  large-zero lines) — dossier v3 §6 Tier-1 item 2, the primary open counting surface;
* `hunsafe` — the **unsafe large-zero branch** `mcaEvent` budget (class: zero-direction-unsafe
  lines, a subclass of zero-set `≥ a` by
  `directionZeroSet_card_ge_of_not_zeroDirectionSafeLine`).

Nothing else: no vanishing-direction residual survives outside the zero-set-`≥ a` class.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, lane W5.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld.SupportAware

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The routing dichotomy: the residual class is EXACTLY zero-set ≥ a -/

/-- **The class-routing dichotomy.**  Every direction is either in the coset-large-zero class
(`∃` coset representative with `≥ a` zero coordinates — the assembled consumer's ONLY residual
class) or is far from the code with zero count `< a` — i.e. support-aware served by the far
branch.  In particular a partially-vanishing direction (`1 ≤ z < a` everywhere on its coset)
never falls into the residual. -/
theorem direction_largeZeroCoset_or_far_supportEligible
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (u₁ : Fin n → F) :
    (∃ v₁ ∈ (rsCode dom k : Submodule F (Fin n → F)),
        a ≤ (directionZeroSet (u₁ - v₁)).card) ∨
      (FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ ∧
        (directionZeroSet u₁).card < a) := by
  by_cases hcase : ∃ v₁ ∈ (rsCode dom k : Submodule F (Fin n → F)),
      a ≤ (directionZeroSet (u₁ - v₁)).card
  · exact Or.inl hcase
  · push_neg at hcase
    have hfar := farFromCode_of_forall_coset_supportEligible dom k a δ haF hcase
    exact Or.inr ⟨hfar, directionZeroSet_card_lt_of_farFromCode dom k a δ haC hfar⟩

/-! ### 2. The sharp per-direction service bound for partially-vanishing far directions -/

open Classical in
/-- **The exact support-aware service bound on a far line.**  A far direction with zero count
`z = #zeroSet(u₁)` (farness forces `z < a`) and list budget `L` has at most
`L·((n−z)/(a−z))` bad scalars — the per-direction bound itself, not a uniform-in-`z`
relaxation through a fit budget.  This is the theorem that serves every partially-vanishing
(`1 ≤ z < a`) far direction, keeping it out of the weld's residual branch. -/
theorem lineBadScalars_card_le_of_far_support_exact
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {L : ℕ}
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    {u₀ u₁ : Fin n → F}
    (hfar : FarFromCode
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁)
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ L * ((n - (directionZeroSet u₁).card) / (a - (directionZeroSet u₁).card)) := by
  have hz := directionZeroSet_card_lt_of_farFromCode dom k a δ haC hfar
  have hb := lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
    dom k a u₀ u₁ hz hL
  rwa [directionSupportSet_card_eq u₁] at hb

/-! ### 3. Satisfiability guards for the far-branch budget positions (skeptic check) -/

open Classical in
/-- **The list-budget position is satisfiable at `L = q^k` on EVERY line** (far or not): the
appearing codewords are a subset of the empty-coordinate agreement fiber, which the MDS
envelope caps at `q^k`.  The far-line production obligation `hfarL` is therefore never vacuous
— its open content is exclusively the SIZE `L ≲ ρ·n`, not existence. -/
theorem lineListBudgeted_field_pow_k
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    LineListBudgeted dom k a u₀ u₁ (Fintype.card F ^ k) := by
  rw [LineListBudgeted]
  have hsub : lineAppearingCodewords dom k a u₀ u₁ ⊆
      coordinateAgreementFiber dom k u₀ (∅ : Finset (Fin n)) := by
    intro c hc
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    rw [coordinateAgreementFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hc.2.1, fun i hi => by simp at hi⟩
  calc (lineAppearingCodewords dom k a u₀ u₁).card
      ≤ (coordinateAgreementFiber dom k u₀ (∅ : Finset (Fin n))).card :=
        Finset.card_le_card hsub
    _ ≤ Fintype.card F ^ (k - (∅ : Finset (Fin n)).card) :=
        coordinateAgreementFiber_card_le_field_pow_sub_card dom k u₀ ∅
    _ = Fintype.card F ^ k := by simp

/-- **The arithmetic-fit position is satisfiable at `B_far = L·n`** for every zero count
`z < a`: the support-aware ratio `(n−z)/(a−z)` never exceeds `n`.  (The adversarial extreme
`z = a−1` costs `L·(n−a+1) ≤ L·n`.) -/
theorem supportAware_fit_satisfiable (a L : ℕ) :
    ∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ L * n := by
  intro z _
  exact Nat.mul_le_mul (Nat.le_refl L)
    (le_trans (Nat.div_le_self _ _) (Nat.sub_le n z))

/-- The z-stratified far positions are jointly satisfiable: `L z := q^k` realizes the
stratified list-budget hypothesis of the consumer below (on every line, a fortiori on far
ones), and `B_far := q^k · n` realizes its per-stratum fit. -/
theorem zeroStratified_far_positions_satisfiable
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) :
    (∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁
          ((fun _ : ℕ => Fintype.card F ^ k) ((directionZeroSet u₁).card)))
    ∧ (∀ z : ℕ, z < a →
        (fun _ : ℕ => Fintype.card F ^ k) z * ((n - z) / (a - z))
          ≤ Fintype.card F ^ k * n) :=
  ⟨fun u₀ u₁ _ => lineListBudgeted_field_pow_k dom k a u₀ u₁,
    fun z hz => supportAware_fit_satisfiable (n := n) a (Fintype.card F ^ k) z hz⟩

/-! ### 4. The z-stratified weld consumer -/

open Classical in
/-- **The z-stratified weld consumer.**  Identical conclusion and branch structure to
`mcaDeltaStar_ge_of_farLineListBudgeted`, but the far-line list budget may depend on the
direction's zero count: `hfarL` supplies `Λ ≤ L z` for a far direction with `z` zeros, and
`hfit` is the per-stratum fit `L z · ((n−z)/(a−z)) ≤ B_far` (`z < a` — the only stratum a far
direction can occupy).  The root weld is the constant-`L` instance; the stratified form lets
the production input exploit puncturing: over the direction's `(n−z)`-coordinate support frame
the appearing-codeword list can shrink with `z`, compensating the `1/(a−z)` fiber loss.

Budget classes (skeptic positions): `hfarL` quantifies over far directions only (forced by
`aligned_line_lambda_ge_q`; satisfiable — `zeroStratified_far_positions_satisfiable`); `hfit`
is pure arithmetic (satisfiable — `supportAware_fit_satisfiable`); `hlow` quantifies over
zero-set-`≥ a` directions only (the exact residual class —
`direction_largeZeroCoset_or_far_supportEligible`). -/
theorem mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞) {Bfar Bnear : ℕ} (L : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hlow : ∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
        ≤ Bnear)
    (hBudget : ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  refine ArkLib.ProximityGap.CharSumDeltaStarBridge.le_mcaDeltaStar_of_uniformCharSumBound
    (F := F) (A := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar δ
    (M := max Bfar Bnear) ?_ hBudget hδ1
  intro u
  by_cases hcase : ∃ v₁ ∈ (rsCode dom k : Submodule F (Fin n → F)),
      a ≤ (directionZeroSet (u 1 - v₁)).card
  · obtain ⟨v₁, hv₁, hzc⟩ := hcase
    calc (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (u 0) (u 1) γ)).card
        = (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (u 0) (u 1 - v₁) γ)).card :=
          mcaEvent_filter_card_direction_sub_codeword (rsCode dom k) δ hv₁
      _ ≤ Bnear := hlow (u 0) (u 1 - v₁) hzc
      _ ≤ max Bfar Bnear := le_max_right _ _
  · push_neg at hcase
    have hfar := farFromCode_of_forall_coset_supportEligible dom k a δ haF hcase
    have hz := directionZeroSet_card_lt_of_farFromCode dom k a δ haC hfar
    have hb := lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
      dom k a (u 0) (u 1) hz (hfarL (u 0) (u 1) hfar)
    rw [directionSupportSet_card_eq (u 1)] at hb
    calc (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (u 0) (u 1) γ)).card
        ≤ (lineBadScalars dom k a (u 0) (u 1)).card :=
          Finset.card_le_card
            (mcaEvent_filter_subset_lineBadScalars dom k a δ haF (u 0) (u 1))
      _ ≤ L ((directionZeroSet (u 1)).card) *
            ((n - (directionZeroSet (u 1)).card) / (a - (directionZeroSet (u 1)).card)) := hb
      _ ≤ Bfar := hfit _ hz
      _ ≤ max Bfar Bnear := le_max_left _ _

/-! ### 5. The deepest assembled form: stratified far branch + low-profile fibers -/

open Classical in
/-- **The z-stratified assembled consumer.**  The stratified far branch composed with the safe
large-zero branch localized to low-profile coordinate fibers (high fibers `k ≤ t` discharged
by RS uniqueness) and the unsafe large-zero branch.  Its named hypotheses are the weld's
TOTAL residual after this file:

1. `hfarL` — the far-line list budget, per zero count (class: far directions; satisfiable);
2. `hfit` — per-stratum arithmetic (satisfiable);
3. `hlowFiber` — the **low-profile fiber theorem** (`t < k` only; class: zero-set-`≥ a`,
   zero-direction-safe; satisfiable — `lowProfileFiber_obligation_satisfiable`);
4. `hsafeFit` — arithmetic fit of the extended envelope on large-zero directions;
5. `hunsafe` — the unsafe large-zero `mcaEvent` budget (class: zero-direction-unsafe lines,
   a subclass of zero-set-`≥ a` by `directionZeroSet_card_ge_of_not_zeroDirectionSafeLine`).

No vanishing-direction residual survives outside the zero-set-`≥ a` class
(`direction_largeZeroCoset_or_far_supportEligible`). -/
theorem mcaDeltaStar_ge_of_zeroStratified_lowProfileFibers
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bsafe Bunsafe : ℕ} (L M : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hlowFiber : ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
        ∀ t : ℕ, t < a → t < k → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
          (coordinateAgreementFiber dom k u₀ S).card ≤ M t)
    (hsafeFit : UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n)
      a Bsafe (fun t => if t < k then M t else 1))
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe)
    (hBudget : ((max Bfar (max Bsafe Bunsafe) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  have hFiber : UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a
      (fun t => if t < k then M t else 1) := by
    intro u₀ u₁ hne hsafeLine t ht S hS
    by_cases hlt : t < k
    · simpa [hlt] using hlowFiber u₀ u₁ hne hsafeLine t ht hlt S hS
    · have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
      have hone := coordinateAgreementFiber_card_le_one_of_k_le dom hk u₀
        (S := S) (by rw [hScard]; exact Nat.le_of_not_lt hlt)
      simpa [hlt] using hone
  have hsafeB : LargeZeroSafeLineBadScalarsBudgeted dom k a Bsafe :=
    largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
      dom k a Bsafe
      (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
        dom k a Bsafe (fun t => if t < k then M t else 1) hFiber hsafeFit)
  exact mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified dom k a δ εstar L haC haF
    hfarL hfit
    (lowWeight_badCount_le_of_largeZeroSafe_budget dom k a δ haF hsafeB hunsafe)
    hBudget hδ1

end ProximityGap.LineListMCAWeld.SupportAware

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LineListMCAWeld.SupportAware.direction_largeZeroCoset_or_far_supportEligible
#print axioms ProximityGap.LineListMCAWeld.SupportAware.lineBadScalars_card_le_of_far_support_exact
#print axioms ProximityGap.LineListMCAWeld.SupportAware.lineListBudgeted_field_pow_k
#print axioms ProximityGap.LineListMCAWeld.SupportAware.supportAware_fit_satisfiable
#print axioms ProximityGap.LineListMCAWeld.SupportAware.zeroStratified_far_positions_satisfiable
#print axioms ProximityGap.LineListMCAWeld.SupportAware.mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified
#print axioms ProximityGap.LineListMCAWeld.SupportAware.mcaDeltaStar_ge_of_zeroStratified_lowProfileFibers
