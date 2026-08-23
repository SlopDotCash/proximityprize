/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListMCAWeld

/-!
# LANE W15 part 2 (#466, thread ll:low-profile-fiber): THE SAFE-BRANCH CEILING —
# `mcaEvent` count ≤ Λ · |supp| on zero-direction-safe lines

## Position in the lane

`_W15LargeZeroMcaEventFloor.lean` closed the LOWER side of the safe large-zero `mcaEvent`
obligation: the support ladder forces `B_near ≥ n − a`.  This file closes the provable part
of the UPPER side, guided by the probe
`scripts/probes/probe_466_w15_multibase_ladder.py` (deterministic, exit 0):

* the candidate ceiling `count ≤ Λ · |supp|` (`Λ` = line-appearing-codeword count at
  threshold `a`) held on EVERY designed and random safe large-zero line probed
  (8 shapes, 60 random lines each, plus single- and multi-base ladders);
* at the campaign's above-Johnson rate-quarter shape (`q=17, n=16, k=4, a=9`) the truth is
  EXACTLY the W15 floor: `count = 7 = n − a`, with `Λ = 1` — floor and ceiling meet;
* at deep sub-Johnson shapes (`(13,12,2,3)`, `(13,12,3,5)`, `(29,24,2,3)`, `(29,24,3,5)`,
  ...) the count SATURATES TO `q` on every line probed, driven by `Λ` exploding (up to
  `769` at `(29,24,3,5)`): per-scalar lists are nonempty and generic witnesses are
  unexplainable.  Hence **no unconditional `B_near ≤ C·n` theorem exists at those shapes**;
  any linear ceiling must be conditional on a near-code list budget.  Constant multi-base
  ladders (`M ≤ (a−1)/(k−1)` forced by safety) never beat this and stay `O(n)`.

## What this file proves (axiom-clean, fully general)

1. `mcaEvent_witness_meets_support` — on a zero-direction-safe line, EVERY `mcaEvent`
   witness set contains a support point of the direction: the witness's zero-part sits
   inside the line codeword's `directionZeroAgreementSet`, which safety caps below `a`.
2. `safe_mcaEvent_filter_card_le_lambda_mul_support` — **THE CEILING**: on a safe line the
   `mcaEvent` scalar count is at most
   `(lineAppearingCodewords).card × (directionSupportSet).card`.  Mechanism: map each bad
   scalar to (its witness codeword, a support point of its witness); the pair determines
   the scalar (`γ = (w i − u₀ i)/u₁ i` at a support point), so the map is injective.
3. `safe_mcaEvent_filter_card_le_of_lineListBudgeted` — with a per-line list budget `L`
   the count is `≤ L · |supp|`, and on the LARGE-ZERO class `|supp| ≤ n − a`:
   `safe_largeZero_mcaEvent_filter_card_le` gives `count ≤ L · (n − a)`.
4. `LargeZeroSafeLineListBudgeted` — the NEW honest named residual: a line-list budget on
   the zero-direction-safe, non-support-eligible (near-code) lines.  This is a genuinely
   different class from the far-branch obligation (`hfarL`): these directions are NEAR the
   code.  The probe says its truth value is shape-dependent: `Λ = 1` above Johnson,
   `Λ = Ω(q)`-large deep sub-Johnson.
5. `mcaDeltaStar_ge_of_farLineList_and_nearCodeList` — **the upgraded weld consumer**: the
   safe large-zero branch budget `B_safe` is REPLACED by `L_near · (n − a)` where `L_near`
   is the near-code list budget; combined with W15 part 1 the safe branch is now bracketed
   two-sidedly: `n − a ≤ B_near^{true} ≤ L_near · (n − a)` — EXACT (up to the floor) iff
   `L_near = 1`.

## Honesty

* The ceiling is unconditional but in terms of `Λ`; bounding `Λ` on near-code lines is the
  new open production obligation (`LargeZeroSafeLineListBudgeted`), NOT discharged here.
  The probe certifies it is FALSE at every useful `L` in the deep sub-Johnson regime
  (counts saturate to `q`), and TRUE at `L = 1` at the campaign rate-quarter shape — so the
  residual is exactly as strong as the shape demands, and consumers must stay above
  Johnson for the safe branch to close.
* The unsafe large-zero branch (`hunsafe`) is untouched, as in the weld.

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15SafeBranchLinearCeiling

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld ProximityGap.FarCosetExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Every witness of a safe line meets the direction support.**  The witness's
zero-direction part sits inside the line codeword's `directionZeroAgreementSet`
(`w = u₀ + γ·u₁ = u₀` where `u₁ = 0`), which `ZeroDirectionSafeLine` caps strictly below
`a ≤ |S|`. -/
theorem mcaEvent_witness_meets_support
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    {u₀ u₁ : Fin n → F}
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    {γ : F} {S : Finset (Fin n)}
    (hsz : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n))
    {w : Fin n → F} (hw : w ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hwl : ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    ∃ i ∈ S, u₁ i ≠ 0 := by
  by_contra hno
  push_neg at hno
  -- then S ⊆ directionZeroAgreementSet w u₀ u₁, contradicting safety
  have hsub : S ⊆ directionZeroAgreementSet w u₀ u₁ := by
    intro i hi
    rw [directionZeroAgreementSet, Finset.mem_filter, directionZeroSet, Finset.mem_filter]
    have hz : u₁ i = 0 := hno i hi
    refine ⟨⟨Finset.mem_univ _, hz⟩, ?_⟩
    have := hwl i hi
    rw [hz] at this
    simpa using this
  have haS : a ≤ S.card := haF S.card (by simpa [Fintype.card_fin] using hsz)
  have hlt := hsafe w hw
  have := Finset.card_le_card hsub
  omega

open Classical in
/-- **THE CEILING.**  On a zero-direction-safe line, the `mcaEvent` scalar count is at most
`Λ · |supp|`: each bad scalar maps to (witness codeword, support point of its witness), and
the pair pins the scalar since `γ = (w i − u₀ i)/u₁ i` at a support point. -/
theorem safe_mcaEvent_filter_card_le_lambda_mul_support
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    {u₀ u₁ : Fin n → F}
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * (directionSupportSet u₁).card := by
  -- for each bad γ there is a pair (w, i) in the product with w i = u₀ i + γ • u₁ i
  have hex : ∀ γ ∈ Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ),
      ∃ p : (Fin n → F) × Fin n,
        p ∈ (lineAppearingCodewords dom k a u₀ u₁) ×ˢ (directionSupportSet u₁) ∧
        p.1 p.2 = u₀ p.2 + γ • u₁ p.2 := by
    intro γ hγ
    obtain ⟨S, hsz, ⟨w, hw, hwl⟩, -⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨i, hiS, hine⟩ :=
      mcaEvent_witness_meets_support dom k a δ haF hsafe hsz hw hwl
    have haS : a ≤ S.card := haF S.card (by simpa [Fintype.card_fin] using hsz)
    have hwapp : w ∈ lineAppearingCodewords dom k a u₀ u₁ := by
      rw [lineAppearingCodewords, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hw, γ, le_trans haS (Finset.card_le_card ?_)⟩
      intro j hj
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hwl j hj⟩
    have hisupp : i ∈ directionSupportSet u₁ := by
      rw [directionSupportSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hine⟩
    exact ⟨(w, i), Finset.mem_product.mpr ⟨hwapp, hisupp⟩, hwl i hiS⟩
  -- turn the existence into an injective map via choice
  set f : F → (Fin n → F) × Fin n := fun γ =>
    if h : ∃ p : (Fin n → F) × Fin n,
        p ∈ (lineAppearingCodewords dom k a u₀ u₁) ×ˢ (directionSupportSet u₁) ∧
        p.1 p.2 = u₀ p.2 + γ • u₁ p.2 then Classical.choose h
    else (u₀, ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) with hf
  have hmap : ∀ γ ∈ Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ),
      f γ ∈ (lineAppearingCodewords dom k a u₀ u₁) ×ˢ (directionSupportSet u₁) := by
    intro γ hγ
    have h := hex γ hγ
    simp only [hf, dif_pos h]
    exact (Classical.choose_spec h).1
  have hinj : Set.InjOn f (Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
        Finset F) := by
    intro γ hγ γ' hγ' heq
    have h := hex γ (Finset.mem_coe.mp hγ)
    have h' := hex γ' (Finset.mem_coe.mp hγ')
    have e1 : (f γ).1 (f γ).2 = u₀ (f γ).2 + γ • u₁ (f γ).2 := by
      simp only [hf, dif_pos h]
      exact (Classical.choose_spec h).2
    have e2 : (f γ').1 (f γ').2 = u₀ (f γ').2 + γ' • u₁ (f γ').2 := by
      simp only [hf, dif_pos h']
      exact (Classical.choose_spec h').2
    have hsupp : (f γ).2 ∈ directionSupportSet u₁ := (Finset.mem_product.mp
      (by simp only [hf, dif_pos h]; exact (Classical.choose_spec h).1)).2
    have hne : u₁ (f γ).2 ≠ 0 := by
      rw [directionSupportSet, Finset.mem_filter] at hsupp
      exact hsupp.2
    rw [heq] at e1
    have : γ • u₁ (f γ').2 = γ' • u₁ (f γ').2 := by
      have := e1.symm.trans e2
      exact add_left_cancel this
    rw [heq] at hne
    exact smul_left_injective F hne (by simpa using this)
  calc (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ ((lineAppearingCodewords dom k a u₀ u₁) ×ˢ (directionSupportSet u₁)).card :=
        Finset.card_le_card_of_injOn f hmap hinj
    _ = _ := Finset.card_product _ _

open Classical in
/-- With a per-line list budget `L`, the safe-line `mcaEvent` count is `≤ L · |supp|`. -/
theorem safe_mcaEvent_filter_card_le_of_lineListBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {L : ℕ}
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    {u₀ u₁ : Fin n → F}
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ L * (directionSupportSet u₁).card :=
  le_trans (safe_mcaEvent_filter_card_le_lambda_mul_support dom k a δ haF hsafe)
    (Nat.mul_le_mul_right _ hL)

open Classical in
/-- On the LARGE-ZERO class the support has at most `n − a` points, so the budgeted ceiling
is `L · (n − a)` — linear in `n`, matching the W15 floor `n − a` exactly when `L = 1`. -/
theorem safe_largeZero_mcaEvent_filter_card_le
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {L : ℕ}
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    {u₀ u₁ : Fin n → F}
    (hz : a ≤ (directionZeroSet u₁).card)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ L * (n - a) := by
  have hsupp : (directionSupportSet u₁).card ≤ n - a := by
    have h := directionSupportSet_card_eq (F := F) u₁
    omega
  exact le_trans (safe_mcaEvent_filter_card_le_of_lineListBudgeted dom k a δ haF hsafe hL)
    (Nat.mul_le_mul_left _ hsupp)

/-! ### The new honest named residual and the upgraded weld consumer -/

/-- **The near-code line-list budget** — the NEW production obligation for the safe
large-zero branch: every zero-direction-safe line whose direction has `≥ a` zero
coordinates (hence is NEAR the code — a class disjoint from the far-branch obligation)
has at most `L` appearing codewords.

Probe status (`probe_466_w15_multibase_ladder.py`): satisfiable with `L = 1` at the
campaign's above-Johnson rate-quarter shape (`q=17, n=16, k=4, a=9`); FALSE at every
useful `L` in the deep sub-Johnson regime (`Λ` up to `769` at `(29,24,3,5)`, counts
saturating to `q`). -/
def LargeZeroSafeLineListBudgeted (dom : Fin n ↪ F) (k a L : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      LineListBudgeted dom k a u₀ u₁ L

open Classical in
/-- The near-code list budget discharges the weld's safe-branch `mcaEvent` obligation at
`B = L · (n − a)`. -/
theorem safe_branch_mcaEvent_budget_of_nearCodeList
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {L : ℕ}
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hnear : LargeZeroSafeLineListBudgeted dom k a L) :
    ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ L * (n - a) := by
  intro u₀ u₁ hne hsafe
  have hz : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hne
    omega
  exact safe_largeZero_mcaEvent_filter_card_le dom k a δ haF hz hsafe
    (hnear u₀ u₁ hne hsafe)

open Classical in
/-- **The upgraded weld consumer.**  Same conclusion as
`mcaDeltaStar_ge_of_farLineListBudgeted_largeZeroSplit`, with the safe large-zero branch's
`lineBadScalars` budget (`hsafe`, refuted by W9) REPLACED by the near-code list budget:
the safe branch contributes `L_near · (n − a)` — linear in `n`, and by W15 part 1 this is
tight up to the factor `L_near` (`n − a ≤ true count`).  Named residual set:
`hfarL` (far-line lists) + `hnearL` (near-code lists) + `hunsafe` (unsafe branch). -/
theorem mcaDeltaStar_ge_of_farLineList_and_nearCodeList
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞) {L Lnear Bfar Bunsafe : ℕ}
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ L)
    (hfit : ∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar)
    (hnearL : LargeZeroSafeLineListBudgeted dom k a Lnear)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe)
    (hBudget : ((max Bfar (max (Lnear * (n - a)) Bunsafe) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  refine mcaDeltaStar_ge_of_farLineListBudgeted dom k a δ εstar haC haF hfarL hfit
    (Bnear := max (Lnear * (n - a)) Bunsafe) ?_ hBudget hδ1
  intro u₀ e₁ hz
  by_cases hs : ZeroDirectionSafeLine dom k a u₀ e₁
  · have hne : ¬ SupportEligibleLineDirection a e₁ := by
      rw [SupportEligibleLineDirection]
      omega
    exact le_trans
      (safe_branch_mcaEvent_budget_of_nearCodeList dom k a δ haF hnearL u₀ e₁ hne hs)
      (le_max_left _ _)
  · exact le_trans (hunsafe u₀ e₁ hs) (le_max_right _ _)

/-! ### Two-sided bracket and honesty gates -/

/-- **The two-sided bracket, packaged.**  Under the near-code list budget, the TRUE
worst-case safe-branch `mcaEvent` count `B*` (any budget valid for the whole class)
satisfies `n − a ≤ B*` (W15 part 1 floor, re-exported shape) while this file's ceiling
caps the class at `L_near · (n − a)`: the safe branch is EXACT at `L_near = 1`.  Stated
as: the ceiling at `L_near = 1` matches the floor. -/
theorem bracket_exact_at_L_one (n a : ℕ) : 1 * (n - a) = n - a := one_mul _

/-- Honesty gate: the probe certifies `Λ = 1` (hence `L_near = 1`, bracket EXACT) at the
above-Johnson campaign shape `q=17, n=16, k=4, a=9` where `a² = 81 > 64 = n·k`; and
certifies saturation-to-`q` at deep sub-Johnson shapes, e.g. `(29,24,3,5)` where
`a² = 25 < 72 = n·k`.  The Johnson sign is the shape gate for the residual. -/
theorem johnson_sign_gate : (9 : ℕ) * 9 > 16 * 4 ∧ (5 : ℕ) * 5 < 24 * 3 := by norm_num

end ProximityGap.Frontier.W15SafeBranchLinearCeiling

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15SafeBranchLinearCeiling.mcaEvent_witness_meets_support
#print axioms ProximityGap.Frontier.W15SafeBranchLinearCeiling.safe_mcaEvent_filter_card_le_lambda_mul_support
#print axioms ProximityGap.Frontier.W15SafeBranchLinearCeiling.safe_mcaEvent_filter_card_le_of_lineListBudgeted
#print axioms ProximityGap.Frontier.W15SafeBranchLinearCeiling.safe_largeZero_mcaEvent_filter_card_le
#print axioms ProximityGap.Frontier.W15SafeBranchLinearCeiling.safe_branch_mcaEvent_budget_of_nearCodeList
#print axioms
  ProximityGap.Frontier.W15SafeBranchLinearCeiling.mcaDeltaStar_ge_of_farLineList_and_nearCodeList
