/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction
import ArkLib.Data.CodingTheory.ProximityGap.CharSumDeltaStarBridge

/-!
# The line-list ⟶ `mcaDeltaStar` weld (#466, re-landing the dossier-§12 phantom)

The prize-facing weld of the line-list counting stack (`LineListReduction.lean`) to the
actual prize objects `epsMCA` / `mcaDeltaStar`: **a δ\* floor from a far-line list budget**,

  > **`mcaDeltaStar_ge_of_farLineListBudgeted`** — if every *far* affine line has list size
  > `Λ ≤ L`, the per-direction arithmetic fits (`L·((n−z)/(a−z)) ≤ B_far` for `z < a`), and
  > the large-zero-direction bad counts are budgeted (`≤ B_near`), then
  > `δ ≤ mcaDeltaStar(RS, ε*)` whenever `max(B_far, B_near)/q ≤ ε*`.

This re-derivation is *slack-free and strictly honest about where farness comes from* — the
two structural facts that make the far restriction correct (not an assumption of convenience):

1. **Badness implies witness farness for free** (`no_direction_codeword_on_witness_of_mcaEvent`):
   if `γ` fires `mcaEvent` with witness set `S`, then *no codeword agrees with the direction
   `u₁` on `S`* — otherwise `(w − γ·c, c)` would be a joint pair on `S`, contradicting the
   `¬pairJointAgreesOn` clause.  In particular **aligned directions (`u₁ ∈ C`) have zero bad
   scalars** (`mcaEvent_false_of_direction_mem`), even though their line lists are maximal.
2. **`mcaEvent` is invariant under shifting the direction by a codeword**
   (`mcaEvent_direction_sub_codeword_iff`).  Hence every stack reduces to its coset
   representative, and the dichotomy `farFromCode_of_forall_coset_supportEligible` splits all
   stacks into (far direction) ∨ (some coset representative has ≥ a zero coordinates) — the
   **large-zero branch**, exactly the stack's named residual
   (`LargeZeroSafeLineBadScalarsBudgeted` + the zero-direction-unsafe lines).

The far restriction on the list budget is *forced*, not chosen: **`aligned_line_lambda_ge_q`**
shows any aligned direction has line list size `≥ q`, so a uniform (all-lines) budget `L < q`
is unsatisfiable (`not_uniform_lineListBudgeted_of_lt_card`) — this is the machine refuter of
the support-eligible capstone that the #464 thread retracted.  Fact 1 is why this does not
hurt: the lines with huge lists contribute *zero* bad scalars.

## What remains open (the honest residual, dossier v3 §6 Tier-1 item 2)

The weld's hypotheses `hfarL` (far-line list budget `L`) and `hlow` (large-zero-direction bad
count `B_near`) are the *production obligations*: `hfarL` at `L ≲ ρ·n` is the far-line
list-size theorem, and `hlow` is the low-profile (`t < k`) fiber theorem on large-zero-safe
lines (plus the zero-direction-unsafe residual, split off by
`lowWeight_badCount_le_of_largeZeroSafe_budget`).  Nothing open is silently discharged; both
sit exactly where `LineListReduction.lean` localizes them.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. Badness implies witness farness (free — from the `¬pairJointAgreesOn` clause) -/

/-- **Witness farness is free.** If the line `u₀ + γ·u₁` agrees with a codeword on `S` and no
joint pair explains `(u₀, u₁)` on `S`, then no codeword agrees with the *direction* `u₁` on
all of `S` — otherwise `(w − γ·c, c)` is a joint pair on `S`. -/
theorem no_direction_codeword_on_witness_of_mcaEvent
    (C : Submodule F (Fin n → F)) {u₀ u₁ : Fin n → F} {γ : F}
    {S : Finset (Fin n)}
    (hline : ∃ w ∈ (C : Set (Fin n → F)), ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hnj : ¬ pairJointAgreesOn (C : Set (Fin n → F)) S u₀ u₁) :
    ∀ c ∈ (C : Set (Fin n → F)), ∃ i ∈ S, c i ≠ u₁ i := by
  intro c hc
  by_contra hno
  push_neg at hno
  obtain ⟨w, hw, hwl⟩ := hline
  apply hnj
  refine ⟨w - γ • c, ?_, c, hc, fun i hi => ⟨?_, hno i hi⟩⟩
  · exact Submodule.sub_mem C hw (Submodule.smul_mem C γ hc)
  · calc (w - γ • c) i = w i - γ • c i := rfl
      _ = (u₀ i + γ • u₁ i) - γ • u₁ i := by rw [hwl i hi, hno i hi]
      _ = u₀ i := add_sub_cancel_right _ _

/-- **Aligned directions are never bad.** If the direction is itself a codeword, `mcaEvent`
never fires: the joint pair `(w − γ·u₁, u₁)` always exists on the witness set.  This is why
the maximal line lists of aligned lines (`aligned_line_lambda_ge_q`) are harmless. -/
theorem mcaEvent_false_of_direction_mem
    (C : Submodule F (Fin n → F)) (δ : ℝ≥0) {u₀ u₁ : Fin n → F}
    (hu₁ : u₁ ∈ C) (γ : F) :
    ¬ mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ u₁ γ := by
  rintro ⟨S, -, hline, hnj⟩
  obtain ⟨i, -, hne⟩ :=
    no_direction_codeword_on_witness_of_mcaEvent C hline hnj u₁ hu₁
  exact hne rfl

/-! ### 2. Direction-shift equivariance of `mcaEvent` -/

/-- Shifting the direction by a codeword preserves `mcaEvent` (forward form).  The witness
codeword shifts by `γ·v₁`; joint pairs transport by `p₁ ↦ p₁ − v₁`. -/
theorem mcaEvent_direction_add_codeword
    (C : Submodule F (Fin n → F)) (δ : ℝ≥0) {u₀ u₁ v₁ : Fin n → F}
    (hv₁ : v₁ ∈ C) {γ : F}
    (h : mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ u₁ γ) :
    mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ (u₁ + v₁) γ := by
  obtain ⟨S, hsz, ⟨w, hw, hwl⟩, hnj⟩ := h
  refine ⟨S, hsz,
    ⟨w + γ • v₁, Submodule.add_mem C hw (Submodule.smul_mem C γ hv₁), fun i hi => ?_⟩, ?_⟩
  · calc (w + γ • v₁) i = w i + γ • v₁ i := rfl
      _ = (u₀ i + γ • u₁ i) + γ • v₁ i := by rw [hwl i hi]
      _ = u₀ i + γ • (u₁ + v₁) i := by
          simp only [Pi.add_apply, smul_eq_mul]
          ring
  · rintro ⟨p₀, hp₀, p₁, hp₁, hpair⟩
    refine hnj ⟨p₀, hp₀, p₁ - v₁, Submodule.sub_mem C hp₁ hv₁, fun i hi =>
      ⟨(hpair i hi).1, ?_⟩⟩
    have h2 : p₁ i = u₁ i + v₁ i := (hpair i hi).2
    calc (p₁ - v₁) i = p₁ i - v₁ i := rfl
      _ = (u₁ i + v₁ i) - v₁ i := by rw [h2]
      _ = u₁ i := add_sub_cancel_right _ _

/-- **`mcaEvent` is invariant under shifting the direction by a codeword.**  Badness of a
stack depends only on the coset `u₁ + C` of its direction. -/
theorem mcaEvent_direction_sub_codeword_iff
    (C : Submodule F (Fin n → F)) (δ : ℝ≥0) {u₀ u₁ v₁ : Fin n → F}
    (hv₁ : v₁ ∈ C) (γ : F) :
    mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ (u₁ - v₁) γ ↔
      mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ u₁ γ := by
  constructor
  · intro h
    have := mcaEvent_direction_add_codeword C δ hv₁ h
    simpa [sub_add_cancel] using this
  · intro h
    have := mcaEvent_direction_add_codeword C δ (Submodule.neg_mem C hv₁) h
    simpa [sub_eq_add_neg] using this

open Classical in
/-- Bad-scalar counts are coset invariants of the direction. -/
theorem mcaEvent_filter_card_direction_sub_codeword
    (C : Submodule F (Fin n → F)) (δ : ℝ≥0) {u₀ u₁ v₁ : Fin n → F} (hv₁ : v₁ ∈ C) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ u₁ γ)).card
      = (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ (u₁ - v₁) γ)).card := by
  have hset : (Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ u₁ γ))
      = (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ (u₁ - v₁) γ)) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mcaEvent_direction_sub_codeword_iff C δ hv₁ γ).symm
  rw [hset]

/-! ### 3. The bad filter sits inside the line-list bad-scalar set -/

open Classical in
/-- **Every bad scalar is a line-list bad scalar** (unconditionally — the forward direction of
the far-coset law needs no farness).  Requires only that the agreement threshold `a` is at most
the witness size: `a ≤ m` for every natural `m ≥ (1−δ)·n`. -/
theorem mcaEvent_filter_subset_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      ⊆ lineBadScalars dom k a u₀ u₁ := by
  intro γ hγ
  obtain ⟨S, hsz, ⟨w, hw, hwl⟩, -⟩ := (Finset.mem_filter.mp hγ).2
  have haS : a ≤ S.card := haF S.card (by simpa [Fintype.card_fin] using hsz)
  rw [lineBadScalars, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, w, hw, le_trans haS (Finset.card_le_card ?_)⟩
  intro i hi
  rw [agreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hwl i hi⟩

/-! ### 4. Farness controls the zero set; the coset dichotomy -/

/-- A far direction has fewer than `a` zero coordinates (for `a ≥ (1−δ)·n`): otherwise the
zero codeword agrees with it on an `a`-sized witness set. -/
theorem directionZeroSet_card_lt_of_farFromCode
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    {u₁ : Fin n → F}
    (hfar : FarFromCode
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁) :
    (directionZeroSet u₁).card < a := by
  by_contra hge
  push_neg at hge
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hge
  have h0 : (0 : Fin n → F) ∈
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) :=
    Submodule.zero_mem _
  obtain ⟨i, hi, hne⟩ := hfar 0 h0 S (by
    rw [hcard]
    simpa [Fintype.card_fin] using haC)
  have hz : u₁ i = 0 := by
    have hmem := hS hi
    rw [directionZeroSet, Finset.mem_filter] at hmem
    exact hmem.2
  exact hne (by simp [hz])

/-- **The coset dichotomy.** If no coset representative of the direction has `≥ a` zero
coordinates, the direction is far from the code (for `a ≤ ⌈(1−δ)·n⌉`): any codeword agreeing
with `u₁` on a witness-sized `S` would put `≥ a` zeros into `u₁ − c`. -/
theorem farFromCode_of_forall_coset_supportEligible
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    {u₁ : Fin n → F}
    (h : ∀ v₁ ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (directionZeroSet (u₁ - v₁)).card < a) :
    FarFromCode
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ := by
  intro c hc S hS
  by_contra hno
  push_neg at hno
  have hsub : S ⊆ directionZeroSet (u₁ - c) := by
    intro i hi
    rw [directionZeroSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show u₁ i - c i = 0
    rw [hno i hi, sub_self]
  have hcard : a ≤ (directionZeroSet (u₁ - c)).card :=
    le_trans (haF S.card (by simpa [Fintype.card_fin] using hS))
      (Finset.card_le_card hsub)
  exact absurd hcard (not_le.mpr (h c hc))

open Classical in
/-- The support of a direction is the complement of its zero set. -/
theorem directionSupportSet_card_eq (u₁ : Fin n → F) :
    (directionSupportSet u₁).card = n - (directionZeroSet u₁).card := by
  have h : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.filter_card_add_filter_neg_card_eq_card]
    simp
  omega

/-! ### 5. The far-line bad-scalar budget from the list budget -/

open Classical in
/-- On a far line with list budget `L`, the bad scalars are at most
`L·((n−z)/(a−z))` where `z < a` is the direction's zero count — hence at most any `B_far`
that the arithmetic fit supplies. -/
theorem lineBadScalars_card_le_of_far_lineListBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {L Bfar : ℕ}
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (hfit : ∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar)
    {u₀ u₁ : Fin n → F}
    (hfar : FarFromCode
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁)
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (lineBadScalars dom k a u₀ u₁).card ≤ Bfar := by
  have hz := directionZeroSet_card_lt_of_farFromCode dom k a δ haC hfar
  have hb := lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
    dom k a u₀ u₁ hz hL
  rw [directionSupportSet_card_eq u₁] at hb
  exact le_trans hb (hfit _ hz)

/-! ### 6. THE WELD -/

open Classical in
/-- **The line-list ⟶ `mcaDeltaStar` weld: a δ\* floor from a far-line list budget.**

Hypotheses (`a` is the agreement threshold, canonically `a = ⌈(1−δ)·n⌉`):

* `haC`/`haF` — `a` equals the witness size: `(1−δ)·n ≤ a` and `a ≤ m` for every natural
  `m ≥ (1−δ)·n`;
* `hfarL` — **the far-line list budget**: every far direction's line has `≤ L` appearing
  codewords (the production obligation from `LineListReduction`);
* `hfit` — the per-direction arithmetic fit `L·((n−z)/(a−z)) ≤ B_far` for all `z < a`
  (at `z = 0` this is `L·⌊n/a⌋`; the adversarial extreme `z = a−1` costs `L·(n−a+1)`);
* `hlow` — **the large-zero branch budget**: stacks whose direction has `≥ a` zero
  coordinates have `≤ B_near` bad scalars (the stack's named low-profile residual — see
  `lowWeight_badCount_le_of_largeZeroSafe_budget` for its safe/unsafe split);
* `hBudget` — `max(B_far, B_near)/q ≤ ε*`.

Conclusion: `δ ≤ mcaDeltaStar(RS[dom,k], ε*)`.

The proof needs no farness assumption on the *stack*: by the direction-shift invariance
(`mcaEvent_direction_sub_codeword_iff`) and the coset dichotomy
(`farFromCode_of_forall_coset_supportEligible`), every stack either reduces to a large-zero
direction (branch `hlow`) or has a genuinely far direction (branch `hfarL`, through
`mcaEvent_filter_subset_lineBadScalars`).  The far restriction on `hfarL` is *necessary*:
`aligned_line_lambda_ge_q`. -/
theorem mcaDeltaStar_ge_of_farLineListBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞) {L Bfar Bnear : ℕ}
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ L)
    (hfit : ∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar)
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
    calc (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (u 0) (u 1) γ)).card
        ≤ (lineBadScalars dom k a (u 0) (u 1)).card :=
          Finset.card_le_card
            (mcaEvent_filter_subset_lineBadScalars dom k a δ haF (u 0) (u 1))
      _ ≤ Bfar := lineBadScalars_card_le_of_far_lineListBudgeted dom k a δ haC hfit hfar
            (hfarL (u 0) (u 1) hfar)
      _ ≤ max Bfar Bnear := le_max_left _ _

/-! ### 7. The refuter: the far restriction is FORCED -/

open Classical in
/-- **Aligned lines have maximal list size.** For a nonzero codeword direction, every scalar
multiple appears on the line `{0 + γ·u₁}` with full agreement, so `Λ ≥ q`.  This is the
machine refuter of any *uniform* (all-directions) line-list budget below `q` — the far
restriction in the weld is forced, and harmless by `mcaEvent_false_of_direction_mem`. -/
theorem aligned_line_lambda_ge_q
    (dom : Fin n ↪ F) (k a : ℕ) (ha : a ≤ n)
    {u₁ : Fin n → F} (hu₁ : u₁ ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hne : u₁ ≠ 0) :
    Fintype.card F ≤ (lineAppearingCodewords dom k a 0 u₁).card := by
  have hmaps : ∀ γ ∈ (Finset.univ : Finset F),
      γ • u₁ ∈ lineAppearingCodewords dom k a 0 u₁ := by
    intro γ _
    rw [lineAppearingCodewords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Submodule.smul_mem _ γ hu₁, γ, ?_⟩
    have hAg : agreeSet (γ • u₁) (fun i => (0 : Fin n → F) i + γ • u₁ i)
        = Finset.univ := by
      rw [agreeSet]
      refine Finset.filter_true_of_mem ?_
      intro i _
      show (γ • u₁) i = (0 : Fin n → F) i + γ • u₁ i
      simp
    rw [hAg, Finset.card_univ, Fintype.card_fin]
    exact ha
  have hinj : Set.InjOn (fun γ : F => γ • u₁)
      ((Finset.univ : Finset F) : Set F) := by
    intro γ _ γ' _ h
    obtain ⟨i, hi⟩ : ∃ i, u₁ i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (funext fun i => hall i)
    have hcoord : γ * u₁ i = γ' * u₁ i := by
      have := congrFun h i
      simpa [smul_eq_mul] using this
    exact mul_right_cancel₀ hi hcoord
  calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
    _ ≤ (lineAppearingCodewords dom k a 0 u₁).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj

/-- **The support-eligible capstone is unsatisfiable** (the #464 retraction, as a theorem):
no uniform all-lines list budget below `q` exists once the code has a nonzero codeword. -/
theorem not_uniform_lineListBudgeted_of_lt_card
    (dom : Fin n ↪ F) (k a : ℕ) (ha : a ≤ n)
    (hex : ∃ u₁ ∈ (rsCode dom k : Submodule F (Fin n → F)), u₁ ≠ (0 : Fin n → F))
    {L : ℕ} (hL : L < Fintype.card F) :
    ¬ ∀ u₀ u₁ : Fin n → F, LineListBudgeted dom k a u₀ u₁ L := by
  intro hall
  obtain ⟨u₁, hu₁, hne⟩ := hex
  have hbudget := hall 0 u₁
  rw [LineListBudgeted] at hbudget
  exact absurd (le_trans (aligned_line_lambda_ge_q dom k a ha hu₁ hne) hbudget)
    (not_le.mpr hL)

/-! ### 8. Wiring `hlow` to the stack's residual layers -/

open Classical in
/-- The weld's large-zero branch splits along zero-direction safety: safe lines are budgeted
by the stack's `LargeZeroSafeLineBadScalarsBudgeted` residual; unsafe lines remain a named
budget.  This places `hlow` exactly on the two open production obligations of
`LineListReduction.lean`. -/
theorem lowWeight_badCount_le_of_largeZeroSafe_budget
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {B Bunsafe : ℕ}
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hsafe : LargeZeroSafeLineBadScalarsBudgeted dom k a B)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe) :
    ∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
        ≤ max B Bunsafe := by
  intro u₀ e₁ hz
  by_cases hs : ZeroDirectionSafeLine dom k a u₀ e₁
  · have hnotel : ¬ SupportEligibleLineDirection a e₁ := by
      rw [SupportEligibleLineDirection]
      exact not_lt.mpr hz
    refine le_trans (le_trans
      (Finset.card_le_card (mcaEvent_filter_subset_lineBadScalars dom k a δ haF u₀ e₁))
      (hsafe u₀ e₁ hnotel hs)) (le_max_left _ _)
  · exact le_trans (hunsafe u₀ e₁ hs) (le_max_right _ _)

end ProximityGap.LineListMCAWeld

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LineListMCAWeld.no_direction_codeword_on_witness_of_mcaEvent
#print axioms ProximityGap.LineListMCAWeld.mcaEvent_false_of_direction_mem
#print axioms ProximityGap.LineListMCAWeld.mcaEvent_direction_sub_codeword_iff
#print axioms ProximityGap.LineListMCAWeld.mcaEvent_filter_subset_lineBadScalars
#print axioms ProximityGap.LineListMCAWeld.farFromCode_of_forall_coset_supportEligible
#print axioms ProximityGap.LineListMCAWeld.mcaDeltaStar_ge_of_farLineListBudgeted
#print axioms ProximityGap.LineListMCAWeld.aligned_line_lambda_ge_q
#print axioms ProximityGap.LineListMCAWeld.not_uniform_lineListBudgeted_of_lt_card
#print axioms ProximityGap.LineListMCAWeld.lowWeight_badCount_le_of_largeZeroSafe_budget
