/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListMCAWeld
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# LANE W15 (#466, thread ll:low-profile-fiber, successor of W9): THE SUPPORT LADDER —
# the surviving `mcaEvent`-vocabulary safe branch has an unconditional `n − a` floor

## Position in the lane

`_W9LowProfilePencilSaturation.lean` refuted the ENTIRE `lineBadScalars`-vocabulary safe
large-zero branch (`hsafe`, `hlowFiber`, the mid-band residual, the uniform stratum budgets):
the root pencil forces every such budget to `≥ |F|`.  Its honesty section names the single
survivor:

> "any surviving line-list route must re-do the safe large-zero branch in the `mcaEvent`
>  vocabulary (joint-pair exclusion is load-bearing), not on `lineBadScalars`."

On the pencil lines the probe measured only `1 + |W| ≤ 3` true `mcaEvent` scalars — leaving
open the sharp production question for the weld's ORIGINAL `hlow` hypothesis
(`mcaDeltaStar_ge_of_farLineListBudgeted`): is the `mcaEvent` bad-scalar count on
zero-direction-safe large-zero lines `O(1)` (pencil scale), or does it grow?

## What this file decides

**It grows: the true count has an unconditional `n − a` floor.**  The *support ladder*: fix
`Z` with `|Z| = a`, a marked point `z₀ ∈ Z`, and set

* `u₁ = 1` off `Z`, `= 0` on `Z`  (direction: large-zero, zero set exactly `Z`);
* `u₀ = 0` on `Z ∖ {z₀}`, `= 1` at `z₀`, and `= −dom i` at each support point `i ∉ Z`.

Then for EVERY support point `i ∉ Z` the scalar `γ = dom i` fires `mcaEvent` with witness
`S = (Z ∖ {z₀}) ∪ {i}` (size `a`): the ZERO codeword lies on the line `u₀ + γ·u₁` over `S`
(`0 = 0 + γ·0` on `Z ∖ {z₀}`, `0 = −dom i + dom i · 1` at `i`), while any joint pair
`(v₀, v₁)` would need a codeword `v₁` equal to `u₁` on `S` — i.e. vanishing on the
`a − 1 ≥ k` points of `Z ∖ {z₀}` (hence `v₁ = 0` by RS degree) yet equal to `1` at `i`.
Impossible: the joint-pair escape hatch that neutralized the W9 pencil is CLOSED here at
every rung of the ladder.  The line is zero-direction-safe by the same degree count: a
codeword agreeing with `u₀` on `≥ a` points of `Z` agrees on all of `Z`, so it vanishes on
`Z ∖ {z₀}` (`a − 1 ≥ k` points, hence is `0`) and then fails at `z₀` where `u₀ z₀ = 1`.
The `n − a` distinct scalars `{dom i : i ∉ Z}` are all bad.

## Headlines (axiom-clean, fully general in `F`, `dom`, `n`, `k`, `a`, `δ`)

1. `ladder_mcaEvent` / `ladder_mcaEvent_filter_card_ge` — the construction: on a
   zero-direction-safe line with zero set exactly `a`, at least `n − a` scalars fire
   `mcaEvent` (whenever `1 ≤ k`, `k + 1 ≤ a`, `(1−δ)·n ≤ a`).
2. `weld_hlow_forces_n_sub_a` — the weld's `hlow` hypothesis
   (`mcaDeltaStar_ge_of_farLineListBudgeted`) forces `B_near ≥ n − a`.
3. `safe_mcaEvent_budget_forces_n_sub_a` — even restricted to the SAFE large-zero class
   (`¬ SupportEligibleLineDirection` AND `ZeroDirectionSafeLine`), any `mcaEvent` budget is
   forced `≥ n − a`: the floor lives exactly on the class W9 left open.
4. `weld_budget_forces_epsilon_ge_n_sub_a_div_q` — through the weld's budget arithmetic,
   every instantiation of the assembled consumer certifies at best
   `ε* ≥ (n − a)/q`.
5. `pencilScale_budget_refuted_rateQuarter` — the pencil-probe scale (`B_near ≤ 3`) is NOT
   the general truth: at the campaign's rate-quarter shape (`n = 16`, `a = 9`) the floor is
   `7 > 3`.

## What survives (honesty)

* This is a **linear-in-`n` floor, NOT a `q`-saturation** — in sharp contrast to W9's
  refutation of the `lineBadScalars` branch.  `ε* ≥ (n − a)/q` is exactly the BCIKS-shaped
  error regime the route is *aiming* for (`ε ~ n/q`), so the `mcaEvent`-vocabulary safe
  branch REMAINS ALIVE: the floor pins the target's order but does not kill it.  The open
  production obligation is now two-sided: prove `B_near ≤ C·n` (upper bound, open) against
  this file's `B_near ≥ n − a` (lower bound, closed).
* The construction needs `a − 1 ≥ k` (i.e. `k + 1 ≤ a`, everywhere in the sub-Johnson
  window) and `a ≤ n − 1` for a nonempty support; at `a = n` the floor is vacuous (`0`), as
  it must be.
* The witness sets of the ladder all share the `a − 1` rungs `Z ∖ {z₀}` and differ in ONE
  support point.  Whether interleaving several base codewords (not just `w = 0`) can push
  the floor superlinearly is NOT decided here; the ladder itself cannot (its base codeword
  is pinned by `u₀` on `a − 1 ≥ k` points).

No probe needed: the construction is fully machine-checked below (probes are for
countermodel searches; this is a constructive floor).

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15LargeZeroMcaEventFloor

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The support-ladder line -/

/-- The ladder direction: `1` off `Z`, `0` on `Z`. -/
def ladderDirection (Z : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ Z then 0 else 1

/-- The ladder offset: `0` on `Z ∖ {z₀}`, `1` at the marked point `z₀`, and `−dom i` at each
support point `i ∉ Z` (so that the scalar `dom i` puts the ZERO codeword on the line at `i`). -/
def ladderOffset (dom : Fin n ↪ F) (Z : Finset (Fin n)) (z₀ : Fin n) : Fin n → F :=
  fun i => if i ∈ Z then (if i = z₀ then 1 else 0) else - dom i

open Classical in
/-- The ladder direction's zero set is exactly `Z`. -/
theorem directionZeroSet_ladder (Z : Finset (Fin n)) :
    directionZeroSet (ladderDirection (F := F) Z) = Z := by
  ext i
  rw [directionZeroSet, Finset.mem_filter]
  constructor
  · rintro ⟨-, hz⟩
    by_contra hiZ
    simp only [ladderDirection, if_neg hiZ] at hz
    exact one_ne_zero hz
  · intro hiZ
    exact ⟨Finset.mem_univ _, by simp only [ladderDirection, if_pos hiZ]⟩

/-- The ladder line is in the large-zero class (not support-eligible) when `|Z| = a`. -/
theorem ladder_not_supportEligible {a : ℕ} {Z : Finset (Fin n)} (hZ : Z.card = a) :
    ¬ SupportEligibleLineDirection a (ladderDirection (F := F) Z) := by
  rw [SupportEligibleLineDirection, directionZeroSet_ladder, hZ]
  omega

/-- An RS codeword vanishing on `≥ k` points is the zero codeword. -/
theorem rsCode_eq_zero_of_vanishes_on
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    {T : Finset (Fin n)} (hT : k ≤ T.card) (hvan : ∀ i ∈ T, c i = 0) :
    c = 0 := by
  classical
  by_contra hne
  have hsub : T ⊆ agreeSet c 0 := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hvan i hi⟩
  have hle : T.card ≤ k - 1 :=
    le_trans (Finset.card_le_card hsub)
      (rsCode_pairwise_agreeSet_card_le dom hk hc (Submodule.zero_mem _) hne)
  omega

open Classical in
/-- **The ladder line is zero-direction-SAFE.**  A codeword agreeing with the offset on
`≥ a` zero-direction coordinates would agree on ALL of `Z` (the zero set has size exactly
`a`), hence vanish on the `a − 1 ≥ k` points of `Z ∖ {z₀}` — so it is `0` — and then fail
at the marked point where the offset is `1`. -/
theorem ladder_zeroDirectionSafeLine
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k) (hka : k + 1 ≤ a)
    {Z : Finset (Fin n)} {z₀ : Fin n} (hz₀ : z₀ ∈ Z) (hZ : Z.card = a) :
    ZeroDirectionSafeLine dom k a (ladderOffset dom Z z₀) (ladderDirection Z) := by
  intro c hc
  by_contra hge
  push_neg at hge
  have hsubZ : directionZeroAgreementSet c (ladderOffset dom Z z₀) (ladderDirection Z)
      ⊆ Z := by
    rw [directionZeroAgreementSet, directionZeroSet_ladder]
    exact Finset.filter_subset _ _
  have heq : directionZeroAgreementSet c (ladderOffset dom Z z₀) (ladderDirection Z) = Z :=
    Finset.eq_of_subset_of_card_le hsubZ (by omega)
  have hall : ∀ i ∈ Z, c i = ladderOffset dom Z z₀ i := by
    intro i hi
    have hmem : i ∈ directionZeroAgreementSet c (ladderOffset dom Z z₀)
        (ladderDirection Z) := heq.symm ▸ hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hmem
    exact hmem.2
  have hvan : ∀ i ∈ Z.erase z₀, c i = 0 := by
    intro i hi
    obtain ⟨hine, hiZ⟩ := Finset.mem_erase.mp hi
    have := hall i hiZ
    simpa [ladderOffset, if_pos hiZ, if_neg hine] using this
  have hTcard : k ≤ (Z.erase z₀).card := by
    rw [Finset.card_erase_of_mem hz₀, hZ]; omega
  have hc0 : c = 0 := rsCode_eq_zero_of_vanishes_on dom hk hc hTcard hvan
  have hz₀val := hall z₀ hz₀
  rw [hc0] at hz₀val
  simp only [ladderOffset, if_pos hz₀, if_pos rfl, Pi.zero_apply] at hz₀val
  exact zero_ne_one hz₀val

/-! ### 2. Every support scalar fires `mcaEvent` -/

open Classical in
/-- **The ladder fires at every support point.**  For `i ∉ Z`, the scalar `γ = dom i` is an
`mcaEvent`: witness `S = insert i (Z ∖ {z₀})` of size `a`, line codeword `0`, and NO joint
pair — a pair's direction component would vanish on the `a − 1 ≥ k` points of `Z ∖ {z₀}`
(hence be the zero codeword) yet equal `1` at `i`. -/
theorem ladder_mcaEvent
    (dom : Fin n ↪ F) {k a : ℕ} (δ : ℝ≥0)
    (hk : 1 ≤ k) (hka : k + 1 ≤ a)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    {Z : Finset (Fin n)} {z₀ : Fin n} (hz₀ : z₀ ∈ Z) (hZ : Z.card = a)
    {i : Fin n} (hi : i ∉ Z) :
    mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (ladderOffset dom Z z₀) (ladderDirection Z) (dom i) := by
  have hiT : i ∉ Z.erase z₀ := fun h => hi (Finset.mem_of_mem_erase h)
  refine ⟨insert i (Z.erase z₀), ?_, ⟨0, Submodule.zero_mem _, ?_⟩, ?_⟩
  · -- size: |S| = 1 + (a − 1) = a ≥ (1 − δ)·n
    have hcard : (insert i (Z.erase z₀)).card = a := by
      rw [Finset.card_insert_of_notMem hiT, Finset.card_erase_of_mem hz₀, hZ]
      omega
    rw [hcard]
    simpa [Fintype.card_fin] using haC
  · -- the zero codeword lies on the line over S
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjT
    · show (0 : F) = ladderOffset dom Z z₀ j + dom j • ladderDirection Z j
      simp only [ladderOffset, ladderDirection, if_neg hi, smul_eq_mul, mul_one]
      ring
    · obtain ⟨hjne, hjZ⟩ := Finset.mem_erase.mp hjT
      show (0 : F) = ladderOffset dom Z z₀ j + dom i • ladderDirection Z j
      simp [ladderOffset, ladderDirection, if_pos hjZ, if_neg hjne]
  · -- no joint pair: v₁ = u₁ on S forces v₁ = 0 on Z ∖ {z₀} (a − 1 ≥ k points) yet 1 at i
    rintro ⟨v₀, hv₀, v₁, hv₁, hpair⟩
    have hvan : ∀ j ∈ Z.erase z₀, v₁ j = 0 := by
      intro j hj
      have hjS : j ∈ insert i (Z.erase z₀) := Finset.mem_insert_of_mem hj
      have hjZ : j ∈ Z := Finset.mem_of_mem_erase hj
      have := (hpair j hjS).2
      simpa [ladderDirection, if_pos hjZ] using this
    have hTcard : k ≤ (Z.erase z₀).card := by
      rw [Finset.card_erase_of_mem hz₀, hZ]; omega
    have hv₁0 : v₁ = 0 := rsCode_eq_zero_of_vanishes_on dom hk hv₁ hTcard hvan
    have hi1 := (hpair i (Finset.mem_insert_self _ _)).2
    rw [hv₁0] at hi1
    simp only [Pi.zero_apply, ladderDirection, if_neg hi] at hi1
    exact zero_ne_one hi1

open Classical in
/-- **The floor: at least `n − a` bad scalars on the ladder line.**  The map `i ↦ dom i` from
the `n − a` support points into the `mcaEvent` filter is injective. -/
theorem ladder_mcaEvent_filter_card_ge
    (dom : Fin n ↪ F) {k a : ℕ} (δ : ℝ≥0)
    (hk : 1 ≤ k) (hka : k + 1 ≤ a)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    {Z : Finset (Fin n)} {z₀ : Fin n} (hz₀ : z₀ ∈ Z) (hZ : Z.card = a) :
    n - a ≤ (Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (ladderOffset dom Z z₀) (ladderDirection Z) γ)).card := by
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)) \ Z,
      dom i ∈ Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          (ladderOffset dom Z z₀) (ladderDirection Z) γ) := by
    intro i hi
    obtain ⟨-, hiZ⟩ := Finset.mem_sdiff.mp hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ladder_mcaEvent dom δ hk hka haC hz₀ hZ hiZ⟩
  have hinj : Set.InjOn (fun i : Fin n => dom i)
      ((Finset.univ : Finset (Fin n)) \ Z : Finset (Fin n)) :=
    fun i _ j _ h => dom.injective h
  have hcard := Finset.card_le_card_of_injOn _ hmem hinj
  have hsd : ((Finset.univ : Finset (Fin n)) \ Z).card = n - a := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ,
      Fintype.card_fin, hZ]
  omega

/-! ### 3. Existence and the packaged forcing theorems -/

/-- The ladder configuration exists at every shape with `k + 1 ≤ a ≤ n`. -/
theorem exists_ladder_configuration {a : ℕ} (ha1 : 1 ≤ a) (han : a ≤ n) :
    ∃ (Z : Finset (Fin n)) (z₀ : Fin n), z₀ ∈ Z ∧ Z.card = a := by
  obtain ⟨Z, -, hZcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := a)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact han)
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp (by omega : 0 < Z.card)
  exact ⟨Z, z₀, hz₀, hZcard⟩

open Classical in
/-- **HEADLINE 2: the weld's `hlow` hypothesis forces `B_near ≥ n − a`.**  Any budget of the
exact shape consumed by `mcaDeltaStar_ge_of_farLineListBudgeted` (an `mcaEvent`-filter bound
over all directions with `≥ a` zero coordinates) is at least `n − a`. -/
theorem weld_hlow_forces_n_sub_a
    (dom : Fin n ↪ F) {k a Bnear : ℕ} (δ : ℝ≥0)
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (han : a ≤ n)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (hlow : ∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
        ≤ Bnear) :
    n - a ≤ Bnear := by
  obtain ⟨Z, z₀, hz₀, hZ⟩ := exists_ladder_configuration (by omega : 1 ≤ a) han
  have hzc : a ≤ (directionZeroSet (ladderDirection (F := F) Z)).card := by
    rw [directionZeroSet_ladder, hZ]
  exact le_trans (ladder_mcaEvent_filter_card_ge dom δ hk hka haC hz₀ hZ)
    (hlow (ladderOffset dom Z z₀) (ladderDirection Z) hzc)

open Classical in
/-- **HEADLINE 3: the floor lives on the SAFE class.**  Even a budget restricted to
zero-direction-safe, non-support-eligible lines — exactly the class W9's honesty section
left open in the `mcaEvent` vocabulary — is forced `≥ n − a`. -/
theorem safe_mcaEvent_budget_forces_n_sub_a
    (dom : Fin n ↪ F) {k a B : ℕ} (δ : ℝ≥0)
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (han : a ≤ n)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (hsafe : ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ B) :
    n - a ≤ B := by
  obtain ⟨Z, z₀, hz₀, hZ⟩ := exists_ladder_configuration (by omega : 1 ≤ a) han
  exact le_trans (ladder_mcaEvent_filter_card_ge dom δ hk hka haC hz₀ hZ)
    (hsafe (ladderOffset dom Z z₀) (ladderDirection Z)
      (ladder_not_supportEligible hZ)
      (ladder_zeroDirectionSafeLine dom hk hka hz₀ hZ))

open Classical in
/-- **HEADLINE 4: through the weld's budget arithmetic, every instantiation of
`mcaDeltaStar_ge_of_farLineListBudgeted` certifies at best `ε* ≥ (n − a)/q`.** -/
theorem weld_budget_forces_epsilon_ge_n_sub_a_div_q
    (dom : Fin n ↪ F) {k a : ℕ} {Bfar Bnear : ℕ} {εstar : ℝ≥0∞} (δ : ℝ≥0)
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (han : a ≤ n)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (hlow : ∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
        ≤ Bnear)
    (hBudget : ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    ((n - a : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar := by
  have hfloor : n - a ≤ Bnear := weld_hlow_forces_n_sub_a dom δ hk hka han haC hlow
  have hle : ((n - a : ℕ) : ℝ≥0∞) ≤ ((max Bfar Bnear : ℕ) : ℝ≥0∞) := by
    exact_mod_cast le_trans hfloor (le_max_right _ _)
  exact le_trans (ENNReal.div_le_div_right hle _) hBudget

/-! ### 4. Numeric gates and the pencil-scale refutation -/

open Classical in
/-- **HEADLINE 5: the pencil-probe scale is refuted.**  At the campaign's rate-quarter shape
(`n = 16`, `k = 4`, `a = 9`) the floor is `16 − 9 = 7 > 3`: the W9 probe's measured
`mcaEvent` count (`≤ 3` on pencil lines) is a feature of the pencil, not the class — no
`B_near ≤ 3` budget exists. -/
theorem pencilScale_budget_refuted_rateQuarter
    (dom : Fin 16 ↪ F) (δ : ℝ≥0) {B : ℕ}
    (haC : (1 - δ) * (16 : ℝ≥0) ≤ (9 : ℝ≥0))
    (hB : B ≤ 3)
    (hsafe : ∀ u₀ u₁ : Fin 16 → F, ¬ SupportEligibleLineDirection 9 u₁ →
      ZeroDirectionSafeLine dom 4 9 u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom 4 : Submodule F (Fin 16 → F)) : Set (Fin 16 → F)) δ u₀ u₁ γ)).card
        ≤ B) : False := by
  have h := safe_mcaEvent_budget_forces_n_sub_a (n := 16) dom δ
    (by norm_num) (by norm_num) (by norm_num) (by simpa using haC) hsafe
  omega

/-- The rate-half in-window shape (`n = 16`, `k = 8`, `a = 11`) satisfies the gates: the
floor there is `5`. -/
theorem rateHalf_inWindow_gate : 1 ≤ 8 ∧ 8 + 1 ≤ 11 ∧ 11 ≤ 16 ∧ 16 - 11 = 5 := by norm_num

/-- Honesty: at `a = n` (empty support) the floor is vacuous, as it must be. -/
theorem floor_vacuous_at_full_agreement : (16 : ℕ) - 16 = 0 := by norm_num

end ProximityGap.Frontier.W15LargeZeroMcaEventFloor

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.directionZeroSet_ladder
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.ladder_not_supportEligible
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.rsCode_eq_zero_of_vanishes_on
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.ladder_zeroDirectionSafeLine
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.ladder_mcaEvent
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.ladder_mcaEvent_filter_card_ge
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.exists_ladder_configuration
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.weld_hlow_forces_n_sub_a
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.safe_mcaEvent_budget_forces_n_sub_a
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.weld_budget_forces_epsilon_ge_n_sub_a_div_q
#print axioms ProximityGap.Frontier.W15LargeZeroMcaEventFloor.pencilScale_budget_refuted_rateQuarter
