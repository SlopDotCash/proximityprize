/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiberMixedProfileFit

/-!
# The mixed-profile top-fit is incompatible with the fiber budget (#466 lane L1)

`LineListAppearanceFiberMixedProfileFit.lean` contracted the whole mixed-profile route of the
line-list counting stack to pure arithmetic fits at the top cardinality `z = n`
(`LowMixedChooseProfileTopSumsFit`, `FieldPowMixedProfileTopFit`, …), consumed together with the
appearance-filtered fiber budget `UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits a B ·`.

This file **decides that arithmetic negatively at every prize shape**: the two named fits are
*jointly unsatisfiable* with the fiber budget whenever the bad-scalar budget `B` is below

* the **field size** `q = |F|` (the field-power route: the same-profile term of the top sum is
  `q·C(n, a−t)·q^{k∸a} ≥ q`, while any direction with exactly `a` zero coordinates caps
  `Mcoarse t₀ ≤ B` through the fiber sum), and — independently of the exact budget `Mexact` —
* the **high singleton binomial** `C(n−t₀, (a−1)−t₀)` (present as soon as the window fact
  `k < a` holds; at prize shape this is `≈ 2^{n·H(a/n)}`, astronomically above any weld budget
  `B ≤ ε*·q`).

Both kills are witnessed by the *step direction* `u₁ = (0,…,0,1,…,1)` with exactly `a` zeros,
which is large-zero (`¬SupportEligibleLineDirection`) and has fiber coefficient
`C(a,t₀)·⌊(n−a)/(a−t₀)⌋ ≥ 1` at any `t₀ < a` with `a − t₀ ≤ n − a`.  Every prize shape
(`ρ ∈ {1/2,1/4,1/8,1/16}`, in-window `a ∈ (ρn, √ρ·n)`, `B ≤ ε*·q` or `B ≈ ρn`) admits such a
`t₀ < k` (take `t₀ = max(0, 2a−n)`); the probe
`scripts/probes/probe_466_mixed_topfit_endpoint.py` verifies non-vacuity and quantifies the
violation (0/416 satisfiable rows at `μ = 4..12`; ≈`10^9` bits of violation at `μ = 30`).

Consequently the `z = n` top-endpoint contraction (`mixedChooseProfileCardSum_le_topCard`) can
never feed the weld `mcaDeltaStar_ge_of_farLineListBudgeted`: the mixed-profile route is closed
as a production path, and the low-profile split is mandatory.
-/

set_option autoImplicit false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The step direction: exactly `a` zero coordinates -/

omit [Fintype F] [NeZero n] in
/-- The zero set of the step direction `i ↦ if i < a then 0 else 1` has exactly `a` elements. -/
theorem directionZeroSet_step_card (a : ℕ) (han : a ≤ n) :
    (directionZeroSet (fun i : Fin n => if (i : ℕ) < a then (0 : F) else 1)).card = a := by
  classical
  have hset :
      directionZeroSet (fun i : Fin n => if (i : ℕ) < a then (0 : F) else 1)
        = (Finset.range a).attachFin
            (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) han) := by
    ext i
    simp only [directionZeroSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_attachFin, Finset.mem_range]
    by_cases h : (i : ℕ) < a
    · simp [h]
    · simp [h, one_ne_zero]
  rw [hset, Finset.card_attachFin, Finset.card_range]

omit [Fintype F] [NeZero n] in
/-- The support set of the step direction has exactly `n − a` elements. -/
theorem directionSupportSet_step_card (a : ℕ) (han : a ≤ n) :
    (directionSupportSet (fun i : Fin n => if (i : ℕ) < a then (0 : F) else 1)).card
      = n - a := by
  classical
  have hcompl :
      directionSupportSet (fun i : Fin n => if (i : ℕ) < a then (0 : F) else 1)
        = (directionZeroSet (fun i : Fin n => if (i : ℕ) < a then (0 : F) else 1))ᶜ := by
    ext i
    simp [directionSupportSet, directionZeroSet]
  rw [hcompl, Finset.card_compl, directionZeroSet_step_card (F := F) (n := n) a han,
    Fintype.card_fin]

/-! ## The fiber budget caps every low coarse budget at `B` -/

omit [NeZero n] in
/-- Single-term extraction from the fiber budget at the step direction: any coarse budget
function passing `UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits a B` is capped by `B`
at every profile `t₀ < a` whose step-direction coefficient is nonzero (`a − t₀ ≤ n − a`). -/
theorem mcoarse_le_budget_of_uniformFiberFits
    (a B t₀ : ℕ) (Mcoarse : ℕ → ℕ)
    (ht₀a : t₀ < a) (han : a ≤ n) (hcoeff : a - t₀ ≤ n - a)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B Mcoarse) :
    Mcoarse t₀ ≤ B := by
  classical
  set u₁ : Fin n → F := fun i : Fin n => if (i : ℕ) < a then (0 : F) else 1 with hu₁
  have hzcard : (directionZeroSet u₁).card = a :=
    directionZeroSet_step_card (F := F) (n := n) a han
  have hscard : (directionSupportSet u₁).card = n - a :=
    directionSupportSet_step_card (F := F) (n := n) a han
  have hnotEligible : ¬ SupportEligibleLineDirection a u₁ := by
    simp [SupportEligibleLineDirection, hzcard]
  have hfits :
      ∑ t ∈ Finset.range a,
        ((directionZeroSet u₁).card.choose t * Mcoarse t) *
          ((directionSupportSet u₁).card / (a - t)) ≤ B :=
    hFiber u₁ hnotEligible
  have hterm :
      ((directionZeroSet u₁).card.choose t₀ * Mcoarse t₀) *
          ((directionSupportSet u₁).card / (a - t₀)) ≤ B :=
    le_trans
      (Finset.single_le_sum
        (f := fun t =>
          ((directionZeroSet u₁).card.choose t * Mcoarse t) *
            ((directionSupportSet u₁).card / (a - t)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht₀a))
      hfits
  rw [hzcard, hscard] at hterm
  have hdiv : 1 ≤ (n - a) / (a - t₀) := by
    have hpos : 0 < a - t₀ := Nat.sub_pos_of_lt ht₀a
    exact (Nat.le_div_iff_mul_le hpos).mpr (by simpa using hcoeff)
  have hchoose : 1 ≤ a.choose t₀ := Nat.choose_pos (le_of_lt ht₀a)
  calc Mcoarse t₀ = (1 * Mcoarse t₀) * 1 := by ring
    _ ≤ (a.choose t₀ * Mcoarse t₀) * ((n - a) / (a - t₀)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hchoose (le_refl (Mcoarse t₀))) hdiv
    _ ≤ B := hterm

/-! ## Kill 1 — the field-power top fit dies below the field size -/

omit [NeZero n] in
/-- **The field-power mixed top fit is incompatible with the fiber budget below the field
size.**  At any profile `t₀ < min(a,k)` with `a − t₀ ≤ n − a` (available at every prize shape),
the top fit forces `Mcoarse t₀ ≥ q` while the fiber budget at the step direction forces
`Mcoarse t₀ ≤ B`; with `B < q` (the weld gives `B ≤ ε*·q`) both cannot hold. -/
theorem not_fieldPowMixedProfileTopFit_and_uniformFiberFits
    (a k B t₀ : ℕ) (Mcoarse : ℕ → ℕ)
    (ht₀a : t₀ < a) (ht₀k : t₀ < k) (han : a ≤ n) (hcoeff : a - t₀ ≤ n - a)
    (hB : B < Fintype.card F)
    (hTop : FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B Mcoarse) :
    False := by
  have hlow : Fintype.card F ≤ Mcoarse t₀ := by
    have h := fieldPowMixedProfileTopFit_exact_le (F := F) (n := n) hTop ht₀a ht₀k
    have hchoose : 0 < n.choose (a - t₀) :=
      Nat.choose_pos (le_trans (Nat.sub_le a t₀) han)
    have hpow : 0 < Fintype.card F ^ (k - a) := pow_pos Fintype.card_pos _
    have hone : 1 ≤ n.choose (a - t₀) * Fintype.card F ^ (k - a) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hchoose hpow).ne'
    exact le_trans (le_mul_of_one_le_right (Nat.zero_le _) hone) h
  have hup : Mcoarse t₀ ≤ B :=
    mcoarse_le_budget_of_uniformFiberFits (F := F) (n := n)
      a B t₀ Mcoarse ht₀a han hcoeff hFiber
  exact absurd (le_trans hlow hup) (not_le_of_gt hB)

omit [NeZero n] in
/-- The full field-power top fit dies the same way (it implies the low one). -/
theorem not_fieldPowFullMixedProfileTopFit_and_uniformFiberFits
    (a k B t₀ : ℕ) (Mcoarse : ℕ → ℕ)
    (ht₀a : t₀ < a) (ht₀k : t₀ < k) (han : a ≤ n) (hcoeff : a - t₀ ≤ n - a)
    (hB : B < Fintype.card F)
    (hTop : FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B Mcoarse) :
    False :=
  not_fieldPowMixedProfileTopFit_and_uniformFiberFits (F := F) (n := n)
    a k B t₀ Mcoarse ht₀a ht₀k han hcoeff hB
    (fun t ht _htk => hTop t ht) hFiber

/-! ## Kill 2 — for EVERY exact budget: the high singleton binomial dies -/

omit [NeZero n] in
/-- **Mexact-independent incompatibility.**  If a high profile `r ∈ [k, a)` exists (in-window
`a > k` gives `r = a−1`), the top sum charges the singleton binomial `C(n−t₀, r−t₀)` regardless
of the exact budget, so any budget `B < C(n−t₀, r−t₀)` is jointly unsatisfiable. -/
theorem not_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits_of_budget_lt_choose
    (a k B t₀ r : ℕ) (Mexact Mcoarse : ℕ → ℕ)
    (ht₀a : t₀ < a) (ht₀k : t₀ < k) (hra : r < a) (hkr : k ≤ r)
    (han : a ≤ n) (hcoeff : a - t₀ ≤ n - a)
    (hB : B < (n - t₀).choose (r - t₀))
    (hTop : LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B Mcoarse) :
    False := by
  have hlow : (n - t₀).choose (r - t₀) ≤ Mcoarse t₀ :=
    lowMixedChooseProfileTopSumsFit_high_choose_le (n := n)
      (r := r) hTop ht₀a ht₀k hra hkr
  have hup : Mcoarse t₀ ≤ B :=
    mcoarse_le_budget_of_uniformFiberFits (F := F) (n := n)
      a B t₀ Mcoarse ht₀a han hcoeff hFiber
  exact absurd (le_trans hlow hup) (not_le_of_gt hB)

omit [NeZero n] in
/-- **Headline: the top-endpoint mixed route is unsatisfiable for every exact budget.**
In-window (`k < a ≤ n`), at any low profile `t₀ < k` with nonzero step coefficient
(`a − t₀ ≤ n − a`), no pair `(Mexact, Mcoarse)` can pass both the low top fit and the fiber
budget once `B < C(n−t₀, (a−1)−t₀)` — which at prize shape is `≈ 2^{n·H(a/n)}` against
`B ≤ ε*·q`.  The `z = n` contraction can never feed the weld. -/
theorem not_exists_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits
    (a k B t₀ : ℕ)
    (ht₀k : t₀ < k) (hka : k < a) (han : a ≤ n) (hcoeff : a - t₀ ≤ n - a)
    (hB : B < (n - t₀).choose (a - 1 - t₀)) :
    ¬ ∃ Mexact Mcoarse : ℕ → ℕ,
        LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse ∧
        UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
          (F := F) (n := n) a B Mcoarse := by
  rintro ⟨Mexact, Mcoarse, hTop, hFiber⟩
  have ht₀a : t₀ < a := lt_trans ht₀k hka
  have hra : a - 1 < a := Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le k) hka) one_pos
  have hkr : k ≤ a - 1 := Nat.le_sub_one_of_lt hka
  exact
    not_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits_of_budget_lt_choose
      (F := F) (n := n) a k B t₀ (a - 1) Mexact Mcoarse
      ht₀a ht₀k hra hkr han hcoeff hB hTop hFiber

omit [NeZero n] in
/-- The full mixed top fit implies the low one, so the headline kills it too. -/
theorem not_exists_fullMixedChooseProfileTopSumsFit_and_uniformFiberFits
    (a k B t₀ : ℕ)
    (ht₀k : t₀ < k) (hka : k < a) (han : a ≤ n) (hcoeff : a - t₀ ≤ n - a)
    (hB : B < (n - t₀).choose (a - 1 - t₀)) :
    ¬ ∃ Mexact Mcoarse : ℕ → ℕ,
        FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse ∧
        UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
          (F := F) (n := n) a B Mcoarse := by
  rintro ⟨Mexact, Mcoarse, hTop, hFiber⟩
  exact
    not_exists_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits
      (F := F) (n := n) a k B t₀ ht₀k hka han hcoeff hB
      ⟨Mexact, Mcoarse, fun t ht _htk => hTop t ht, hFiber⟩

/-! ## Concrete prize-shaped instance (`ρ = 1/4` scale model: `n = 16`, `k = 4`, `a = 7`) -/

/-- Scale model of the prize shape (`ρ = 1/4`, `n = 16`, in-window `a = 7`, weld-shaped budget
`B ≤ ρ·n = 4`): the mixed top-endpoint route is unsatisfiable for every exact budget.
The binding binomial is `C(16, 6) = 8008 > 4`. -/
theorem not_exists_mixedTop_n16_prizeShape
    (hn : n = 16) (B : ℕ) (hB : B ≤ 4) :
    ¬ ∃ Mexact Mcoarse : ℕ → ℕ,
        LowMixedChooseProfileTopSumsFit (n := n) 7 4 Mexact Mcoarse ∧
        UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
          (F := F) (n := n) 7 B Mcoarse := by
  subst hn
  refine not_exists_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits
    (F := F) (n := 16) 7 4 B 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  -- `C(16 − 0, 7 − 1 − 0) = C(16, 6) = 8008`
  have h : (16 - 0 : ℕ).choose (7 - 1 - 0) = 8008 := by decide
  rw [h]
  omega

section SourceAudit

#print axioms directionZeroSet_step_card
#print axioms directionSupportSet_step_card
#print axioms mcoarse_le_budget_of_uniformFiberFits
#print axioms not_fieldPowMixedProfileTopFit_and_uniformFiberFits
#print axioms not_fieldPowFullMixedProfileTopFit_and_uniformFiberFits
#print axioms not_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits_of_budget_lt_choose
#print axioms not_exists_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits
#print axioms not_exists_fullMixedChooseProfileTopSumsFit_and_uniformFiberFits
#print axioms not_exists_mixedTop_n16_prizeShape

end SourceAudit

end ProximityGap.Ownership
