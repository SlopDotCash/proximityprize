/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreReductionComplete

/-!
# Core Reduction — the NECESSITY direction (Lane 2 capstone tightening, #444)

**Spec (Lane 2, citable capstone).** The master reduction `_CoreReductionComplete` proves the
*sufficient* direction: a BCHKS subset-sum budget at the binding fold forces the binding depth down
(`mStar_le_of_BCHKS`), and the window-interior `1 − √ρ < δ* < 1 − ρ` follows. This file adds the
*missing converse rung*: that the budget control of `m*` is **two-sided** — failure of the BCHKS
budget at a fold pushes `m*` strictly past that fold — and packages the exact `m* ≤ M ↔ BCHKS`
biconditional under cascade monotonicity. This makes the prose claim "prize ⟺ Sh(n)=O(1)" backed by
a kernel-checked equivalence at the `m*` level, not only the sufficient half.

The arithmetic content is pure `Nat.find` order theory through the proven P2/E3 identification
`hident : ∀ m, D n m = Σ (smap n) (rmap n m)` and the proven E4 cascade monotonicity.
No new analytic input, no CORE/cancellation/completion/moment/capacity claim — only the logical
packaging of necessity alongside the already-landed sufficiency.

## Main results
* `mStar_gt_of_fold_over_budget`: a fold that is strictly over budget binds nowhere below it (under
  monotonicity), so `M < m*`.
* `mStar_gt_of_BCHKS_fails`: the BCHKS-named form of the above (`¬ BCHKSBudget … ⟹ M < m*`).
* `mStar_le_iff_BCHKS`: the exact two-sided characterization `m* ≤ M ↔ BCHKSBudget …` at any fold,
  under monotonicity.
* `not_clears_johnson_of_BCHKS_fails`: the necessity-facing corollary — if the BCHKS budget fails at
  the fold matching `k − 1`, then `m* ≥ k`, hence the Johnson crossing is NOT cleared
  (`¬ (m* < k)`), i.e. the window-interior conclusion fails on the Johnson side.
-/

namespace ArkLib.ProximityGap.CoreReductionComplete

open Real

/-- **Necessity (raw `D` form).** If the cascade `D n ·` is non-increasing and the fold `M` is
strictly over budget, then *no* depth `≤ M` binds, so the least binder satisfies `M < m*`.
This is the exact contrapositive of `mStar_le_of_binds` propagated downward by monotonicity. -/
theorem mStar_gt_of_fold_over_budget
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a) (M : ℕ)
    (hover : budget n < D n M) :
    M < mStar D budget n hex := by
  -- `m* > M` ⟺ every depth `≤ M` is over budget. Monotone decay pushes the single over-budget
  -- fold `M` down to all `j ≤ M`.
  unfold mStar
  rw [Nat.lt_find_iff]
  intro j hj
  -- `j ≤ M` ⟹ `budget < D n M ≤ D n j`, so `j` does not bind.
  exact Nat.not_le.mpr (lt_of_lt_of_le hover (hmono hj))

/-- **Necessity (BCHKS-named form).** Through the P2/E3 identification, failure of the BCHKS budget
at the fold `rmap n M` forces the binding depth strictly past `M`. The exact converse of
`mStar_le_of_BCHKS`. -/
theorem mStar_gt_of_BCHKS_fails
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ)
    (hfail : ¬ BCHKSBudget Sigma (smap n) (rmap n M) (budget n)) :
    M < mStar D budget n hex := by
  -- `¬ (Σ ≤ budget)` unfolds to `budget < Σ`, and `Σ = D n M` by the identification.
  have hover : budget n < D n M := by
    rw [hident M]
    exact Nat.not_le.mp hfail
  exact mStar_gt_of_fold_over_budget D budget n hex hmono M hover

/-- **Two-sided characterization.** Under cascade monotonicity and the P2/E3 identification, the
binding depth is at most a fold **iff** the BCHKS budget holds at that fold:

  `m*(n) ≤ M  ↔  |Σ_{rmap n M}(μ_{smap n})| ≤ budget n`.

The `←` direction is the already-landed `mStar_le_of_BCHKS` (sufficiency, monotonicity-free); the
`→` direction is the new necessity (`mStar_gt_of_BCHKS_fails`, contrapositive). Together they make
the budget the *exact* gate on `m*`. -/
theorem mStar_le_iff_BCHKS
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    mStar D budget n hex ≤ M ↔ BCHKSBudget Sigma (smap n) (rmap n M) (budget n) := by
  constructor
  · -- forward: contrapose into the necessity lemma.
    intro hle
    by_contra hfail
    exact absurd hle (Nat.not_le.mpr (mStar_gt_of_BCHKS_fails D budget Sigma smap rmap n hex
      hmono hident M hfail))
  · -- backward: the already-landed sufficiency reduction.
    intro hBCHKS
    exact mStar_le_of_BCHKS D budget Sigma smap rmap n hex hident M hBCHKS

/-- **Necessity corollary at the Johnson fold.** If the BCHKS budget *fails* at the fold matching
`kNat − 1` (the binding fold the master reduction uses), then `kNat ≤ m*`, i.e. the Johnson-side
strict inequality `m* < kNat` does NOT hold. Contrapositive of the master reduction's Johnson step:
clearing Johnson *requires* the budget. No analytic claim — pure `m*`-gate bookkeeping. -/
theorem not_clears_johnson_of_BCHKS_fails
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (kNat : ℕ) (hk_pos : 1 ≤ kNat)
    (hfail : ¬ BCHKSBudget Sigma (smap n) (rmap n (kNat - 1)) (budget n)) :
    ¬ (mStar D budget n hex < kNat) := by
  -- failure at fold `kNat - 1` gives `kNat - 1 < m*`, i.e. `kNat ≤ m*` (since `kNat ≥ 1`).
  have hgt : kNat - 1 < mStar D budget n hex :=
    mStar_gt_of_BCHKS_fails D budget Sigma smap rmap n hex hmono hident (kNat - 1) hfail
  -- `kNat - 1 < m*` with `kNat ≥ 1` ⟹ `kNat ≤ m*`.
  omega

/-- **Johnson fold equivalence.** At a positive Johnson fold `kNat`, clearing the strict
Johnson-side gate `m* < kNat` is equivalent to satisfying the BCHKS budget at the preceding fold
`kNat - 1`.

This is the consumer-facing form of `mStar_le_iff_BCHKS`: the Nat inequality `m* < kNat` is the same
as `m* ≤ kNat - 1` when `kNat > 0`.  It is pure reduction bookkeeping and proves no new
anti-concentration, CORE cancellation, or capacity claim. -/
theorem clears_johnson_iff_BCHKS_at_prev_fold
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (kNat : ℕ) (hk_pos : 1 ≤ kNat) :
    mStar D budget n hex < kNat ↔
      BCHKSBudget Sigma (smap n) (rmap n (kNat - 1)) (budget n) := by
  rw [← mStar_le_iff_BCHKS D budget Sigma smap rmap n hex hmono hident (kNat - 1)]
  omega

/-! ## Non-vacuity: the necessity gate fires on the concrete model. -/

/-- **Non-vacuity of necessity.** On the concrete cascade `modelD` (`n = 16`), the fold `2` is over
budget (`modelD 16 2 = 97 > 16`), so the necessity lemma forces `2 < m*`. This is the over-budget
edge the master reduction's `m* ≥ 3` lower bound also uses — here driving the converse direction —
confirming the necessity statement is not vacuous. -/
example : (2 : ℕ) < mStar modelD (fun _ => 16) 16 ⟨3, by decide⟩ := by
  refine mStar_gt_of_fold_over_budget modelD (fun _ => 16) 16 ⟨3, by decide⟩ ?_ 2 (by decide)
  -- `modelD 16 ·` is non-increasing: `97` for depth `≤ 2`, then `0`.
  intro a b hab
  unfold modelD
  by_cases hb : 16 = 16 ∧ b ≤ 2
  · -- if the larger index `b` is in the high plateau, so is the smaller `a`.
    have ha : 16 = 16 ∧ a ≤ 2 := ⟨rfl, le_trans hab hb.2⟩
    rw [if_pos hb, if_pos ha]
  · -- otherwise the larger index gives `0`, which is `≤` anything.
    rw [if_neg hb]
    exact Nat.zero_le _

end ArkLib.ProximityGap.CoreReductionComplete

/-! ## Axiom audit (expected: no axioms or only theorem dependencies already allowed). -/
#print axioms ArkLib.ProximityGap.CoreReductionComplete.clears_johnson_iff_BCHKS_at_prev_fold
