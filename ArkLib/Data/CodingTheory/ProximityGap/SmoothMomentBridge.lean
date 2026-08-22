/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionTower
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionRigidity
import ArkLib.Data.CodingTheory.ProximityGap.CosetVanishingDichotomy

/-!
# Power-of-2 bridge: the smooth-domain `N_t(0)` fiber vanishes off the power-of-2 lattice (#232)

Connects the fleet's GENERIC moment-collision framework (`MomentCollisionTower.statCount`/`momentVec`,
`MomentCollisionRigidity`) — which never instantiates the smooth domain — to the POWER-OF-2 structure
(`CosetVanishingDichotomy`). For `μ_n` (`n`-th roots of unity), the first cell beyond the
anti-concentrated `a ≤ t` regime is `a = t+1`; its zero-fiber count
`statCount μ_n (t+1) (momentVec t) 0 = N_t(0)` is **`0` whenever `t+1 ∤ n`** — because a
`(t+1)`-subset with all power sums vanishing has all `e_1,…,e_t = 0` (Newton, via
`esymm_eq_of_psum_eq` against `∅`), so it would be a coset of `μ_{t+1}`, which cannot fit in `μ_n`
unless `t+1 ∣ n`. Over `μ_{2^k}` this means the `N_t(0)` fiber is empty unless `t+1` is a power of 2.
Axiom-clean.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.SmoothMomentBridge

open ArkLib.ProximityGap.MomentCollisionTower
open ArkLib.ProximityGap.MomentCollisionRigidity
open ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-- `momentVec t S = 0` says every power sum `p_i(S)` vanishes for `1 ≤ i ≤ t`. Comparing to the
empty set (`p_i(∅)=0`) via Newton (`esymm_eq_of_psum_eq`) forces `e_k(S)=0` for `1 ≤ k ≤ t`. -/
theorem esymm_zero_of_momentVec_zero {t : ℕ}
    (hchar : ∀ i, 0 < i → i ≤ t → (i : F) ≠ 0) {S : Finset F}
    (hmv : momentVec t S = 0) :
    ∀ k, 1 ≤ k → k ≤ t → S.val.esymm k = 0 := by
  intro k hk1 hkt
  have hpsum : ∀ i, 1 ≤ i → i ≤ t → psumMs S.val i = psumMs (∅ : Finset F).val i := by
    intro i hi1 hit
    rw [psumMs_val, psumMs_val]
    simp only [Finset.sum_empty]
    have : (⟨i - 1, by omega⟩ : Fin t) = (⟨i - 1, by omega⟩ : Fin t) := rfl
    have hmv' := congrFun hmv (⟨i - 1, by omega⟩ : Fin t)
    simp only [momentVec, Pi.zero_apply] at hmv'
    rwa [Nat.sub_add_cancel hi1] at hmv'
  have hE := esymm_eq_of_psum_eq S (∅ : Finset F) hchar hpsum k hkt
  rw [hE, Finset.empty_val]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold Multiset.esymm
  rw [Multiset.powersetCard_zero_right, Multiset.map_zero, Multiset.sum_zero]

/-- **Power-of-2 smooth-domain bridge: the first open cell vanishes off the power-of-2 lattice.**
For the smooth domain `μ_n` (`n`-th roots of unity, primitive `n`-th root `ζ`, `char` large enough),
the count of `(t+1)`-subsets with the full depth-`t` power-sum statistic equal to `0` is **`0`**
whenever `t+1 ∤ n`. Over `μ_{2^k}` this means the `N_t(0)` fiber at the first cell beyond the
anti-concentrated `a ≤ t` regime is EMPTY unless `t+1` is a power of `2`. Connects the fleet's
generic `statCount`/`momentVec` framework to the power-of-2 dichotomy (`CosetVanishingDichotomy`). -/
theorem statCount_momentVec_zero_eq_zero_of_not_dvd {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hchar : ∀ i, 0 < i → i ≤ t → (i : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hnd : ¬ (t + 1) ∣ n) :
    statCount (nthRootsFinset n (1 : F)) (t + 1) (momentVec t) 0 = 0 := by
  rw [statCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS hmv
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSsub, hScard⟩ := hS
  have hesymm := esymm_zero_of_momentVec_zero hchar hmv
  have hSroots : ∀ x ∈ S, x ^ n = 1 := by
    intro x hx
    exact (mem_nthRootsFinset hn _).mp (hSsub hx)
  exact not_exists_esymm_zero_of_not_dvd hn (by omega) hnd S hSroots
    hScard (fun j hj1 hjt => hesymm j hj1 (by omega))

end ArkLib.ProximityGap.SmoothMomentBridge

#print axioms ArkLib.ProximityGap.SmoothMomentBridge.statCount_momentVec_zero_eq_zero_of_not_dvd
