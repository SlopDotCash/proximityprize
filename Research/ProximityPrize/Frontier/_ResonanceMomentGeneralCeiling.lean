/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# The uniform (all-`r`) trivial ceiling on the resonance moment (#407 / #444)

Extends `GaussPhaseResonance` and the per-rung files `_ResonanceMomentBaseCase` (`r=1`),
`_ResonanceMomentRTwo{,Bounds}` (`r=2`), `_ResonanceMomentRThree` (`r=3`), each of which proved a
TRIVIAL upper ceiling for ONE depth by a per-`r` convolution collapse + triangle inequality. This
file proves the SINGLE uniform statement subsuming all of them, directly from the `phaseSum`
definition (no per-`r` collapse), for every `r ≥ 1`:

* `phaseSum_norm_le_general` — `‖phaseSum u r c‖ ≤ (m-1)^(r-1)` for unit phases and any `r ≥ 1`.
* `resonanceMoment_le_general` — `T r = resonanceMoment u r ≤ m · (m-1)^(2(r-1))`.

## The card bound

The phase-sum filter `{X : Fin r → ZMod m | ∀ i, X i ≠ 0, ∑ X = c}` has at most `(m-1)^(r-1)`
elements: the map `X ↦ Fin.init X` (drop the last coordinate) is INJECTIVE on the filter — the last
coordinate `X (last) = c − ∑_{i<r-1} X i` is recovered from the sum constraint — and lands in the
product set `(ZMod m ∖ {0})^(r-1)`, which has `(m-1)^(r-1)` elements. Triangle inequality on the
unit terms then gives the L∞ ceiling; squaring and summing over the `m` frequencies gives the L²
ceiling.

## Honest scope

These are the TRIVIAL (triangle/L¹) ceilings, uniform in `r`. Probe truth: `T r = Θ(m^r)`, sitting
FAR below `m·(m-1)^(2(r-1))` for `r ≥ 2` (the off-diagonal `(r-1)`-fold convolution has strong
cancellation the triangle bound cannot see). For `r=1` the bound is TIGHT (`(m-1)^0 = 1` per term,
`T 1 = m-1`). The gap for `r ≥ 2` is exactly the open `ResonanceConjecture` content / the prize
L²→L∞ sup-norm wall. NO CORE / cancellation / completion / anti-concentration / capacity claim.
CORE `M(μ_n) ≤ C √(n log m)` UNCHANGED / OPEN. Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The phase-sum filter at depth `r ≥ 1` and frequency `c` has at most `(m-1)^(r-1)` elements:
the map `X ↦ Fin.init X` is injective (last coordinate recovered from `∑ X = c`) into the nonzero
product set. -/
theorem card_phaseSum_filter_le (r : ℕ) (hr : 1 ≤ r) (c : ZMod m) :
    ((Finset.univ.filter (fun X : Fin r → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c))).card ≤ (m - 1) ^ (r - 1) := by
  classical
  -- r = k + 1 since r ≥ 1, so Fin.init : (Fin (k+1) → _) → (Fin k → _) typechecks
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- target: functions Fin k → ZMod m with all values ≠ 0
  set S : Finset (ZMod m) := Finset.univ.filter (fun a : ZMod m => a ≠ 0) with hS
  have hScard : S.card = m - 1 := by
    rw [hS, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  -- the product target finset
  set T : Finset (Fin k → ZMod m) := Fintype.piFinset (fun _ => S) with hT
  have hTcard : T.card = (m - 1) ^ k := by
    rw [hT, Fintype.card_piFinset_const, hScard]
  rw [← hTcard]
  -- inject via Fin.init (drop the last coordinate)
  refine Finset.card_le_card_of_injOn (fun X => Fin.init X) ?_ ?_
  · -- maps into T
    intro X hX
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hX
    obtain ⟨hne, _⟩ := hX
    simp only [hT, Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hne _⟩
  · -- InjOn: Fin.init X = Fin.init Y on the filter ⇒ X = Y (last coord forced by the sum)
    intro X hX Y hY heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hX hY
    obtain ⟨_, hsumX⟩ := hX
    obtain ⟨_, hsumY⟩ := hY
    -- X = Fin.snoc (Fin.init X) (X last); same for Y. inits equal, lasts equal.
    have hlast : X (Fin.last k) = Y (Fin.last k) := by
      have hsX : (∑ i, X i) = (∑ i : Fin k, Fin.init X i) + X (Fin.last k) :=
        Fin.sum_univ_castSucc X
      have hsY : (∑ i, Y i) = (∑ i : Fin k, Fin.init Y i) + Y (Fin.last k) :=
        Fin.sum_univ_castSucc Y
      have heq' : Fin.init X = Fin.init Y := heq
      rw [hsX] at hsumX
      rw [hsY] at hsumY
      rw [heq'] at hsumX
      -- (∑ init Y) + X last = c = (∑ init Y) + Y last
      have : (∑ i : Fin k, Fin.init Y i) + X (Fin.last k)
           = (∑ i : Fin k, Fin.init Y i) + Y (Fin.last k) := by
        rw [hsumX, hsumY]
      exact add_left_cancel this
    -- reconstruct X = Y from equal inits and equal lasts
    have heq' : Fin.init X = Fin.init Y := heq
    funext i
    induction i using Fin.lastCases with
    | last => exact hlast
    | cast j =>
      have := congrFun heq' j
      simpa [Fin.init] using this

/-- **Uniform per-frequency L∞ ceiling: `‖phaseSum u r c‖ ≤ (m-1)^(r-1)`** for unit phases and any
`r ≥ 1`. Triangle inequality on the `≤ (m-1)^(r-1)` unit terms (the filter card bound). -/
theorem phaseSum_norm_le_general (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (r : ℕ) (hr : 1 ≤ r) (c : ZMod m) :
    ‖phaseSum u r c‖ ≤ ((m : ℝ) - 1) ^ (r - 1) := by
  classical
  unfold phaseSum
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
      (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)), ‖∏ i, u (X i)‖ = 1 := by
    intro X _
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro i _
    exact hu _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard := card_phaseSum_filter_le r hr c
  have hm : 1 ≤ m := NeZero.one_le
  calc ((Finset.univ.filter (fun X : Fin r → ZMod m =>
          (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)).card : ℝ)
      ≤ (((m - 1) ^ (r - 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((m : ℝ) - 1) ^ (r - 1) := by push_cast [Nat.cast_sub hm]; ring

/-- **Uniform aggregate L² ceiling: `T r = resonanceMoment u r ≤ m · (m-1)^(2(r-1))`** for unit
phases and any `r ≥ 1`. Squaring the per-frequency ceiling and summing over the `m` frequencies. -/
theorem resonanceMoment_le_general (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (r : ℕ) (hr : 1 ≤ r) :
    resonanceMoment u r ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) := by
  classical
  unfold resonanceMoment
  have hbd : ∀ c : ZMod m, ‖phaseSum u r c‖ ^ 2 ≤ (((m : ℝ) - 1) ^ (r - 1)) ^ 2 := by
    intro c
    have h1 := phaseSum_norm_le_general u hu r hr c
    have h0 : (0 : ℝ) ≤ ‖phaseSum u r c‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  calc ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2
      ≤ ∑ _c : ZMod m, (((m : ℝ) - 1) ^ (r - 1)) ^ 2 := Finset.sum_le_sum (fun c _ => hbd c)
    _ = (Finset.univ.card : ℝ) * (((m : ℝ) - 1) ^ (r - 1)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) := by
        rw [Finset.card_univ, ZMod.card, ← pow_mul, Nat.mul_comm]

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.card_phaseSum_filter_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_norm_le_general
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_le_general
