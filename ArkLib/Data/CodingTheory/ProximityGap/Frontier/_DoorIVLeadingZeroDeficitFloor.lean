/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitBudgetBoundedExceptions

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) Lane-3: the LEADING-ZERO-DEFICIT block confines the dilation saving to a thin tail (#444)

The measured worst-frequency 2-dilation descent (see `probe_dooriv_realized_deficit_descent.py` /
`probe_dooriv_leading_zero_block.py` in the worker log) has a sharp structure: at the adversarial `b*`
the per-level coherence deficit `δ_k = 0` (coset halves *exactly same-ray*, `ρ = 1`) on a LEADING BLOCK
of the top `T` levels, with `T` numerically `≈ a − O(1)` (e.g. `T = a−1` at `a = 3,4,5`).  All the
deficit — hence all the `exp(−S)` saving the dilation budget can extract — is confined to the thin
**tail** of the bottom `a − T` levels.

This module records the consequence as an axiom-clean **support-confinement** floor, specialising the
bounded-exception lemma (`_DoorIVDeficitBudgetBoundedExceptions`) at `ε = 0` (the good levels carry
*zero* deficit, not merely sub-`ε`).  The exceptional set is exactly the tail support
`{k | δ_k ≠ 0} ⊆ {T, …, a−1}` of size `≤ a − T`.  The density floor at `ε = 0` reads

> `a − T ≤ ((log 2)/2)·a`,  i.e.  `T ≥ (1 − (log 2)/2)·a ≈ 0.6534·a`,

so whenever the leading zero block covers at least a `≈ 0.6534` fraction of the levels — which the
measured `T ≈ a − O(1)` does, overwhelmingly — the dilation budget bound stays at/above the
`√(2^a)·M 0` Plancherel/prize scale.  A descent whose saving is confined to an `O(1)` (or any
sub-`((log 2)/2)·a`) tail cannot reach the `√n` prize scale.

## What this module proves (and what it does NOT)

* `tail_card_le_of_leading_zero` : if `δ_k = 0` for all `k < T` (`T ≤ a`), the support of `δ` inside
  `range a` has card `≤ a − T`.
* `budget_ge_sqrt_scale_of_leading_zero_block` : if `δ_k = 0` on the top `T` levels, `δ_k ≤ 1`
  everywhere on `range a`, the leading block is large enough (`(a : ℝ) − T ≤ ((log 2)/2)·a`), and
  `M 0 ≥ 0`, then `(√2)^a·M 0 ≤ 2^a·exp(−S)·M 0` for the realized total `S = ∑_{k<a} δ_k`.

It does **NOT** lower-bound the true `M(μ_n)` (the open CORE) and asserts nothing about achievability.
Lane-3 constraint lemma; CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVLeadingZeroDeficitFloor

open Real Finset
open ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetBoundedExceptions

/-- The exceptional (nonzero-deficit) set inside the first `a` levels.  (`noncomputable`: the
membership predicate `δ k ≠ 0` over `ℝ` uses classical decidability.) -/
noncomputable def tailSupport (a : ℕ) (δ : ℕ → ℝ) : Finset ℕ :=
  (Finset.range a).filter (fun k => δ k ≠ 0)

/-- **Leading-zero block ⟹ thin tail support.**  If `δ_k = 0` for every `k < T` (with `T ≤ a`), then
the nonzero-deficit set inside `range a` is contained in `{T, …, a−1}`, so its cardinality is `≤ a − T`.
-/
theorem tail_card_le_of_leading_zero {a T : ℕ} (δ : ℕ → ℝ)
    (hzero : ∀ k, k < T → δ k = 0) :
    (tailSupport a δ).card ≤ a - T := by
  -- tailSupport ⊆ range a \ range T = Ico T a, which has card a - T.
  have hsub : tailSupport a δ ⊆ Finset.Ico T a := by
    intro k hk
    simp only [tailSupport, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hka, hknz⟩ := hk
    rw [Finset.mem_Ico]
    refine ⟨?_, hka⟩
    by_contra hlt
    push_neg at hlt
    exact hknz (hzero k hlt)
  calc (tailSupport a δ).card ≤ (Finset.Ico T a).card := Finset.card_le_card hsub
    _ = a - T := Nat.card_Ico T a

/-- **Leading-zero-block √-floor.**  Suppose at the adversarial `b*` the realized 2-dilation descent
has a leading block of `T` zero-deficit levels (`δ_k = 0` for `k < T`, `T ≤ a`), bounded deficit
elsewhere (`δ_k ≤ 1` on `range a`), and the block is large enough that the tail fits inside the budget
threshold: `(a : ℝ) − T ≤ ((log 2)/2)·a`.  Then for `M 0 ≥ 0` the exp-relaxed dilation budget bound
stays at/above the `√(2^a)·M 0` Plancherel/prize scale:
`(√2)^a · M 0 ≤ 2^a · exp(−S) · M 0`,  `S = ∑_{k<a} δ_k`.

The numerically measured descent has `T ≈ a − O(1)`, i.e. `a − T = O(1) ≪ ((log 2)/2)·a`, so the
hypothesis holds with room to spare: the dilation saving is confined to an `O(1)` tail and cannot reach
the `√n` prize scale.  Lane-3 constraint lemma; CORE not discharged. -/
theorem budget_ge_sqrt_scale_of_leading_zero_block {a T : ℕ} {M0 : ℝ}
    (δ : ℕ → ℝ) (hT : T ≤ a)
    (hzero : ∀ k, k < T → δ k = 0)
    (hbad : ∀ k ∈ Finset.range a, δ k ≤ 1)
    (hblock : (a : ℝ) - T ≤ (Real.log 2 / 2) * a)
    (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0
      ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M0 := by
  -- instantiate the bounded-exception lemma with ε = 0 and E = tailSupport.
  set E : Finset ℕ := tailSupport a δ with hEdef
  have hE : E ⊆ Finset.range a := by
    intro k hk
    simp only [hEdef, tailSupport, Finset.mem_filter] at hk
    exact hk.1
  -- good levels (k ∉ E): δ k = 0 ≤ ε = 0.
  have hgood : ∀ k ∈ Finset.range a, k ∉ E → δ k ≤ (0 : ℝ) := by
    intro k hk hknotE
    simp only [hEdef, tailSupport, Finset.mem_filter, Finset.mem_range] at hknotE
    -- k ∈ range a, so the filter membership negation forces δ k = 0.
    have hka : k < a := Finset.mem_range.mp hk
    have : ¬ (k < a ∧ δ k ≠ 0) := hknotE
    push_neg at this
    exact le_of_eq (this hka)
  have hbad' : ∀ k ∈ Finset.range a, k ∈ E → δ k ≤ 1 := fun k hk _ => hbad k hk
  -- ε = 0 < (log 2)/2.
  have hεthr : (0 : ℝ) < Real.log 2 / 2 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  -- density floor at ε = 0: (1 - 0)·|E| ≤ ((log2)/2 - 0)·a, i.e. |E| ≤ ((log2)/2)·a.
  have hcard : (E.card : ℝ) ≤ (a : ℝ) - T := by
    have := tail_card_le_of_leading_zero (a := a) (T := T) δ hzero
    -- cast the Nat inequality, then a - T (Nat truncated) ≤ (a:ℝ) - T since T ≤ a.
    have hnatcast : (E.card : ℝ) ≤ ((a - T : ℕ) : ℝ) := by exact_mod_cast this
    have hsub : ((a - T : ℕ) : ℝ) = (a : ℝ) - T := by
      rw [Nat.cast_sub hT]
    rw [hsub] at hnatcast
    exact hnatcast
  have hdensity : (1 - (0:ℝ)) * (E.card : ℝ) ≤ (Real.log 2 / 2 - 0) * a := by
    have : (E.card : ℝ) ≤ (Real.log 2 / 2) * a := le_trans hcard hblock
    simpa using this
  exact budget_ge_sqrt_scale_of_bounded_exceptions δ E hE hgood hbad' hεthr hdensity hM0

#print axioms tail_card_le_of_leading_zero
#print axioms budget_ge_sqrt_scale_of_leading_zero_block

end ArkLib.ProximityGap.Frontier.DoorIVLeadingZeroDeficitFloor
