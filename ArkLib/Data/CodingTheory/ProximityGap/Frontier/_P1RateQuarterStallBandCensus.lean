/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterDChargeDerecursion

/-!
# Stall-band census: single- and double-pencil `StallResidual` instances are theorems

Issue #466, P1 rate-quarter predecessor pin — empirical calibration of the stall wall
(`StallResidual`, `_P1RateQuarterDChargeDerecursion.lean`), probe-first.

**Probe** (`scripts/probes/probe_rate_quarter_p1_stall_band_census.py`, deterministic,
exact): censuses the stall band at scaled shapes with the exact P1 ratios
(`T = ⌈N·592794966/2^30⌉`, `k = N/4`).  Findings:

* Maximal stall-band bad families exist at every scale; every pool the census realizes
  sits at the TOP of the stall band (`F = N − T`).
* The exhaustive μ_16/F_17 census found the extremal structure: the designed
  weight-`N−T+1` error pattern spawns an **emergent second pencil** aligned on the
  error support, and the extremal family is exactly a **two-pencil cover at capacity**
  `2(N − T + 1)` — equal to `N` at μ_16 (where `2(T−1) = N`), so the `≤ N` budget is
  TIGHT there with zero slack.
* At the real ratios (`2(T−1) > N`) the two aligned regions must overlap by
  `2T − 2 − N ≤ k − 1` (it fits), and the dual construction `v² = v¹ + (x·d, d)` with
  `d` vanishing on the overlap realizes exactly `2(N − T + 1)` stall-bad scalars
  (cancellation-ratio map `γ = −x`, injective) — `≈ 0.898·N` at μ_128/μ_256/μ_512.
* Nothing found ever exceeded the two-pencil capacity: hill-climbed 3-pencil
  composites produced FEWER bad scalars (their cancellation ratios are values of a
  degree `< k` rational function on the other pencils' aligned regions and collide).
* Rider directions on `Z` for census families sit at/above the `Z`-Johnson radius —
  genuine top-of-band stall witnesses.

**What this file makes kernel-checked** (at the PRIZE shape, not just scaled):

* `singlePencil_card_le` / `stall_budget_of_single_pencil`: any bad family riding a
  SINGLE pencil has `#bad ≤ N − T + 1 = 480946859 ≤ N` — i.e. **the `StallResidual`
  obligation holds unconditionally for single-pencil families** (the stall-pool
  hypothesis is not even needed).  First evidence-grade brick on the wall itself.
* `stall_budget_of_two_pencil_cover`: families covered by TWO pencils — the census's
  extremal class — also obey the budget: `2·(N − T + 1) = 961893718 ≤ N`, with slack
  exactly `2T − N − 2 = 111848106 ≈ 0.104·N` (`twoPencil_slack`).  (Three pencils
  would overflow this counting route — `3·480946859 > N` — matching the probe's
  capacity ledger; beyond two pencils the open content is genuine.)
* `stallResidual_of_pencil_pair_cover`: the same, phrased literally against the
  `StallResidual` quantifier shape (with the stall-pool hypothesis carried).
* Scaled-shape boundary dichotomies (μ_128 / μ_256 / μ_512) and the capacity
  arithmetic used by the probe, as `norm_num` rungs.

**Honesty**: this does NOT discharge `StallResidual` — bad families whose scalars ride
three or more distinct pencils (or none at all) remain the open beyond-Johnson wall.
No δ* movement; the bracket `3/8 ≤ δ* ≤ 43/96 + ε` is untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterStallBandCensus

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The universal pool bound (local copy of `pool_card_le_N_sub_T`)

`_P1RateQuarterMDSPoolSecondCharge.lean` proves this; it is re-proved here (same
10-line argument) to keep this file's import at the derecursion layer, whose olean
exists — frontier lane files are iterated without taking the build lock. -/

/-- The base witness sinks into `{D = 0}`, so the pool never exceeds `N − T`. -/
theorem pool_card_le_N_sub_T' (u₀ u₁ p₀ : Fin N → F) (γ₀ : F) (S : Finset (Fin N))
    (hS : predecessorThreshold ≤ S.card)
    (hagr : ∀ i ∈ S, p₀ i = u₀ i + γ₀ * u₁ i) :
    (Dsupport u₀ u₁ p₀ γ₀).card ≤ N - predecessorThreshold := by
  classical
  have hsink : S ⊆ Dzero u₀ u₁ p₀ γ₀ := by
    intro i hi
    rw [mem_Dzero_iff, Dfun]
    linear_combination hagr i hi
  have hz := Finset.card_le_card hsink
  have hpart := Dsupport_card_add_Dzero_card u₀ u₁ p₀ γ₀
  omega

/-! ## The single-pencil stall budget (prize shape, unconditional) -/

section SinglePencil

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- **Single-pencil cap**: a bad family all of whose witnesses ride ONE pencil
`(w₀, w₁)` has at most `1 + (N − T)` members — the base plus at most pool-many riders
(`riders_card_le_pool`), and the pool is universally `≤ N − T`
(`pool_card_le_N_sub_T`). -/
theorem singlePencil_card_le
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {w₀ w₁ : Fin N → F}
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hpencil : ∀ γ ∈ G, pf γ = w₀ + γ • w₁) :
    G.card ≤ N - predecessorThreshold + 1 := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · simp
  · set R := G.erase γ₀ with hRdef
    have hbase : ∀ i, w₀ i + γ₀ * w₁ i = pf γ₀ i := by
      intro i
      rw [hpencil γ₀ hγ₀]
      simp [smul_eq_mul]
    have hrides : RidesAll dom u₀ u₁ w₀ w₁ R Sf := by
      intro γ hγ
      have hγG : γ ∈ G := Finset.mem_of_mem_erase hγ
      obtain ⟨hcard, _hmem, hagree, hno⟩ := hdata γ hγG
      refine ⟨hcard, fun i hi => ?_, hno⟩
      have h := hagree i hi
      rw [hpencil γ hγG] at h
      simpa [smul_eq_mul] using h
    have hR : R.card ≤ (Dsupport u₀ u₁ (pf γ₀) γ₀).card :=
      riders_card_le_pool u₀ u₁ (pf γ₀) γ₀ dom R Sf hw₀ hw₁ hbase hrides
        (Finset.notMem_erase _ _)
    have hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ N - predecessorThreshold :=
      pool_card_le_N_sub_T' u₀ u₁ (pf γ₀) γ₀ (Sf γ₀) (hdata γ₀ hγ₀).1
        (fun i hi => (hdata γ₀ hγ₀).2.2.1 i hi)
    have hcard : R.card = G.card - 1 := Finset.card_erase_of_mem hγ₀
    have hGpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨γ₀, hγ₀⟩
    omega

/-- The cap clears the budget: `N − T + 1 = 480946859 ≤ N = 2^30`. -/
theorem singlePencil_cap_le_N : N - predecessorThreshold + 1 ≤ N := by
  norm_num [predecessorThreshold_eq, N]

/-- **The `StallResidual` obligation holds for single-pencil families**, without even
using the stall-pool hypothesis: `#bad ≤ 480946859 ≤ N`. -/
theorem stall_budget_of_single_pencil
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {w₀ w₁ : Fin N → F}
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hpencil : ∀ γ ∈ G, pf γ = w₀ + γ • w₁) :
    G.card ≤ N :=
  (singlePencil_card_le dom u₀ u₁ G Sf pf hdata hw₀ hw₁ hpencil).trans
    singlePencil_cap_le_N

end SinglePencil

/-! ## The two-pencil cover budget -/

section TwoPencil

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- Two single-pencil caps still fit under the budget:
`2·(N − T + 1) = 961893718 ≤ N = 2^30`.  (Three do not: `3·480946859 > N` — the
counting route through pencil covers ends at two pencils, matching the probe's
capacity ledger.) -/
theorem twoPencil_cap_le_N :
    (N - predecessorThreshold + 1) + (N - predecessorThreshold + 1) ≤ N := by
  norm_num [predecessorThreshold_eq, N]

theorem threePencil_cap_overflows :
    N < 3 * (N - predecessorThreshold + 1) := by
  norm_num [predecessorThreshold_eq, N]

/-- The exact slack of the two-pencil budget at the prize shape:
`N − 2(N − T + 1) = 2T − N − 2 = 111848106 ≈ 0.104·N` — this is the entire numeric
room between the census's realized extremal families and the `StallResidual` budget. -/
theorem twoPencil_slack :
    N - ((N - predecessorThreshold + 1) + (N - predecessorThreshold + 1)) =
      111848106 := by
  norm_num [predecessorThreshold_eq, N]

/-- The dual two-pencil construction FITS at the prize shape: the two aligned regions
of size `T − 1` overlap by `2T − 2 − N = 111848106 ≤ k − 1 = 268435455`, respecting
MDS separation — so the census's `2(N−T+1)`-sized extremal families scale up. -/
theorem dual_construction_fits :
    2 * (predecessorThreshold - 1) - N ≤ k - 1 := by
  norm_num [predecessorThreshold_eq, N, k]

/-- **Two-pencil cover budget**: a bad family whose scalars are covered by TWO pencils
(each scalar's witness rides one of them) obeys the stall budget `#bad ≤ N`. -/
theorem stall_budget_of_two_pencil_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {w₀ w₁ w₀' w₁' : Fin N → F}
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hw₀' : w₀' ∈ predecessorCode dom) (hw₁' : w₁' ∈ predecessorCode dom)
    (hcover : ∀ γ ∈ G, pf γ = w₀ + γ • w₁ ∨ pf γ = w₀' + γ • w₁') :
    G.card ≤ N := by
  classical
  set G₁ := G.filter (fun γ => pf γ = w₀ + γ • w₁) with hG₁
  set G₂ := G.filter (fun γ => pf γ ≠ w₀ + γ • w₁) with hG₂
  have hdata₁ : BadFamilyData dom u₀ u₁ G₁ Sf pf :=
    fun γ hγ => hdata γ (Finset.mem_of_mem_filter γ hγ)
  have hdata₂ : BadFamilyData dom u₀ u₁ G₂ Sf pf :=
    fun γ hγ => hdata γ (Finset.mem_of_mem_filter γ hγ)
  have h₁ : G₁.card ≤ N - predecessorThreshold + 1 :=
    singlePencil_card_le dom u₀ u₁ G₁ Sf pf hdata₁ hw₀ hw₁
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have h₂ : G₂.card ≤ N - predecessorThreshold + 1 :=
    singlePencil_card_le dom u₀ u₁ G₂ Sf pf hdata₂ hw₀' hw₁'
      (fun γ hγ => by
        have hm := Finset.mem_filter.mp hγ
        rcases hcover γ hm.1 with h | h
        · exact absurd h hm.2
        · exact h)
  have hsplit : G.card = G₁.card + G₂.card := by
    rw [hG₁, hG₂]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = w₀ + γ • w₁) (s := G)).symm
  calc G.card = G₁.card + G₂.card := hsplit
    _ ≤ (N - predecessorThreshold + 1) + (N - predecessorThreshold + 1) :=
        Nat.add_le_add h₁ h₂
    _ ≤ N := twoPencil_cap_le_N

/-- The two-pencil cover budget, phrased with the literal `StallResidual` stall-pool
hypothesis carried (the pools play no role — the counting closes regardless): the
`StallResidual` obligation is a THEOREM on the two-pencil-cover subclass. -/
theorem stallResidual_of_pencil_pair_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (_hstall : ∀ γ₀ ∈ G, 75018134 ≤ (Dsupport u₀ u₁ (pf γ₀) γ₀).card)
    {w₀ w₁ w₀' w₁' : Fin N → F}
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hw₀' : w₀' ∈ predecessorCode dom) (hw₁' : w₁' ∈ predecessorCode dom)
    (hcover : ∀ γ ∈ G, pf γ = w₀ + γ • w₁ ∨ pf γ = w₀' + γ • w₁') :
    G.card ≤ N :=
  stall_budget_of_two_pencil_cover dom u₀ u₁ G Sf pf hdata
    hw₀ hw₁ hw₀' hw₁' hcover

end TwoPencil

/-! ## Scaled-shape calibration rungs (probe cross-checks, kernel-pinned)

The probe's scaled shapes use the exact P1 ratios.  The boundary `F₀(N)` is the
largest pool for which the whole contributing range clears the `Z`-Johnson radius:
`(T − F)² > (N − F)(k − 1)`. -/

/-- μ_128 (`N=128, T=71, k=32`): boundary `F₀ = 10`, stall band `[11, 57]`. -/
theorem mu128_boundary :
    (71 - 10) ^ 2 > (128 - 10) * (32 - 1) ∧
    (71 - 11) ^ 2 ≤ (128 - 11) * (32 - 1) ∧
    128 - 71 = 57 := by
  norm_num

/-- μ_256 (`N=256, T=142, k=64`): boundary `F₀ = 20`, stall band `[21, 114]`. -/
theorem mu256_boundary :
    (142 - 20) ^ 2 > (256 - 20) * (64 - 1) ∧
    (142 - 21) ^ 2 ≤ (256 - 21) * (64 - 1) ∧
    256 - 142 = 114 := by
  norm_num

/-- μ_512 (`N=512, T=283, k=128`): boundary `F₀ = 37`, stall band `[38, 229]`. -/
theorem mu512_boundary :
    (283 - 37) ^ 2 > (512 - 37) * (128 - 1) ∧
    (283 - 38) ^ 2 ≤ (512 - 38) * (128 - 1) ∧
    512 - 283 = 229 := by
  norm_num

/-- The scaled thresholds are the exact ceilings `⌈N·592794966/2^30⌉` used by the
probe: `T(128) = 71`, `T(256) = 142`, `T(512) = 283`. -/
theorem mu_thresholds_exact :
    70 * 2 ^ 30 < 128 * 592794966 ∧ 128 * 592794966 ≤ 71 * 2 ^ 30 ∧
    141 * 2 ^ 30 < 256 * 592794966 ∧ 256 * 592794966 ≤ 142 * 2 ^ 30 ∧
    282 * 2 ^ 30 < 512 * 592794966 ∧ 512 * 592794966 ≤ 283 * 2 ^ 30 := by
  norm_num

/-- Scaled single-pencil caps clear the scaled budgets with slack — the census's
per-scale headline (`max #stall-bad found` never exceeded these caps):
`58 ≤ 128`, `115 ≤ 256`, `230 ≤ 512`. -/
theorem mu_singlePencil_caps :
    128 - 71 + 1 ≤ 128 ∧ 256 - 142 + 1 ≤ 256 ∧ 512 - 283 + 1 ≤ 512 := by
  norm_num

/-- Scaled TWO-pencil caps — the census's realized extremal value `2(N − T + 1)` —
still clear the scaled budgets: `116 ≤ 128`, `230 ≤ 256`, `460 ≤ 512`; and at the
degenerate μ_16 (`T = 9`) the cap is TIGHT: `2·(16 − 9 + 1) = 16` — the exhaustive
census attains it, so no per-scale slack survives below μ_128. -/
theorem mu_twoPencil_caps :
    2 * (16 - 9 + 1) = 16 ∧ 2 * (128 - 71 + 1) ≤ 128 ∧
    2 * (256 - 142 + 1) ≤ 256 ∧ 2 * (512 - 283 + 1) ≤ 512 := by
  norm_num

end ArkLib.ProximityGap.Frontier.P1RateQuarterStallBandCensus

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterStallBandCensus

#print axioms pool_card_le_N_sub_T'
#print axioms singlePencil_card_le
#print axioms singlePencil_cap_le_N
#print axioms stall_budget_of_single_pencil
#print axioms twoPencil_cap_le_N
#print axioms threePencil_cap_overflows
#print axioms twoPencil_slack
#print axioms dual_construction_fits
#print axioms stall_budget_of_two_pencil_cover
#print axioms stallResidual_of_pencil_pair_cover
#print axioms mu128_boundary
#print axioms mu256_boundary
#print axioms mu512_boundary
#print axioms mu_thresholds_exact
#print axioms mu_singlePencil_caps
#print axioms mu_twoPencil_caps
