/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterDChargeDerecursion

/-!
# Pencil harvest cap: the `StallResidual` budget for three- and four-pencil covers

Issue #466, P1 rate-quarter predecessor pin — follow-up to
`_P1RateQuarterStallBandCensus.lean` (extremal stall families = two-pencil covers at
capacity `2(N−T+1)`; open corridor = families needing ≥ 3 pencils inside the slack
`2T − N − 2 = 111848106 ≈ 0.104·N`).

**Probe** (`scripts/probes/probe_rate_quarter_p1_pencil_harvest_cap.py`, exact linear
algebra over `F_q`): the ratio-collision mechanism is a **dimension count**.  Pencil
differences `d_ij` are codeword pairs vanishing on the pairwise aligned-overlaps and
telescoping (`d₁₂ + d₂₃ = d₁₃`); the solution space of the three-pencil linear system
has dimension exactly `max(0, 2k − Σ|ov|)` in every geometry probed, while coverage
forces `Σ|ov| ≥ 3(T−1−t) − N` at alignment shortfall `t`.  Measured consequences:

* three `(T−1−t)`-aligned pencils are linearly IMPOSSIBLE for `t ≤ 13` at μ_256
  (`t ≤ 9` at μ_128) — matching the generic threshold `(3(T−1) − N − 2k + 1)/3`;
* with TWO full pencils fixed (the census's extremal configuration), the third
  pencil's aligned size caps at exactly `k` (affine-system feasibility), forcing
  margin `D = T − k` and a **marginal harvest of 2** at μ_128 and μ_256;
* at prize ratios `3(T−1) − N = 704643071 > 2k = 536870912`
  (`fully_aligned_triple_dimension_deficit`), so the mechanism scales.

**What this file makes kernel-checked** (prize shape, UNCONDITIONAL given the margin
hypotheses — the margin itself is what the probe shows is forced generically):

* `underAligned_riders_mul_le`: a pencil under-aligned by margin `D`
  (`A + D ≤ T`) harvests at most `(N − T + D)/D` riders: `#riders · D ≤ N − T + D`.
* `thirdPencil_card_le_of_margin_five`: at margin `D = 5`, `#riders ≤ 96189372 <`
  slack `111848106`.
* `stall_budget_of_three_pencil_cover`: a bad family covered by three pencils, the
  third under-aligned by ≥ 5, obeys the `StallResidual` budget `#bad ≤ N`.  (The
  probe-measured forced margin is `T − k = 324359510` — 8 orders of magnitude more
  than the `5` needed.)
* `stall_budget_of_four_pencil_cover`: four pencils, the third and fourth
  under-aligned by ≥ 9 each: still `≤ N` — the compounding form.
* `margin_four_fails`: margin 4 does NOT close the three-pencil ledger
  (`2(N−T+1) + ⌊(N−T+4)/4⌋ > N`) — 5 is the sharp uniform margin for this route.

**Honesty**: `StallResidual` is NOT discharged.  The margin hypotheses are exactly
what remains open: the probe pins them generically (exact rank computations), but a
kernel proof that the geometry FORCES the margin (the `Σ|ov| > 2k` dimension argument
needs rank-independence of the vanishing conditions, which an adversarial point
configuration could in principle defeat — none was found) is future work; and
families needing ≥ 3 pencils with all margins `< 5`, or unboundedly many pencils with
`Σ 1/D_j` too large, remain the wall.  Marginal harvests do NOT automatically sum
below the slack for arbitrarily many pencils (`Σ_j (N−T)/D_j ≤ 111848106` needs
`Σ 1/D_j ≤ 0.2326`), so `StallResidual` does NOT fall entirely by this route.
No δ* movement; the bracket `3/8 ≤ δ* ≤ 43/96 + ε` is untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion

local instance localInstance_P1RateQuarterPencilHarvestCap_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterPencilHarvestCap_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The under-aligned harvest bound -/

section Harvest

variable (dom : Fin N ↪ F) (u₀ u₁ w₀ w₁ : Fin N → F)
variable (R : Finset F) (Sf : F → Finset (Fin N))

/-- **Margin harvest bound**: a pencil whose aligned set is `D` under the threshold
(`A + D ≤ T`) carries at most `(N − T + D)/D` riders: each rider burns `≥ T − A ≥ D`
disjoint votes in the `N − A = (N − T) + (T − A)` off-aligned coordinates. -/
theorem underAligned_riders_mul_le (D : ℕ)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf)
    (hD : (alignedSet u₀ u₁ w₀ w₁).card + D ≤ predecessorThreshold) :
    R.card * D ≤ N - predecessorThreshold + D := by
  classical
  have hmul := riders_card_mul_le dom u₀ u₁ w₀ w₁ R Sf h
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hAdef
  set x := predecessorThreshold - A with hxdef
  have hTN : predecessorThreshold ≤ N := by
    rw [predecessorThreshold_eq]; norm_num [N]
  have hxD : D ≤ x := by omega
  obtain ⟨e, hx⟩ : ∃ e, x = D + e := ⟨x - D, by omega⟩
  have hNA : N - A = (N - predecessorThreshold) + x := by omega
  rcases Nat.eq_zero_or_pos R.card with h0 | h1
  · simp [h0]
  · have hxe : R.card * x = R.card * D + R.card * e := by
      rw [hx, Nat.mul_add]
    have hge : e ≤ R.card * e := Nat.le_mul_of_pos_left e h1
    omega

/-- At margin `D = 5` the harvest is at most `96189372` — under the two-pencil slack
`2T − N − 2 = 111848106`. -/
theorem thirdPencil_card_le_of_margin_five
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf)
    (hD : (alignedSet u₀ u₁ w₀ w₁).card + 5 ≤ predecessorThreshold) :
    R.card ≤ 96189372 := by
  have hmul := underAligned_riders_mul_le dom u₀ u₁ w₀ w₁ R Sf 5 h hD
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- At margin `D = 9` the harvest is at most `53438540` — two such fit under the
slack. -/
theorem extraPencil_card_le_of_margin_nine
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf)
    (hD : (alignedSet u₀ u₁ w₀ w₁).card + 9 ≤ predecessorThreshold) :
    R.card ≤ 53438540 := by
  have hmul := underAligned_riders_mul_le dom u₀ u₁ w₀ w₁ R Sf 9 h hD
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

end Harvest

/-! ## RidesAll extraction from bad-family data on a pencil cover -/

section Cover

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- Scalars whose witness sits on a given pencil ride it. -/
theorem ridesAll_of_pencil_subfamily {w₀ w₁ : Fin N → F} {G' : Finset F}
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (hsub : G' ⊆ G) (hpencil : ∀ γ ∈ G', pf γ = w₀ + γ • w₁) :
    RidesAll dom u₀ u₁ w₀ w₁ G' Sf := by
  intro γ hγ
  obtain ⟨hcard, _hmem, hagree, hno⟩ := hdata γ (hsub hγ)
  refine ⟨hcard, fun i hi => ?_, hno⟩
  have h := hagree i hi
  rw [hpencil γ hγ] at h
  simpa [smul_eq_mul] using h

/-- **Three-pencil cover budget**: a bad family covered by three pencils, the third
of which is under-aligned by margin ≥ 5, obeys the `StallResidual` budget:
`#bad ≤ 2·480946859 + 96189372 = 1058083090 ≤ N`.  (The probe-measured forced margin
for a third pencil next to two full ones is `T − k = 324359510` ≫ 5.) -/
theorem stall_budget_of_three_pencil_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hcover : ∀ γ ∈ G, pf γ = wa₀ + γ • wa₁ ∨ pf γ = wb₀ + γ • wb₁ ∨
      pf γ = wc₀ + γ • wc₁)
    (hmargin : (alignedSet u₀ u₁ wc₀ wc₁).card + 5 ≤ predecessorThreshold) :
    G.card ≤ N := by
  classical
  set G₁ := G.filter (fun γ => pf γ = wa₀ + γ • wa₁) with hG₁
  set Grest := G.filter (fun γ => pf γ ≠ wa₀ + γ • wa₁) with hGrest
  set G₂ := Grest.filter (fun γ => pf γ = wb₀ + γ • wb₁) with hG₂
  set G₃ := Grest.filter (fun γ => pf γ ≠ wb₀ + γ • wb₁) with hG₃
  have hsub₁ : G₁ ⊆ G := Finset.filter_subset _ _
  have hsubrest : Grest ⊆ G := Finset.filter_subset _ _
  have hsub₂ : G₂ ⊆ G := (Finset.filter_subset _ _).trans hsubrest
  have hsub₃ : G₃ ⊆ G := (Finset.filter_subset _ _).trans hsubrest
  have hr₁ : RidesAll dom u₀ u₁ wa₀ wa₁ G₁ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₁
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₂ : RidesAll dom u₀ u₁ wb₀ wb₁ G₂ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₂
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₃ : RidesAll dom u₀ u₁ wc₀ wc₁ G₃ Sf := by
    refine ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₃
      (fun γ hγ => ?_)
    have hm := Finset.mem_filter.mp hγ
    have hm' := Finset.mem_filter.mp hm.1
    rcases hcover γ hm'.1 with h | h | h
    · exact absurd h hm'.2
    · exact absurd h hm.2
    · exact h
  have h₁ : G₁.card ≤ 480946859 :=
    riders_card_le_uniform dom u₀ u₁ wa₀ wa₁ G₁ Sf hwa₀ hwa₁ hr₁
  have h₂ : G₂.card ≤ 480946859 :=
    riders_card_le_uniform dom u₀ u₁ wb₀ wb₁ G₂ Sf hwb₀ hwb₁ hr₂
  have h₃ : G₃.card ≤ 96189372 :=
    thirdPencil_card_le_of_margin_five dom u₀ u₁ wc₀ wc₁ G₃ Sf hr₃ hmargin
  have hsplit1 : G.card = G₁.card + Grest.card := by
    rw [hG₁, hGrest]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wa₀ + γ • wa₁) (s := G)).symm
  have hsplit2 : Grest.card = G₂.card + G₃.card := by
    rw [hG₂, hG₃]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wb₀ + γ • wb₁) (s := Grest)).symm
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- **Four-pencil cover budget**: two arbitrary pencils plus two under-aligned by
margin ≥ 9 each: `#bad ≤ 2·480946859 + 2·53438540 = 1068770798 ≤ N` — the marginal
harvests compound. -/
theorem stall_budget_of_four_pencil_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ wd₀ wd₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hcover : ∀ γ ∈ G, pf γ = wa₀ + γ • wa₁ ∨ pf γ = wb₀ + γ • wb₁ ∨
      pf γ = wc₀ + γ • wc₁ ∨ pf γ = wd₀ + γ • wd₁)
    (hmargin₃ : (alignedSet u₀ u₁ wc₀ wc₁).card + 9 ≤ predecessorThreshold)
    (hmargin₄ : (alignedSet u₀ u₁ wd₀ wd₁).card + 9 ≤ predecessorThreshold) :
    G.card ≤ N := by
  classical
  set G₁ := G.filter (fun γ => pf γ = wa₀ + γ • wa₁) with hG₁
  set R1 := G.filter (fun γ => pf γ ≠ wa₀ + γ • wa₁) with hR1
  set G₂ := R1.filter (fun γ => pf γ = wb₀ + γ • wb₁) with hG₂
  set R2 := R1.filter (fun γ => pf γ ≠ wb₀ + γ • wb₁) with hR2
  set G₃ := R2.filter (fun γ => pf γ = wc₀ + γ • wc₁) with hG₃
  set G₄ := R2.filter (fun γ => pf γ ≠ wc₀ + γ • wc₁) with hG₄
  have hsub₁ : G₁ ⊆ G := Finset.filter_subset _ _
  have hsubR1 : R1 ⊆ G := Finset.filter_subset _ _
  have hsub₂ : G₂ ⊆ G := (Finset.filter_subset _ _).trans hsubR1
  have hsubR2 : R2 ⊆ G := (Finset.filter_subset _ _).trans hsubR1
  have hsub₃ : G₃ ⊆ G := (Finset.filter_subset _ _).trans hsubR2
  have hsub₄ : G₄ ⊆ G := (Finset.filter_subset _ _).trans hsubR2
  have hr₁ : RidesAll dom u₀ u₁ wa₀ wa₁ G₁ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₁
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₂ : RidesAll dom u₀ u₁ wb₀ wb₁ G₂ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₂
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₃ : RidesAll dom u₀ u₁ wc₀ wc₁ G₃ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₃
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₄ : RidesAll dom u₀ u₁ wd₀ wd₁ G₄ Sf := by
    refine ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata hsub₄
      (fun γ hγ => ?_)
    have hm := Finset.mem_filter.mp hγ
    have hm' := Finset.mem_filter.mp hm.1
    have hm'' := Finset.mem_filter.mp hm'.1
    rcases hcover γ hm''.1 with h | h | h | h
    · exact absurd h hm''.2
    · exact absurd h hm'.2
    · exact absurd h hm.2
    · exact h
  have h₁ : G₁.card ≤ 480946859 :=
    riders_card_le_uniform dom u₀ u₁ wa₀ wa₁ G₁ Sf hwa₀ hwa₁ hr₁
  have h₂ : G₂.card ≤ 480946859 :=
    riders_card_le_uniform dom u₀ u₁ wb₀ wb₁ G₂ Sf hwb₀ hwb₁ hr₂
  have h₃ : G₃.card ≤ 53438540 :=
    extraPencil_card_le_of_margin_nine dom u₀ u₁ wc₀ wc₁ G₃ Sf hr₃ hmargin₃
  have h₄ : G₄.card ≤ 53438540 :=
    extraPencil_card_le_of_margin_nine dom u₀ u₁ wd₀ wd₁ G₄ Sf hr₄ hmargin₄
  have hs1 : G.card = G₁.card + R1.card := by
    rw [hG₁, hR1]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wa₀ + γ • wa₁) (s := G)).symm
  have hs2 : R1.card = G₂.card + R2.card := by
    rw [hG₂, hR2]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wb₀ + γ • wb₁) (s := R1)).symm
  have hs3 : R2.card = G₃.card + G₄.card := by
    rw [hG₃, hG₄]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wc₀ + γ • wc₁) (s := R2)).symm
  have hN : N = 1073741824 := by norm_num [N]
  omega

end Cover

/-! ## The mechanism and ledger arithmetic (kernel-pinned) -/

/-- **The dimension deficit at prize ratios**: three fully-aligned pencils force
overlap mass `3(T−1) − N = 704643071` strictly beyond the difference-parameter budget
`2k = 536870912` — the linear system of pencil differences is over-constrained (the
probe's exact rank computations realize `dim = max(0, 2k − Σ|ov|)` in every geometry
tried). -/
theorem fully_aligned_triple_dimension_deficit :
    2 * k < 3 * (predecessorThreshold - 1) - N := by
  norm_num [predecessorThreshold_eq, N, k]

/-- Three-pencil margin ledger: `2·480946859 + 96189372 = 1058083090 ≤ N`. -/
theorem threePencil_margin_ledger :
    480946859 + 480946859 + 96189372 ≤ N := by
  norm_num [N]

/-- Four-pencil margin ledger: `2·480946859 + 2·53438540 = 1068770798 ≤ N`. -/
theorem fourPencil_margin_ledger :
    480946859 + 480946859 + 53438540 + 53438540 ≤ N := by
  norm_num [N]

/-- Margin 4 does NOT close the three-pencil ledger: `⌊(N−T+4)/4⌋ = 120236715` and
`2·480946859 + 120236715 = 1082130433 > N` — margin 5 is sharp for this route. -/
theorem margin_four_fails :
    N < 480946859 + 480946859 + (N - predecessorThreshold + 4) / 4 := by
  norm_num [predecessorThreshold_eq, N]

/-- The probe-measured forced margin for a third pencil next to two full ones is
`T − k = 324359510` (aligned size caps at `k`), with marginal harvest
`⌊(N − k)/(T − k)⌋ = 2` — the margin-5 hypothesis of the cover theorems is weaker by
seven orders of magnitude than what the generic-rank geometry actually forces. -/
theorem forced_margin_arith :
    predecessorThreshold - k = 324359510 ∧
    2 * (predecessorThreshold - k) ≤ N - k ∧
    N - k < 3 * (predecessorThreshold - k) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

#print axioms underAligned_riders_mul_le
#print axioms thirdPencil_card_le_of_margin_five
#print axioms extraPencil_card_le_of_margin_nine
#print axioms ridesAll_of_pencil_subfamily
#print axioms stall_budget_of_three_pencil_cover
#print axioms stall_budget_of_four_pencil_cover
#print axioms fully_aligned_triple_dimension_deficit
#print axioms threePencil_margin_ledger
#print axioms fourPencil_margin_ledger
#print axioms margin_four_fails
#print axioms forced_margin_arith
