/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedUD
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import ArkLib.Data.CodingTheory.ProximityGap.CappedSupplyMassIdentity
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The strongest UNCONDITIONAL small-subgroup δ* statement (#389)

The complete δ* pin (`SmallSubgroupDeltaStarPin.smallSubgroup_deltaStar_pin`) is gated on
the named all-pairs hypothesis `SmallSubgroupGoodList` — the open beyond-Johnson interleaved
list bound for the canonical small-subgroup RS code.  This file proves the strongest δ*
statement that needs NO such bridge: a fully **unconditional δ\* LOWER bound** for the
small-subgroup (and in fact ANY) Reed–Solomon code, valid in the unique-decoding quarter
window `δ < d/(4n)`.

## What is proven here (axiom-clean, unconditional)

The all-pairs interleaved list bound `SmallSubgroupGoodList` is only OPEN beyond the Johnson
radius.  Below the *quarter* of the relative distance the interleaved code `C^{≡2}` is
uniquely decodable, so the list is `≤ 1` for ALL stacks `(u₀, u₁)` automatically — no
literature input.  We make this explicit on the small-subgroup RS code:

* `pairClosed_codeFinset` — every RS-code Finset (any submodule's Finset) is `PairClosed`:
  the two-term combinations `(γ−γ')⁻¹•(c−c')` and `c − γ•(…)` are linear, hence in the
  submodule.  Removes the only side condition `epsMCA_le_interleavedUD` carries.

* `rsCode_codeFinset_agree_le` — distinct codewords of the RS-code Finset agree on
  `≤ k − 1` points (the `e = k − 1` agreement parameter), repackaging the in-tree
  root-counting bound `rsCode_pairwise_agreeSet_card_le` into the `filter (g₁ = g₂)` shape
  `epsMCA_le_interleavedUD` consumes.

* `rsCode_epsMCA_le_quarter` — **the unconditional ε_mca bound**: for `1 ≤ k`,
  `4δn + (k−1) < n`  (i.e. `δ < (n − k + 1)/(4n) = d/(4n)`),
    `ε_mca(rsCode dom k, δ) ≤ (1 + (n − (2t − n)))/q`,  `t = ⌈(1−δ)n⌉₊`,
  for ANY evaluation domain `dom`.  No all-pairs hypothesis, no `SmallSubgroupGoodList`.

* `rsCode_deltaStar_ge_quarter` — **the unconditional δ\* lower bound**: if at the quarter
  radius `δ` the (proven) ε_mca bound clears the budget `ε*`, then `δ ≤ δ*(rsCode dom k, ε*)`.

* `smallSubgroup_deltaStar_ge_quarter` — the same, specialised to the 2-power NTT subgroup
  domain `μ_n`, recorded as the unconditional companion to `smallSubgroup_deltaStar_pin`.

## The coverage map: which stacks are covered, which need the open bridge

* **Covered unconditionally (this file).**  ALL stacks `(u₀, u₁)`, at every `δ < d/(4n)`.
  Above this radius the interleaved unique-decoding argument fails (the list can have ≥ 2
  members) and the bound is genuinely vacuous — but the LOWER bound on δ* it produces is
  real: `δ* ≥ d/(4n)` for the small-subgroup RS code, with zero conjectural input.

* **Needs the open all-pairs bridge (`SmallSubgroupGoodList`).**  Pushing the lower bound
  past `d/(4n)` toward the Johnson radius `1−√ρ` and beyond requires an interleaved list
  bound `L` for ALL pairs at the larger radius.  The proven small-subgroup supply data
  (`cubicSupply_sq_le_sharp`: `T(μ_n) ≤ √3·n^{3/2}`) controls a SINGLE structured
  obstruction (the cubic/power word), not the all-pairs list; bridging single-word supply
  to all-pairs interleaved lists is exactly issue #334 core A / [ABF26] §5.

So the honest split is: the quarter window is unconditional and uniform over stacks; the
window `(d/(4n), …)` is where the named hypothesis is load-bearing.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
* `EpsMCAInterleavedUD.lean` (the quarter-window collapse), `JohnsonSplitSupply.lean`
  (RS pairwise agreement), `MCAThresholdLedger.lean` (the δ* bracketing engine),
  `SmallSubgroupDeltaStarPin.lean` (the conditional full pin this complements).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.SmallSubgroupUncondQuarter

open ProximityGap ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap.PairRank
open ProximityGap.MCAThresholdLedger Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Part 1 — every RS-code Finset is `PairClosed` -/

/-- **Every RS-code Finset is `PairClosed`.**  The two-term combinations that the pair
extraction produces — `(γ−γ')⁻¹•(c−c')` and `c − γ•((γ−γ')⁻¹•(c−c'))` — are `F`-linear in
the codewords, hence lie in the submodule `rsCode dom k`.  This discharges the only
structural side condition of `epsMCA_le_interleavedUD` for the explicit RS code. -/
theorem pairClosed_codeFinset (dom : Fin n ↪ F) (k : ℕ) :
    Round17CAPair.PairClosed (codeFinset dom k) := by
  classical
  intro c hc c' hc' γ γ' _
  -- membership in the Finset ↔ membership in the submodule
  rw [codeFinset, Finset.mem_filter] at hc hc'
  have hcM : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := hc.2
  have hc'M : c' ∈ (rsCode dom k : Submodule F (Fin n → F)) := hc'.2
  -- the submodule is closed under the two combinations
  have hsub : (γ - γ')⁻¹ • (c - c') ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hcM hc'M)
  have hsub2 : c - γ • ((γ - γ')⁻¹ • (c - c'))
      ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
    Submodule.sub_mem _ hcM (Submodule.smul_mem _ _ hsub)
  refine ⟨?_, ?_⟩
  · rw [codeFinset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
  · rw [codeFinset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub2⟩

/-! ## Part 2 — the `e = k − 1` agreement parameter of the RS-code Finset -/

/-- **RS-code Finset pairwise agreement**, in the `filter (g₁ = g₂)` shape.  Distinct
codewords of `codeFinset dom k` agree on `≤ k − 1` coordinates — the agreement parameter
`e = k − 1` that the quarter window consumes.  Repackages the in-tree root-counting bound
`rsCode_pairwise_agreeSet_card_le`. -/
theorem rsCode_codeFinset_agree_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    ∀ g₁ ∈ codeFinset dom k, ∀ g₂ ∈ codeFinset dom k, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ k - 1 := by
  classical
  intro g₁ hg₁ g₂ hg₂ hne
  rw [codeFinset, Finset.mem_filter] at hg₁ hg₂
  -- `agreeSet g₁ g₂ = univ.filter (g₁ = g₂)` definitionally; rewrite and apply the lemma
  have heq : (Finset.univ.filter (fun x => g₁ x = g₂ x)) = agreeSet g₁ g₂ := rfl
  rw [heq]
  exact rsCode_pairwise_agreeSet_card_le dom hk hg₁.2 hg₂.2 hne

/-! ## Part 3 — the unconditional `ε_mca` bound in the quarter window -/

/-- **The unconditional small-subgroup ε_mca bound.**  For any evaluation domain
`dom : Fin n ↪ F`, any RS degree `1 ≤ k`, and any `δ` with `4δn + (k−1) < n` — i.e.
`δ < (n − k + 1)/(4n) = d/(4n)` — the MCA error of the RS-code Finset obeys

  `ε_mca(rsCode dom k, δ) ≤ (1 + (n − (2t − n)))/q`,  `t = ⌈(1−δ)n⌉₊`,

with NO list-decoding, extraction, or all-pairs hypothesis: the interleaved code `C^{≡2}` is
uniquely decodable at the doubled radius, so the list is `≤ 1` for every stack.  This is the
stack-uniform, fully unconditional half of the δ* picture. -/
theorem rsCode_epsMCA_le_quarter (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ : 4 * δ * (Fintype.card (Fin n) : ℝ≥0) + ((k - 1 : ℕ) : ℝ≥0)
      < (Fintype.card (Fin n) : ℝ≥0)) :
    ProximityGap.epsMCA (F := F) (A := F)
        (↑(codeFinset dom k) : Set (Fin n → F)) δ ≤
      ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) :=
  ProximityGap.epsMCA_le_interleavedUD_of_quarter_dist (codeFinset dom k)
    (pairClosed_codeFinset dom k) δ (k - 1)
    (rsCode_codeFinset_agree_le dom hk) hδ

/-! ## Part 4 — the unconditional δ* lower bound -/

/-- **The unconditional small-subgroup δ\* lower bound.**  If, at a quarter-window radius
`δ ≤ 1` with `4δn + (k−1) < n`, the proven ε_mca bound clears the budget `ε*`, then
`δ ≤ δ*(rsCode dom k, ε*)`.  No `SmallSubgroupGoodList`, no beyond-Johnson list data: the
lower bracket holds for the explicit RS code unconditionally, uniformly over all stacks.

In rate units this pins `δ* ≥ d/(4n) = (1 − ρ + 1/n)/4` whenever the budget admits the
quarter-window numerator `(1 + 2δn + O(1))/q ≤ ε*` — the cryptographic regime
`q ≫ n / ε*`. -/
theorem rsCode_deltaStar_ge_quarter (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ1 : δ ≤ 1)
    (hδ : 4 * δ * (Fintype.card (Fin n) : ℝ≥0) + ((k - 1 : ℕ) : ℝ≥0)
      < (Fintype.card (Fin n) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
        (↑(codeFinset dom k) : Set (Fin n → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (rsCode_epsMCA_le_quarter dom hk hδ) hbudget)

/-- **The small-subgroup specialisation.**  The unconditional δ\* lower bound on the
2-power NTT evaluation domain `dom : Fin n ↪ ZMod p` (the small-subgroup setting of
`smallSubgroup_deltaStar_pin`).  This is the companion that needs NEITHER the deep-band
budget NOR `SmallSubgroupGoodList`: it pins `δ*(rsCode dom k, ε*) ≥ d/(4n)` for the explicit
small-subgroup RS code outright. -/
theorem smallSubgroup_deltaStar_ge_quarter {p : ℕ} [Fact p.Prime]
    (dom : Fin n ↪ ZMod p) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : 4 * δ * (Fintype.card (Fin n) : ℝ≥0) + ((k - 1 : ℕ) : ℝ≥0)
      < (Fintype.card (Fin n) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) : ℕ) : ℝ≥0∞)
        / (Fintype.card (ZMod p) : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (↑(codeFinset dom k) : Set (Fin n → ZMod p)) εstar :=
  rsCode_deltaStar_ge_quarter dom hk hδ1 hδ εstar hbudget

end ArkLib.ProximityGap.SmallSubgroupUncondQuarter

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.SmallSubgroupUncondQuarter.pairClosed_codeFinset
#print axioms ArkLib.ProximityGap.SmallSubgroupUncondQuarter.rsCode_codeFinset_agree_le
#print axioms ArkLib.ProximityGap.SmallSubgroupUncondQuarter.rsCode_epsMCA_le_quarter
#print axioms ArkLib.ProximityGap.SmallSubgroupUncondQuarter.rsCode_deltaStar_ge_quarter
#print axioms ArkLib.ProximityGap.SmallSubgroupUncondQuarter.smallSubgroup_deltaStar_ge_quarter
