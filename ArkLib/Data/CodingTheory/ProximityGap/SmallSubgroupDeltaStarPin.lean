/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality
import ArkLib.Data.CodingTheory.ProximityGap.CubicSupplyCosetBridge
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicCapstone
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandDeltaStarCeiling
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarSandwich

/-!
# The complete small-subgroup δ* pin (#389): `n = 2^m`, `p > 2^n`

This file assembles the *closed* small-subgroup ingredients into the sharpest in-tree
δ* consequence for the 2-power NTT subgroup `μ_n ⊂ F_p` with `n = 2^m`, `p > 2^n`.

The load-bearing PROVEN input is the **exact additive energy**
`E(μ_n) = 3n² − 3n` (`EnergyEqualitySidonModNeg.mu_n_additiveEnergy_eq`), the char-0
minimal value, unconditional for `p > 2^n` (cyclotomic resultant only — no Weil, no
Stepanov, no open sum-product conjecture).

## What is proven here (axiom-clean, unconditional for `p > 2^n`)

* `cubicSupply_sq_le_sharp` — feeding the EXACT energy through the in-tree
  Cauchy–Schwarz list/supply bridge `T(G)² ≤ |G|·E(G)`
  (`zeroSumTriples_sq_le_card_energy_viaCoset`) gives the SHARP cubic-supply ceiling on
  `μ_n`:
    `zeroSumTriples (μ_n)² ≤ 3·n²·(n−1)`,
  i.e. `T(μ_n) ≤ √3 · n · √(n−1) < √3 · n^{3/2}`.  This sharpens the conditional
  `zeroSumTriples_sq_le_of_sidonModNeg` bound `T² ≤ 3n³` by the exact `3n²` correction —
  the minimal additive obstruction, now machine-checked with the equality input.

* `cubic_explainable_core_sq_le_sharp` — transported to the *cubic word* `x ↦ x³` over any
  domain whose image is `μ_n`: its explainable-3-core supply `S` satisfies
    `S² ≤ 3·n²·(n−1)`,
  via `cubicSupply_eq_sumZeroCard` + `sumZeroCard_le_zeroSumTriples_image`.  The Sylvester
  cubic — the worst-case sub-Johnson *additive* obstruction, `Θ(n²)` on the full field — is
  pinned to `Θ(n^{3/2})` on the smooth NTT domain, UNCONDITIONALLY (the open Garcia–Voloch
  sum-product input is no longer needed; the cyclotomic energy equality supplies it exactly).

## The complete δ* pin

The δ* failure side is the in-tree ceiling `mcaDeltaStar_le_of_deep_band`
(`DeepBandDeltaStarCeiling`), wired here as `smallSubgroup_deltaStar_le`.

The δ* success (lower) side requires an interleaved **list-size** bound at the good radius
for ALL word pairs `u₀, u₁` (`mcaDeltaStar_ge_of_interleavedList`).  The minimal-energy /
small cubic-supply data proven above controls the *single canonical* obstruction word, but
the general per-pair interleaved list bound that the MCA lower dictionary consumes is NOT a
closed in-tree consumer of the cubic supply: bridging single-word supply to the all-pairs
interleaved list is the open beyond-Johnson question for explicit RS (issue #334 core A,
[ABF26] §5).  We therefore state it as the explicit named hypothesis
`SmallSubgroupGoodList` and assemble the FULL two-sided pin from it — no `sorry`, the
literature gap is a visible binder.

* `smallSubgroup_deltaStar_pin` — under `SmallSubgroupGoodList` (success-side list data) and
  the deep-band budget condition (failure-side, proven engine), the formal threshold is
  pinned to the sandwich `δgood ≤ δ*(rsCode dom k, ε*) ≤ δbad`.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
* Issue #389; `SidonModNegEnergyEquality.lean` (`E(μ_n) = 3n²−3n`),
  `CubicSupplyCosetBridge.lean` (`T(G)² ≤ |G|·E(G)`),
  `DeepBandDeltaStarCeiling.lean` (the failure-side ceiling),
  `MCADeltaStarSandwich.lean` (the bracket-engine sandwich).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.SmallSubgroupDeltaStarPin

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.EnergyEqualitySidonModNeg

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-! ## Part 1 — the SHARP cubic supply pin from the EXACT energy -/

/-- **The sharp small-subgroup cubic-supply pin.**  For `n = 2^m` (`m ≥ 1`) and a prime
`p > 2^n` with a primitive `n`-th root `ω`, the zero-sum-triple count of `μ_n` obeys

  `zeroSumTriples (μ_n)² ≤ 3·n²·(n−1)`,

i.e. `T(μ_n) ≤ √3 · n · √(n−1) < √3 · n^{3/2}`.  This is the minimal cubic supply, derived
from the EXACT additive energy `E(μ_n) = 3n²−3n` through the in-tree Cauchy–Schwarz bridge
`T(G)² ≤ |G|·E(G)` — sharper than the `T² ≤ 3n³` bound from the inequality `E ≤ 3n²` by the
exact `3n²` correction.  Unconditional for `p > 2^n`. -/
theorem cubicSupply_sq_le_sharp (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    (zeroSumTriples (muN p n)) ^ 2 ≤ 3 * n ^ 2 * (n - 1) := by
  have hnpos : 0 < n := by rw [hn2]; positivity
  have hn1 : 1 ≤ n := hnpos
  -- membership predicate of μ_n
  have hGmem : ∀ z : ZMod p, z ∈ muN p n ↔ z ^ n = 1 := fun z => mem_muN hnpos z
  -- negation closure (n is even)
  have hneg : ∀ x ∈ muN p n, -x ∈ muN p n := by
    intro x hx
    rw [hGmem] at hx ⊢
    have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [neg_pow, he.neg_one_pow, one_mul]; exact hx
  -- card and exact energy
  have hcard : (muN p n).card = n := mu_n_card_eq hω
  have hE : additiveEnergy (muN p n) = 3 * n ^ 2 - 3 * n := mu_n_additiveEnergy_eq hn2 hm hp hω
  -- the in-tree Cauchy–Schwarz bridge: T(G)² ≤ |G|·E(G)
  have hCS : (zeroSumTriples (muN p n)) ^ 2 ≤ (muN p n).card * additiveEnergy (muN p n) :=
    zeroSumTriples_sq_le_card_energy_viaCoset hn1 hGmem hneg
  -- plug in card = n and E = 3n²−3n, then n·(3n²−3n) = 3n²(n−1)
  rw [hcard, hE] at hCS
  refine le_trans hCS ?_
  -- n·(3n²−3n) = 3n²(n−1) (natural-number subtraction, n ≥ 1)
  have hkey : n * (3 * n ^ 2 - 3 * n) = 3 * n ^ 2 * (n - 1) := by
    -- distribute both nat-subtractions, then match the subtraction-free factors
    rw [Nat.mul_sub, Nat.mul_sub, mul_one]
    congr 1 <;> ring
  rw [hkey]

open Classical in
/-- **The sharp cubic-word explainable-core supply pin** over a domain with image `μ_n`.
For any `dom : Fin n ↪ ZMod p` whose image is the 2-power NTT subgroup `μ_n`, the cubic word
`x ↦ x³` has explainable-3-core supply `S` with

  `S² ≤ 3·n²·(n−1)`,

i.e. `S ≤ √3 · n · √(n−1) ≪ n²`.  The Sylvester additive obstruction, `Θ(n²)` on the full
field, is pinned to `Θ(n^{3/2})` on the smooth NTT domain — UNCONDITIONALLY for `p > 2^n`
(the cyclotomic energy equality replaces the open Garcia–Voloch input). -/
theorem cubic_explainable_core_sq_le_sharp [NeZero n]
    (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    (dom : Fin n ↪ ZMod p) (hdom : Finset.image dom Finset.univ = muN p n) :
    (((Finset.univ.powersetCard 3).filter
        (fun T => ProximityGap.Ownership.ExplainableOn dom 2
          (ProximityGap.Cubic.cubicWord dom) T)).card) ^ 2
      ≤ 3 * n ^ 2 * (n - 1) := by
  -- S = sum-zero count ≤ zeroSumTriples(image) = zeroSumTriples(μ_n)
  have hStep : ((Finset.univ.powersetCard 3).filter
      (fun T => ProximityGap.Ownership.ExplainableOn dom 2
        (ProximityGap.Cubic.cubicWord dom) T)).card
      ≤ zeroSumTriples (muN p n) := by
    rw [ProximityGap.Cubic.cubicSupply_eq_sumZeroCard]
    have h := ProximityGap.Cubic.sumZeroCard_le_zeroSumTriples_image dom
    rwa [hdom] at h
  calc (((Finset.univ.powersetCard 3).filter
        (fun T => ProximityGap.Ownership.ExplainableOn dom 2
          (ProximityGap.Cubic.cubicWord dom) T)).card) ^ 2
      ≤ (zeroSumTriples (muN p n)) ^ 2 := Nat.pow_le_pow_left hStep 2
    _ ≤ 3 * n ^ 2 * (n - 1) := cubicSupply_sq_le_sharp hn2 hm hp hω

/-! ## Part 2 — the complete δ* pin: failure-side ceiling + named success-side list data -/

open ProximityGap ProximityGap.MCAThresholdLedger ProximityGap.PairRank
open ProximityGap.Ownership ProximityGap.SpikeFloor Code

/-- **Failure (upper) side of the small-subgroup δ\* pin.**  The proven deep-band ceiling
`mcaDeltaStar_le_of_deep_band`, specialized to the small-subgroup RS code: whenever the
closed-form deep-band failure count clears the `ε*` budget at band radius `(1−δ)n ≤ k+m'+1`,
the formal threshold is at most `δ`.  Verbatim re-export, no new hypotheses. -/
theorem smallSubgroup_deltaStar_le {q : ℕ} [Fact q.Prime] [NeZero n]
    (dom : Fin n ↪ ZMod q) {k m' : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m' + 1 : ℕ) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hnum : εstar * ((Fintype.card (ZMod q) : ℝ≥0∞)
        * (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m' + 1)).card
              / (Fintype.card (ZMod q)) ^ (m' + 1)
            + (k + m' + 1).choose (k + 1) * (n - (k + 1)).choose m' + 2) : ℝ≥0∞) ^ 2)
      < (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m' + 1)).card
          * (((Finset.univ : Finset (Fin n)).powersetCard (k + m' + 1)).card
              / (Fintype.card (ZMod q)) ^ (m' + 1)
            + (k + m' + 1).choose (k + 1) * (n - (k + 1)).choose m' + 2)
          / (Fintype.card (ZMod q)) ^ m') : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod q) (A := ZMod q)
        ((ProximityGap.SpikeFloor.rsCode dom k :
            Submodule (ZMod q) (Fin n → ZMod q)) : Set (Fin n → ZMod q)) εstar ≤ δ :=
  mcaDeltaStar_le_of_deep_band dom hk hhi εstar hnum

/-- **The success-side list hypothesis** for the small-subgroup δ* pin.  This is the open
beyond-Johnson list-decoding obligation, stated as an explicit named `Prop` (NOT proven —
issue #334 core A / [ABF26] §5): at the good radius `δgood`, the interleaved list of `C` at
the collapse floor has size `≤ L` for ALL word pairs `u₀, u₁`.  The minimal-energy / small
cubic-supply data (`cubicSupply_sq_le_sharp`) controls the canonical obstruction word; this
hypothesis packages the missing all-pairs upgrade. -/
def SmallSubgroupGoodList {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Finset (ι → F)) (δgood : ℝ≥0) (L : ℕ) : Prop :=
  ∀ u₀ u₁ : ι → F,
    (InterleavedMCACollapse.interleavedList C u₀ u₁
      (2 * ⌈(1 - δgood) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card ≤ L

/-- The named small-subgroup good-list hypothesis is monotone in the advertised list
budget.  This is the local packaging lemma for passing from a sharper producer bound to the
budget consumed by the δ* sandwich. -/
theorem SmallSubgroupGoodList.mono_L {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {C : Finset (ι → F)} {δgood : ℝ≥0} {L L' : ℕ}
    (h : SmallSubgroupGoodList C δgood L) (hLL : L ≤ L') :
    SmallSubgroupGoodList C δgood L' := by
  intro u₀ u₁
  exact le_trans (h u₀ u₁) hLL

/-- A producer form for `SmallSubgroupGoodList` from the natural doubled-radius floor
`⌈(1 - 2δ) n⌉₊`.  The in-tree floor bridge shows this floor is no larger than the O74
collapse floor used by the MCA dictionary, so antitonicity of the interleaved list transfers
the bound to the exact hypothesis expected by `smallSubgroup_deltaStar_pin`. -/
theorem SmallSubgroupGoodList.of_doubledRadius_bound {ι : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {C : Finset (ι → F)} {δgood : ℝ≥0} {L : ℕ}
    (hL : ∀ u₀ u₁ : ι → F,
      (InterleavedMCACollapse.interleavedList C u₀ u₁
        ⌈(1 - 2 * δgood) * (Fintype.card ι : ℝ≥0)⌉₊).card ≤ L) :
    SmallSubgroupGoodList C δgood L := by
  intro u₀ u₁
  exact le_trans
    (ProximityGap.interleavedList_card_anti C u₀ u₁
      (ProximityGap.ceil_doubled_radius_le (Fintype.card ι) δgood))
    (hL u₀ u₁)

/-- **The complete small-subgroup δ\* pin.**  Combining:
* the success (lower) side from the named list hypothesis `SmallSubgroupGoodList` together
  with the budget `(1 + (n − (2t − n))·L)/q ≤ ε*` (the LD⇒MCA dictionary
  `epsMCA_le_of_interleavedList_card_le` ∘ bracket), and
* the failure (upper) side from a deep-band bad family `G` of mass `ε* < |G|/q` at `δbad`,

the formal threshold of the small-subgroup RS code is pinned to the sandwich

  `δgood ≤ mcaDeltaStar C ε* ≤ δbad`.

The success-side input is the explicit literature obligation (named hypothesis); everything
else — the bracket engine, the dictionary, the bad-family transfer — is proven in-tree. -/
theorem smallSubgroup_deltaStar_pin {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Finset (ι → F)) (hC : Round17CAPair.PairClosed C) (εstar : ℝ≥0∞)
    {δgood δbad : ℝ≥0} (hδg : δgood ≤ 1) (L : ℕ)
    (hgood : SmallSubgroupGoodList C δgood L)
    (hε : ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δgood) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (u : WordStack F (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, ProximityGap.mcaEvent (↑C : Set (ι → F)) δbad (u 0) (u 1) γ)
    (hbad : εstar < (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    δgood ≤ mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar ∧
      mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar ≤ δbad :=
  mcaDeltaStar_sandwich C hC εstar hδg L hgood hε u G hG hbad

end ArkLib.ProximityGap.SmallSubgroupDeltaStarPin

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.SmallSubgroupDeltaStarPin.cubicSupply_sq_le_sharp
#print axioms ArkLib.ProximityGap.SmallSubgroupDeltaStarPin.cubic_explainable_core_sq_le_sharp
#print axioms ArkLib.ProximityGap.SmallSubgroupDeltaStarPin.smallSubgroup_deltaStar_le
#print axioms ArkLib.ProximityGap.SmallSubgroupDeltaStarPin.SmallSubgroupGoodList.mono_L
#print axioms ArkLib.ProximityGap.SmallSubgroupDeltaStarPin.SmallSubgroupGoodList.of_doubledRadius_bound
#print axioms ArkLib.ProximityGap.SmallSubgroupDeltaStarPin.smallSubgroup_deltaStar_pin
