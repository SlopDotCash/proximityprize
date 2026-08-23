/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26AlignmentSupply
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction

/-!
# The census-domination weld: the deployed `δ*` pin from ONE combinatorial Prop (#371)

`kkh26_deltaStar_pin_of_interior_ceiling` pins `δ* = 1 − r/2^μ` from `InteriorCeiling`;
the universal alignment law turned every band of `InteriorCeiling` into an alignable-set
census.  This file welds the two: the named Prop

  **`CensusDomination dom k a₀ K`** — every stack has at most `K` alignable `a`-sets at
  every band `a ≥ a₀`

implies `InteriorCeiling` (`interiorCeiling_of_censusDomination`), hence

  **`kkh26_deltaStar_pin_of_censusDomination`**: `δ* = 1 − r/2^μ` **exactly**, conditional
  on `CensusDomination` alone (with `K/p ≤ ε*`).

This is the $1M obligation in its final in-tree normal form: one combinatorial statement
about divided-difference pencil alignment, whose supply half is realized exactly by the
KKH26 fibre family (`KKH26AlignmentSupply`) and whose empirical truth at small scales is
on record (`probe_alignment_census.py`, `probe_deep_extremal_search.py`).  Also includes
the `evalCode ↔ rsCode` bridge (`evalCode_eq_rsCode`), reconciling the KKH26 ceiling files
with the alignment-law substrate.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction ProximityGap.SpikeFloor

namespace ProximityGap.Ownership

variable {p : ℕ} [Fact p.Prime]

/-- **The `evalCode ↔ rsCode` bridge**: the KKH26 degree-`≤ d` evaluation code is the
generic Reed–Solomon code of dimension `d + 1` on the smooth domain embedding. -/
theorem evalCode_eq_rsCode {g : ZMod p} {n : ℕ} [NeZero n] (hg : orderOf g = n) (d : ℕ) :
    evalCode g n d
      = ((rsCode (smoothDom g n hg) (d + 1) :
          Submodule (ZMod p) (Fin n → ZMod p)) : Set (Fin n → ZMod p)) := by
  ext w
  constructor
  · rintro ⟨q, hq, hw⟩
    refine ⟨q, ?_, funext hw⟩
    by_cases hq0 : q = 0
    · subst hq0
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (Polynomial.natDegree_lt_iff_degree_lt hq0).mp (by omega)
  · rintro ⟨P, hP, rfl⟩
    refine ⟨P, ?_, fun i => rfl⟩
    by_cases hP0 : P = 0
    · subst hP0
      simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
      omega

open Classical in
/-- **THE CENSUS-DOMINATION PROP** — the $1M obligation in census normal form: every
stack has at most `K` alignable `a`-sets at every band `a ≥ a₀`. -/
def CensusDomination {n : ℕ} [NeZero n] (dom : Fin n ↪ ZMod p) (k a₀ K : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → ZMod p, ∀ a : ℕ, a₀ ≤ a →
    ((Finset.univ.powersetCard a).filter (fun S : Finset (Fin n) =>
      ∃ γ : ZMod p, Aligned dom k u₀ u₁ γ S ∧
        ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
          ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))).card ≤ K

open Classical in
/-- **The band-split assembly**: census domination at all bands `a ≥ rm + 1` gives the
interior ceiling — each radius below the ceiling lands in some deep band, where the
universal census bound caps the bad count by the alignable supply. -/
theorem interiorCeiling_of_censusDomination
    {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r) {n : ℕ} (hn : n = 2 ^ μ * m)
    [NeZero n] {g : ZMod p} (hg : orderOf g = n) {K : ℕ} (εstar : ℝ≥0∞)
    (hK : (K : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hdom : CensusDomination (smoothDom g n hg) ((r - 2) * m + 1) (r * m + 1) K) :
    InteriorCeiling p n g μ m r εstar := by
  intro δ hδ
  rw [show evalCode g n ((r - 2) * m)
      = ((rsCode (smoothDom g n hg) ((r - 2) * m + 1) :
          Submodule (ZMod p) (Fin n → ZMod p)) : Set (Fin n → ZMod p)) from
    evalCode_eq_rsCode hg ((r - 2) * m)]
  -- the agreement mass exceeds rm
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsum : δ + ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < 1 := lt_tsub_iff_right.mp hδ
  have hlt : ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < 1 - δ := by
    rw [lt_tsub_iff_right]
    calc ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) + δ
        = δ + ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by ring
    _ < 1 := hsum
  have hcn : ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) * ((n : ℕ) : ℝ≥0)
      = ((r * m : ℕ) : ℝ≥0) := by
    have h2 : ((2 : ℝ≥0) ^ μ) ≠ 0 := by positivity
    rw [hn]
    push_cast
    field_simp
  have hrm : ((r * m : ℕ) : ℝ≥0) < (1 - δ) * ((n : ℕ) : ℝ≥0) := by
    rw [← hcn]
    refine mul_lt_mul_of_pos_right hlt ?_
    exact_mod_cast hn0
  -- the band index
  set a : ℕ := ⌈(1 - δ) * ((n : ℕ) : ℝ≥0)⌉₊ with hadef
  have ha_ge : r * m + 1 ≤ a := Nat.lt_ceil.mpr hrm
  have ha_hhi : (1 - δ) * ((n : ℕ) : ℝ≥0) ≤ (a : ℕ) := Nat.le_ceil _
  have ha_hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * ((n : ℕ) : ℝ≥0) := by
    rw [← Nat.lt_ceil, ← hadef]
    omega
  have hka : (r - 2) * m + 1 + 1 ≤ a := by
    have : (r - 2) * m + 2 ≤ r * m + 1 := by
      have h1 : (r - 2) * m + 2 * m ≤ r * m := by
        rw [← Nat.add_mul]
        exact Nat.mul_le_mul_right m (by omega)
      omega
    omega
  -- the per-stack census cap
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  refine le_trans ?_ hK
  unfold epsMCA
  refine iSup_le fun u => ?_
  classical
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have hcount := badScalars_card_le_alignable (smoothDom g n hg)
    (k := (r - 2) * m + 1) (a := a) (by omega) hka
    (by rw [Fintype.card_fin]; exact ha_hlo) (by rw [Fintype.card_fin]; exact ha_hhi)
    (u 0) (u 1)
  have hcap := hdom (u 0) (u 1) a (by omega)
  exact_mod_cast le_trans hcount hcap

open Classical in
/-- **THE WELD: the deployed `δ*` pin from census domination alone.**  Granting the one
combinatorial Prop, `δ* = 1 − r/2^μ` exactly. -/
theorem kkh26_deltaStar_pin_of_censusDomination
    {n : ℕ} [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    {K : ℕ} (hK : (K : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hdom : CensusDomination (smoothDom g n (hn ▸ hg)) ((r - 2) * m + 1) (r * m + 1) K) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  kkh26_deltaStar_pin_of_interior_ceiling hμ hm hn hg hp hr2 hr εstar hεstar
    (interiorCeiling_of_censusDomination hμ hm hr2 hn (hn ▸ hg) εstar hK hdom)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.evalCode_eq_rsCode
#print axioms ProximityGap.Ownership.interiorCeiling_of_censusDomination
#print axioms ProximityGap.Ownership.kkh26_deltaStar_pin_of_censusDomination
