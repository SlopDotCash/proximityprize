/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R298MixedDepthCorrelation

/-!
# LANE B2 (#466, r=3 rung, route ii, third brick): pattern stratification of the
  off-coset remainder — the (I2) pair-twist stratum is r=2-REDUCIBLE; the generic
  patterns are the irreducible carrier

## Probe verdicts (`scripts/probes/probe_466_r3_pattern_stratification.py`, exact,
   14 nondegenerate cells + fixed-m growth ladder to p = 181; 0 structural failures)

Partitioning ordered nonzero triples by the multiset of `H`-cosets
(`H = {0,u,2u}`, `u = m/3`):

* **mass census**: `FULL` (the R298-extracted diagonal) and `SAME3` carry ≤ 3% of
  the energy each; `TWO` (exactly two indices share a coset) and `DIST` (all
  distinct) carry essentially everything, each O(0.1–0.5)·Wick, FLAT in `p` along
  fixed `m` (square-root cancellation is numerically present in both classes —
  consistent with R23's O(1) total);
* **(HP1, exact)**: with `v = m/2` (the full order-2-subgroup offset, `2 ∣ m`,
  `χ²` nontrivial), the pair-twist stratum
  `S(d) = ∑_j J_j·J_{j+v}·J_{d−2j−v}` collapses EXACTLY to `κ₂·M(d)` with
  `κ₂ = χ(2)²·J(χ,χ)` (`‖κ₂‖ = √q`) and `M = (J₂ ⋆ J)` a MIXED DEPTH-(1,1)
  convolution (`J₂ = jacobiCoeff χ² lam`) — verified at every `d` in every cell;
  measured `∑‖M‖²/(m²q²) ≈ 1.0–1.9`, i.e. `M` is Wick-flat at the r=2-type scale;
* **refutation (no within-pattern collapse)**: the offset the `TWO` class would
  need is `u = m/3` (NOT a full order-2 coset); the candidate
  `J_j·J_{j+u} = c·J₂(2j+u)` with `j`-independent `c` FAILS with ratio spread
  O(q) in every tested cell.  HD pair rigidity lives exactly at the subgroup
  offset `m/2` and nowhere else.

## What this brick lands (all axiom-clean)

* `HDPairCollapse` — the named (I2) exact input (same classical HD source as
  R297's triple version; probe-verified);
* `pairTwistStratum` / `mixedConv` — the stratum and its depth-(1,1) shadow;
* `pairTwistStratum_collapse` — the EXACT collapse `S = κ₂·M` (unconditional
  given the named input);
* `pairTwistStratum_energy_eq` — exact energy transfer `∑‖S‖² = ‖κ₂‖²·∑‖M‖²`;
* `MixedConvEnergyBound` — the r=2-type named input at scale `C·m²·q²`
  (probe: `C ≈ 2` comfortable);
* `pairTwistStratum_energy_le` — the consumer: `∑‖S‖² ≤ K²·C·m²·q²`; at the
  classical `K = √q` this is `C·m²·q³ = (C/6m)·Wick` — every triple carrying an
  `m/2`-pair is REDUCIBLE TO THE r=2 RUNG (which is closed mod textbook Weil).

## Calibrated refutation / the corrected core

Every HD-type collapse available on the ladder is now spent: (I3) = the full
order-3 coset (R297/R298), (I2) = the full order-2 offset (this brick).  The
probe shows the remaining `TWO`/`DIST` pattern classes (a) carry ~all the
remainder energy, (b) admit NO constant-ratio HD collapse (offset-`u`
countermodel), and (c) are already numerically Wick-flat.  The minimal open
Prop for the r=3 rung stays `OffCosetRemainderEnergyBound` (R298), now with the
sharpened content: its mass is the generic-pattern (`TWO ∪ DIST`) triples, and
closing it requires genuinely analytic input (Katz route (i)) rather than
further exact HD structure.  CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R299PatternStratification

variable {m : ℕ} [NeZero m]

/-- **The named (I2) Hasse–Davenport pair collapse** (probe-verified exact identity;
classical instantiation: `J = jacobiCoeff χ lam`, `J₂ = jacobiCoeff (χ²) lam`,
`v = m/2`, `κ₂ = χ(2)²·J(χ,χ)` with `‖κ₂‖ = √q`, under `2 ∣ m`, `p ≠ 2`, `χ²`
nontrivial).  Same classical Gauss-sum product source as `HDCosetTripleCollapse`. -/
def HDPairCollapse (J J₂ : ZMod m → ℂ) (v : ZMod m) (κ₂ : ℂ) : Prop :=
  ∀ j : ZMod m, J j * J (j + v) = κ₂ * J₂ (2 * j)

/-- The index set of the `v`-pair-twist stratum at output `d`: pair anchor `j` with
all three triple coordinates nonzero (matching the `tripleConv` convention). -/
def pairIndex (m : ℕ) [NeZero m] (v d : ZMod m) : Finset (ZMod m) :=
  Finset.univ.filter (fun j => j ≠ 0 ∧ j + v ≠ 0 ∧ d - 2 * j - v ≠ 0)

/-- **The `v`-pair-twist stratum**: the sub-sum of triple products whose first two
coordinates form a `v`-pair, `(j, j+v, d−2j−v)`. -/
noncomputable def pairTwistStratum (J : ZMod m → ℂ) (v d : ZMod m) : ℂ :=
  ∑ j ∈ pairIndex m v d, J j * J (j + v) * J (d - 2 * j - v)

/-- **The mixed depth-(1,1) convolution shadow** of the stratum: `J₂` against `J`. -/
noncomputable def mixedConv (J₂ J : ZMod m → ℂ) (v d : ZMod m) : ℂ :=
  ∑ j ∈ pairIndex m v d, J₂ (2 * j) * J (d - 2 * j - v)

/-- **The exact collapse (probe identity HP1)**: under (I2), the pair-twist stratum
IS `κ₂` times the mixed convolution — depth 3 falls to depth (1,1). -/
theorem pairTwistStratum_collapse {J J₂ : ZMod m → ℂ} {v : ZMod m} {κ₂ : ℂ}
    (h : HDPairCollapse J J₂ v κ₂) (d : ZMod m) :
    pairTwistStratum J v d = κ₂ * mixedConv J₂ J v d := by
  unfold pairTwistStratum mixedConv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h j]
  ring

/-- **Exact energy transfer**: `∑_d ‖S(d)‖² = ‖κ₂‖²·∑_d ‖M(d)‖²`. -/
theorem pairTwistStratum_energy_eq {J J₂ : ZMod m → ℂ} {v : ZMod m} {κ₂ : ℂ}
    (h : HDPairCollapse J J₂ v κ₂) :
    ∑ d : ZMod m, ‖pairTwistStratum J v d‖ ^ 2
      = ‖κ₂‖ ^ 2 * ∑ d : ZMod m, ‖mixedConv J₂ J v d‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [pairTwistStratum_collapse h d, norm_mul, mul_pow]

/-- **The r=2-type named input**: mixed-convolution energy at the quartic Wick scale
`C·m²·q²` (probe calibration: ratio ≈ 1.0–1.9, so `C = 4` is comfortable).  This is
a depth-(1,1) object of the same analytic class as `SelfConvEnergyBound` (R23),
i.e. it belongs to the r=2 rung, which is closed mod textbook Weil. -/
def MixedConvEnergyBound (J₂ J : ZMod m → ℂ) (v : ZMod m) (q : ℕ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, ‖mixedConv J₂ J v d‖ ^ 2 ≤ C * (m : ℝ) ^ 2 * (q : ℝ) ^ 2

/-- **Consumer: the pair-twist stratum is r=2-reducible.**  Under (I2) with
`‖κ₂‖ ≤ K` and the mixed r=2-type input, `∑_d‖S(d)‖² ≤ K²·C·m²·q²`.  At the
classical `K = √q` (so `K² = q`) this is `C·m²·q³` — a `1/m`-fraction of the r=3
Wick budget, supplied entirely by r=2-class inputs. -/
theorem pairTwistStratum_energy_le {J J₂ : ZMod m → ℂ} {v : ZMod m} {κ₂ : ℂ}
    {K C : ℝ} {q : ℕ} (h : HDPairCollapse J J₂ v κ₂) (hκ : ‖κ₂‖ ≤ K)
    (hM : MixedConvEnergyBound J₂ J v q C) :
    ∑ d : ZMod m, ‖pairTwistStratum J v d‖ ^ 2
      ≤ K ^ 2 * (C * (m : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
  rw [pairTwistStratum_energy_eq h]
  have hκ2 : ‖κ₂‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hκ 2
  have hMnn : (0 : ℝ) ≤ ∑ d : ZMod m, ‖mixedConv J₂ J v d‖ ^ 2 :=
    Finset.sum_nonneg (fun d _ => sq_nonneg _)
  calc ‖κ₂‖ ^ 2 * ∑ d : ZMod m, ‖mixedConv J₂ J v d‖ ^ 2
      ≤ K ^ 2 * ∑ d : ZMod m, ‖mixedConv J₂ J v d‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hκ2 hMnn
    _ ≤ K ^ 2 * (C * (m : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
        have hK2 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg _
        exact mul_le_mul_of_nonneg_left hM hK2

end ArkLib.ProximityGap.Frontier.R299PatternStratification

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R299PatternStratification in
#print axioms pairTwistStratum_collapse
open ArkLib.ProximityGap.Frontier.R299PatternStratification in
#print axioms pairTwistStratum_energy_eq
open ArkLib.ProximityGap.Frontier.R299PatternStratification in
#print axioms pairTwistStratum_energy_le
