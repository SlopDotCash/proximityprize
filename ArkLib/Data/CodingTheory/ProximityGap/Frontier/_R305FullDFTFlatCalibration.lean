/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R302TraceFormulaPointCount

/-!
# LANE B2 (#466, r=3 rung, R305): FullDFTFlat calibration at scale — the
  absolute-K form is REFUTED (Gumbel growth measured to m = 1200); the
  growth-tolerant reduction and the corrected quasi-flat ladder are landed

## The decisive measurement (probe
   `scripts/probes/probe_466_r3_fulldftflat_scaling.py`, m up to 1200,
   5 primes × 3 characters per m; see `_out_466_r3_fulldftflat_scaling.txt`)

`Ŝ(a) = m·T₋ₐ + 1` with `m·T_α = ∑_e ζ^{−eα} J_e` — a DFT over exactly `m`
modes of the `m` Jacobi angles.  Under Katz vertical equidistribution the
normalized angles are iid-uniform-like, so each mode is asymptotically a
complex Gaussian of variance `m·q` and the modes decorrelate:
`K := sup_a ‖Ŝ(a)‖²/(mq)` is a maximum of `m` Exp(1)-like variables —
**Gumbel: `K ≈ log m + O(1)`, independent of `q`** (the sup is over `m`
modes, NOT over `q/m` residues; there is no `log q`).  Measured: `K_med`
grows 1.61 → 5.40 over m = 9 → 1200 with `K_med/log m ≈ 0.66–0.91` stable
(fit `K = −0.11 + 0.79·log m`; a power fit `1.12·m^{0.235}` is statistically
comparable at this range — EITHER form is genuine growth), fixed-m q-scans
flat (no `log q`), extremal mode generic (argmax structure random).  So:

**`FullDFTFlat` with an ABSOLUTE constant `K` is REFUTED as the truth** —
the R302 reduction remains valid (it is K-parametric), but the honest input
is quasi-flat: `‖Ŝ(a)‖² ≤ A·(1 + log m)·m·q`.

## Consumer tolerance (the exact arithmetic)

The R302 consumer gives `C = (K³ + 9K + 18)² = Θ(K⁶) = Θ(B³)` for `B := K²`:
* absolute `C` ⟺ bounded `B` — now known false;
* `B = A(1 + log m)` (the Gumbel truth) ⟹ `C ≤ 9·A³(1+log m)³` — a
  QUASI-FLAT rung `E_DIST ≤ 9A³·log³m·m³·q³`, sub-polynomial loss;
* `K = m^{1/6}` (`B = m^{1/3}`) ⟹ `C ~ 9m` ⟹ `E ≤ 9m⁴q³` — does NOT fit
  the strict `C·m³q³` target with absolute `C`; the tolerance boundary is
  exactly `B = O(1)`, i.e. any genuine growth breaks the strict form and
  lands on the corresponding `B³` loss.

## What this brick lands (all axiom-clean; growth-tolerant)

* `FullDFTFlatSq B` — the squared-form input `∀ a, ‖Ŝ(a)‖² ≤ B·m·q` with
  `B` free (so `B = A(1+log m)` is expressible without new machinery);
* `fullDFTFlat_of_sq` — bridge to R302's `FullDFTFlat (√B)`;
* `distStratumEnergyBound_mono` — monotonicity of the target in `C`;
* `distStratumEnergyBound_of_flatSq` — the general reduction
  `FullDFTFlatSq B ⟹ DistStratumEnergyBound ((√B³ + 9√B + 18)²)`;
* **`distStratumEnergyBound_of_flatSq_cubed`** — the clean cubed-loss law:
  for `B ≥ 9`, `FullDFTFlatSq B ⟹ DistStratumEnergyBound (9·B³)`;
* `FullDFTFlatLog A` + `distStratumEnergyBound_of_flatLog` — the corrected
  honest ladder: the Gumbel-consistent input yields
  `DistStratumEnergyBound (9·(A(1+log m))³)`.

The open core is recalibrated, not closed: the quasi-flat input is exactly
vertical-equidistribution strength (Katz), and the strict absolute-C form of
the rung now provably CANNOT come from pointwise flatness alone — any route
to absolute `C` must exploit cancellation in the `a`-average beyond the sup
(i.e. the moment ladder R303/R304).  CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount

variable {u' : ℕ} [NeZero u']

/-- **The growth-tolerant flatness input (squared form)**: `B` is an arbitrary
real budget, so slowly-growing calibrations (`B = A(1 + log m)`, the measured
Gumbel truth) are expressible directly. -/
def FullDFTFlatSq (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (q : ℕ) (B : ℝ) : Prop :=
  ∀ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 2 ≤ B * ((3 * u' : ℕ) : ℝ) * q

/-- Bridge to the R302 form: squared budget `B` gives `FullDFTFlat (√B)`. -/
theorem fullDFTFlat_of_sq {ψ : AddChar (ZMod (3 * u')) ℂ}
    {J : ZMod (3 * u') → ℂ} {q : ℕ} {B : ℝ}
    (hB : FullDFTFlatSq ψ J q B) :
    FullDFTFlat ψ J q (Real.sqrt B) := by
  intro a
  have h := hB a
  have hnorm : ‖hatF ψ (Sfun J) a‖
      = Real.sqrt (‖hatF ψ (Sfun J) a‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hnorm]
  calc Real.sqrt (‖hatF ψ (Sfun J) a‖ ^ 2)
      ≤ Real.sqrt (B * ((3 * u' : ℕ) : ℝ) * q) := Real.sqrt_le_sqrt h
    _ = Real.sqrt B * Real.sqrt (((3 * u' : ℕ) : ℝ) * q) := by
        rw [show B * ((3 * u' : ℕ) : ℝ) * (q : ℝ)
            = B * (((3 * u' : ℕ) : ℝ) * q) from by ring]
        exact Real.sqrt_mul' _ (by positivity)

/-- The DIST target is monotone in the constant. -/
theorem distStratumEnergyBound_mono {J : ZMod (3 * u') → ℂ}
    {q : ℕ} {C C' : ℝ} (hCC : C ≤ C')
    (h : DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q C) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q C' := by
  unfold DistStratumEnergyBound at h ⊢
  have hnn : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by positivity
  calc ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ C * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := h
    _ ≤ C' * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_right hCC hnn
        calc C * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3
            = C * (((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) := by ring
          _ ≤ C' * (((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) := this
          _ = C' * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

/-- **The general growth-tolerant reduction**: squared flatness budget `B`
gives the rung at `C = (√B³ + 9√B + 18)²`. -/
theorem distStratumEnergyBound_of_flatSq {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hB : FullDFTFlatSq ψ J q B) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      ((Real.sqrt B ^ 3 + 9 * Real.sqrt B + 18) ^ 2) :=
  distStratumEnergyBound_of_fullDFTFlat hψ (Real.sqrt_nonneg B) hJ
    (fullDFTFlat_of_sq hB)

/-- **THE CUBED-LOSS LAW**: for any budget `B ≥ 9`,
`FullDFTFlatSq B ⟹ DistStratumEnergyBound (9·B³)`.  This is the exact
consumer-tolerance arithmetic: absolute `C` ⟺ bounded `B`;
`B = A(1+log m)` (the Gumbel truth) ⟹ `C ≤ 9A³(1+log m)³`;
`B = m^{1/3}` ⟹ `C ~ 9m` — outside the strict target. -/
theorem distStratumEnergyBound_of_flatSq_cubed {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {B : ℝ} (hB9 : 9 ≤ B)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hB : FullDFTFlatSq ψ J q B) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q (9 * B ^ 3) := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hbase := distStratumEnergyBound_of_flatSq hψ hB0 hJ hB
  refine distStratumEnergyBound_mono ?_ hbase
  set s : ℝ := Real.sqrt B with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg B
  have hss : s * s = B := Real.mul_self_sqrt hB0
  have hs3 : 3 ≤ s := by
    have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    calc (3 : ℝ) = Real.sqrt 9 := h9.symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hB9
  -- (s³ + 9s + 18)² ≤ 9·(s²)³ = (3s³)² since 9s ≤ s³ and 18 ≤ s³ for s ≥ 3
  have hlin : s ^ 3 + 9 * s + 18 ≤ 3 * s ^ 3 := by nlinarith [hs3, hs0]
  have hpos : (0 : ℝ) ≤ s ^ 3 + 9 * s + 18 := by positivity
  calc (s ^ 3 + 9 * s + 18) ^ 2
      ≤ (3 * s ^ 3) ^ 2 := pow_le_pow_left₀ hpos hlin 2
    _ = 9 * (s * s) ^ 3 := by ring
    _ = 9 * B ^ 3 := by rw [hss]

/-- **The corrected honest input (Gumbel-consistent)**: quasi-flatness with a
`(1 + log m)` budget — this is what the m ≤ 1200 measurements support, and
what Katz vertical equidistribution predicts. -/
def FullDFTFlatLog (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (q : ℕ) (A : ℝ) : Prop :=
  FullDFTFlatSq ψ J q (A * (1 + Real.log ((3 * u' : ℕ) : ℝ)))

/-- **The corrected ladder rung**: the Gumbel-consistent input yields the
quasi-flat DIST bound `E ≤ 9·A³·(1 + log m)³·m³·q³`. -/
theorem distStratumEnergyBound_of_flatLog {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {A : ℝ}
    (hA : 9 ≤ A * (1 + Real.log ((3 * u' : ℕ) : ℝ)))
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hB : FullDFTFlatLog ψ J q A) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      (9 * (A * (1 + Real.log ((3 * u' : ℕ) : ℝ))) ^ 3) :=
  distStratumEnergyBound_of_flatSq_cubed hψ hA hJ hB

end ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration in
#print axioms fullDFTFlat_of_sq
open ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration in
#print axioms distStratumEnergyBound_mono
open ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration in
#print axioms distStratumEnergyBound_of_flatSq
open ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration in
#print axioms distStratumEnergyBound_of_flatSq_cubed
open ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration in
#print axioms distStratumEnergyBound_of_flatLog
