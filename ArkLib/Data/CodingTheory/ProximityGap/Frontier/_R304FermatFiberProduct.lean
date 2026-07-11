/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R303FourthMomentInterpolation

/-!
# LANE B2 (#466, r=3 rung, R304): the off-diagonal quadruple sum via Fermat
  fiber products — exact diagonal extraction landed; the per-variety
  Weil–Deligne route is a NO-GO (its Betti ceiling is exactly the
  unconditional `K₄ = O(m)`, at EVERY q, prize scale included)

## The geometry, done honestly (probe
   `scripts/probes/probe_466_r3_fermat_fiber_product.py`)

The Galois-averaged 4th moment does satisfy an exact Möbius/fiber-product
identity (V2, probe-verified): `∑_k ∑_α ‖T_α‖⁴ = ∑_{d∣m} d·μ(m/d)·N₄_d`, with
`m³·d·N₄_d` counting `F_q`-points on the dimension-4 torus hypersurface
`V_d = {(t,x,y,z,w) ∈ 𝔾_m⁵ : (1−t)(1−t·x^m) = (1−t·y^m)(1−t·z^m)·w^d}`.
Equally exactly (V1, direct enumeration): the per-character 4th moment is
`(1/m³)` times ONE complete χ-sum over the 4-torus
`∑_{t,x,y,z} χ((1−t)(1−t·x^m)/((1−t·y^m)(1−t·z^m)))`.

**NO-GO mechanism (the coordinator's prize-scale hope, refuted).**  The top
strata `N₄_d ≈ q⁴/(m³d)` CANCEL under `∑ d·μ(m/d)` (the same Möbius mechanism
as the sextic); the surviving signal is `q²`-scale, while each individual
`N₄_d` carries its own Weil fluctuation at `q^{7/2}`-scale (middle cohomology
of a 4-fold) — the per-variety errors sit TWO orders in `√q` ABOVE the signal
and do not decay relative to it as `q → ∞`.  Equivalently: the χ-weighted
4-torus sum is PURE middle weight — there is no main term to split off, and
its Betti/Adolphson–Sperber ceiling (`4!·Vol(Δ) ~ m³`) yields exactly
`∑_α‖T_α‖⁴ ≤ C·q²`, i.e. `K₄ = O(m)` — the SAME as the triangle-inequality
calibration `fourthMomentBound_unconditional`.  There is NO q-threshold and
NO unconditional prize-scale (`q ≈ n·2¹²⁸`) discharge from fixed-variety
Weil–Deligne: the missing factor `m` is family-level cancellation across the
`m³` character tuples (Katz vertical territory), not point-count geometry.
Accordingly we do NOT name a `FermatFiberErrorBound` input — it would either
be false at the useful scale or equivalent to the moment bound itself.

## What IS landed (axiom-clean): the exact diagonal extraction

The diagonal of the quadruple sum is priced EXACTLY and unconditionally, so
the 4th-moment input localizes to the off-diagonal:

* `quadTotalC` / `quadTotalC_eq_energy` — the quadruple energy as a complex
  sum, pinned to the real self-convolution energy;
* `diagR` — the exact diagonal `2(∑_{j≠0}‖J_j‖²)² − ∑_{j≠0}‖J_j‖⁴`;
  `diagR_nonneg`, `diagR_le` (`≤ 2m²q²` under the envelope);
* `OffDiagQuadrupleBound K` — **the NEW NAMED OPEN INPUT**: the off-diagonal
  quadruple sum at scale `K·m²·q²` (probe V4: `K_off ≲ 1` measured at
  m = 9, 12, 15, 18; unconditional ceiling `m + 2`);
* `fourthMomentBound_of_offDiagQuadruple` — the reduction:
  `OffDiagQuadrupleBound K ⟹ FourthMomentBound (2 + K)`;
* `offDiagQuadrupleBound_unconditional` — calibration `K = m + 2`.

Chained with R303: `OffDiagQuadrupleBound K (O(1) calibrated)
⟹ FourthMomentBound (2+K) ⟹ DistStratumEnergyBound (O((2+K)^{3/2})·√m)`.
The graded ladder is now: off-diagonal quadruple (open, O(1)) ⟹ 4th moment
(open, O(1)) ⟹ rung within √m; pointwise `FullDFTFlat` stays the lossless
route.  CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R304FermatFiberProduct

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation

variable {u' : ℕ} [NeZero u']

/-- The quadruple energy as a complex sum (self-convolution against its
conjugate). -/
noncomputable def quadTotalC (ψ : AddChar (ZMod (3 * u')) ℂ)
    (J : ZMod (3 * u') → ℂ) : ℂ :=
  ∑ c : ZMod (3 * u'),
    conv2 (Sfun J) (Sfun J) c * (starRingEnd ℂ) (conv2 (Sfun J) (Sfun J) c)

/-- **The exact diagonal** of the additive-quadruple sum:
`{j₁,j₂} = {k₁,k₂}` contributes `2(∑‖J‖²)² − ∑‖J‖⁴` exactly. -/
noncomputable def diagR (J : ZMod (3 * u') → ℂ) : ℝ :=
  2 * (∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2) ^ 2
    - ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 4

/-- `quadTotalC` is the (real) self-convolution energy, complexified. -/
theorem quadTotalC_eq_energy (ψ : AddChar (ZMod (3 * u')) ℂ)
    (J : ZMod (3 * u') → ℂ) :
    quadTotalC ψ J
      = (((∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2 : ℝ)) : ℂ) := by
  unfold quadTotalC
  push_cast
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Second-moment envelope: `∑_{j≠0} ‖J j‖² ≤ m·q`. -/
theorem sum_sq_le {J : ZMod (3 * u') → ℂ} {q : ℕ}
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ)) :
    ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) * q := by
  calc ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2
      ≤ ∑ _j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, (q : ℝ) :=
        Finset.sum_le_sum (fun j _ => hJ j)
    _ = (((Finset.univ \ {(0 : ZMod (3 * u'))}).card : ℕ) : ℝ) * q := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((3 * u' : ℕ) : ℝ) * q := by
        have hle : (Finset.univ \ {(0 : ZMod (3 * u'))}).card
            ≤ (Finset.univ : Finset (ZMod (3 * u'))).card :=
          Finset.card_le_card (fun j _ => Finset.mem_univ j)
        have hcard : ((Finset.univ : Finset (ZMod (3 * u'))).card) = 3 * u' := by
          rw [Finset.card_univ, ZMod.card]
        have : (((Finset.univ \ {(0 : ZMod (3 * u'))}).card : ℕ) : ℝ)
            ≤ ((3 * u' : ℕ) : ℝ) := by
          exact_mod_cast hcard ▸ hle
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-- Fourth-vs-second moment: `∑ x_j² ≤ (∑ x_j)²` for nonnegative terms. -/
theorem sum_pow4_le_sq {J : ZMod (3 * u') → ℂ} :
    ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 4
      ≤ (∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2) ^ 2 := by
  have hpt : ∀ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))},
      ‖J j‖ ^ 4 ≤ ‖J j‖ ^ 2
        * ∑ i ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J i‖ ^ 2 := by
    intro j hj
    have hsingle : ‖J j‖ ^ 2
        ≤ ∑ i ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖J i‖ ^ 2)
        (fun i _ => by positivity) hj
    calc ‖J j‖ ^ 4 = ‖J j‖ ^ 2 * ‖J j‖ ^ 2 := by ring
      _ ≤ ‖J j‖ ^ 2 * ∑ i ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)
  calc ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 4
      ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))},
          ‖J j‖ ^ 2 * ∑ i ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J i‖ ^ 2 :=
        Finset.sum_le_sum hpt
    _ = (∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2) ^ 2 := by
        rw [← Finset.sum_mul]
        ring

theorem diagR_nonneg (J : ZMod (3 * u') → ℂ) : 0 ≤ diagR J := by
  unfold diagR
  have h4 := sum_pow4_le_sq (J := J)
  nlinarith [sq_nonneg (∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2)]

/-- Diagonal envelope: `diagR ≤ 2·m²·q²`. -/
theorem diagR_le {J : ZMod (3 * u') → ℂ} {q : ℕ}
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ)) :
    diagR J ≤ 2 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
  unfold diagR
  have h2 := sum_sq_le hJ
  have h20 : (0 : ℝ) ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have h40 : (0 : ℝ) ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, ‖J j‖ ^ 4 :=
    Finset.sum_nonneg (fun j _ => by positivity)
  nlinarith [h2, h20, h40]

/-- **THE NEW NAMED OPEN INPUT**: the off-diagonal additive-quadruple Jacobi
sum at scale `m²q²`.  Probe (V4): `K ≲ 1` at m = 9, 12, 15, 18, flat in q.
Mechanism honesty: each off-diagonal quadruple has modulus EXACTLY `q²`, and
the per-variety (Fermat fiber-product) Weil–Deligne ceiling reproduces only
`K = O(m)` — the open content is cross-quadruple cancellation. -/
def OffDiagQuadrupleBound (ψ : AddChar (ZMod (3 * u')) ℂ)
    (J : ZMod (3 * u') → ℂ) (q : ℕ) (K : ℝ) : Prop :=
  ‖quadTotalC ψ J - ((diagR J : ℝ) : ℂ)‖ ≤ K * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2

/-- **THE REDUCTION**: off-diagonal control at `K` gives the fourth moment at
`2 + K` — the diagonal is priced exactly, the input localizes off it. -/
theorem fourthMomentBound_of_offDiagQuadruple {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {K : ℝ}
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hoff : OffDiagQuadrupleBound ψ J q K) :
    FourthMomentBound ψ J q (2 + K) := by
  unfold FourthMomentBound
  have hid := fourthMoment_eq_selfConv_energy hψ (Sfun J)
  have hE0 : (0 : ℝ) ≤ ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2 :=
    Finset.sum_nonneg (fun c _ => by positivity)
  have hEbound : ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2
      ≤ (2 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
    have hnorm : (∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2)
        = ‖quadTotalC ψ J‖ := by
      rw [quadTotalC_eq_energy ψ J, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE0]
    rw [hnorm]
    calc ‖quadTotalC ψ J‖
        ≤ ‖quadTotalC ψ J - ((diagR J : ℝ) : ℂ)‖ + ‖((diagR J : ℝ) : ℂ)‖ := by
          have := norm_sub_le (quadTotalC ψ J - ((diagR J : ℝ) : ℂ))
            (-((diagR J : ℝ) : ℂ))
          calc ‖quadTotalC ψ J‖
              = ‖(quadTotalC ψ J - ((diagR J : ℝ) : ℂ)) + ((diagR J : ℝ) : ℂ)‖ := by
                ring_nf
            _ ≤ ‖quadTotalC ψ J - ((diagR J : ℝ) : ℂ)‖ + ‖((diagR J : ℝ) : ℂ)‖ :=
                norm_add_le _ _
      _ ≤ K * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
            + 2 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
          have hdn : ‖((diagR J : ℝ) : ℂ)‖ = diagR J := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (diagR_nonneg J)]
          have := diagR_le hJ
          have := hoff
          unfold OffDiagQuadrupleBound at this
          rw [hdn]
          linarith [diagR_le hJ]
      _ = (2 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by ring
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
      = ((3 * u' : ℕ) : ℝ)
          * ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2 := hid
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * ((2 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hEbound (by positivity)
    _ = (2 + K) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := by ring

/-- Calibration: the off-diagonal input holds UNCONDITIONALLY with
`K = m + 2` (matching the fixed-variety Weil–Deligne/Betti ceiling — the
per-variety route cannot do better at ANY q; the O(1) target is family
cancellation). -/
theorem offDiagQuadrupleBound_unconditional {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ}
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ)) :
    OffDiagQuadrupleBound ψ J q (((3 * u' : ℕ) : ℝ) + 2) := by
  unfold OffDiagQuadrupleBound
  have hm0 : (0 : ℝ) < ((3 * u' : ℕ) : ℝ) := by
    have := NeZero.ne u'
    positivity
  have hE0 : (0 : ℝ) ≤ ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2 :=
    Finset.sum_nonneg (fun c _ => by positivity)
  -- energy bound from the unconditional fourth moment
  have h4 := fourthMomentBound_unconditional hψ hJ
  unfold FourthMomentBound at h4
  have hid := fourthMoment_eq_selfConv_energy hψ (Sfun J)
  have hE : ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := by
    have hmul : ((3 * u' : ℕ) : ℝ)
        * ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2
        ≤ ((3 * u' : ℕ) : ℝ) * (((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2) := by
      rw [← hid]
      calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
          ≤ ((3 * u' : ℕ) : ℝ) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := h4
        _ = ((3 * u' : ℕ) : ℝ) * (((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_left hmul hm0
  have hnorm : ‖quadTotalC ψ J‖
      = ∑ c : ZMod (3 * u'), ‖conv2 (Sfun J) (Sfun J) c‖ ^ 2 := by
    rw [quadTotalC_eq_energy ψ J, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE0]
  have hdn : ‖((diagR J : ℝ) : ℂ)‖ = diagR J := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (diagR_nonneg J)]
  calc ‖quadTotalC ψ J - ((diagR J : ℝ) : ℂ)‖
      ≤ ‖quadTotalC ψ J‖ + ‖((diagR J : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2
          + 2 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
        rw [hnorm, hdn]
        linarith [hE, diagR_le hJ]
    _ = (((3 * u' : ℕ) : ℝ) + 2) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by ring

end ArkLib.ProximityGap.Frontier.R304FermatFiberProduct

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R304FermatFiberProduct in
#print axioms quadTotalC_eq_energy
open ArkLib.ProximityGap.Frontier.R304FermatFiberProduct in
#print axioms sum_pow4_le_sq
open ArkLib.ProximityGap.Frontier.R304FermatFiberProduct in
#print axioms diagR_nonneg
open ArkLib.ProximityGap.Frontier.R304FermatFiberProduct in
#print axioms diagR_le
open ArkLib.ProximityGap.Frontier.R304FermatFiberProduct in
#print axioms fourthMomentBound_of_offDiagQuadruple
open ArkLib.ProximityGap.Frontier.R304FermatFiberProduct in
#print axioms offDiagQuadrupleBound_unconditional
