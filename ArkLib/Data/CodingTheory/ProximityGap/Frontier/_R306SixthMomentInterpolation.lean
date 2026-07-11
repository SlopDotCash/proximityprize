/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R303FourthMomentInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R305FullDFTFlatCalibration

/-!
# LANE B2 (#466, r=3 rung, R306): sixth-moment interpolation — the LOG-ONLY
  rung: `FullDFTFlatLog A ∧ FourthMomentBound K₄ ⟹
  DistStratumEnergyBound (3·A·K₄·(1+log m) + 1215)`; the direct sixth-moment
  route is machine-checked CIRCULAR

## Circularity (formalized, `sixthMoment_eq_tripleConv_energy`)

`∑_a ‖f̂(a)‖⁶ = N·∑_c ‖(f⋆f⋆f)(c)‖²` — the sixth moment of the DFT IS the
full triple-convolution energy, i.e. (at `f = Sfun J`) precisely the r=3 core
object (R23 `TripleConvEnergyBound` up to zero-removals).  A direct
"SixthMomentBound" hypothesis is therefore NOT an input — it IS the target;
the Prop below is an INTERFACE, and its only honest sources are strictly
lower-order: the quartic moment + flatness.

## The log-only rung (probe
   `scripts/probes/probe_466_r3_sixth_moment.py`, m ≤ 1200)

Hölder: `∑‖Ŝ‖⁶ ≤ (sup‖Ŝ‖²)·∑‖Ŝ‖⁴ ≤ (B·mq)·(K₄·m³q²) = B·K₄·m⁴q³`.  With the
R305 Gumbel truth `B = A(1+log m)` and the R303/R304 quartic input
`K₄ = O(1)`, the R302 mode identity yields

  **`E_DIST ≤ (3·A·K₄·(1+log m) + 1215)·m³·q³`** — LOG-ONLY loss,

improving the R303 `√m` route and the R305 `log³` route at once.  Probe
verdicts: the direct sixth moment `K₆ = ∑‖Ŝ‖⁶/(m⁴q³)` is FLAT in m near the
complex-Gaussian value `6·((m−2)/m)³ → 6` (the average is Gumbel-immune —
only the sup carries the log), so the r=3 core truth has an ABSOLUTE
constant `≈ 3·K₆ + o(1) ≈ 20`, and the composed route overpays exactly the
measured `~0.8·log m` waste factor.

## Downstream tolerance (checked in-tree)

`TripleConvEnergyBound` and its whole consumer chain (R23 → R27:
`sextic_moment_of_tripleConvEnergyBound`, `sup_pureFace_…`, the pointwise
targets of R26) are stated with `C` a FREE parameter — the ladder is
log-tolerant at the formal level.  The R23 calibration comment (`C = 40`
comfortable) is numeric headroom: at any fixed prize modulus the factor
`(1 + log m)` is a concrete number (e.g. `log 2³⁰ ≈ 20.8`), so with the
probe-calibrated `A ≈ 1, K₄ ≈ 1–3` the composed constant sits at
`3·A·K₄·(1+log m) + 1215 ≈ O(10³)` — finite and explicit.  PRECISE STATUS:
the r=3 rung is now CLOSED MODULO the two named inputs
`FullDFTFlatLog A ∧ FourthMomentBound K₄`, with only a `(1+log m)` loss
against the absolute-constant form; the absolute form itself remains open
(= `OffDiagQuadrupleBound`/`FourthMomentBound` at `O(1)` PLUS removing the
sup, i.e. the interface Prop below at `O(1)` — which is the core verbatim).

CORE OPEN, ON-BGK.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation
open ArkLib.ProximityGap.Frontier.R305FullDFTFlatCalibration

/-! ### The circularity record -/

section Circularity

variable {N : ℕ} [NeZero N]

/-- **CIRCULARITY, MACHINE-CHECKED**: the sixth moment of the DFT is `N` times
the full triple-convolution energy — i.e. the r=3 core object itself.  A
"sixth-moment input" is the target, not an input. -/
theorem sixthMoment_eq_tripleConv_energy {ψ : AddChar (ZMod N) ℂ}
    (hψ : ψ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖hatF ψ f a‖ ^ 6
      = (N : ℝ) * ∑ c : ZMod N, ‖conv3 f f f c‖ ^ 2 := by
  have hpt : ∀ a : ZMod N, ‖hatF ψ f a‖ ^ 6 = ‖hatF ψ (conv3 f f f) a‖ ^ 2 := by
    intro a
    rw [hatF_conv3 ψ f f f a, norm_mul, norm_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a)]
  exact hatF_parseval hψ (conv3 f f f)

end Circularity

/-! ### The interface Prop and the two-input decomposition -/

section SixthMoment

variable {u' : ℕ} [NeZero u']

/-- **INTERFACE Prop (NOT an input — see the circularity theorem)**: the sixth
moment at Wick scale.  Probe: the truth is flat near the Gaussian value
`6((m−2)/m)³ → 6`; its only honest sources are the strictly-lower-order pair
`FullDFTFlatSq B ∧ FourthMomentBound K₄` below. -/
def SixthMomentBound (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (q : ℕ) (K₆ : ℝ) : Prop :=
  ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6
    ≤ K₆ * ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3

/-- **Hölder composition**: flatness budget `B` (pointwise) and quartic moment
`K₄` give the sixth moment at `B·K₄` — quartic + log-flat ⟹ sextic. -/
theorem sixthMomentBound_of_flatSq_and_fourth {ψ : AddChar (ZMod (3 * u')) ℂ}
    {J : ZMod (3 * u') → ℂ} {q : ℕ} {B K₄ : ℝ} (hB0 : 0 ≤ B)
    (hflat : FullDFTFlatSq ψ J q B)
    (h4 : FourthMomentBound ψ J q K₄) :
    SixthMomentBound ψ J q (B * K₄) := by
  unfold SixthMomentBound
  have hstep : ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6
      ≤ (B * ((3 * u' : ℕ) : ℝ) * q)
        * ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have h6 : ‖hatF ψ (Sfun J) a‖ ^ 6
        = ‖hatF ψ (Sfun J) a‖ ^ 2 * ‖hatF ψ (Sfun J) a‖ ^ 4 := by ring
    rw [h6]
    exact mul_le_mul_of_nonneg_right (hflat a) (by positivity)
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6
      ≤ (B * ((3 * u' : ℕ) : ℝ) * q)
          * ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4 := hstep
    _ ≤ (B * ((3 * u' : ℕ) : ℝ) * q)
          * (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (B * K₄) * ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3 := by ring

/-- **The sixth-moment consumer**: `SixthMomentBound K₆ ⟹
DistStratumEnergyBound (3·K₆ + 1215)` — the R302 mode identity with the
`P₂, P₃` slice terms priced unconditionally as before. -/
theorem distStratumEnergyBound_of_sixthMoment {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {K₆ : ℝ}
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (h6 : SixthMomentBound ψ J q K₆) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q (3 * K₆ + 1215) := by
  classical
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hm0 : (0 : ℝ) < ((3 * u' : ℕ) : ℝ) := by
    have := NeZero.ne u'
    positivity
  have hJroot : ∀ x, ‖J x‖ ≤ Real.sqrt (q : ℝ) := by
    intro x
    have h := Real.sqrt_le_sqrt (hJ x)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hsqq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hslice : ∀ (a : ZMod (3 * u')) (c : ZMod u'),
      ‖hatF ψ (slice J c) a‖ ≤ 3 * Real.sqrt (q : ℝ) :=
    fun a c => norm_hatSlice_le ψ (Real.sqrt_nonneg _) hJroot c a
  have hcardu : ((Finset.univ : Finset (ZMod u')).card : ℝ) = ((u' : ℕ) : ℝ) := by
    rw [Finset.card_univ, ZMod.card]
  have hmcast : ((3 * u' : ℕ) : ℝ) = 3 * ((u' : ℕ) : ℝ) := by push_cast; ring
  have hP2 : ∀ a : ZMod (3 * u'),
      ‖∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 2‖ ≤ 3 * ((3 * u' : ℕ) : ℝ) * q := by
    intro a
    calc ‖∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 2‖
        ≤ ∑ c : ZMod u', ‖(hatF ψ (slice J c) a) ^ 2‖ := norm_sum_le _ _
      _ ≤ ∑ _c : ZMod u', 9 * (q : ℝ) := by
          refine Finset.sum_le_sum (fun c _ => ?_)
          rw [norm_pow]
          calc ‖hatF ψ (slice J c) a‖ ^ 2
              ≤ (3 * Real.sqrt (q : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (hslice a c) 2
            _ = 9 * (q : ℝ) := by rw [mul_pow, hsqq]; norm_num
      _ = ((u' : ℕ) : ℝ) * (9 * q) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardu]
      _ = 3 * ((3 * u' : ℕ) : ℝ) * q := by rw [hmcast]; ring
  have hP3 : ∀ a : ZMod (3 * u'),
      ‖∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 3‖
        ≤ 9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ) := by
    intro a
    calc ‖∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 3‖
        ≤ ∑ c : ZMod u', ‖(hatF ψ (slice J c) a) ^ 3‖ := norm_sum_le _ _
      _ ≤ ∑ _c : ZMod u', 27 * (q : ℝ) * Real.sqrt (q : ℝ) := by
          refine Finset.sum_le_sum (fun c _ => ?_)
          rw [norm_pow]
          calc ‖hatF ψ (slice J c) a‖ ^ 3
              ≤ (3 * Real.sqrt (q : ℝ)) ^ 3 :=
                pow_le_pow_left₀ (norm_nonneg _) (hslice a c) 3
            _ = 27 * (q : ℝ) * Real.sqrt (q : ℝ) := by
                rw [mul_pow]
                rw [show (Real.sqrt (q : ℝ)) ^ 3
                    = (Real.sqrt (q : ℝ)) ^ 2 * Real.sqrt (q : ℝ) from by ring, hsqq]
                ring
      _ = ((u' : ℕ) : ℝ) * (27 * (q : ℝ) * Real.sqrt (q : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardu]
      _ = 9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ) := by rw [hmcast]; ring
  have hmode : ∀ a : ZMod (3 * u'),
      ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ 3 * ‖hatF ψ (Sfun J) a‖ ^ 6
          + 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 * ‖hatF ψ (Sfun J) a‖ ^ 2
          + 972 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 3 := by
    intro a
    set S : ℂ := hatF ψ (Sfun J) a with hSdef
    have hnorm : ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖
        ≤ ‖S‖ ^ 3 + 3 * ‖S‖ * (3 * ((3 * u' : ℕ) : ℝ) * q)
          + 2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ)) := by
      rw [hatF_distStratum, ← hatSfun_eq_sum_hatSlice ψ J a, ← hSdef]
      set P2 : ℂ := ∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 2 with hP2def
      set P3 : ℂ := ∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 3 with hP3def
      calc ‖S ^ 3 - 3 * S * P2 + 2 * P3‖
          ≤ ‖S ^ 3 - 3 * S * P2‖ + ‖2 * P3‖ := norm_add_le _ _
        _ ≤ (‖S ^ 3‖ + ‖3 * S * P2‖) + ‖2 * P3‖ := by
            have := norm_sub_le (S ^ 3) (3 * S * P2)
            linarith
        _ = ‖S‖ ^ 3 + 3 * (‖S‖ * ‖P2‖) + 2 * ‖P3‖ := by
            rw [norm_pow, norm_mul, norm_mul, norm_mul]
            simp only [Complex.norm_ofNat]
            ring
        _ ≤ ‖S‖ ^ 3 + 3 * ‖S‖ * (3 * ((3 * u' : ℕ) : ℝ) * q)
              + 2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ)) := by
            have h2 := hP2 a
            have h3 := hP3 a
            have hS0 : (0 : ℝ) ≤ ‖S‖ := norm_nonneg _
            nlinarith [mul_le_mul_of_nonneg_left h2 hS0]
    have hsq2 : ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ (‖S‖ ^ 3 + 3 * ‖S‖ * (3 * ((3 * u' : ℕ) : ℝ) * q)
            + 2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hCsq : (2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ))) ^ 2
        = 324 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 3 := by
      have : (2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ))) ^ 2
          = 324 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 * (Real.sqrt (q : ℝ)) ^ 2 := by
        ring
      rw [this, hsqq]
      ring
    nlinarith [hsq2, hCsq,
      sq_nonneg (‖S‖ ^ 3 - 3 * ‖S‖ * (3 * ((3 * u' : ℕ) : ℝ) * q)),
      sq_nonneg (‖S‖ ^ 3 - 2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ))),
      sq_nonneg (3 * ‖S‖ * (3 * ((3 * u' : ℕ) : ℝ) * q)
        - 2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ)))]
  have htwo : ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) ^ 2 * q := hatSfun_energy_le hψ hJ
  unfold DistStratumEnergyBound
  have hpars := distStratum_energy_spectral (u' := u') hψ J
  have htotal : ∑ a : ZMod (3 * u'),
      ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
      ≤ (3 * K₆ + 1215) * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) := by
    have hm4 : ((3 * u' : ℕ) : ℝ) ^ 3 ≤ ((3 * u' : ℕ) : ℝ) ^ 4 := by
      have hm1 : (1 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by
        have h1 : (1 : ℕ) ≤ 3 * u' := by have := NeZero.ne u'; omega
        exact_mod_cast h1
      exact pow_le_pow_right₀ hm1 (by norm_num)
    calc ∑ a : ZMod (3 * u'),
        ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ ∑ a : ZMod (3 * u'),
            (3 * ‖hatF ψ (Sfun J) a‖ ^ 6
              + 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 * ‖hatF ψ (Sfun J) a‖ ^ 2
              + 972 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 3) :=
          Finset.sum_le_sum (fun a _ => hmode a)
      _ = 3 * (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6)
            + 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
              * (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 2)
            + ((3 * u' : ℕ) : ℝ) * (972 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 3) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            ZMod.card]
      _ ≤ 3 * (K₆ * ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3)
            + 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
              * (((3 * u' : ℕ) : ℝ) ^ 2 * q)
            + 972 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
          have t1 := mul_le_mul_of_nonneg_left h6 (by norm_num : (0:ℝ) ≤ 3)
          have t2 := mul_le_mul_of_nonneg_left htwo
            (by positivity : (0:ℝ) ≤ 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2)
          have t3 : ((3 * u' : ℕ) : ℝ) * (972 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 3)
              = 972 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring
          unfold SixthMomentBound at t1
          linarith [t1, t2, t3.le, t3.ge]
      _ ≤ (3 * K₆ + 1215) * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) := by
          have e2 : 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
                * (((3 * u' : ℕ) : ℝ) ^ 2 * q)
              = 243 * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) := by ring
          have e3 : 972 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3
              ≤ 972 * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) := by
            have := mul_le_mul_of_nonneg_right hm4
              (by positivity : (0:ℝ) ≤ (q : ℝ) ^ 3)
            nlinarith [this]
          nlinarith [e2.le, e2.ge, e3]
  have hE : ((3 * u' : ℕ) : ℝ)
        * ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ)
        * ((3 * K₆ + 1215) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) := by
    rw [hpars]
    calc ∑ a : ZMod (3 * u'),
        ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ (3 * K₆ + 1215) * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) := htotal
      _ = ((3 * u' : ℕ) : ℝ)
            * ((3 * K₆ + 1215) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) := by ring
  have hfinal := le_of_mul_le_mul_left hE hm0
  calc ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ (3 * K₆ + 1215) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := hfinal

/-- **THE LOG-ONLY RUNG (headline)**: the Gumbel-consistent flatness input and
the O(1)-calibrated quartic input give the r=3 DIST rung with only a
`(1 + log m)` loss:
`E_DIST ≤ (3·A·K₄·(1+log m) + 1215)·m³·q³`.
At any fixed prize modulus this is a concrete finite constant. -/
theorem distStratumEnergyBound_of_flatLog_and_fourthMoment
    {ψ : AddChar (ZMod (3 * u')) ℂ} (hψ : ψ.IsPrimitive)
    {J : ZMod (3 * u') → ℂ} {q : ℕ} {A K₄ : ℝ} (hA0 : 0 ≤ A)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hflat : FullDFTFlatLog ψ J q A)
    (h4 : FourthMomentBound ψ J q K₄) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      (3 * (A * (1 + Real.log ((3 * u' : ℕ) : ℝ)) * K₄) + 1215) := by
  have hm1 : (1 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ 3 * u' := by have := NeZero.ne u'; omega
    exact_mod_cast h1
  have hlog0 : (0 : ℝ) ≤ Real.log ((3 * u' : ℕ) : ℝ) := Real.log_nonneg hm1
  have hB0 : (0 : ℝ) ≤ A * (1 + Real.log ((3 * u' : ℕ) : ℝ)) := by positivity
  have h6 := sixthMomentBound_of_flatSq_and_fourth hB0 hflat h4
  exact distStratumEnergyBound_of_sixthMoment hψ hJ h6

end SixthMoment

end ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation in
#print axioms sixthMoment_eq_tripleConv_energy
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation in
#print axioms sixthMomentBound_of_flatSq_and_fourth
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation in
#print axioms distStratumEnergyBound_of_sixthMoment
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation in
#print axioms distStratumEnergyBound_of_flatLog_and_fourthMoment
