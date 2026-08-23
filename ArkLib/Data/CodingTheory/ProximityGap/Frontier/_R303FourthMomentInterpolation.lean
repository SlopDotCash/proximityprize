/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R302TraceFormulaPointCount

/-!
# LANE B2 (#466, r=3 rung, R303): fourth-moment interpolation — the DIST rung
  within a `√m` loss from ONE fourth-moment bound; the 4th moment IS the r=2
  additive-quadruple energy, and its main term SURVIVES the Möbius cancellation

## Scale correction (probe `scripts/probes/probe_466_r3_fourth_moment.py`,
   m = 9, 12, 15, 18, all primes ≤ 1200, per character and Galois-max)

The proposed target `∑_a ‖Ŝ(a)‖⁴ ≤ K₄·m²·q²` is IMPOSSIBLE: Parseval pins
`∑_a ‖Ŝ(a)‖² ≈ m²q`, so power-mean forces `∑_a ‖Ŝ‖⁴ ≥ (m²q)²/m = m³q²`, and
the EXACT diagonal (`{j₁,j₂} = {k₁,k₂}` additive quadruples) contributes
`≈ 2(1−2/m)²·m³q²`.  The correct flat scale is `K₄·m³·q²`, and the probe
measures `K₄ ∈ [0.67, 3.2]` across all four m — bounded, flat in q.

## Main-term structure (the coordinator's Möbius question, resolved)

Unlike the sextic (R302: `∑_{d∣m} μ(m/d) = 0`, pure error term), at the 4th
moment the surviving main term is the DIAGONAL, whose ratio is exactly 1 ∈
`(F_q^*)^d` for EVERY `d`, so its Möbius weight is `∑_{d∣m} d·μ(m/d) = φ(m) ≠ 0`
— the main term survives.  Exact identity (F1, probe-verified to machine
precision at all four m, and FORMALIZED below):

  `∑_a ‖Ŝ(a)‖⁴ = m · ∑_c ‖(Sfun J ⋆ Sfun J)(c)‖²`

— the fourth moment IS the r=2 zero-removed self-convolution energy
(additive-quadruple Jacobi sum).  Its off-diagonal is a signed sum of `~m³`
unit-modulus-`q²` Jacobi phase products; each term has modulus EXACTLY `q²`,
so there is NO per-tuple Weil saving — the open content of the 4th-moment
bound is cancellation ACROSS quadruples (a strictly WEAKER demand than
per-mode flatness).  Accordingly we do NOT name a per-tuple-Weil input (cf.
the refuted per-tuple class in DISPROOF_LOG); the honest named input is the
moment bound itself, `FourthMomentBound`, calibrated three ways below.

## What this brick lands (all axiom-clean)

* `conv2` / `hatF_conv2` — the DFT diagonalizes the 2-fold convolution;
* `fourthMoment_eq_selfConv_energy` — **the exact F1 identity** (unconditional);
* `FourthMomentBound K₄` — the NEW NAMED OPEN INPUT at the correct scale
  `∑_a ‖Ŝ(a)‖⁴ ≤ K₄·m³·q²`; probe: `K₄ ≤ 3.2` at m ≤ 18, diagonal floor ≈ 2;
* `fourthMomentBound_of_fullDFTFlat` — hierarchy: flatness `K` ⟹ `K₄ = K⁴`
  (the 4th moment is strictly weaker than R302's `FullDFTFlat`);
* `fourthMomentBound_unconditional` — calibration: `K₄ = m` always holds;
* `sum_cube_le_sqrt_mul` — the ℓ³-vs-ℓ² interpolation inequality;
* **`distStratumEnergyBound_of_fourthMoment`** (main theorem): the
  interpolated rung —
  `FourthMomentBound K₄ ⟹ DistStratumEnergyBound ((3·K₄·√K₄ + 1215)·√m)`,
  i.e. `E_DIST ≤ C(K₄)·√m·m³·q³` — the full rung within a `√m` loss from one
  O(1)-calibrated fourth-moment bound (vs the lossless reduction from the
  pointwise `FullDFTFlat`).  With the unconditional `K₄ = m` this recovers the
  `m^{5/2}`-type envelope, strictly between trivial (`m²`) routes and flat.

CORE OPEN, ON-BGK.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount

/-! ### The 2-fold convolution and the fourth-moment identity -/

section GenericDFT2

variable {N : ℕ} [NeZero N]

/-- Two-fold additive convolution on `ZMod N`. -/
noncomputable def conv2 (f g : ZMod N → ℂ) (c : ZMod N) : ℂ :=
  ∑ j : ZMod N, f j * g (c - j)

/-- **The DFT diagonalizes `conv2`**: `(f⋆g)^(a) = f̂(a)·ĝ(a)`. -/
theorem hatF_conv2 (ψ : AddChar (ZMod N) ℂ) (f g : ZMod N → ℂ) (a : ZMod N) :
    hatF ψ (conv2 f g) a = hatF ψ f a * hatF ψ g a := by
  unfold hatF conv2
  calc ∑ c : ZMod N, ψ (a * c) * ∑ j : ZMod N, f j * g (c - j)
      = ∑ c : ZMod N, ∑ j : ZMod N, ψ (a * c) * (f j * g (c - j)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ j : ZMod N, ∑ c : ZMod N, ψ (a * c) * (f j * g (c - j)) := Finset.sum_comm
    _ = ∑ j : ZMod N, ∑ y : ZMod N, (ψ (a * j) * f j) * (ψ (a * y) * g y) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine (Fintype.sum_bijective (fun y : ZMod N => y + j)
          (Equiv.addRight j).bijective
          (fun y => (ψ (a * j) * f j) * (ψ (a * y) * g y))
          (fun c => ψ (a * c) * (f j * g (c - j))) (fun y => ?_)).symm
        show (ψ (a * j) * f j) * (ψ (a * y) * g y)
            = ψ (a * (y + j)) * (f j * g (y + j - j))
        have hy : (y : ZMod N) + j - j = y := by ring
        have hsplit : a * (y + j) = a * y + a * j := by ring
        rw [hy, hsplit, map_add_eq_mul]
        ring
    _ = (∑ x : ZMod N, ψ (a * x) * f x) * (∑ x : ZMod N, ψ (a * x) * g x) := by
        rw [Finset.sum_mul_sum]

/-- **THE FOURTH-MOMENT IDENTITY (F1)**: the 4th moment of the DFT is the
self-convolution energy — the r=2 additive-quadruple structure, whose diagonal
main term survives Möbius (weight `φ(m)`), unlike the sextic. -/
theorem fourthMoment_eq_selfConv_energy {ψ : AddChar (ZMod N) ℂ}
    (hψ : ψ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖hatF ψ f a‖ ^ 4 = (N : ℝ) * ∑ c : ZMod N, ‖conv2 f f c‖ ^ 2 := by
  have hpt : ∀ a : ZMod N, ‖hatF ψ f a‖ ^ 4 = ‖hatF ψ (conv2 f f) a‖ ^ 2 := by
    intro a
    rw [hatF_conv2 ψ f f a, norm_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a)]
  exact hatF_parseval hψ (conv2 f f)

end GenericDFT2

/-! ### The named input, its calibration, and the hierarchy -/

section FourthMoment

variable {u' : ℕ} [NeZero u']

/-- **THE NAMED OPEN INPUT (correct scale)**: the fourth moment of the
zero-removed Jacobi DFT at the flat/diagonal scale `m³q²`.  The `m²q²` scale is
IMPOSSIBLE (power-mean + Parseval); the diagonal forces `K₄ ⪆ 2`; probe:
`K₄ ≤ 3.2` at m = 9, 12, 15, 18, flat in q.  Strictly weaker than
`FullDFTFlat` (see the hierarchy lemma). -/
def FourthMomentBound (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (q : ℕ) (K₄ : ℝ) : Prop :=
  ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
    ≤ K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2

/-- Hierarchy: pointwise flatness at `K` gives the fourth moment at `K⁴` —
`FourthMomentBound` is (at most as strong as) `FullDFTFlat`. -/
theorem fourthMomentBound_of_fullDFTFlat {ψ : AddChar (ZMod (3 * u')) ℂ}
    {J : ZMod (3 * u') → ℂ} {q : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hflat : FullDFTFlat ψ J q K) :
    FourthMomentBound ψ J q (K ^ 4) := by
  unfold FourthMomentBound
  have hmq0 : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) * q := by positivity
  have hsq : (Real.sqrt (((3 * u' : ℕ) : ℝ) * q)) ^ 2 = ((3 * u' : ℕ) : ℝ) * q :=
    Real.sq_sqrt hmq0
  have hpt : ∀ a : ZMod (3 * u'),
      ‖hatF ψ (Sfun J) a‖ ^ 4 ≤ K ^ 4 * (((3 * u' : ℕ) : ℝ) * q) ^ 2 := by
    intro a
    calc ‖hatF ψ (Sfun J) a‖ ^ 4
        ≤ (K * Real.sqrt (((3 * u' : ℕ) : ℝ) * q)) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) (hflat a) 4
      _ = K ^ 4 * ((Real.sqrt (((3 * u' : ℕ) : ℝ) * q)) ^ 2) ^ 2 := by ring
      _ = K ^ 4 * (((3 * u' : ℕ) : ℝ) * q) ^ 2 := by rw [hsq]
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
      ≤ ∑ _a : ZMod (3 * u'), K ^ 4 * (((3 * u' : ℕ) : ℝ) * q) ^ 2 :=
        Finset.sum_le_sum (fun a _ => hpt a)
    _ = ((3 * u' : ℕ) : ℝ) * (K ^ 4 * (((3 * u' : ℕ) : ℝ) * q) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
    _ = K ^ 4 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := by ring

/-- Calibration: the fourth moment holds UNCONDITIONALLY with `K₄ = m`
(sup × Parseval; one factor `m` above the flat/diagonal scale). -/
theorem fourthMomentBound_unconditional {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ}
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ)) :
    FourthMomentBound ψ J q ((3 * u' : ℕ) : ℝ) := by
  unfold FourthMomentBound
  have hflat := fullDFTFlat_sqrt_m ψ hJ
  have hmq0 : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) * q := by positivity
  have hm0 : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by positivity
  have hsup : ∀ a : ZMod (3 * u'),
      ‖hatF ψ (Sfun J) a‖ ^ 2 ≤ ((3 * u' : ℕ) : ℝ) ^ 2 * q := by
    intro a
    calc ‖hatF ψ (Sfun J) a‖ ^ 2
        ≤ (Real.sqrt ((3 * u' : ℕ) : ℝ) * Real.sqrt (((3 * u' : ℕ) : ℝ) * q)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hflat a) 2
      _ = ((Real.sqrt ((3 * u' : ℕ) : ℝ)) ^ 2)
            * ((Real.sqrt (((3 * u' : ℕ) : ℝ) * q)) ^ 2) := by ring
      _ = ((3 * u' : ℕ) : ℝ) * (((3 * u' : ℕ) : ℝ) * q) := by
          rw [Real.sq_sqrt hm0, Real.sq_sqrt hmq0]
      _ = ((3 * u' : ℕ) : ℝ) ^ 2 * q := by ring
  have hpars := hatSfun_energy_le hψ hJ
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
      ≤ ∑ a : ZMod (3 * u'), (((3 * u' : ℕ) : ℝ) ^ 2 * q) * ‖hatF ψ (Sfun J) a‖ ^ 2 := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        have h4 : ‖hatF ψ (Sfun J) a‖ ^ 4
            = ‖hatF ψ (Sfun J) a‖ ^ 2 * ‖hatF ψ (Sfun J) a‖ ^ 2 := by ring
        rw [h4]
        exact mul_le_mul_of_nonneg_right (hsup a) (by positivity)
    _ = (((3 * u' : ℕ) : ℝ) ^ 2 * q) * ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (((3 * u' : ℕ) : ℝ) ^ 2 * q) * (((3 * u' : ℕ) : ℝ) ^ 2 * q) := by
        refine mul_le_mul_of_nonneg_left hpars (by positivity)
    _ = ((3 * u' : ℕ) : ℝ) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := by ring

end FourthMoment

/-! ### The ℓ³-vs-ℓ² interpolation inequality -/

/-- For nonnegative sequences: `∑ f³ ≤ √(∑ f²) · ∑ f²` (each value is at most
the ℓ² norm). -/
theorem sum_cube_le_sqrt_mul {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ∑ a : ZMod N, (f a) ^ 3
      ≤ Real.sqrt (∑ a : ZMod N, (f a) ^ 2) * ∑ a : ZMod N, (f a) ^ 2 := by
  have hsum2 : (0 : ℝ) ≤ ∑ a : ZMod N, (f a) ^ 2 :=
    Finset.sum_nonneg (fun a _ => by positivity)
  have hpt : ∀ a : ZMod N, f a ≤ Real.sqrt (∑ b : ZMod N, (f b) ^ 2) := by
    intro a
    have hsingle : (f a) ^ 2 ≤ ∑ b : ZMod N, (f b) ^ 2 :=
      Finset.single_le_sum (f := fun b => (f b) ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc f a = Real.sqrt ((f a) ^ 2) := (Real.sqrt_sq (hf a)).symm
      _ ≤ Real.sqrt (∑ b : ZMod N, (f b) ^ 2) := Real.sqrt_le_sqrt hsingle
  calc ∑ a : ZMod N, (f a) ^ 3
      = ∑ a : ZMod N, f a * (f a) ^ 2 := Finset.sum_congr rfl (fun a _ => by ring)
    _ ≤ ∑ a : ZMod N, Real.sqrt (∑ b : ZMod N, (f b) ^ 2) * (f a) ^ 2 := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        exact mul_le_mul_of_nonneg_right (hpt a) (by positivity)
    _ = Real.sqrt (∑ a : ZMod N, (f a) ^ 2) * ∑ a : ZMod N, (f a) ^ 2 :=
        (Finset.mul_sum _ _ _).symm

/-! ### The interpolated rung -/

section Interpolation

variable {u' : ℕ} [NeZero u']

/-- **THE INTERPOLATED RUNG (main theorem)**: one fourth-moment bound at the
correct scale discharges the r=3 DIST rung within a `√m` loss:
`E_DIST ≤ (3·K₄·√K₄ + 1215)·√m·m³·q³`.  With the probe-calibrated `K₄ ≤ 3.2`
this is `O(√m)·m³·q³`; with the unconditional `K₄ = m` it recovers an
`m^{5/2}`-type envelope.  The lossless route stays `FullDFTFlat` (R302). -/
theorem distStratumEnergyBound_of_fourthMoment {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {K₄ : ℝ} (hK : 0 ≤ K₄)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (h4 : FourthMomentBound ψ J q K₄) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      ((3 * K₄ * Real.sqrt K₄ + 1215) * Real.sqrt ((3 * u' : ℕ) : ℝ)) := by
  classical
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hm0 : (0 : ℝ) < ((3 * u' : ℕ) : ℝ) := by
    have := NeZero.ne u'
    positivity
  have hm1 : (1 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ 3 * u' := by have := NeZero.ne u'; omega
    exact_mod_cast h1
  have hσ1 : (1 : ℝ) ≤ Real.sqrt ((3 * u' : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hm1
  have hσ0 : (0 : ℝ) ≤ Real.sqrt ((3 * u' : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ x, ‖J x‖ ≤ Real.sqrt (q : ℝ) := by
    intro x
    have h := Real.sqrt_le_sqrt (hJ x)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hsqq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  -- pointwise slice-polynomial bounds (as in R302)
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
  -- per-mode square bound: ‖D̂(a)‖² ≤ 3‖Ŝ‖⁶ + 243 m²q²‖Ŝ‖² + 972 m²q³
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
    have hA0 : (0 : ℝ) ≤ ‖S‖ ^ 3 := by positivity
    have hB0 : (0 : ℝ) ≤ 3 * ‖S‖ * (3 * ((3 * u' : ℕ) : ℝ) * q) := by positivity
    have hC0 : (0 : ℝ) ≤ 2 * (9 * ((3 * u' : ℕ) : ℝ) * q * Real.sqrt (q : ℝ)) := by
      positivity
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
  -- the three summed pieces
  have hsix : ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6
      ≤ K₄ * Real.sqrt K₄
          * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 3) := by
    have hcube := sum_cube_le_sqrt_mul (fun a => ‖hatF ψ (Sfun J) a‖ ^ 2)
      (fun a => by positivity)
    have hrw6 : ∀ a : ZMod (3 * u'),
        (‖hatF ψ (Sfun J) a‖ ^ 2) ^ 3 = ‖hatF ψ (Sfun J) a‖ ^ 6 := fun a => by ring
    have hrw4 : ∀ a : ZMod (3 * u'),
        (‖hatF ψ (Sfun J) a‖ ^ 2) ^ 2 = ‖hatF ψ (Sfun J) a‖ ^ 4 := fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => hrw6 a),
        Finset.sum_congr rfl (fun a _ => hrw4 a)] at hcube
    have hM4 : ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
        ≤ K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := h4
    have hM40 : (0 : ℝ) ≤ ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4 :=
      Finset.sum_nonneg (fun a _ => by positivity)
    have hmono : Real.sqrt (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4)
          * ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
        ≤ Real.sqrt (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)
          * (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt hM4) hM4 hM40 (Real.sqrt_nonneg _)
    have hsqrtsplit : Real.sqrt (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)
        = Real.sqrt K₄
          * (((3 * u' : ℕ) : ℝ) * Real.sqrt ((3 * u' : ℕ) : ℝ)) * (q : ℝ) := by
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ K₄ * ((3 * u' : ℕ) : ℝ) ^ 3),
          Real.sqrt_mul hK,
          show ((3 * u' : ℕ) : ℝ) ^ 3 = ((3 * u' : ℕ) : ℝ) ^ 2 * ((3 * u' : ℕ) : ℝ)
            from by ring,
          Real.sqrt_mul (by positivity),
          Real.sqrt_sq hm0.le, Real.sqrt_sq hq0]
    calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6
        ≤ Real.sqrt (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4)
            * ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4 := hcube
      _ ≤ Real.sqrt (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)
            * (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2) := hmono
      _ = K₄ * Real.sqrt K₄
            * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 3) := by
          rw [hsqrtsplit]
          ring
  have htwo : ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) ^ 2 * q := hatSfun_energy_le hψ hJ
  -- assemble
  unfold DistStratumEnergyBound
  have hpars := distStratum_energy_spectral (u' := u') hψ J
  have htotal : ∑ a : ZMod (3 * u'),
      ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
      ≤ (3 * (K₄ * Real.sqrt K₄) + 1215)
          * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 3) := by
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
      _ ≤ 3 * (K₄ * Real.sqrt K₄
              * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 3))
            + 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
              * (((3 * u' : ℕ) : ℝ) ^ 2 * q)
            + 972 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
          have t1 := mul_le_mul_of_nonneg_left hsix (by norm_num : (0:ℝ) ≤ 3)
          have t2 := mul_le_mul_of_nonneg_left htwo
            (by positivity : (0:ℝ) ≤ 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2)
          have t3 : ((3 * u' : ℕ) : ℝ) * (972 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 3)
              = 972 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring
          linarith [t1, t2, t3.le, t3.ge]
      _ ≤ (3 * (K₄ * Real.sqrt K₄) + 1215)
            * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 3) := by
          have hbig : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3 := by positivity
          have e2 : 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
                * (((3 * u' : ℕ) : ℝ) ^ 2 * q)
              ≤ 243 * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ)
                * (q : ℝ) ^ 3) := by
            have : 243 * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2
                * (((3 * u' : ℕ) : ℝ) ^ 2 * q)
                = 243 * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) := by ring
            rw [this]
            nlinarith [mul_le_mul_of_nonneg_left hσ1
              (by positivity : (0:ℝ) ≤ 243 * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3))]
          have e3 : 972 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3
              ≤ 972 * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ)
                * (q : ℝ) ^ 3) := by
            have hm4 : ((3 * u' : ℕ) : ℝ) ^ 3 ≤ ((3 * u' : ℕ) : ℝ) ^ 4 :=
              pow_le_pow_right₀ hm1 (by norm_num)
            have hstep : ((3 * u' : ℕ) : ℝ) ^ 4
                ≤ ((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) := by
              nlinarith [mul_le_mul_of_nonneg_left hσ1
                (by positivity : (0:ℝ) ≤ ((3 * u' : ℕ) : ℝ) ^ 4)]
            nlinarith [mul_le_mul_of_nonneg_right (le_trans hm4 hstep)
              (by positivity : (0:ℝ) ≤ (q : ℝ) ^ 3)]
          linarith [e2, e3]
  -- divide by m
  have hE : ((3 * u' : ℕ) : ℝ)
        * ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ)
        * ((3 * K₄ * Real.sqrt K₄ + 1215) * Real.sqrt ((3 * u' : ℕ) : ℝ)
          * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) := by
    rw [hpars]
    calc ∑ a : ZMod (3 * u'),
        ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ (3 * (K₄ * Real.sqrt K₄) + 1215)
            * (((3 * u' : ℕ) : ℝ) ^ 4 * Real.sqrt ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 3) :=
          htotal
      _ = ((3 * u' : ℕ) : ℝ)
            * ((3 * K₄ * Real.sqrt K₄ + 1215) * Real.sqrt ((3 * u' : ℕ) : ℝ)
              * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) := by ring
  have hfinal := le_of_mul_le_mul_left hE hm0
  calc ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ (3 * K₄ * Real.sqrt K₄ + 1215) * Real.sqrt ((3 * u' : ℕ) : ℝ)
          * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := hfinal
    _ = ((3 * K₄ * Real.sqrt K₄ + 1215) * Real.sqrt ((3 * u' : ℕ) : ℝ))
          * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

end Interpolation

end ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation in
#print axioms hatF_conv2
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation in
#print axioms fourthMoment_eq_selfConv_energy
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation in
#print axioms fourthMomentBound_of_fullDFTFlat
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation in
#print axioms fourthMomentBound_unconditional
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation in
#print axioms sum_cube_le_sqrt_mul
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation in
#print axioms distStratumEnergyBound_of_fourthMoment
