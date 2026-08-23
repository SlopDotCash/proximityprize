/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R306SixthMomentInterpolation

/-!
# LANE B2 (#466, r=3 rung, R307): the moment sandwich — the ABSOLUTE-C rung
  from two a-AVERAGE inputs (no sup anywhere): Cauchy–Schwarz
  `∑‖Ŝ‖⁶ ≤ √(∑‖Ŝ‖⁴)·√(∑‖Ŝ‖⁸)`

## The mechanism

R305 proved the sup carries a Gumbel `log m` — pointwise flatness can NEVER
give the absolute-constant rung.  R306 paid that log through Hölder.  This
brick removes the sup entirely: Cauchy–Schwarz in the mode variable,

  `∑_a ‖Ŝ‖⁶ = ∑_a ‖Ŝ‖²·‖Ŝ‖⁴ ≤ √(∑_a‖Ŝ‖⁴)·√(∑_a‖Ŝ‖⁸)`,

sandwiches the sextic core between the QUARTIC average (r=2-class,
`FourthMomentBound`, measured `K₄ → 2` = Gaussian) and the OCTIC average
(`EighthMomentBound`, Gaussian prediction `K₈ = 4! = 24`).  Both factors are
averages — **Gumbel-immune** — and the composition gives

  **`E_DIST ≤ (3·√(K₄·K₈) + 1215)·m³·q³`** — an ABSOLUTE constant.

Probe (`scripts/probes/probe_466_r3_moment_sandwich.py`, m ≤ 1200): `K₈`
flat near `24·((m−2)/m)⁴ → 24`, no growth; sandwich constant `√(K₄K₈)`
tracks the direct `K₆` within ~15% (Gaussian: `√48 ≈ 6.93` vs `6`) — the
Cauchy–Schwarz step is essentially tight.

## Honest tower position of the octic input

`eighthMoment_eq_quadConv_energy` (formalized): `∑_a‖f̂‖⁸ = N·∑_c‖(f⋆f⋆f⋆f)(c)‖²`
— the 8th moment is the r = 4 rung of the R27 `IterConvEnergyWick` ladder
(the Wick factor `4! = 24` matches the Gaussian prediction exactly; at
`C = 1+ε` the tower rung IS `EighthMomentBound (24(1+ε)⁴)`).  The sandwich
therefore SHIFTS the open content — r=3 is now pinched between the r=2-class
quartic and the r=4 average — rather than closing it; but the shift is
structurally decisive: the REFUTED sup-shaped input is replaced by ladder
rungs of the EXISTING tower, all of whose averages are measured
Gaussian-flat with no known obstruction (the Gumbel mechanism only inflates
sups, never averages).

## Final honest ladder of the r=3 rung (end of the R297 → R307 arc)

* **absolute-C (this brick)**: `FourthMomentBound K₄ ∧ EighthMomentBound K₈`
  (probe: `K₄ ≈ 2`, `K₈ ≈ 24`, both Gaussian-exact, flat to m = 1200)
  ⟹ `C = 3√(K₄K₈) + 1215` — no sup, no log;
* log-only (R306): `FullDFTFlatLog A ∧ FourthMomentBound K₄`;
* √m (R303): `FourthMomentBound K₄` alone;
* log³ (R305): `FullDFTFlatLog A` alone;
* quartic sources (R304): `OffDiagQuadrupleBound K ⟹ K₄ = 2 + K`;
* REFUTED: absolute pointwise flatness (R305 Gumbel), per-variety
  Weil–Deligne at any moment order (R304), closed cyclotomic forms (R301).

CORE OPEN, ON-BGK.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R307MomentSandwich

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation

/-! ### The generic sandwich and the octic identity -/

section Generic

variable {N : ℕ} [NeZero N]

/-- **The moment sandwich (pure Cauchy–Schwarz, unconditional)**: the sixth
moment is dominated by the geometric mean of the fourth and eighth — all
a-averages, no sup. -/
theorem sixthMoment_sandwich (F : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖F a‖ ^ 6
      ≤ Real.sqrt (∑ a : ZMod N, ‖F a‖ ^ 4)
        * Real.sqrt (∑ a : ZMod N, ‖F a‖ ^ 8) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun a : ZMod N => ‖F a‖ ^ 2) (fun a : ZMod N => ‖F a‖ ^ 4)
  calc ∑ a : ZMod N, ‖F a‖ ^ 6
      = ∑ a : ZMod N, ‖F a‖ ^ 2 * ‖F a‖ ^ 4 :=
        Finset.sum_congr rfl (fun a _ => by ring)
    _ ≤ Real.sqrt (∑ a : ZMod N, (‖F a‖ ^ 2) ^ 2)
        * Real.sqrt (∑ a : ZMod N, (‖F a‖ ^ 4) ^ 2) := h
    _ = Real.sqrt (∑ a : ZMod N, ‖F a‖ ^ 4)
        * Real.sqrt (∑ a : ZMod N, ‖F a‖ ^ 8) := by
        rw [Finset.sum_congr rfl (fun a _ => by ring :
              ∀ a ∈ Finset.univ, (‖F a‖ ^ 2) ^ 2 = ‖F a‖ ^ 4),
            Finset.sum_congr rfl (fun a _ => by ring :
              ∀ a ∈ Finset.univ, (‖F a‖ ^ 4) ^ 2 = ‖F a‖ ^ 8)]

/-- **The octic identity (tower position, machine-checked)**: the eighth
moment of the DFT is `N` times the 4-fold self-convolution energy — the
r = 4 rung of the R27 `IterConvEnergyWick` ladder (Wick factor `4! = 24`). -/
theorem eighthMoment_eq_quadConv_energy {ψ : AddChar (ZMod N) ℂ}
    (hψ : ψ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖hatF ψ f a‖ ^ 8
      = (N : ℝ) * ∑ c : ZMod N, ‖conv2 (conv2 f f) (conv2 f f) c‖ ^ 2 := by
  have hpt : ∀ a : ZMod N,
      ‖hatF ψ f a‖ ^ 8 = ‖hatF ψ (conv2 (conv2 f f) (conv2 f f)) a‖ ^ 2 := by
    intro a
    rw [hatF_conv2 ψ (conv2 f f) (conv2 f f) a, hatF_conv2 ψ f f a, norm_mul,
      norm_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a)]
  exact hatF_parseval hψ (conv2 (conv2 f f) (conv2 f f))

end Generic

/-! ### The named octic input and the absolute-C rung -/

section AbsoluteC

variable {u' : ℕ} [NeZero u']

/-- **THE OCTIC NAMED INPUT**: the eighth moment at Wick scale — exactly the
r = 4 rung of the R27 tower in DFT coordinates (see
`eighthMoment_eq_quadConv_energy`).  Gaussian prediction `K₈ = 4! = 24`;
probe: flat at `24((m−2)/m)⁴` to m = 1200.  Gumbel-immune (an average). -/
def EighthMomentBound (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (q : ℕ) (K₈ : ℝ) : Prop :=
  ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8
    ≤ K₈ * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4

/-- **Sandwich composition**: quartic + octic averages give the sextic
interface at `√(K₄·K₈)`. -/
theorem sixthMomentBound_of_fourth_and_eighth {ψ : AddChar (ZMod (3 * u')) ℂ}
    {J : ZMod (3 * u') → ℂ} {q : ℕ} {K₄ K₈ : ℝ}
    (hK₄ : 0 ≤ K₄) (hK₈ : 0 ≤ K₈)
    (h4 : FourthMomentBound ψ J q K₄)
    (h8 : EighthMomentBound ψ J q K₈) :
    SixthMomentBound ψ J q (Real.sqrt (K₄ * K₈)) := by
  unfold SixthMomentBound
  have hsw := sixthMoment_sandwich (fun a => hatF ψ (Sfun J) a)
  have hM4 : (0 : ℝ) ≤ ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4 :=
    Finset.sum_nonneg (fun a _ => by positivity)
  have hM8 : (0 : ℝ) ≤ ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8 :=
    Finset.sum_nonneg (fun a _ => by positivity)
  have hstep : Real.sqrt (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4)
        * Real.sqrt (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8)
      ≤ Real.sqrt (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)
        * Real.sqrt (K₈ * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4) :=
    mul_le_mul (Real.sqrt_le_sqrt h4) (Real.sqrt_le_sqrt h8)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsplit : Real.sqrt (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)
        * Real.sqrt (K₈ * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4)
      = Real.sqrt (K₄ * K₈) * ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3 := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)]
    rw [show K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2
          * (K₈ * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4)
        = (K₄ * K₈) * (((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3) ^ 2 from by ring]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ K₄ * K₈),
      Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3)]
    ring
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 6
      ≤ Real.sqrt (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4)
          * Real.sqrt (∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8) := hsw
    _ ≤ Real.sqrt (K₄ * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2)
          * Real.sqrt (K₈ * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4) := hstep
    _ = Real.sqrt (K₄ * K₈) * ((3 * u' : ℕ) : ℝ) ^ 4 * (q : ℝ) ^ 3 := hsplit

/-- **THE ABSOLUTE-C RUNG (headline)**: two a-average moment inputs — the
quartic (r=2-class, `K₄ ≈ 2`) and the octic (r=4 tower rung, `K₈ ≈ 24`) —
give the r=3 DIST rung with an ABSOLUTE constant, no sup and no log:
`E_DIST ≤ (3·√(K₄·K₈) + 1215)·m³·q³`. -/
theorem distStratum_absoluteC_of_fourth_and_eighth
    {ψ : AddChar (ZMod (3 * u')) ℂ} (hψ : ψ.IsPrimitive)
    {J : ZMod (3 * u') → ℂ} {q : ℕ} {K₄ K₈ : ℝ}
    (hK₄ : 0 ≤ K₄) (hK₈ : 0 ≤ K₈)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (h4 : FourthMomentBound ψ J q K₄)
    (h8 : EighthMomentBound ψ J q K₈) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      (3 * Real.sqrt (K₄ * K₈) + 1215) :=
  distStratumEnergyBound_of_sixthMoment hψ hJ
    (sixthMomentBound_of_fourth_and_eighth hK₄ hK₈ h4 h8)

end AbsoluteC

end ArkLib.ProximityGap.Frontier.R307MomentSandwich

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R307MomentSandwich in
#print axioms sixthMoment_sandwich
open ArkLib.ProximityGap.Frontier.R307MomentSandwich in
#print axioms eighthMoment_eq_quadConv_energy
open ArkLib.ProximityGap.Frontier.R307MomentSandwich in
#print axioms sixthMomentBound_of_fourth_and_eighth
open ArkLib.ProximityGap.Frontier.R307MomentSandwich in
#print axioms distStratum_absoluteC_of_fourth_and_eighth
