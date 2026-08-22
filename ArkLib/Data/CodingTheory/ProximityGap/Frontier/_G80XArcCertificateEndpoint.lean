/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80YArcEquivalenceConverse

/-!
# LANE G80X (#466, 2026-07-10): the CERTIFICATE→PRIZE ENDPOINT — formal AM-GM over the
  arc count K: an ε-uniformity certificate yields `‖charSum‖ ≤ 2√(2π·#S·ε) + ε`
  (axiom-clean; the arc program's closing quantitative brick).

## Position

G80Y gives `‖charSum‖ ≤ K·ε + #S·(2π/K)` for every arc count `K ≥ 2`. This lane performs the
K-optimization FORMALLY: for `K` in the unit bracket `[√(2π·#S/ε), √(2π·#S/ε) + 1]`
(e.g. `K = ⌈√(2π·#S/ε)⌉`),

`K·ε + #S·(2π/K) ≤ 2·√(2π·#S·ε) + ε`.

So the quantitative content of the missing non-Fourier certificate is pinned as a single
function of its strength: an arc-uniformity certificate of strength `ε` at ONE well-chosen
`K` yields `‖η_b‖ ≤ 2√(2πn·ε) + ε`; at `ε = C·log q` this is `M = O(√(n log q))` — the prize
bound — with every constant explicit and machine-checked. Conversely (G80Z, forward
direction), an arc-uniformity level `ε ≪ (M − 2πn/K)/K` is impossible, so `ε ≍ log q` at the
optimal `K` is exactly the certificate the prize requires: no weaker input suffices and no
stronger input is needed.

* `amgm_arc_budget` : the pure real-arithmetic optimization
  `K·ε + 2πn/K ≤ 2√(2πnε) + ε` for `K` in the unit bracket above `√(2πn/ε)`.
* `charSum_le_sqrt_of_arc_uniformity` : the ZMod p capstone composing G80Y with the
  optimization.

## Honest scope

Pure consumer-side arithmetic: no progress on producing the certificate (the
BGK/Cilleruelo–Garaev non-Fourier anti-concentration frontier — THE open core). The arc
program (G80 → G80Z → G80Y → G80X) is now complete on both sides of that single missing
input. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80XArcCertificateEndpoint

open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation
open ArkLib.ProximityGap.Frontier.G80YArcEquivalenceConverse

/-- **The K-optimization (pure real AM-GM)**: for `K` in the unit bracket above
`√(2πn/ε)`, the G80Y budget `K·ε + 2πn/K` is at most `2√(2πnε) + ε`. -/
theorem amgm_arc_budget {n K ε : ℝ} (hε : 0 < ε) (hn : 0 ≤ n) (hKpos : 0 < K)
    (hK1 : Real.sqrt (2 * Real.pi * n / ε) ≤ K)
    (hK2 : K ≤ Real.sqrt (2 * Real.pi * n / ε) + 1) :
    K * ε + 2 * Real.pi * n / K ≤ 2 * Real.sqrt (2 * Real.pi * n * ε) + ε := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pin : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
  have hεne : ε ≠ 0 := ne_of_gt hε
  set s : ℝ := Real.sqrt (2 * Real.pi * n / ε) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- s·ε = √(2πnε)
  have hsε : s * ε = Real.sqrt (2 * Real.pi * n * ε) := by
    have hsq : (s * ε) ^ 2 = 2 * Real.pi * n * ε := by
      rw [mul_pow, hs, Real.sq_sqrt (by positivity)]
      field_simp
    rw [← hsq, Real.sqrt_sq (mul_nonneg hs0 hε.le)]
  -- s·√(2πnε) = 2πn
  have hsprod : s * Real.sqrt (2 * Real.pi * n * ε) = 2 * Real.pi * n := by
    rw [hs, ← Real.sqrt_mul (by positivity)]
    rw [show 2 * Real.pi * n / ε * (2 * Real.pi * n * ε) = (2 * Real.pi * n) ^ 2 by
      field_simp]
    exact Real.sqrt_sq h2pin
  -- the two budget halves
  have h2 : 2 * Real.pi * n / K ≤ Real.sqrt (2 * Real.pi * n * ε) := by
    rw [div_le_iff₀ hKpos]
    calc 2 * Real.pi * n = s * Real.sqrt (2 * Real.pi * n * ε) := hsprod.symm
      _ ≤ K * Real.sqrt (2 * Real.pi * n * ε) :=
          mul_le_mul_of_nonneg_right hK1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * Real.pi * n * ε) * K := by ring
  have h1 : K * ε ≤ Real.sqrt (2 * Real.pi * n * ε) + ε := by
    have hmul := mul_le_mul_of_nonneg_right hK2 hε.le
    have hexp : (s + 1) * ε = s * ε + ε := by ring
    rw [hexp, hsε] at hmul
    exact hmul
  linarith

/-- **ZMod p capstone — certificate strength ⟹ sup-norm bound, optimized.** An arc-occupancy
`ε`-uniformity certificate at one `K` in the unit bracket above `√(2π·#S/ε)` yields
`‖∑_{y∈S} e(val(y)/p)‖ ≤ 2√(2π·#S·ε) + ε`. At `S = b·μ_n`, `ε = C·log q`, this is
`‖η_b‖ = O(√(n log q))` — the prize shape, with explicit constants. -/
theorem charSum_le_sqrt_of_arc_uniformity {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    {K : ℕ} (hK : 2 ≤ K) (ε m : ℝ) (hε : 0 < ε)
    (hK1 : Real.sqrt (2 * Real.pi * S.card / ε) ≤ (K : ℝ))
    (hK2 : (K : ℝ) ≤ Real.sqrt (2 * Real.pi * S.card / ε) + 1)
    (hunif : ∀ j ∈ Finset.range K,
      |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m| ≤ ε) :
    ‖∑ y ∈ S, Complex.exp ((charPhase y : ℂ) * Complex.I)‖ ≤
      2 * Real.sqrt (2 * Real.pi * S.card * ε) + ε := by
  have h := charSum_le_of_arc_uniformity S hK ε m hunif
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hopt := amgm_arc_budget hε (by positivity : (0 : ℝ) ≤ (S.card : ℝ)) hKpos hK1 hK2
  have halign : (S.card : ℝ) * (2 * Real.pi / K) = 2 * Real.pi * (S.card : ℝ) / K := by
    ring
  linarith

end ArkLib.ProximityGap.Frontier.G80XArcCertificateEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80XArcCertificateEndpoint.amgm_arc_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G80XArcCertificateEndpoint.charSum_le_sqrt_of_arc_uniformity
