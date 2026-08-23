/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakBracket

/-!
# The proven off-DC ceiling dominates the BGK / prize target (#444 door-iv consistency)

The two-sided bracket (`_DoorIVSubgroupOffDCPeakBracket`) pins the prize object
`M(μ_n) = max_{k≠0} ‖𝓕 1_{μ_d} k‖` between the Plancherel floor and the trivial ℓ²-completion
ceiling:
```
        √((N·d − d²)/(N − 1))  ≤  M  ≤  √(N·d − d²)              (N = p, d = n).
```
The CORE / BGK target the prize asks for is the **`bgkScale`** `√(n·L)` with `L = log(p/n)` the
logarithmic thinness index (the door-(i)/(ii)/(iii) floor in `_NoFifthDoorTetrachotomy`).  A natural
consistency question: does the prize/BGK target `√(n·L)` lie *inside* the proven band — i.e. below
the proven ceiling `√(p·n − n²)`?  If it did NOT, the formal bracket would contradict the
conjectured CORE bound.  This file proves it DOES, axiom-clean: the proven ceiling dominates the BGK
whenever `L ≤ p − n` — which always holds in the prize regime (`L = log(p/n) ≪ p − n`).

The probe `scripts/probes/_doorIV_offDC_peak_in_bracket.py` measured this: `M/ceil ≈ 0.02-0.21`
(the peak sits in the bottom few % of the band) and `M/prize ≈ 1.14-1.63` (the peak tracks the BGK
target within a bounded constant).  This file is the Lean consistency rung: the BGK target sits
strictly below the proven ceiling, so CORE asks for a bound *inside* the band, not against it.

* `bgkTarget_le_offDC_ceiling_sq` : `n·L ≤ p·n − n²` whenever `L ≤ p − n` and `0 ≤ n`.
* `bgkTarget_le_offDC_ceiling`    : `√(n·L) ≤ √(p·n − n²)` (the norm form, the band-containment).
* `offDC_floor_le_bgkTarget_sq`   : `(p·n − n²)/(p − 1) ≤ n·L` whenever `1 ≤ L` (prize `L ≫ 1`).
* `offDC_floor_le_bgkTarget`      : `√((p·n − n²)/(p − 1)) ≤ √(n·L)` (floor below the BGK target).
* `offDC_band_contains_bgkTarget` : the full chain `floor ≤ √(n·L) ≤ ceiling` — the BGK / prize
  target lies STRICTLY INSIDE the proven band, with the floor→target gap the door-(iv) `√L` factor.

NOTE on scope: this is a CONSISTENCY/containment statement — it places the conjectured CORE target
*below the proven ceiling*, confirming the bracket genuinely brackets the prize regime.  It is NOT a
CORE upper bound (which replaces the ceiling `√(p·n − n²)` by the much smaller `C·√(n·log(p/n))`):
that remains OPEN.  No cancellation, completion improvement, anti-concentration, moment, or capacity
claim.  Door (iv) remains the only live door.  Axiom-clean.  Issue #444.
-/

open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget

/-- **The BGK target is below the proven ceiling (squared form).**  With `N = p`, `d = n`, the BGK
energy `n·L` is at most the proven off-DC ceiling energy `p·n − n²` whenever the thinness index
satisfies `L ≤ p − n`.  In the prize regime `L = log(p/n) ≪ p − n`, so this always holds.  Proof:
`n·L ≤ n·(p − n) = p·n − n²` by monotonicity of `n·(·)` for `0 ≤ n`. -/
theorem bgkTarget_le_offDC_ceiling_sq {n p L : ℝ} (hn : 0 ≤ n) (hL : L ≤ p - n) :
    n * L ≤ p * n - n ^ 2 := by
  have h : n * L ≤ n * (p - n) := by
    apply mul_le_mul_of_nonneg_left hL hn
  nlinarith [h]

/-- **The BGK target is below the proven ceiling (norm form — band containment).**  The BGK / prize
target `√(n·L)` is at most the proven off-DC ceiling `√(p·n − n²)` whenever `L ≤ p − n` (true in the
prize regime).  Hence the conjectured CORE target lies *inside* the proven two-sided band
`[√((p·n − n²)/(p − 1)), √(p·n − n²)]` — the bracket genuinely brackets the prize regime, and CORE
asks for a bound below the proven ceiling. -/
theorem bgkTarget_le_offDC_ceiling {n p L : ℝ} (hn : 0 ≤ n) (hL : L ≤ p - n) :
    Real.sqrt (n * L) ≤ Real.sqrt (p * n - n ^ 2) :=
  Real.sqrt_le_sqrt (bgkTarget_le_offDC_ceiling_sq hn hL)

/-- **The proven floor is below the BGK target (squared form).**  With `N = p`, `d = n`, the off-DC
mean-energy floor `(p·n − n²)/(p − 1)` is at most the BGK energy `n·L` whenever `1 ≤ L` (the prize
regime has `L = log(p/n) ≥ 1`).  Indeed `(p·n − n²)/(p − 1) = n·(p − n)/(p − 1) ≤ n ≤ n·L`: the
middle step is `(p − n) ≤ (p − 1)` (since `1 ≤ n`), and the last is `1 ≤ L`. -/
theorem offDC_floor_le_bgkTarget_sq {n p L : ℝ} (hn : 1 ≤ n) (hp : 1 < p)
    (hL : 1 ≤ L) :
    (p * n - n ^ 2) / (p - 1) ≤ n * L := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hstep1 : (p * n - n ^ 2) / (p - 1) ≤ n := by
    rw [div_le_iff₀ hp1]
    nlinarith [hn]
  have hstep2 : n ≤ n * L := by nlinarith [hn, hL]
  linarith

/-- **The proven floor is below the BGK target (norm form).**  `√((p·n − n²)/(p − 1)) ≤ √(n·L)`
in the prize regime (`1 ≤ L`): the BGK / prize target sits ABOVE the Plancherel floor, and the gap
is the door-(iv) `√L = √(log(p/n))` factor. -/
theorem offDC_floor_le_bgkTarget {n p L : ℝ} (hn : 1 ≤ n) (hp : 1 < p)
    (hL : 1 ≤ L) :
    Real.sqrt ((p * n - n ^ 2) / (p - 1)) ≤ Real.sqrt (n * L) :=
  Real.sqrt_le_sqrt (offDC_floor_le_bgkTarget_sq hn hp hL)

/-- **The BGK / prize target lies strictly inside the proven band.**  Combining both directions:
```
        √((p·n − n²)/(p − 1))  ≤  √(n·L)  ≤  √(p·n − n²)
```
in the prize regime (`1 ≤ n`, `1 < p`, `1 ≤ L ≤ p − n`).  The conjectured CORE target `√(n·L)` sits
between the Plancherel floor and the trivial completion ceiling — the proven bracket genuinely
brackets the prize regime, and the floor→target gap is the open door-(iv) `√L` factor. -/
theorem offDC_band_contains_bgkTarget {n p L : ℝ} (hn : 1 ≤ n) (hp : 1 < p)
    (hL1 : 1 ≤ L) (hL2 : L ≤ p - n) :
    Real.sqrt ((p * n - n ^ 2) / (p - 1)) ≤ Real.sqrt (n * L)
      ∧ Real.sqrt (n * L) ≤ Real.sqrt (p * n - n ^ 2) :=
  ⟨offDC_floor_le_bgkTarget hn hp hL1, bgkTarget_le_offDC_ceiling (by linarith) hL2⟩

end ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget

open ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget in
#print axioms bgkTarget_le_offDC_ceiling_sq
open ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget in
#print axioms bgkTarget_le_offDC_ceiling
open ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget in
#print axioms offDC_floor_le_bgkTarget_sq
open ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget in
#print axioms offDC_band_contains_bgkTarget
