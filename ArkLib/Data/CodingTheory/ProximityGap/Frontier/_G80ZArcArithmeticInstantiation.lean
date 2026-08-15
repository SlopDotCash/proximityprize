/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80ArcOscillationWeld

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80Z (#466, 2026-07-10): the ARITHMETIC instantiation of the G80 arc model on
  `ZMod p` — character-sum bias forces an arc-occupancy increment, end-to-end
  (axiom-clean; closes the "pure plumbing" gap G80 recorded).

## What this closes

G80 (`_G80ArcOscillationWeld.lean`) proved the abstract rank-one arc-increment extraction
(`exists_arc_deviation_equally_spaced`) and recorded as its remaining gap: *"instantiating
`θ x = 2π·val(x)/p`, `κ = arc index ⌊K·val(x)/p⌋`, for which the width hypothesis holds with
`wid = 2π/K` by construction"*. This lane performs that instantiation for an ARBITRARY point
set `S ⊆ ZMod p` and its standard additive-character phase sum
`∑_{y ∈ S} e(val(y)/p)`, `e(t) = exp(2πit)`:

* `arcIndex` : the canonical arc assignment `y ↦ ⌊K·val(y)/p⌋ ∈ [0, K)` (ℕ-division).
* `arcIndex_mem_range` : it lands in `range K` (from `val(y) < p`).
* `arcIndex_width` : the WIDTH hypothesis `|2π·val(y)/p − 2π·arcIndex(y)/K| ≤ 2π/K` — by
  construction of the floor: `j·p ≤ K·v < (j+1)·p` gives `j/K ≤ v/p < (j+1)/K`.
* `exists_arc_deviation_of_charSum_bias` (CAPSTONE) : if the character sum over `S` has norm
  `≥ A`, then for any reference mass `m ≥ 0` some arc `j < K` has occupancy deviating by

  `(A − #S·(2π/K)) / K ≤ |#{y ∈ S : arcIndex y = j} − m|`.

Instantiated at `S = b·μ_n` (so the phase sum IS the Gauss-period frequency `η_b`) and
`m = n/K`, this is the fully arithmetic rank-one statement: `‖η_b‖ ≥ A` forces a value-arc of
`Z/p` where the dilated subgroup over- or under-concentrates by `(A − 2πn/K)/K` relative to
uniform. Taking `K ≍ n/√(n log q)` (so the oscillation cost `2πn/K` is half of `A ≍ √(n log q)`)
makes the increment `≳ A/(2K)` — the exact spreadness-failure certificate shape that the KM
engine (G78) consumes, now with ZERO analytic slack left in the chain: chord-arc, center
cancellation (`B = 0`), and the floor-width bound are all machine-checked.

## Honest scope

The Fourier ⟹ arc-increment direction is now END-TO-END formal on `ZMod p`. This does NOT
close the KM spreadness circularity (G78's verdict stands): the missing prize input is the
CONVERSE certificate — anti-concentration of the dilated subgroup in arcs obtained WITHOUT
Fourier analysis (the BGK/Cilleruelo–Garaev frontier; tool-shape doctrine v2's "single missing
non-Fourier certificate"). What changed: that certificate now has a precise, machine-checked
consumer — any future arc-occupancy bound plugs into `exists_arc_deviation_of_charSum_bias`'s
contrapositive to bound `‖η_b‖` with no further analytic work. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation

open ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld

variable {p : ℕ} [NeZero p]

/-- The canonical arc assignment: `y` lands in arc `⌊K·val(y)/p⌋`. -/
def arcIndex (K : ℕ) (y : ZMod p) : ℕ := K * y.val / p

/-- The standard additive-character phase of `y`: `2π·val(y)/p`. -/
noncomputable def charPhase (y : ZMod p) : ℝ := 2 * Real.pi * (y.val : ℝ) / p

/-- The arc assignment lands in `[0, K)`. -/
theorem arcIndex_mem_range (K : ℕ) (hK : 0 < K) (y : ZMod p) :
    arcIndex K y ∈ Finset.range K := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hv : y.val < p := ZMod.val_lt y
  rw [Finset.mem_range, arcIndex, Nat.div_lt_iff_lt_mul hp]
  exact mul_lt_mul_of_pos_left hv hK

/-- **The width hypothesis, by construction of the floor**: every point's phase is within
`2π/K` of its arc's center `2π·arcIndex/K`. -/
theorem arcIndex_width (K : ℕ) (hK : 0 < K) (y : ZMod p) :
    |charPhase y - 2 * Real.pi * (arcIndex K y : ℝ) / K| ≤ 2 * Real.pi / K := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set v : ℕ := y.val with hv
  set j : ℕ := arcIndex K y with hj
  -- floor inequalities: j·p ≤ K·v < (j+1)·p
  have hfloor1 : j * p ≤ K * v := by
    rw [hj, arcIndex]
    exact Nat.div_mul_le_self (K * v) p
  have hfloor2 : K * v < (j + 1) * p := by
    rw [hj, arcIndex]
    exact (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  -- real versions
  have h1 : (j : ℝ) * p ≤ (K : ℝ) * v := by exact_mod_cast hfloor1
  have h2 : (K : ℝ) * v < ((j : ℝ) + 1) * p := by exact_mod_cast hfloor2
  -- j/K ≤ v/p < (j+1)/K
  have hx1 : (j : ℝ) / K ≤ (v : ℝ) / p := by
    rw [div_le_div_iff₀ hKR hpR]
    linarith [h1]
  have hx2 : (v : ℝ) / p < ((j : ℝ) + 1) / K := by
    rw [div_lt_div_iff₀ hpR hKR]
    linarith [h2]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hphase : charPhase y = 2 * Real.pi * ((v : ℝ) / p) := by
    rw [charPhase, hv]
    ring
  have hcenter : 2 * Real.pi * (j : ℝ) / K = 2 * Real.pi * ((j : ℝ) / K) := by ring
  rw [hphase, hcenter, abs_le]
  constructor
  · have hnonneg : 0 ≤ 2 * Real.pi * ((v : ℝ) / p) - 2 * Real.pi * ((j : ℝ) / K) := by
      nlinarith [hx1, hpi]
    have hwid : (0 : ℝ) ≤ 2 * Real.pi / K := by positivity
    linarith
  · have hlt : 2 * Real.pi * ((v : ℝ) / p) - 2 * Real.pi * ((j : ℝ) / K)
        ≤ 2 * Real.pi / K := by
      have hd : (v : ℝ) / p - (j : ℝ) / K ≤ 1 / K := by
        have hsplit : ((j : ℝ) + 1) / K = (j : ℝ) / K + 1 / K := by ring
        rw [hsplit] at hx2
        linarith
      calc
        2 * Real.pi * ((v : ℝ) / p) - 2 * Real.pi * ((j : ℝ) / K) =
            (2 * Real.pi) * ((v : ℝ) / p - (j : ℝ) / K) := by ring
        _ ≤ (2 * Real.pi) * (1 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
        _ = 2 * Real.pi / K := by ring
    linarith

/-- **CAPSTONE — arithmetic rank-one arc-increment extraction on `ZMod p`.** If the standard
character sum over `S ⊆ ZMod p` has norm `≥ A`, then for `K ≥ 2` arcs and ANY reference mass
`m ≥ 0`, some arc's occupancy deviates from `m` by at least `(A − #S·(2π/K))/K`. With
`S = b·μ_n` the phase sum is the Gauss-period frequency `η_b`: Fourier bias forces arc
over/under-concentration of the dilated subgroup. -/
theorem exists_arc_deviation_of_charSum_bias (S : Finset (ZMod p))
    {K : ℕ} (hK : 2 ≤ K) (A m : ℝ) (hm : 0 ≤ m)
    (hbias : A ≤ ‖∑ y ∈ S, Complex.exp ((charPhase y : ℂ) * Complex.I)‖) :
    ∃ j ∈ Finset.range K,
      (A - (S.card : ℝ) * (2 * Real.pi / K)) / (K : ℝ) ≤
        |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m| := by
  have hK0 : 0 < K := by omega
  have h := exists_arc_deviation_equally_spaced S hK (arcIndex K)
    (fun y _ => arcIndex_mem_range K hK0 y)
    charPhase (2 * Real.pi / K) A m hm
    (fun y _ => arcIndex_width K hK0 y) hbias
  simpa using h

end ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation.arcIndex_mem_range
#print axioms
  ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation.arcIndex_width
#print axioms
  ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation.exists_arc_deviation_of_charSum_bias
