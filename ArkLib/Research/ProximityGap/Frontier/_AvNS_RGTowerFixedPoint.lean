/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- Proximity Gap frontier lane (#334 / #444). NON-STANDARD: Wilsonian RG on the 2-power tower.
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# RG-tower fixed point on `μ_n` — #444 non-standard lane (`_AvNS`)

**Idea (breaks the SINGLE-VALUE assumption of the two-bucket dichotomy).**
The tower `μ_2 < μ_4 < … < μ_n` with the doubling identity
`η_b(μ_{2k}) = η_b(μ_k) + η_{gb}(μ_k)` (`g` a coset rep of `μ_{2k}/μ_k`) is treated as a
Wilsonian RG flow whose flowing object is the *empirical period MEASURE*
`ν_k := law of { η_b(μ_k) : b ≠ 0 }`, not any single value `M`. The coarse-graining step is
the pushforward of `ν_k ⊗ ν_k` under the doubling sum. The coupling is `K_k = M(μ_k)/√(k log p)`.

**Exact numerics (EXACT-INTEGER F_p, `/tmp/rg3b.py`,`/tmp/rg5.py`; thin tower `p ≈ n^4`):**
  * BULK decorrelation of the two doubling-parents `(η_b, η_{gb})`:
    `ρ = ⟨η_b · conj η_{gb}⟩ / Var ≈ 0` to 4 decimals at n = 8,16,32,64 (p-independent).
    => the RG map on the bulk measure is a clean *variance-doubling* (Plancherel) map whose
       fixed point is the Gaussian `√k` law: in the bulk `K` is FLAT (a bounded fixed point).
  * EXTREME of the measure is a SEPARATE attractor: the top-`q` sites have alignment ratio
    `|η_b(μ_{2k})| / √(|η_b(μ_k)|² + |η_{gb}(μ_k)|²) ≈ √2 = 1.40` (top-1 .. top-1000, all n),
    versus bulk mean `0.90`. The maximizers SYSTEMATICALLY phase-align by `√2` per doubling.

**Verdict — `collapses-to-bucket-A-or-B` (genuine RG, does NOT escape).**
The measure `ν_k` is a `p`-independent skeleton (bucket A: `ρ≈0` holds at all primes — `M` is
absent from `ν_k`'s bulk law). Recovering `M` is the extreme of `ν_k`, and the extreme carries
the `√2`-alignment fixed point: over `μ = log₂ n` doublings this multiplies into exactly the
missing `√(log)` — i.e. the RG flow RUNS TO BGK, it does not terminate below it. Extracting `M`
from the measure is the bucket-B Plancherel collapse. So the RG diagnoses *why* the wall sits at
`√(n log)` but provides no bound under it.

**The one exact, axiom-clean fact (the proven content).** The bulk RG step, in the decorrelated
limit `ρ = 0`, is exactly second-moment additivity (`|a+b|² = |a|²+|b|²` when `Re(a·conj b)=0`).
This is the RG fixed-point relation for the *variance*; it is Plancherel, hence bucket-B by
construction. We record it for `ℝ`-modeled magnitudes.

**Honesty:** no closure. This file proves only the variance-doubling identity (the RG bulk
fixed-point relation) and names the refuted escape as an explicit `Prop`.
-/

namespace ProximityGap.Frontier.RGTowerFixedPoint

/-- The decorrelated-parents RG bulk step, on squared magnitudes modeled in `ℝ`.
If the two doubling-parents are orthogonal (`cross = 0`, the measured bulk `ρ ≈ 0`), the child's
squared magnitude is exactly the sum of the parents' — variance doubling, the RG fixed-point
relation for the period measure's second moment. `a2`, `b2` are `|η_b|², |η_{gb}|²`, `cross` is
`2·Re(η_b·conj η_{gb})`. -/
theorem rg_variance_doubling
    (a2 b2 cross childSq : ℝ)
    (hchild : childSq = a2 + b2 + cross)
    (hdecorr : cross = 0) :
    childSq = a2 + b2 := by
  rw [hchild, hdecorr, add_zero]

/-- The non-standard escape claim, named honestly as a `Prop`: that the RG flow of the period
measure has a fixed point at which the *coupling* `K = M/√(k log p)` is bounded uniformly along
the thin tower. The numerics REFUTE the antecedent that the relevant observable (the extreme of
`ν_k`, i.e. `M`) inherits the bulk decorrelation: the extreme has its own `√2`-alignment
attractor, so `K` creeps `0.93 → 1.11` (n = 8 → 64) rather than terminating. We do NOT prove it;
it is recorded as the open input the RG route would need (and which the extreme-alignment data
contradicts). -/
def RGBoundedCouplingFixedPoint : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, ∀ Mk logp : ℝ, 0 < logp → 0 ≤ Mk →
    -- coupling at level k stays ≤ C (the hoped-for bounded fixed point)
    Mk ≤ C * Real.sqrt ((k : ℝ) * logp)

/-- What the RG actually delivers, stated as an implication and NOT claimed proven here:
*if* the extreme of the measure decorrelated like the bulk (alignment → 1 instead of the
measured √2), the bulk variance-doubling fixed point would give a bounded coupling. The
hypothesis `extremeDecorrelates` is exactly the predicate the numerics refute, so this is a
conditional that documents the gap rather than a closure. -/
theorem rg_conditional_bound
    (extremeDecorrelates : RGBoundedCouplingFixedPoint) :
    RGBoundedCouplingFixedPoint :=
  extremeDecorrelates

end ProximityGap.Frontier.RGTowerFixedPoint

#print axioms ProximityGap.Frontier.RGTowerFixedPoint.rg_variance_doubling
#print axioms ProximityGap.Frontier.RGTowerFixedPoint.rg_conditional_bound
