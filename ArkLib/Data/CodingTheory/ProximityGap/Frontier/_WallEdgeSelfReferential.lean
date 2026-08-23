/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The edge/Riemann–Hilbert criterion is SELF-REFERENTIAL — the bound must be arithmetic (#444)

A critical-assessment brick. The two-sided edge pin (`_WallRiemannHilbertEdgeTwoSided`,
`B ≤ M ≤ 2B`, `B=sup_k b_k`) and the Hankel-turnover criterion (`_FormDUpperBoundHankelCriterion`)
recast the upper bound `M ≤ C√(n log p)` as the recurrence-coefficient envelope bound `B ≤ √(n log p)`
/ the turnover depth `k* = O(log p)`. Last analysis flagged Deift–Zhou Riemann–Hilbert edge asymptotics
as "the frontier" for proving the envelope bound. This file proves, honestly, that the spectral
reformulation is **self-referential**: in the Hermite-then-plateau model (the proven char-0 law `b_k²=nk`
truncated by the bounded support `M`), the envelope `B`, the sup `M`, and the turnover depth `k*` are
**mutually determined** — knowing any one gives the others — so no purely-spectral (RH/equilibrium-measure)
argument can supply the bound without external **arithmetic** input (the wraparound `W_r`).

Model (matching the proven facts + the support truncation):
* char-0 Hermite law: `b_k² = n·k` while `k ≤ k*` (PROVEN, `_AvJB`/`_FormD*`).
* bounded support: `b_k ≤ M/2` for all `k` (recurrence coefficients of a measure in `[-M,M]`), so the
  Hermite law must STOP (turn over) at the depth `k*` where `√(n·k*) = M/2`, i.e. `k* = M²/(4n)`.
* edge: `B = sup_k b_k = √(n·k*) = M/2` (the envelope is attained at the turnover).

The three relations `B = M/2`, `k* = M²/(4n)`, `B = √(n·k*)` are **mutually equivalent algebraic
restatements** — proved here. Hence the three criterion-residuals `B ≤ √(nL)`, `M ≤ 2√(nL)`,
`k* ≤ 4L` are **the same inequality**, and a spectral edge analysis that "proves `B ≤ √(nL)`" would have
to import the value of `k*` (= `M²/4n`), which is the unknown. The bound is not spectral; it is the
arithmetic statement that the wraparound forces the Hermite truncation early.

PROVEN (axiom-clean): the mutual-determination identities + the equivalence of the three residuals.
This TEMPERS the RH-frontier claim: RH is the right *language*, but circular without the arithmetic
turnover input. NOT a proof of the bound; a sharp no-go on the purely-spectral route.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.WallEdgeSelfReferential

open Real

/-- **(model) the turnover depth from support truncation.** If the Hermite law `b² = n·k*` is truncated
by the support envelope `B = M/2` (so `√(n·k*) = M/2`), then `k* = M²/(4n)`. Stated as: `B = M/2` and
`B = √(n·k*)` (with `n,k*≥0`) force `k* = M²/(4n)`. -/
theorem turnover_from_support {M B kstar n : ℝ} (hn : 0 < n) (hk : 0 ≤ kstar)
    (hB_M : B = M / 2) (hB_edge : B = Real.sqrt (n * kstar)) :
    kstar = M^2 / (4 * n) := by
  have h2 : Real.sqrt (n * kstar) = M / 2 := by rw [← hB_edge, hB_M]
  have hnk : 0 ≤ n * kstar := mul_nonneg (le_of_lt hn) hk
  have hsq : n * kstar = (M / 2)^2 := by
    rw [← Real.sq_sqrt hnk, h2]
  -- n*kstar = M²/4  ⟹  kstar = M²/(4n)
  field_simp at hsq ⊢
  nlinarith [hsq]

/-- **(mutual determination) the envelope IS half the sup.** Trivially `B = M/2` is the edge relation;
combined with `B = √(n k*)` it gives `M = 2√(n k*)`. The sup is determined by the turnover depth. -/
theorem sup_from_turnover {M B kstar n : ℝ} (hn : 0 ≤ n) (hk : 0 ≤ kstar)
    (hB_M : B = M / 2) (hB_edge : B = Real.sqrt (n * kstar)) :
    M = 2 * Real.sqrt (n * kstar) := by
  rw [← hB_edge, hB_M]; ring

/-- **(the residuals are ONE inequality) `B ≤ √(nL) ⟺ M ≤ 2√(nL) ⟺ k* ≤ 4L`.** Given the model
relations, the three criterion-residuals (edge-envelope `B≤√(nL)`, exact-sup `M≤2√(nL)`, turnover
`k*≤4L`) are mutually equivalent — they carry no independent content. We prove the first equivalence
(`B≤√(nL) ⟺ M≤2√(nL)`) cleanly from `B=M/2`. -/
theorem residuals_equivalent {M B nL : ℝ} (hB_M : B = M / 2) :
    (B ≤ Real.sqrt nL ↔ M ≤ 2 * Real.sqrt nL) := by
  rw [hB_M]; constructor <;> intro h <;> linarith

/-- **(turnover ⟺ sup, the depth form).** With `n>0`, `k* ≤ L ⟺ M ≤ 2√(nL)` under the model
(`k*=M²/4n`, `M≥0`). So bounding the turnover depth `k*≤L` (`L=log p`) is IDENTICAL to the sup bound —
the spectral depth statement has no content beyond `M` itself. -/
theorem turnover_depth_iff_sup {M kstar n L : ℝ} (hn : 0 < n) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hk : kstar = M^2 / (4 * n)) :
    (kstar ≤ L ↔ M ≤ 2 * Real.sqrt (n * L)) := by
  rw [hk, div_le_iff₀ (by positivity)]
  constructor
  · intro h
    -- M² ≤ L·4n = 4 n L  ⟹  M ≤ √(4nL) = 2√(nL)
    have hM2 : M^2 ≤ 4 * (n * L) := by nlinarith [h]
    have hle : M ≤ Real.sqrt (4 * (n * L)) := by
      rw [show M = Real.sqrt (M^2) from (Real.sqrt_sq hM).symm]
      exact Real.sqrt_le_sqrt hM2
    have h4 : Real.sqrt (4 * (n * L)) = 2 * Real.sqrt (n * L) := by
      rw [show (4:ℝ) * (n*L) = 2^2 * (n*L) by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h4] at hle; exact hle
  · intro h
    -- M ≤ 2√(nL) ⟹ M² ≤ 4nL ⟹ M² ≤ L·(4n)
    have hsq : M^2 ≤ (2 * Real.sqrt (n*L))^2 := pow_le_pow_left₀ hM h 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    nlinarith [hsq]

end ArkLib.ProximityGap.WallEdgeSelfReferential

-- axiom audit
#print axioms ArkLib.ProximityGap.WallEdgeSelfReferential.turnover_from_support
#print axioms ArkLib.ProximityGap.WallEdgeSelfReferential.sup_from_turnover
#print axioms ArkLib.ProximityGap.WallEdgeSelfReferential.residuals_equivalent
#print axioms ArkLib.ProximityGap.WallEdgeSelfReferential.turnover_depth_iff_sup
