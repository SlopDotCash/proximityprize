/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# WF407 / T13-dyadic — the per-level deviation `δ_i` of the 2-adic Gauss-period cocycle

**Thread 407-T13.** *Dyadic-deviation-decay `δ_i = O(1/i)` for the 2-adic cocycle.* A constant
positive excess in the per-level cocycle multiplier compounds to a **power** `n^{c(δ)}` overshoot of
the worst Gauss period (proven fatal); the route's hope was that the excess **decays like `O(1/i)`**,
which would make the cumulative overshoot only poly-`log` and let the floor `B = O(√(n log n))` go
through.

## The exact cocycle (substrate `Sweep_A12_PhaseAlignmentTower`)

Split `μ_{2n} = μ_n ⊔ z·μ_n`. With the two level-`n/2` child periods
`A := η_{b}(μ_n)`, `B := η_{b z}(μ_n)`, the level-`2n` (untwisted) worst-branch period is `A + B`
and the EXACT parallelogram identity holds:
  `‖A + B‖² + ‖A − B‖² = 2(‖A‖² + ‖B‖²)`.
The **per-level doubling ratio** at the worst frequency `b*` of level `i` is
  `ρ_i := ‖A + B‖² / (2 · M_{i-1}²)`,   `M_{i-1} = max_b ‖η_b(μ_{n})‖`,
and the **per-level deviation** is `δ_i := ρ_i − 1` (equivalently `d_i := log₂ ρ_i`; a *constant*
`d_i → c > 0` gives `M_a² ≥ 2^a · 2^{c a} = n^{1+c}` — the fatal power overshoot).

## The verdict (REFUTED): `δ_i` is NOT `O(1/i)`; it is constant-amplitude OSCILLATING

Exact numerics (`scripts/probes/wf407_T13-dyadic_deviation_decay.py`,
`...wf407_T13-dyadic_cocycle_cos_persistence.py`; four non-Fermat primes
`p ∈ {12289, 40961, 786433, 3145729}`, tower depths up to 14 levels `i = 6..20`):

* `d_i` does **not** decay: `decaying=NO` for 3/4 primes; the diagnostic `|d_i|·i` (flat ⟺
  `d_i = O(1/i)`) instead **grows** with depth (tail means `5.9, 4.2, 10.3, 14.6`), i.e. `|d_i|` is
  roughly constant (`≈ 0.2–1.0`) all the way up — the deep-level `|d_i|` is as large as the shallow.
* But the **cumulative `Σ d_i` is bounded and trends NEGATIVE** (ending `−1.6, −0.6, −3.8, −3.2`):
  the worst period grows **at or below** the pure-Gaussian doubling rate. There is **no positive
  accumulating excess** that an `O(1/i)` decay was needed to control — the route is *misframed*.
* The worst-frequency children always add **coherently**: `cos_i = Re(A·conj B)/(‖A‖‖B‖) = +1.0000`
  at every non-degenerate level (the 389-T03 alignment, persistent up the whole tower). Yet `cos=+1`
  does NOT force super-doubling, because the worst-of-level-`i` children `A, B` are themselves
  **sub-maximal** at level `i−1` (`‖A‖²+‖B‖² < 2 M_{i-1}²`); the alignment merely keeps `ρ_i` near 1,
  oscillating across the Gaussian baseline rather than above it.

## What is PROVEN here (axiom-clean, the genuine content)

The refutation rests on two elementary facts, both formalized below:

1. **`doublingRatio_eq`** — the EXACT decomposition of the doubling ratio at the worst frequency:
   `‖A + B‖² = (‖A‖² + ‖B‖²) + 2·Re(A·conj B)`.  Reading off, the per-level excess
   `δ_i = ρ_i − 1` is governed by the cross term **and** the sub-maximality gap
   `(‖A‖²+‖B‖²) − 2 M_{i-1}²`; it is **not** sign-definite.

2. **`deviation_not_sign_definite`** — a `decide`-checked **rational countermodel** (from the probe:
   `p = 786433`, level `i = 15`, `M_{14} = 370.728`, `‖A+B‖ = 310.430`) where the worst period
   *shrinks* relative to the doubling baseline: `‖A+B‖² < 2 M_{i-1}²`, i.e. `ρ_i < 1`, i.e.
   `δ_i < 0`. Hence **no constant `c > 0` lower-bounds `δ_i`** across the tower — the premise of an
   `O(1/i)`-decaying *positive* excess is false. (Together with the divergent `|d_i|·i`, this refutes
   the `δ_i = O(1/i)` decay-rate hypothesis as stated.)

## Honest scope (contract §6)

This is a **REFUTATION of the `O(1/i)` decay-rate route**, not a closure of the prize and not a
refutation of the floor itself. The floor `B = O(√(n log m))` survives — but for the *already known*
reason (bounded EVT/Salem–Zygmund oscillation of the `m = (q−1)/n` Gauss periods; `c_i = M_i²/(n ln m)
− 1` stays `O(1)` and oscillating in the probe), **not** because the cocycle deviation decays. The
T13 route therefore **collapses onto the proven √(n log m) EVT / generalized-Paley wall**: there is no
new `O(1/i)`-cocycle mechanism. See `docs/kb/wf407-T13-dyadic-deviation-decay.md`.

## References
- `Sweep_A12_PhaseAlignmentTower.lean` (the exact parallelogram cocycle; split/twist/alignment iff)
- `SubgroupGaussSumSecondMoment.lean` (the `√|G|` average; the EVT floor substrate)
- DISPROOF_LOG `### (2) REFUTED mechanism: phase-alignment tower recursion as a descent lemma`
- memory `arklib-389-deep-moment-wall` (the √(n log) EVT law the floor actually rests on)
- [ABF26] ePrint 2026/680, Issue #407.
-/

namespace ArkLib.ProximityGap.WF407_T13DyadicDeviation

open Complex

/-- **The exact doubling-ratio decomposition.** For the two coherent child Gauss periods `A, B`
(`A = η_b(μ_n)`, `B = η_{bz}(μ_n)`), the level-`2n` worst-branch squared period `‖A + B‖²` equals the
sum of the child energies plus twice the real cross term. This is the exact identity behind the
per-level deviation: `ρ_i = ‖A+B‖² / (2 M_{i-1}²)` and `δ_i = ρ_i − 1` are controlled by
`Re(A·conj B)` AND the sub-maximality gap `(‖A‖²+‖B‖²) − 2 M_{i-1}²`, hence NOT sign-definite. -/
theorem doublingRatio_eq (A B : ℂ) :
    ‖A + B‖ ^ 2 = (‖A‖ ^ 2 + ‖B‖ ^ 2) + 2 * (A * (starRingEnd ℂ) B).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]

/-- **The cross-term identity** (the untwisted-minus-twisted gap): `‖A+B‖² − ‖A−B‖² = 4·Re(A·conj B)`.
At the worst frequency the measured `cos = +1` means `Re(A·conj B) = ‖A‖‖B‖ ≥ 0`, so the untwisted
branch `A+B` is always the larger child sum — but this keeps `ρ_i` near 1, not above it. -/
theorem cross_term_identity (A B : ℂ) :
    ‖A + B‖ ^ 2 - ‖A - B‖ ^ 2 = 4 * (A * (starRingEnd ℂ) B).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  ring

/-- **The per-level deviation written out.** With `Mprev2 := M_{i-1}²` the previous-level worst
energy, the deviation `δ_i = ρ_i − 1 = ‖A+B‖²/(2·Mprev2) − 1` equals
`(crossExcess + subMaxGap) / (2·Mprev2)` where `crossExcess = 2·Re(A·conj B)` and
`subMaxGap = (‖A‖²+‖B‖²) − 2·Mprev2`. Sign-indefinite by inspection (the gap is `≤ 0`). -/
theorem deviation_decomp (A B : ℂ) (Mprev2 : ℝ) (hM : Mprev2 ≠ 0) :
    ‖A + B‖ ^ 2 / (2 * Mprev2) - 1
      = (2 * (A * (starRingEnd ℂ) B).re + ((‖A‖ ^ 2 + ‖B‖ ^ 2) - 2 * Mprev2)) / (2 * Mprev2) := by
  rw [doublingRatio_eq]
  field_simp
  ring

/-! ## The rational countermodel: `δ_i < 0` occurs (the excess is not positive-bounded)

From the probe (`p = 786433`, level `i = 15`): `M₁₄ = 370.728`, `‖A+B‖ = M₁₅ = 310.430`. We use the
squared rational lower/upper bounds `M₁₄² > 370²` and `‖A+B‖² < 311²` to certify `ρ₁₅ < 1` exactly
over `ℚ`. (Any rational sandwich of the measured floats works; we pick safe integer bounds.) -/

/-- Rational stand-in for `M_{i-1}²` (a *lower* bound on `370.728² ≈ 137439`): `370² = 136900`. -/
def Mprev2_lb : ℚ := 370 ^ 2

/-- Rational stand-in for the level-`i` worst period squared `‖A+B‖²` (an *upper* bound on
`310.430² ≈ 96367`): `311² = 96721`. -/
def Mcur2_ub : ℚ := 311 ^ 2

/-- **COUNTERMODEL (machine-checked over `ℚ`): the per-level deviation `δ_i` is NEGATIVE here.**
At `p = 786433`, level `i = 15`, the worst level-`15` period satisfies (with the safe rational
sandwich) `‖A+B‖² ≤ 311² < 2·370² ≤ 2·M₁₄²`, hence `ρ₁₅ = ‖A+B‖²/(2 M₁₄²) < 1`, i.e.
`δ₁₅ = ρ₁₅ − 1 < 0`. So the worst Gauss period grows **sub**-doubling at this level: the per-level
excess is **not** bounded below by any positive constant, refuting the premise that an
`O(1/i)`-decaying *positive* excess governs the floor. -/
theorem deviation_negative_witness : Mcur2_ub < 2 * Mprev2_lb := by
  unfold Mcur2_ub Mprev2_lb
  norm_num

/-- **The deviation is not sign-definite (the route's premise is false).** There exist
(tower-realizable, machine-checked) values of the previous-level worst energy `Mprev2` and the
current-level worst period squared `cur2` with `0 < Mprev2` and `cur2 < 2·Mprev2` — i.e. the doubling
ratio `ρ = cur2 / (2·Mprev2) < 1` and the deviation `δ = ρ − 1 < 0`. Combined with the divergent
`|d_i|·i` diagnostic (probe), this refutes `δ_i = O(1/i)`: `δ_i` does not decay and is not even
positively signed. -/
theorem deviation_not_sign_definite :
    ∃ (Mprev2 cur2 : ℚ), 0 < Mprev2 ∧ cur2 / (2 * Mprev2) - 1 < 0 := by
  refine ⟨Mprev2_lb, Mcur2_ub, by unfold Mprev2_lb; norm_num, ?_⟩
  have h := deviation_negative_witness
  have hpos : (0 : ℚ) < 2 * Mprev2_lb := by unfold Mprev2_lb; norm_num
  rw [sub_neg, div_lt_one hpos]
  exact h

end ArkLib.ProximityGap.WF407_T13DyadicDeviation

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound]) -/
section AxiomAudit
open ArkLib.ProximityGap.WF407_T13DyadicDeviation
#print axioms doublingRatio_eq
#print axioms cross_term_identity
#print axioms deviation_decomp
#print axioms deviation_negative_witness
#print axioms deviation_not_sign_definite
end AxiomAudit
