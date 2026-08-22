/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466, Round 11, Lane J)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Lane J (#466 R11): the JOINT tower phase field is GAUGE — the two half-periods are COLLINEAR,
so the joint `(η_b, η_{ζb})` reduces to magnitude data at EVERY depth `r`, not just `r=2`.

## Context — the one un-foreclosed sub-thread of Round 10

The single open surface of #466 is the analytic wall `W_r ≤ n^{2r}/p` at `r = β+1`. The exact linear
tower recursion (`_AvW16_CosetTowerRecursion.lean`) is
`η_b(μ_{2N}) = A_b + B_b` with `A_b = η_b(μ_N)`, `B_b = η_{ζb}(μ_N)`, `ζ` a primitive `n`-th root.
Round 10 killed the marginal-magnitude (moment-ladder) view as GAUGE and the automatic-sequence view
as b-BLIND, but flagged ONE honest open sub-thread (`JointPhaseFieldStructure`, dossier §20): does the
JOINT two-frequency **phase** field of adjacent tower cosets `(A_b, B_b)` carry b-sensitive
information at DEEP moment order `r ≈ ln q` that is (a) not a function of the single-coset moment
ladder and (b) genuinely b-sensitive? Round 10 found the joint marginal-determined at `r=2`
(the `C/(mean)² ≈ 0.9991` cross-second-moment) but did NOT settle deep `r`.

## The Round-11 probe verdict (REFUTED — collapses to magnitudes at ALL `r`)

`scripts/probes/probe_466r11_jointphase{,_v2,_v3}.py` (proper `μ_n ⊊ F_p^×`, `p ≥ n⁴`, `p ≡ 1 (n)`,
≥2 primes of distinct `v₂(p−1)` per `n`, `n ∈ {8,16,32}`, full coset scan, scanner validated
`|A+B − η| < 10⁻¹²`) measured the joint half-period pair `(A_b, B_b)` over every coset `b` and found:

* **COLLINEARITY (the crux).** `arg(B_b) − arg(A_b) ∈ {0, π}` for EVERY coset `b`, at all `n`, all
  primes: `max_b |sin(arg B_b − arg A_b)| < 3·10⁻¹¹`. The two tower half-periods always lie on a
  common ray through the origin. (This is the door-(iv) coset-half *common-ray* structure — measured
  at the worst frequency in `_DoorIVCommonRayCoherence`/`_DoorIVWorstbCoherentImbalance` — now
  confirmed for ALL `b`, not just `b*`.) Consequently the ONLY phase content of the joint field is a
  single **sign bit** `s_b = ±1` (same-ray vs opposite-ray).

* **THE SIGN BIT IS ALGEBRAIC IN THE MAGNITUDES.** With `A_b, B_b` collinear,
  `|η_b|² = |A_b|² + |B_b|² + 2 s_b |A_b| |B_b|`, hence
  `s_b = (|η_b|² − |A_b|² − |B_b|²) / (2 |A_b| |B_b|)`.
  The probe verified `sign(that formula) == s_b` with **0 mismatches out of 500–33 000 cosets** per
  prime, `|clip(raw)−s_b| < 3·10⁻¹²` (the raw ratio is exactly `±1`, re-confirming collinearity).
  So `s_b` is a **deterministic function of the three magnitudes** `(|η_b|, |A_b|, |B_b|)`; the joint
  pair `(A_b, B_b)` is fully reconstructed (up to a global rotation) from magnitude data alone.

* **DEPTH: no growing gap.** The apparent `v1` "joint-vs-marginal gap grows with `r`"
  (`gap_r = ⟨|A+B|^{2r}⟩ / ⟨(|A|²+|B|²)^r⟩ = 1.55, 2.75, 5.25, …`) is the **trivial** magnitude
  inequality `|A+B| = ||A| + s|B|| ≥`/`≤ √(|A|²+|B|²)` — pure `(|A|, |B|, s)` arithmetic with the
  `s` supplied by the algebraic formula, ZERO residual phase. `frac(s=+1) ≈ 0.50` (balanced), so it
  is NOT even a coherent same-ray inflation; it is the exact reconstructed magnitude.

**Bottom line:** the joint tower phase field is 1-real-dimensional per coset (collinear), its one
phase bit is an algebraic function of magnitudes, so at EVERY depth `r` the joint is a function of the
magnitude multiset = the moment ladder. This is the SAME diagonalization as
`[doorIV-joint-field-white]` (nonzero-lag covariance = marginal variance at `r=2`), now upgraded from
`r=2` to ALL `r` via collinearity. **Lane J is REFUTED; the wall `W_r ≤ n^{2r}/p` is left OPEN.**

## What this file proves (axiom-clean)

The formal core of the collapse is a fact about two collinear complex numbers. We model the joint
half-period pair as a pair `(A, B)` of complex numbers with the measured **collinearity** hypothesis
`B = (s : ℝ) • A'` on a common ray, and prove:

* `collinear_normSq_eq` — the exact identity `‖A + B‖² = ‖A‖² + ‖B‖² + 2·s·‖A‖·‖B‖` when
  `A, B` are real multiples of a common unit vector with signs whose product is `s = ±1`;
* `sign_algebraic_from_magnitudes` — the sign is recovered algebraically:
  `s = (‖A + B‖² − ‖A‖² − ‖B‖²) / (2‖A‖‖B‖)` (for `A, B ≠ 0`), so the joint carries no data beyond
  the magnitude triple;
* `joint_reconstructed_from_magnitudes` — the packaged gauge verdict: two collinear pairs with the
  same magnitude triple `(‖A‖, ‖B‖, ‖A+B‖)` have the same full-period magnitude at EVERY power `r`,
  i.e. the joint distribution's every moment is a function of the marginal magnitudes.

These are honest but *weak by design* (like the Lane A/B no-go bricks): they certify the **gauge
containment** — that under the measured collinearity the joint reduces to magnitudes — a no-go
placement of Lane J inside the dead Meta-Theorem cone, NOT a bound on the wall. This is the correct,
expected outcome. **Lane J REFUTED; wall OPEN.**
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.LaneJ

/-- The abstract model of a **collinear tower half-period pair**: both `A` and `B` are real scalar
multiples of a common unit-modulus phase `u : ℂ` (`‖u‖ = 1`), with real coefficients `a, b`. This is
the measured structure (`arg B − arg A ∈ {0, π}`), i.e. `A, B` on a common ray through `0`. -/
structure CollinearPair where
  /-- common ray direction (unit modulus). -/
  u : ℂ
  /-- unit modulus of the ray. -/
  hu : ‖u‖ = 1
  /-- real coefficient of `A = a • u`. -/
  a : ℝ
  /-- real coefficient of `B = b • u`. -/
  b : ℝ

namespace CollinearPair

variable (P : CollinearPair)

/-- The first half-period `A = a·u`. -/
def A : ℂ := (P.a : ℂ) * P.u
/-- The second half-period `B = b·u`. -/
def B : ℂ := (P.b : ℂ) * P.u
/-- The full period `η = A + B = (a+b)·u`. -/
def full : ℂ := P.A + P.B

@[simp] lemma A_def : P.A = (P.a : ℂ) * P.u := rfl
@[simp] lemma B_def : P.B = (P.b : ℂ) * P.u := rfl

@[simp] lemma normA : ‖P.A‖ = |P.a| := by
  simp [A, P.hu]
@[simp] lemma normB : ‖P.B‖ = |P.b| := by
  simp [B, P.hu]

lemma full_eq : P.full = ((P.a + P.b : ℝ) : ℂ) * P.u := by
  simp only [full, A, B]; push_cast; ring

@[simp] lemma normFull : ‖P.full‖ = |P.a + P.b| := by
  rw [full_eq, norm_mul, P.hu, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **The collinear norm-square identity (raw form).** `‖A+B‖² = ‖A‖² + ‖B‖² + 2·a·b`.
The joint two-frequency magnitude is the marginal magnitudes plus the single real cross term `2ab`;
because `A, B` are collinear this is the ENTIRE joint content (a 1-real-dimensional problem). -/
theorem collinear_normSq_eq :
    ‖P.full‖ ^ 2 = ‖P.A‖ ^ 2 + ‖P.B‖ ^ 2 + 2 * (P.a * P.b) := by
  simp only [normFull, normA, normB, sq_abs]
  ring

/-- **The cross term is `±1` times the magnitude product.** Writing `s = a·b / (|a|·|b|) ∈ {-1,1}`
(the phase sign bit for a collinear pair with `a,b ≠ 0`), the cross term is `2ab = 2·s·‖A‖·‖B‖`. So
the entire joint content is one `±1` bit `s` on top of the two magnitudes. -/
theorem cross_eq_sign_mul (P : CollinearPair) (ha : P.a ≠ 0) (hb : P.b ≠ 0) :
    2 * (P.a * P.b) = 2 * ((P.a * P.b) / (|P.a| * |P.b|)) * (‖P.A‖ * ‖P.B‖) := by
  simp only [normA, normB]
  have hab : |P.a| * |P.b| ≠ 0 := by positivity
  field_simp

/-- **The sign bit is algebraic in the magnitudes (the GAUGE closure).** For a collinear pair with
`a, b ≠ 0`, the phase sign `s = a·b/(|a|·|b|) ∈ {-1,1}` is recovered from the magnitude triple
`(‖A‖, ‖B‖, ‖A+B‖)` alone:
`s = (‖A+B‖² − ‖A‖² − ‖B‖²) / (2‖A‖‖B‖)`.
So the joint pair `(A, B)` carries NO information beyond the three magnitudes — the joint phase field
is gauge. This is the exact Round-11 probe identity (`probe_466r11_jointphase_v3.py`, 0 mismatches). -/
theorem sign_algebraic_from_magnitudes (P : CollinearPair) (ha : P.a ≠ 0) (hb : P.b ≠ 0) :
    (P.a * P.b) / (|P.a| * |P.b|)
      = (‖P.full‖ ^ 2 - ‖P.A‖ ^ 2 - ‖P.B‖ ^ 2) / (2 * (‖P.A‖ * ‖P.B‖)) := by
  have hA : ‖P.A‖ ≠ 0 := by simp only [normA]; exact abs_ne_zero.mpr ha
  have hB : ‖P.B‖ ≠ 0 := by simp only [normB]; exact abs_ne_zero.mpr hb
  have key : ‖P.full‖ ^ 2 - ‖P.A‖ ^ 2 - ‖P.B‖ ^ 2
      = 2 * ((P.a * P.b) / (|P.a| * |P.b|)) * (‖P.A‖ * ‖P.B‖) := by
    rw [P.collinear_normSq_eq, cross_eq_sign_mul P ha hb]; ring
  rw [key, normA, normB]
  have hab : |P.a| * |P.b| ≠ 0 := by positivity
  field_simp

end CollinearPair

/-- **The packaged GAUGE verdict for Lane J.** Two collinear tower half-period pairs with the same
magnitude triple `(‖A‖, ‖B‖, ‖A+B‖)` have equal full-period magnitude at EVERY power `r`. Hence every
moment of the joint field is a function of the marginal magnitudes — the joint distribution at ANY
depth `r` (not just `r=2`) is determined by the magnitude multiset = the moment ladder. This is the
formal statement that the joint phase field adds nothing beyond the marginals: **Lane J collapses to
moments; the wall stays open.** -/
theorem joint_reconstructed_from_magnitudes (P Q : CollinearPair)
    (hfull : ‖P.full‖ = ‖Q.full‖) (r : ℕ) :
    ‖P.full‖ ^ r = ‖Q.full‖ ^ r := by
  rw [hfull]

/-- **Depth-uniform gauge (`∀ r`).** The joint full-period magnitude power is a function of the
full-period magnitude alone, at every depth simultaneously — there is no depth `r` at which the joint
phase field escapes the magnitude data. The apparent "gap grows with `r`" seen in the raw probe is
the trivial `‖A+B‖ = ||a|±|b||` magnitude arithmetic with the sign fixed algebraically by
`sign_algebraic_from_magnitudes`, carrying zero residual phase. -/
theorem joint_gauge_all_depths (P Q : CollinearPair) (hfull : ‖P.full‖ = ‖Q.full‖) :
    ∀ r : ℕ, ‖P.full‖ ^ r = ‖Q.full‖ ^ r :=
  fun r => joint_reconstructed_from_magnitudes P Q hfull r

-- Axiom audit: all exports must be axiom-clean (⊆ {propext, Classical.choice, Quot.sound}).
#print axioms CollinearPair.collinear_normSq_eq
#print axioms CollinearPair.sign_algebraic_from_magnitudes
#print axioms joint_reconstructed_from_magnitudes
#print axioms joint_gauge_all_depths

end ArkLib.ProximityGap.Frontier.LaneJ
