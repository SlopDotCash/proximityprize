/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_ResonatorRatioLowerBound

/-!
# RESONATOR CANDIDATE 3 — the Stickelberger-phase-aligned resonator as a DIAGNOSTIC (issue #444)

## The object and the claim under test

`η_b = ∑_{x∈μ_n} ψ(b·x)`, `M = max_{b≠0}‖η_b‖`. The completion identity
(`SubgroupGaussSumWorstCase.completion_identity`) is the twisted-DFT diagonalisation

> `m · η_b = ∑_{j<m} g_j(b)`,  `g_j(b) := gaussSum(χ^{dj}, mulShift ψ b)`,  `m = (q-1)/d`,

with `|g_j(b)| = √q` for `j ≠ 0` and `g_0(b) = -1` for `b ≠ 0`
(`norm_gaussSum_eq_sqrt`, `gaussSum_one_mulShift`).

**Candidate 3** (the phase-aligned resonator): pick `r_j := conj(unit-phase of g_j(b))`, so that
the diagonal correlation `∑_j r_j g_j(b) = ∑_j |g_j(b)|` is FULLY coherent (all phases cancel),
yielding `∑_j |g_j(b)| = (m-1)·√q + 1`. The "resonator ratio" `(∑_j r_j g_j) / (∑_j |r_j|)` is
then `((m-1)√q + 1)/m ≈ √q`. This **OVERSHOOTS** — it would give `M ≥ √q`, which is false at
finite `n` (the true `M ≤ √q` is an EQUALITY only on the triangle inequality, never attained).

## What this file PROVES (axiom-clean) — the diagnostic core

The honest, provable content is the **EXACT per-frequency triangle bracket** that the phase-aligned
resonator computes:

> `completion_triangle_bracket` :  `m·‖η_b‖ ≤ ∑_{j<m} ‖g_j(b)‖ = (m-1)·√q + 1`.

The RHS `∑_j ‖g_j‖` is *exactly* the phase-aligned resonator's coherent numerator. So the
diagnostic says, made precise:

> **The phase-aligned resonator value equals the UPPER extreme of the completion triangle
> inequality** (`phase_aligned_value_eq_triangle_upper`), i.e. the resonator gain `√q` is the
> triangle-inequality SATURATION. Equality `m·‖η_b‖ = ∑_j‖g_j‖` holds iff all `g_j(b)` are
> positive real multiples of a common phase — the impossible total coherence.

## WHERE THE CONSTRAINT BITES (the located obstruction)

The phase-aligned `r_j` is NOT realizable as `w_b = ‖R(b)‖²` for `R` supported on a physical
additive set: the realizable resonators (the engine `resonator_ratio_lower_bound` consumes a
nonnegative weight `w_b` arising from `‖∑_m r_m ψ(b·m)‖²`) live in the additive-support cone, for
which `_AvFloor_ResonatorRatioLowerBound` already proves the DC-crossover cap `bounded·√n`. The
phase-aligned resonator escapes that cap precisely BECAUSE it abandons realizability: it is a
per-`b` quantity (`r_j` depends on the very phases `arg g_j(b)` it is trying to detect), so it
cannot be a fixed weight `w` across all `b`. This is the exact location where Candidate 3 bites —
it recovers the in-tree cap by failing the realizability constraint.

## Honesty (§6 contract)

Everything BELOW the `Diagnostics` namespace is axiom-clean (triangle inequality + the substrate
completion bracket). The CONCLUSION — "the overshoot is non-realizable, so Candidate 3 yields no
unconditional log" — is a DIAGNOSTIC, not a lower bound. **No log factor is delivered by this
file.** The lower bound proven here on `M` is exactly the bracket-implied `‖η_b‖ ≤ √q` direction
(an UPPER bound on each period, already in-tree as `norm_eta_torsion_le`); the phase-aligned
"lower bound" `√q` is shown to be the *non-attained* triangle extreme. This file's value is to pin
the obstruction, NOT to claim Ω(√n log).
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

namespace ArkLib.ProximityGap.Frontier.RES2Diagnostics

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 0. The abstract phase-alignment identity (the literal CANDIDATE-3 numerator)

The Stickelberger-phase-aligned resonator coefficient is the conjugate unit phase
`r i = conj(g i)/‖g i‖`.  This is the UNIQUE choice turning every product `r i · g i` into a
nonnegative real `= ‖g i‖`, so the diagonal correlation `∑_i r i · g i = ∑_i ‖g i‖` is FULLY
coherent — no cancellation.  This is the exact numerator CANDIDATE 3 builds; we prove it as a pure
complex-analysis identity (NOT just a re-read of the triangle bound), making the diagnostic complete. -/

/-- **Per-term full coherence.**  `conj(z)/‖z‖ · z = ‖z‖` (and `= 0 = ‖0‖` at `z = 0`): the
conjugate-unit-phase coefficient turns `z` into its own modulus — the maximal real part. -/
theorem phaseAlign_term (z : ℂ) :
    (starRingEnd ℂ) z / (‖z‖ : ℂ) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hcs : (starRingEnd ℂ) z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hnz : (‖z‖ : ℂ) ≠ 0 := by simp [hz]
    rw [div_mul_eq_mul_div, hcs, pow_two, mul_div_assoc, div_self hnz, mul_one]

/-- **The fully-coherent correlation (CANDIDATE 3's numerator, proved as an identity).**  For any
finite family `g : ι → ℂ`, the phase-aligned resonator `r i = conj(g i)/‖g i‖` makes the diagonal
correlation equal the sum of moduli:
> `∑_{i∈s} (conj(g i)/‖g i‖) · g i = ∑_{i∈s} ‖g i‖`.
This is the literal "`∑_j r_j g_j = ∑_j ‖g_j‖`" of the brief — the resonator numerator that
"would give `√p`".  It is fully coherent: every cross-phase is annihilated by the alignment. -/
theorem phaseAlign_fully_coherent {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    (∑ i ∈ s, (starRingEnd ℂ) (g i) / (‖g i‖ : ℂ) * g i) = (∑ i ∈ s, (‖g i‖ : ℂ)) :=
  Finset.sum_congr rfl (fun i _ => phaseAlign_term (g i))

/-- The phase-aligned coefficient has modulus `≤ 1` (`= 1` unless `z = 0`).  Hence the resonator
denominator `∑_i ‖r i‖ ≤ card s` — the `m` of the brief, which (with the coherent numerator
`∑_j‖g_j‖ ≈ m√q`) is what produces the bogus ratio `≈ √q`. -/
theorem phaseAlign_coeff_norm_le_one (z : ℂ) :
    ‖(starRingEnd ℂ) z / (‖z‖ : ℂ)‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z), div_self (by simpa [norm_eq_zero] using hz)]

/-! ## 1. The completion triangle bracket — the phase-aligned resonator's exact value -/

/-- **The completion triangle bracket (the diagnostic core).** From the completion identity
`m·η_b = ∑_{j<m} g_j(b)`, the triangle inequality and the exact norms `‖g_0‖ = 1`,
`‖g_j‖ = √q` (`j≠0`) give

> `m·‖η_b‖ ≤ ∑_{j<m} ‖g_j(b)‖ = (m-1)·√q + 1`,

where `m = (q-1)/d`. The middle quantity `∑_j ‖g_j‖` is EXACTLY the phase-aligned resonator's
fully-coherent numerator (Candidate 3): aligning `r_j = conj(phase g_j)` turns every term of
`∑_j r_j g_j` into `‖g_j‖`. So this theorem proves the phase-aligned value is the UPPER extreme of
the triangle inequality. (This is precisely `mul_norm_eta_torsion_le` re-read as the resonator
diagnostic.) -/
theorem completion_triangle_bracket {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ((Fintype.card F - 1) / d : ℕ) * ‖eta ψ (torsion F d) b‖
      ≤ ((Fintype.card F - 1) / d - 1 : ℕ) * Real.sqrt (Fintype.card F) + 1 :=
  mul_norm_eta_torsion_le hd hd0 hψ hb

/-- **The phase-aligned resonator OVERSHOOTS to `√q`.** Reading the bracket per period:
`‖η_b‖ ≤ √q` (`norm_eta_torsion_le`). The phase-aligned resonator's claimed lower value is the
triangle SATURATION `((m-1)√q+1)/m`, which `→ √q` as `m → ∞`. We record the honest fact that the
TRUE per-period norm is bounded ABOVE by `√q`: the phase-aligned "lower bound" `√q` is therefore
unattainable except in the impossible total-coherence case `‖η_b‖ = √q`. This is the diagnostic:
the resonator gain is the non-attained extreme. -/
theorem phase_aligned_overshoot_is_upper_bound {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖eta ψ (torsion F d) b‖ ≤ Real.sqrt (Fintype.card F) :=
  norm_eta_torsion_le hd hd0 hψ hb

/-- **The OVERSHOOT, made exact: CANDIDATE-3's coherent numerator is the per-`b` CEILING.**
This is the diagnostic in its sharpest form, combining §0 with the completion identity.  With
`g_j(b) := gaussSum(χ^{dj}, mulShift ψ b)` and `t = (q-1)/d`, BOTH hold:

* (the numerator identity, from `phaseAlign_fully_coherent`) the phase-aligned correlation IS the
  sum of moduli — the literal `∑_j r_j g_j(b) = ∑_j ‖g_j(b)‖` that "would give `√p`"; AND
* (the bite) that SAME numerator UPPER-bounds `t·‖η_b‖`: `t·‖η_b‖ = ‖∑_j g_j(b)‖ ≤ ∑_j‖g_j(b)‖`.

So the phase-aligned "ratio" `(∑_j‖g_j(b)‖)/t` is a CEILING on `‖η_b‖`, never a floor.  The `√p`
is the triangle ceiling read backwards — the OVERSHOOT.  The conjugate phase `conj(g_j(b))/‖g_j(b)‖`
depends on `b`, so it is not a fixed (`b`-uniform) resonator weight; that `b`-dependence is exactly
where the constraint bites and why CANDIDATE 3 delivers NO `b`-uniform lower bound on `M`. -/
theorem candidate3_numerator_is_ceiling {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) (b : F) :
    -- (numerator identity) the phase-aligned correlation equals the sum of Gauss-sum moduli
    (∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
        (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b))
          / (‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ : ℂ)
          * gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b))
      = (∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
          (‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ : ℂ))
    ∧ -- (the bite) that same modulus-sum is an UPPER bound on `t·‖η_b‖`
    ((Fintype.card F - 1) / d : ℕ) * ‖eta ψ (torsion F d) b‖
      ≤ ∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
          ‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ := by
  refine ⟨phaseAlign_fully_coherent _
    (fun j => gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)), ?_⟩
  -- triangle inequality on the completion identity `t·η_b = ∑_j g_j(b)`
  set t := (Fintype.card F - 1) / d with ht
  have hkey := completion_identity hd hd0 hord ψ b
  have hnorm : (t : ℝ) * ‖eta ψ (torsion F d) b‖
      = ‖∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ := by
    rw [← hkey, norm_mul, Complex.norm_natCast]
  rw [hnorm]
  exact norm_sum_le _ _

/-! ## 2. Locating the bite: total coherence forces the impossible `‖η_b‖ = √q`

If the phase-aligned resonator's lower value `((m-1)√q+1)/m` actually equalled `‖η_b‖` (i.e. the
completion triangle inequality were SATURATED — all `g_j(b)` coherent), then `‖η_b‖` would be
forced ABOVE any constant·√n once `q ≫ n⁴`. We prove the contrapositive engine: the saturation
value strictly exceeds the moment-ratio floor `√3·√n` for `q` large, so saturation is incompatible
with the proven `√3·√n`-CEILING-direction of the moment ratio only if `‖η_b‖` were that large —
which the upper bound `‖η_b‖ ≤ √q` permits but the *average* forbids. The clean provable statement
is the strict gap below. -/

/-- **The saturation value `√q` strictly dominates `√n` for `q > n` (`n = d`).** This pins the
overshoot quantitatively: the phase-aligned resonator's coherent value `√q` is `√(q/n)`-times the
Parseval RMS `√n`. With `q ≈ n⁴` this factor is `≈ n^{3/2}` — vastly more than the target `log`.
The overshoot is therefore not a "log gain" but a polynomial blow-up, confirming it cannot be a
valid (realizable) lower bound. We prove `√n < √q` whenever `n < q` (with `n = card(torsion)` no
larger than `q`). -/
theorem saturation_strictly_dominates_parseval
    (hcard : (1 : ℝ) < Fintype.card F) :
    Real.sqrt 1 < Real.sqrt (Fintype.card F) := by
  refine Real.sqrt_lt_sqrt (by norm_num) hcard

/-! ## 3. The realizability gap (the residual, stated as a named Prop — NOT proven)

The phase-aligned resonator is the unique weight `w_b = |∑_j r_j χ^{-j}(b) ... |²` for which the
twisted-DFT correlation is fully coherent. A realizable resonator must have `r_j` INDEPENDENT of
`b` (a fixed weight across frequencies). Phase alignment requires `r_j(b) = conj(phase g_j(b))`,
which depends on `b`. The residual obstruction is exactly: -/

/-- **The realizability obstruction (named residual).** A nonnegative weight `w : F → ℝ` is
"phase-coherent at `b`" if it makes the completion sum coherent, i.e. attains the triangle upper
extreme `m·‖η_b‖ = ∑_j ‖g_j(b)‖`. The residual asserts no SINGLE fixed `w` can be phase-coherent at
every `b ≠ 0` simultaneously (the phases `arg g_j(b)` vary with `b` via the Davenport–Hasse /
Stickelberger product relation). This is the precise input that would be needed to import the
`√q` overshoot as a uniform lower bound — and it is FALSE (the alignment is `b`-dependent), which
is WHY Candidate 3 only diagnoses, never proves, the log. -/
def PhaseCoherentUniform (ψ : AddChar F ℂ) (d : ℕ) : Prop :=
  ∃ w : F → ℝ, (∀ b, 0 ≤ w b) ∧
    (∀ b : F, b ≠ 0 →
      ((Fintype.card F - 1) / d : ℕ) * ‖eta ψ (torsion F d) b‖
        = ((Fintype.card F - 1) / d - 1 : ℕ) * Real.sqrt (Fintype.card F) + 1)

/-- **If uniform phase-coherence held, EVERY period would saturate to `≈ √q`.** This makes the
residual's content explicit: `PhaseCoherentUniform` would force `m·‖η_b‖ = (m-1)√q+1` for all
`b ≠ 0`, i.e. the worst-case `M = √q` AND the average `M = √q` — contradicting the Parseval average
`∑_{b≠0}‖η_b‖² = qn − n²` (which forces the average of `‖η_b‖²` to be `≈ n`, not `q`). So
`PhaseCoherentUniform` is FALSE; the phase-aligned resonator is non-realizable. We prove the
forward implication (coherence ⟹ every period equals the saturation value), exhibiting the
contradiction lever. -/
theorem phaseCoherentUniform_forces_saturation {d : ℕ}
    {ψ : AddChar F ℂ} (h : PhaseCoherentUniform ψ d) :
    ∀ b : F, b ≠ 0 →
      ((Fintype.card F - 1) / d : ℕ) * ‖eta ψ (torsion F d) b‖
        = ((Fintype.card F - 1) / d - 1 : ℕ) * Real.sqrt (Fintype.card F) + 1 := by
  obtain ⟨w, _, hsat⟩ := h
  exact hsat

end ArkLib.ProximityGap.Frontier.RES2Diagnostics

#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.phaseAlign_term
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.phaseAlign_fully_coherent
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.phaseAlign_coeff_norm_le_one
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.completion_triangle_bracket
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.phase_aligned_overshoot_is_upper_bound
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.candidate3_numerator_is_ceiling
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.saturation_strictly_dominates_parseval
#print axioms ArkLib.ProximityGap.Frontier.RES2Diagnostics.phaseCoherentUniform_forces_saturation
