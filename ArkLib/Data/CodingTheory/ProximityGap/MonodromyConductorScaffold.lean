/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KatzEffectiveGaussSum

/-!
# The monodromy/conductor scaffold for the prize core (#407)

This file makes the **geometric (étale-cohomology) program** for `M(n) ≤ √(2n·ln q)` explicit and
**modular**, decomposing the named open input `EffectiveConductorBound` into its two genuine
arithmetic-geometry constituents, with the *provable arithmetic glue* between them machine-checked here.

## The program (honest map of what is open and why)

**Correction (audit 2026-10-28, PG-107): the cited source does not prove the prize maximum.** An
earlier version of this header said the prize sup-norm bound `M(n) ≈ √(n·ln q)` is "a theorem as
`q → ∞`" by Rojas-León (arXiv:2207.12439) / Katz [Kat88]. That overstates the source. Rojas-León's
Theorem 1 fixes the dimension, the exponent vectors and the twists over a base finite field and
proves **torus equidistribution over extension fields as the extension degree `m → ∞`**, under
independence hypotheses. Such fixed-dimensional weak equidistribution does **not** give a uniform
deterministic maximum over a growing family of subgroup periods (`n → ∞` with `q`), nor the
extreme-value (`√(n·ln q)`, Gumbel-scale) behaviour of that maximum. An effective growing-parameter
equidistribution statement plus a separate maximum argument would be needed before any source could
be said to prove this bound; neither is formalized here, and the cited source does not supply them.
The `√(n·ln q)` scale is a heuristic / conjectural target, not a cited theorem.

**What this file formalizes.** The definitions below are scalar moment inequalities on the additive
energy `rEnergy G r`; there is no sheaf, monodromy group, or conductor construction in Lean. The
words "Deligne", "conductor" and "monodromy" name the *intended* (unformalized) geometric source of
each scalar hypothesis, not anything proved or specialized here:

* **(I) `DeligneEffectiveEquidistribution`** — the scalar inequality "the `r`-th energy cumulant
  deviates from the Wick value by at most `cond · √q`". The intended source is a Weil-II-type
  estimate for a suitable sheaf; no such sheaf or estimate is constructed or proved, so this is an
  **unformalized geometric input** carried as a hypothesis (with `cond` an arbitrary real).

* **(II) `ConductorGeometricBound`** — the scalar inequality `cond ≤ K^r`. Its docstring below
  records that the naive reading "`cond` is a sheaf conductor and `K = O(1)`" is **false** (the
  conductor is rank-driven `~ n^{2r-1}`); the meaningful content is an effective cancellation base
  `K`, which is the recognized open core (BGK-type square-root cancellation for subgroup character
  sums; SOTA `n^{1−1/2880}`, half a power short). Carried as a hypothesis.

`(I) ∧ (II) ⟹ EffectiveConductorBound` is then **pure arithmetic**, proven below — the valid
conditional content of this file. It discharges neither (I) nor (II), and it does not prove any
specialization of the cited geometric results.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.CumulantGaussPeriodBound
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.KatzEffectiveGaussSum

namespace ArkLib.ProximityGap.MonodromyConductorScaffold

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **(I) "Deligne effective equidistribution", as a named scalar hypothesis.**  The cumulant
deviates from the real-Gaussian (Wick) value by at most `cond · √q`, for an arbitrary real `cond`.
The intended source is a Weil-II-type estimate for a suitable sheaf attached to the Gauss-sum
family, with `cond` its conductor; no such sheaf, conductor or estimate is constructed or proved
(Mathlib has no étale cohomology), and the cited fixed-dimensional equidistribution theorems do
not by themselves give this inequality uniformly in a growing `n` (PG-107).  Hence an
unformalized hypothesis, not a proved specialization. -/
def DeligneEffectiveEquidistribution (G : Finset F) (r : ℕ) (cond : ℝ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      + cond * Real.sqrt (Fintype.card F)

/-- **(II) The effective-cancellation bound, as a named hypothesis = the OPEN core.**  The cumulant
deviation is `≤ K^r·√q` with `K = O(1)`.
**SHARPENED (dual-assault conductor angle, 2026-06-13):** the *crude* sheaf conductor reading of (II) is
FALSE — the conductor of `M^{*r}` (= `dim H¹_c` of the moment sheaf) is **rank-driven `~ n^{2r-1}`** with
**Swan = 0** (all Kummer sheaves tame, NOT factorial-from-wild-ramification), so the naive Weil-II bound
`cond ≤ K^r` with `K=O(1)` does NOT hold from the conductor; Weil-II over the `n^{2r-1}`-dim `H¹_c` is
lossy by `√rank = n^{r-1/2}` (exactly the `n^{1/2}`-per-step L² deficit).  The genuine `K` here is the
**effective Frobenius-eigenvalue-cancellation base** (measured `K ≈ 1.28`, `probe_conductor_prize_regime.py`)
— it captures the actual cancellation in the WEIGHTS, which requires the joint equidistribution of the
Gauss-sum arguments at fixed `q`, NOT a small conductor.  That is the recognized open core (BGK; the
large-sieve angle shows it is dimension-obstructed in-regime: effective only when `f ≤ √q ⟺ n ≳ √p`,
which the prize `n ≪ √p` violates by construction). -/
def ConductorGeometricBound (cond K : ℝ) (r : ℕ) : Prop :=
  cond ≤ K ^ r

/-- **The monodromy/conductor toolkit, its provable (conditional) content.**  The scalar
hypotheses (I) and (II) yield `EffectiveConductorBound` — and hence, via
`KatzEffectiveGaussSum.worstCaseIncompleteSumBound_of_effectiveConductorBound`, the per-frequency bound
and the `δ*` floor.  This is the modular reduction of the open input to its two arithmetic-geometry
constituents; the implication is pure arithmetic (monotonicity of the error term), proven here. -/
theorem effectiveConductorBound_of_deligne_and_conductor {G : Finset F} {r : ℕ} {cond K : ℝ}
    (hI : DeligneEffectiveEquidistribution G r cond)
    (hII : ConductorGeometricBound cond K r) :
    EffectiveConductorBound G r K := by
  unfold DeligneEffectiveEquidistribution at hI
  unfold ConductorGeometricBound at hII
  unfold EffectiveConductorBound
  have hsqrt : 0 ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  have herr : cond * Real.sqrt (Fintype.card F) ≤ K ^ r * Real.sqrt (Fintype.card F) :=
    mul_le_mul_of_nonneg_right hII hsqrt
  calc (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          + cond * Real.sqrt (Fintype.card F) := hI
    _ ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          + K ^ r * Real.sqrt (Fintype.card F) := by linarith [herr]

/-- **End-to-end geometric reduction (modular).**  The two arithmetic-geometry inputs discharge the
in-tree `WorstCaseIncompleteSumBound` at the effective Katz scale.  Composing with the proven downstream
chain pins `δ*` at the prize floor — conditional on the two scalar hypotheses (I) (an
unformalized geometric input, not proved for this family) and (II) (the effective `K = O(1)`
cancellation base, the open core).  Everything between is machine-checked. -/
theorem worstCaseIncompleteSumBound_of_geometricInputs {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {cond K : ℝ} (hr : 1 ≤ r)
    (hI : DeligneEffectiveEquidistribution G r cond)
    (hII : ConductorGeometricBound cond K r) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        + K ^ r * Real.sqrt (Fintype.card F)) ^ ((r : ℝ)⁻¹)) :=
  worstCaseIncompleteSumBound_of_effectiveConductorBound hψ hr
    (effectiveConductorBound_of_deligne_and_conductor hI hII)

end ArkLib.ProximityGap.MonodromyConductorScaffold
