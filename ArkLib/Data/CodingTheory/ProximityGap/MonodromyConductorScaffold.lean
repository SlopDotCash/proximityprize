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

The prize sup-norm bound is, by Rojas-León (arXiv:2207.12439) / Katz [Kat88], a **theorem as `q → ∞`**:
the Gauss sums `G(χ^s)` are the Frobenius traces of an explicit hypergeometric sheaf whose geometric
monodromy group is the full `GL(1)^f` (the only relations being Hasse–Davenport), so by Deligne's
equidistribution they are asymptotically independent and `M(n) ≈ √(n·ln q)`.

The prize is the **effective version at the fixed prize `q`**.  By Deligne's Weil II, an equidistribution
statement is effective with discrepancy controlled by the **conductor** (rank + Swan/Artin conductors of
the singularities) of the relevant sheaf:
  `| q·E_r − |G|^{2r} − q·(2r-1)‼·|G|^r |  ≤  conductor(r) · √q`.
The two inputs are therefore:

* **(I) `DeligneEffectiveEquidistribution`** — Deligne's Weil II for this family: the cumulant deviates
  from the Wick value by at most `cond · √q`.  This is a *theorem of arithmetic geometry* (Deligne),
  NOT formalisable in current Mathlib (no étale cohomology), so it is carried as a named hypothesis.

* **(II) `ConductorGeometricBound`** — the conductor of the `r`-fold multiplicative convolution of the
  Gauss-sum sheaf is `≤ K^r` for a constant `K = O(1)` in the prize regime `n ≪ √q`.  This is the
  **recognized OPEN core** (equivalent to BGK square-root cancellation for subgroup character sums;
  SOTA `n^{1−1/2880}`, half a power short).  Carried as a named hypothesis.

`(I) ∧ (II) ⟹ EffectiveConductorBound` is then **pure arithmetic**, proven below — that is the entire
provable content of "the monodromy/conductor toolkit".  The toolkit does NOT discharge (I) or (II): (I)
needs unformalised étale machinery; (II) IS the open problem.  Honest modular scaffolding, no fabrication.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.CumulantGaussPeriodBound
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.KatzEffectiveGaussSum

namespace ArkLib.ProximityGap.MonodromyConductorScaffold

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **(I) Deligne effective equidistribution (Weil II), as a named hypothesis.**  The cumulant deviates
from the real-Gaussian (Wick) value by at most `cond · √q`, where `cond` is the conductor of the relevant
hypergeometric sheaf at order `r`.  This is Deligne's theorem of arithmetic geometry applied to the
Gauss-sum family — TRUE but not formalisable in current Mathlib (no étale cohomology), hence a hypothesis. -/
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

/-- **The monodromy/conductor toolkit, its entire provable content.**  Deligne effective equidistribution
(I) plus the geometric conductor bound (II) yield `EffectiveConductorBound` — and hence, via
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
chain pins `δ*` at the prize floor — conditional ONLY on (I) Deligne Weil II for this family and (II) the
`K = O(1)` conductor bound (the open core).  Everything between is machine-checked. -/
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
