/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail

/-!
# The hypercontractive / sub-Gaussian route IS the Wick wall — no escape (#444, route wf-F1)

**Route under test (wf-F1).** Does the Gauss period `η_b = ∑_{y∈G} ψ(b·y)`, viewed as a random
variable `X = |η|` over the *frequency group* `b ∈ F_q`, have a `(2,2r)`-hypercontractive /
sub-Gaussian moment structure — `‖X‖_{2r} ≤ C·√r·‖X‖_2` — that would yield the Wick bound and hence
the prize sup-norm floor `M ≤ C'·√(n log q)` via a Bonami–Beckner / log-Sobolev argument on the
character group?

**This file proves the route does NOT supply an independent bound: the hypercontractive inequality,
with its *sharp* sub-Gaussian (Wick) constant, is LOGICALLY EQUIVALENT to `GaussianEnergyBound`
(Route B's named open core).** It is a reformulation, not an escape.

Concretely, normalise `X` over the full frequency space `F_q` (uniform `b`):
`‖X‖_{2r}^{2r} = (1/q)·∑_b ‖η_b‖^{2r}` and `‖X‖_2^2 = (1/q)·∑_b ‖η_b‖^2 = |G| = n`
(the in-tree moment identities `subgroup_gaussSum_moment` and `subgroup_gaussSum_secondMoment`).
The sub-Gaussian moment bound `‖X‖_{2r}^{2r} ≤ (2r−1)‼·(‖X‖_2^2)^r` then reads, after multiplying by
`q`, as `∑_b ‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` — i.e. `E_r ≤ (2r−1)‼·n^r`, which is exactly the named
`GaussianEnergyBound G r`. We prove this equivalence as a clean `↔` (the powered, root-free form, so
no real-exponent analysis is needed).

**Honest verdict (route REDUCES TO WICK AT LOG DEPTH — no escape).** A genuine hypercontractive
attack would need to *produce* the constant from an external log-Sobolev / noise-operator structure
on `(F_q, μ_n)`. The companion probes (`scripts/probes/probe_dsar_hypercontractivity_wf_F1.py`,
`probe_dsar_hyperc_constant_growth_wf_F1.py`) show by exact FFT that no such *free* structure exists:
at the maximally 2-adically resonant prime `p = 65537 = 2^16+1` the period family is measurably
**super-Gaussian** (`‖X‖_{2r}/‖X‖_2` exceeds the sub-Gaussian envelope `((2r−1)‼)^{1/2r}` by a factor
growing to ≈ 1.43 in `r`), so the textbook `(2,4)`-Bonami–Beckner step that would bootstrap the
higher moments FAILS — the 4th/6th-moment excess (kurtosis up to 4.78) is the obstruction. Hence the
hypercontractive constant the route needs *is* the BGK / Paley-graph eigenvalue ratio
`C = M/√(2 n log q)` itself; bounding it = proving the open core. This file makes that "no escape"
rigorous: the hypercontractive bound and the Wick bound are the *same* proposition.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #444.
-/

set_option linter.style.longLine false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ProximityGap.Frontier.HypercontractiveWickEquivalence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The `(2,2r)`-hypercontractive / sub-Gaussian moment bound on the period family, root-free.**

Over the uniform frequency space `b ∈ F_q`, with `X = ‖η‖`, this is
`‖X‖_{2r}^{2r} ≤ (2r−1)‼·(‖X‖_2^2)^r`, written in unnormalised (powered, `×q`) form as

> `∑_b ‖η_b‖^{2r} ≤ (2r−1)‼ · n^{r−1} · (∑_b ‖η_b‖^2)`.

This is the *sharp* sub-Gaussian shape: `L^{2r}` controlled by `L^2` with the exact Wick constant
`((2r−1)‼)^{1/2r} ∼ √(2r/e)`, which is precisely what a Bonami–Beckner hypercontractive estimate
would deliver. -/
def HypercontractiveMomentBound (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : Prop :=
  ∑ b : F, ‖eta ψ G b‖ ^ (2 * r)
    ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ (r - 1) * (∑ b : F, ‖eta ψ G b‖ ^ 2)

/-- **The L² normalisation: `∑_b ‖η_b‖² = q·n`, so `‖X‖_2^2 = n`.** (Restatement of the in-tree exact
second moment, the denominator of the hypercontractive ratio.) -/
theorem l2_sq_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * (G.card : ℝ) :=
  subgroup_gaussSum_secondMoment hψ G

/-- **No escape (the equivalence theorem).** For `r ≥ 1`, the `(2,2r)`-hypercontractive / sub-Gaussian
moment bound on the Gauss-period family with its sharp Wick constant is *logically equivalent* to the
named open core `GaussianEnergyBound G r` (`E_r ≤ (2r−1)‼·n^r`).

So the hypercontractivity route is a reformulation of Route B's Wick wall, not an independent bound:
proving the hypercontractive inequality at depth `r ∼ log q` (the depth the prize floor needs) is
*exactly* proving the char-`p` Wick energy bound at that depth — the recognised open BGK / Paley core.
Proof: the full-frequency moment identities `∑_b ‖η‖^{2r} = q·E_r` and `∑_b ‖η‖^2 = q·n` turn both
sides into `q·E_r ≤ q·(2r−1)‼·n^r`, cancellable since `q > 0`. -/
theorem hypercontractive_iff_wick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {r : ℕ} (hr : 1 ≤ r) :
    HypercontractiveMomentBound ψ G r ↔ GaussianEnergyBound G r := by
  classical
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F); exact_mod_cast this
  -- rewrite both moment sums via the in-tree identities
  have hmom : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) :=
    subgroup_gaussSum_moment hψ G r
  have hl2 : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * (G.card : ℝ) :=
    subgroup_gaussSum_secondMoment hψ G
  -- the RHS of the hypercontractive bound: (2r-1)!!·n^{r-1}·(q·n) = q·(2r-1)!!·n^r
  have hrhs :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ (r - 1)
          * (∑ b : F, ‖eta ψ G b‖ ^ 2)
        = (Fintype.card F : ℝ)
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
    rw [hl2]
    have hpow : (G.card : ℝ) ^ (r - 1) * (G.card : ℝ) = (G.card : ℝ) ^ r := by
      rw [← pow_succ]
      congr 1
      omega
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ (r - 1)
            * ((Fintype.card F : ℝ) * (G.card : ℝ))
        = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * ((G.card : ℝ) ^ (r - 1) * (G.card : ℝ)) := by ring
      _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
            rw [hpow]
      _ = (Fintype.card F : ℝ)
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by ring
  constructor
  · intro h
    unfold HypercontractiveMomentBound at h
    rw [hmom, hrhs] at h
    -- q·E_r ≤ q·(Wick) ⟹ E_r ≤ Wick
    unfold GaussianEnergyBound
    exact le_of_mul_le_mul_left h hqpos
  · intro h
    unfold GaussianEnergyBound at h
    unfold HypercontractiveMomentBound
    rw [hmom, hrhs]
    exact mul_le_mul_of_nonneg_left h hqpos.le

/-- **Consumer corollary: the proven `r = 1` base case in hypercontractive form.** The exact second
moment gives the `r = 1` instance of the hypercontractive bound unconditionally (`E_1 = n` ≤ `1·n`),
confirming the equivalence is non-vacuous at the base; the open content is `r ∼ log q`. -/
theorem hypercontractive_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    HypercontractiveMomentBound ψ G 1 := by
  rw [hypercontractive_iff_wick hψ G (le_refl 1)]
  -- GaussianEnergyBound G 1 : E_1 ≤ 1·n.  E_1 = #{x=y} = |G|, and (2·1−1)‼ = 1.
  unfold GaussianEnergyBound
  rw [ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_one]
  simp [Nat.doubleFactorial]

end ProximityGap.Frontier.HypercontractiveWickEquivalence

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.HypercontractiveWickEquivalence.l2_sq_eq
#print axioms ProximityGap.Frontier.HypercontractiveWickEquivalence.hypercontractive_iff_wick
#print axioms ProximityGap.Frontier.HypercontractiveWickEquivalence.hypercontractive_one
